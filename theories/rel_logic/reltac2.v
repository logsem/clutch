(* The tactics in this file are a more performant but less general alternative
to the tactics in rel_tactics. The essential difference is that the tactics for
symbolic evaluation defined here syntactically traverse the goal to find the
redex, which is unique, by definition of the operational semantics. Instead
rel_tactics is heavily unification based. In some scenarios, the unification
may succeed in applying a tactic when reltac2 does not. The advantage of
reltac2 on the other hand is better performance and the ability to generate
(Coq and Iris) names for variables from the variable names used in the program.
If the head of the redex expression is a folded (local or global) definition,
reltac2 tries to unfold the definition enough to proceed with evaluation.

For instance, with e ≜ `let: "c" := ref 42 in k`, if `e` occurs on the
left-hand side of a refinement and the expression `ref 42` is the redex, then
invoking `iredl` will introduce `c : loc` and `"c" : c ↦ #42`. If `e` occurs as
part of the spec, i.e. on the right, the names are instead sub-scripted with
"ₛ", and we get `cₛ : loc` and `"cₛ" : cₛ ↦ₛ #42`. *)

From Coq Require Import ZArith String.

From clutch.prelude Require Import stdpp_ext.
From clutch.prob_lang Require Import lang.
From clutch.rel_logic Require Import model rel_rules rel_tactics.

From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require String Char Fresh Ident.

Ltac2 rec ltac_int_of_pos (p : constr) : int :=
  let res :=
    lazy_match! p with
    | xH => 1
    | xO ?p' => Int.mul 2 (ltac_int_of_pos p')
    | xI ?p' => Int.add (Int.mul 2 (ltac_int_of_pos p')) 1
    end in
  if Int.lt res 0
  then Control.throw (Out_of_bounds (Some (fprintf "ltac_int_of_pos: value is too large: %t" p)))
  else res.

Ltac2 ltac_int_of_Z (z : constr) : int :=
  lazy_match! z with
  | Z0 => 0
  | Zpos ?p => ltac_int_of_pos p
  | Zneg ?p => Int.sub 0 (ltac_int_of_pos p)
  end.

Ltac2 ltac_char_of_ascii (c : constr) : char :=
  let c := constr:(Z.of_nat (Ascii.nat_of_ascii $c)) in
  let c := eval vm_compute in $c in
  Char.of_int (ltac_int_of_Z c).

Ltac2 ltac_string_of_string (s : constr) : string :=
  let s := eval vm_compute in $s in
  let rec ltac_copy_to_string (s : constr) (out : string) (i : int) : unit :=
    lazy_match! s with
    | EmptyString => ()
    | String ?c ?s => String.set out i (ltac_char_of_ascii c) ;
                      ltac_copy_to_string s out (Int.add i 1)
    end
  in
  let len := constr:(Z.of_nat (String.length $s)) in
  let len := eval vm_compute in $len in
  let out := String.make (ltac_int_of_Z len) (Char.of_int 0) in
  ltac_copy_to_string s out 0 ;
  out.

Ltac2 ident_of_cstring cs :=
  let s := ltac_string_of_string cs in
  match Ident.of_string s with
  | None => Control.throw (Tactic_failure (Some (fprintf "invalid ident: %t" cs)))
  | Some i => i
  end.

Ltac2 fresh_ident_of_cstring cs :=
  let i := ident_of_cstring cs in
  Fresh.fresh (Fresh.Free.of_goal ()) i.

Ltac2 i_eval_at_redex fpure falloc fload fstore falloctape frand fforeign tm :=
  let rec f name tm k :=
    let f' := f in
    let f tm k := f' None tm k in
    lazy_match! tm with
    | Val _ => ()
    | Var ?v =>
        Message.print (fprintf "Warning: bare variable %t" v)
    | (Rec _ _ _)             => fpure tm k
    | App ?e1 ?e2 =>
        lazy_match! e2 with
        | Val ?v =>
            lazy_match! e1 with
            | Val _ => fpure tm k
            | _ => f e1 constr:(AppLCtx $v :: $k)
            end
        | _ =>
            let argname :=
              lazy_match! e1 with
              | (Rec _ (BNamed ?argname) _) => Some argname
              | Val (RecV _ (BNamed ?argname) _) => Some argname
              | _ => None
              end in
            f' argname e2 constr:(AppRCtx $e1 :: $k)
        end
    | UnOp _ (Val _)          => fpure tm k
    | UnOp ?e ?tm              => f tm constr:(UnOpCtx $e :: $k)
    | BinOp ?op ?e1 ?e2 =>
        lazy_match! e2 with
        | Val ?v =>
            lazy_match! e1 with
            | Val _ => fpure tm k
            | _ => f e1 constr:(BinOpLCtx $op $v :: $k)
            end
        | _ => f e2 constr:(BinOpRCtx $op $e1 :: $k)
        end
    | If (Val _) _ _          => fpure tm k
    | If ?tm ?e1 ?e2          => f tm constr:(IfCtx $e1 $e2 :: $k)
    | Pair ?e1 ?e2 =>
        lazy_match! e2 with
        | Val ?v =>
            lazy_match! e1 with
            | Val _ => fpure tm k
            | _ => f e1 constr:(PairLCtx $v :: $k)
            end
        | _ => f e2 constr:(PairRCtx $e1 :: $k)
        end
    | Fst (Val _)             => fpure tm k
    | Fst ?tm                 => f tm constr:(FstCtx :: $k)
    | Snd (Val _)             => fpure tm k
    | Snd ?tm                 => f tm constr:(SndCtx :: $k)
    | InjL (Val _)            => fpure tm k
    | InjL ?tm                => f tm constr:(InjLCtx :: $k)
    | InjR (Val _)            => fpure tm k
    | InjR ?tm                => f tm constr:(InjRCtx :: $k)
    | Case (Val _) _ _        => fpure tm k
    | Case ?tm ?e1 ?e2        => f tm constr:(CaseCtx $e1 $e2 :: $k)
    | (Alloc (Val _))         => falloc tm k name
    | (Alloc ?tm)             => f tm constr:(AllocCtx :: $k)
    | (Load (Val _))          => fload tm k
    | (Load ?tm)              => f tm constr:(LoadCtx :: $k)
    | Store ?e1 ?e2 =>
        lazy_match! e2 with
        | Val ?v =>
            lazy_match! e1 with
            | Val _ => fstore tm k
            | _ => f e1 constr:(StoreLCtx $v :: $k)
            end
        | _ => f e2 constr:(StoreRCtx $e1 :: $k)
        end
    | AllocTape (Val _)       => falloctape tm k name
    | AllocTape ?tm           => f tm constr:(AllocTapeCtx :: $k)
    | Rand ?e1 ?e2 =>
        lazy_match! e2 with
        | Val ?v =>
            lazy_match! e1 with
            | Val _ => frand tm k name
            | _ => f e1 constr:(RandLCtx $v :: $k)
            end
        | _ => f e2 constr:(RandRCtx $e1 :: $k)
        end
    | _ => fforeign tm k name
    end
  in
  f None tm constr:(@nil ectx_item).

Ltac2 foreign_unfold tm k name :=
  let rec app_head e := lazy_match! e with ?e _ => app_head e | _ => e end in

  let unfold_it tm := ltac1:(tm |- unfold tm at 1) (Ltac1.of_constr tm) in
  let tm := app_head tm in
  match Constr.Unsafe.kind tm with
  | Constr.Unsafe.Var i  =>
      (* printf "Var" ; *)
      (* Std.unfold [(Std.VarRef i , Std.AllOccurrences)] *)
      (*   ({Std.on_hyps := None ; Std.on_concl := (Std.OnlyOccurrences [1])}) *)
      unfold_it tm
  | Constr.Unsafe.Constant _ _  =>
      unfold_it tm
  | _ => printf "foreign_unfold: can't unfold %t" tm
  end
.

Ltac2 Type side := [ L | R ].

Ltac2 rec ired side fpure falloc fload fstore falloctape frand fforeign :=
  lazy_match! goal with
  | [ |- context[⊢ (refines _ ?lhs ?rhs _)] ] =>
      ltac1:(iStartProof) ; ired side fpure falloc fload fstore falloctape frand fforeign
  | [ |- context[environments.envs_entails _ (refines _ ?lhs ?rhs _)] ] =>
      match side with
      | L => i_eval_at_redex fpure falloc fload fstore falloctape frand fforeign lhs
      | R => i_eval_at_redex fpure falloc fload fstore falloctape frand fforeign rhs
      end
  | [ |- _ ] => Control.throw (Tactic_failure (Some (fprintf "ired: Not proving a refinement.")))
  end.

Ltac2 rel_pure_l (tm : constr) (k : constr) := ltac1:(ef kf |- rel_pure_l ef in kf) (Ltac1.of_constr tm) (Ltac1.of_constr k).
Ltac2 rel_pure_r (tm : constr) (k : constr) := ltac1:(ef kf |- rel_pure_r ef in kf) (Ltac1.of_constr tm) (Ltac1.of_constr k).
Ltac2 rel_load_l (tm : constr) (k : constr) := ltac1:(ef kf |- rel_load_l ef in kf) (Ltac1.of_constr tm) (Ltac1.of_constr k).
Ltac2 rel_load_r (tm : constr) (k : constr) := ltac1:(ef kf |- rel_load_r ef in kf) (Ltac1.of_constr tm) (Ltac1.of_constr k).
Ltac2 rel_store_l (tm : constr) (k : constr) := ltac1:(ef kf |- rel_store_l ef in kf) (Ltac1.of_constr tm) (Ltac1.of_constr k).
Ltac2 rel_store_r (tm : constr) (k : constr) := ltac1:(ef kf |- rel_store_r ef in kf) (Ltac1.of_constr tm) (Ltac1.of_constr k).

Ltac2 rel_named_l name fnone fsome :=
  match name with
  | None => fnone ()
  | Some name => let i := Ltac1.of_ident (fresh_ident_of_cstring name) in
                 let cs := Ltac1.of_constr name in
                 fsome i cs
  end.

Ltac2 rel_named_r name fnone fsome :=
  match name with
  | None => fnone ()
  | Some name => let name := constr:(String.append $name "ₛ") in
                 let name := (eval vm_compute in $name) in
                 let i := Ltac1.of_ident (fresh_ident_of_cstring name) in
                 let cs := Ltac1.of_constr name in
                 fsome i cs
  end.

Ltac2 rel_alloc_l tm k name :=
  let ef := Ltac1.of_constr tm in
  let kf := Ltac1.of_constr k in
  rel_named_l name (fun () => ltac1:(ef kf |- rel_alloc_l ? as "?" at ef in kf) ef kf)
    (fun i cs => ltac1:(i cs ef kf |-
                          first [ rel_alloc_l i as cs at ef in kf
                                | let cs' := iFresh in rel_alloc_l i as cs' at ef in kf ]
                       ) i cs ef kf).

Ltac2 rel_alloc_r tm k name :=
  let ef := Ltac1.of_constr tm in
  let kf := Ltac1.of_constr k in
  rel_named_r name (fun () => ltac1:(ef kf |- rel_alloc_r ? as "?" at ef in kf) ef kf)
    (fun i cs => ltac1:(i cs ef kf |-
                          first [ rel_alloc_r i as cs at ef in kf
                                | let cs' := iFresh in rel_alloc_r i as cs' at ef in kf ]
                       ) i cs ef kf).

Ltac2 rel_alloctape_l tm k name :=
  let ef := Ltac1.of_constr tm in
  let kf := Ltac1.of_constr k in
  rel_named_l name (fun () => ltac1:(ef kf |- rel_alloctape_l ? as "?" at ef in kf) ef kf)
    (fun i cs => ltac1:(i cs ef kf |-
                          first [ rel_alloctape_l i as cs at ef in kf
                                | let cs' := iFresh in rel_alloctape_l i as cs' at ef in kf ]
                       ) i cs ef kf).

Ltac2 rel_alloctape_r tm k name :=
  let ef := Ltac1.of_constr tm in
  let kf := Ltac1.of_constr k in
  rel_named_r name (fun () => ltac1:(ef kf |- rel_alloctape_r ? as "?" at ef in kf) ef kf)
    (fun i cs => ltac1:(i cs ef kf |-
                          first [ rel_alloctape_r i as cs at ef in kf
                                | let cs' := iFresh in rel_alloctape_r i as cs' at ef in kf ]
                       ) i cs ef kf).

Ltac2 rel_randT_empty_l tm k name :=
  let kf := Ltac1.of_constr k in
  ltac1:(kf |- rel_apply_l (refines_randT_empty_l kf) ; iFrame ) kf ;
  rel_named_l name (fun () => ltac1:(iIntros "!>" (?) "?"))
    (fun i cs => ltac1:(i cs |-
                          first [ iIntros "!>" (i) cs
                                | let cs' := iFresh in iIntros "!>" (i) cs' ]
                       ) i cs).

Ltac2 rel_randT_empty_r tm k name :=
  let kf := Ltac1.of_constr k in
  ltac1:(kf |- rel_apply_r (refines_randT_empty_r kf) ; [reflexivity|iFrame] ) kf ;
  rel_named_r name (fun () => ltac1:(iIntros (?) "?"))
    (fun i cs => ltac1:(i cs |-
                          first [ iIntros (i) cs
                                | let cs' := iFresh in iIntros (i) cs' ]
                       ) i cs).

Ltac2 rel_randU_l tm k name :=
  let kf := Ltac1.of_constr k in
  ltac1:( kf |- rel_apply_l (refines_randU_l _ _) ; iFrame ) kf ;
  rel_named_l name (fun () => ltac1:(iIntros (?)))
    (fun i _ => ltac1:(i |- iIntros (i)) i).

Ltac2 rel_randU_r tm k name :=
  let kf := Ltac1.of_constr k in
  ltac1:( kf |- rel_apply_r refines_randU_r ; [reflexivity|iFrame] ) kf ;
  rel_named_r name (fun () => ltac1:(iIntros (?)))
    (fun i _ => ltac1:(i |- iIntros (i)) i).

Ltac2 rel_randT_l tm k name :=
  lazy_match! tm with
  | Rand _ (Val (LitV (LitLbl _))) =>
      ltac1:(ef kf |- rel_rand_l ef in kf ) (Ltac1.of_constr tm) (Ltac1.of_constr k)
  | _ => () end.

Ltac2 rel_randT_r tm k name :=
  lazy_match! tm with
  | Rand _ (Val (LitV (LitLbl _))) =>
      ltac1:(ef kf |- rel_rand_r ef in kf ) (Ltac1.of_constr tm) (Ltac1.of_constr k)
  | _ => () end.

#[local] Ltac2 ign2 := fun _ _ => ().
#[local] Ltac2 ign3 := fun _ _ _ => ().

(* Parametrised rand only tactical *)
Ltac2 ired_rand_r frand := ired R ign2 ign3 ign2 ign2 ign3 frand ign3.
Ltac2 ired_rand_l frand := ired L ign2 ign3 ign2 ign2 ign3 frand ign3.

(* One step of pure reduction *)
Ltac2 iredpurer () := ired R rel_pure_r ign3 ign2 ign2 ign3 ign3 foreign_unfold.
Ltac iredpurer := ltac2:(iredpurer ()).
Ltac2 iredpurel () := ired L rel_pure_l ign3 ign2 ign2 ign3 ign3 foreign_unfold.
Ltac iredpurel := ltac2:(iredpurel ()).

(* Iterated pure reduction *)
Ltac2 iredpuresr () := repeat (iredpurer ()).
Ltac iredpuresr := ltac2:(iredpuresr ()).
Ltac2 iredpuresl () := repeat (iredpurel ()).
Ltac iredpuresl := ltac2:(iredpuresl ()).

(* One step of possibly effectful reduction; rand can only read from tapes *)
Ltac2 iredall_r frand := ired R rel_pure_r rel_alloc_r rel_load_r rel_store_r rel_alloctape_r frand foreign_unfold.
Ltac2 iredr () := iredall_r rel_randT_r.
Ltac iredr := ltac2:(iredr ()).
Ltac2 iredall_l frand := ired L rel_pure_l rel_alloc_l rel_load_l rel_store_l rel_alloctape_l frand foreign_unfold.
Ltac2 iredl () := iredall_l rel_randT_l.
Ltac iredl := ltac2:(iredl ()).

(* Iterated effectful reduction *)
Ltac2 iredrs () := repeat (iredr ()).
Ltac iredrs := ltac2:(iredrs ()).
Ltac2 iredls () := repeat (iredl ()).
Ltac iredls := ltac2:(iredls ()).

(* Iterated reduction on both sides *)
Ltac ireds := iredrs ; iredls.
Ltac iredpures := iredpuresr ; iredpuresl.

(* Single step of reading from a tape, no other effects. *)
Ltac rel_randT_l := ltac2:(ired_rand_l rel_randT_l).
Ltac rel_randT_r := ltac2:(ired_rand_r rel_randT_r).

(* Single step of sampling an empty tape, no other effects. *)
Ltac rel_randT_empty_l := ltac2:(ired_rand_l rel_randT_empty_l).
Ltac rel_randT_empty_r := ltac2:(ired_rand_r rel_randT_empty_r).

(* Single step of unlabelled sampling, no other effects. *)
Ltac rel_randU_l := ltac2:(ired_rand_l rel_randU_l).
Ltac rel_randU_r := ltac2:(ired_rand_r rel_randU_r).

Ltac2 rel_couple_TT bij tapes tm k name :=
  let kf := Ltac1.of_constr k in
  let tps := Ltac1.of_constr tapes in
  let tpsi := constr:(String.append "[ " (String.append $tapes " ]")) in
  let tpsi := Ltac1.of_constr (eval vm_compute in $tpsi) in
  match bij with
  | None => ltac1:(tps kf |- rel_apply (refines_couple_TT) ; [reflexivity|] ; iFrame tps) tps kf
  | Some bij =>
      ltac1:(bij tps kf |- rel_apply (refines_couple_TT _ bij) ; [reflexivity|] ; iFrame tps) bij tps kf
  end ;
  rel_named_l name (fun () => ltac1:(iIntros (?) "[??]"))
    (fun i cs => ltac1:(i tpsi |- iIntros (i) tpsi) i tpsi).

Tactic Notation "rel_couple_TT" constr(tapes) open_constr(bij) :=
  let f :=
    ltac2:(bij tapes |- ired_rand_l
                          (rel_couple_TT (Some bij)
                             (Option.get (Ltac1.to_constr tapes)))) in
  f bij tapes.

Tactic Notation "rel_couple_TT" constr(tapes) :=
  let f := ltac2:(tapes |- ired_rand_l
                             (rel_couple_TT None (Option.get (Ltac1.to_constr tapes))))
  in f tapes.

Ltac2 rel_couple_UU bij tm k name :=
  let kf := Ltac1.of_constr k in
  match bij with
  | None => ltac1:(kf |- rel_apply (refines_couple_UU _ _ kf)) kf
  | Some bij => ltac1:(bij kf |- rel_apply (refines_couple_UU _ bij kf)) bij kf
  end ;
  rel_named_l name (fun () => ltac1:(iIntros "!>" (?)))
    (fun i cs => ltac1:(i |- iIntros "!>" (i)) i).

Tactic Notation "rel_couple_UU" open_constr(bij) :=
  let f := ltac2:(bij |- ired_rand_l (rel_couple_UU (Some bij))) in f bij.

Tactic Notation "rel_couple_UU" := ltac2:(|- ired_rand_l (rel_couple_UU None)).

Ltac2 rel_couple_UT bij tapes tm k name :=
  let kf := Ltac1.of_constr k in
  let tpsf := constr:(String.append "[ -$" (String.append $tapes " ]")) in
  let tpsf := Ltac1.of_constr (eval vm_compute in $tpsf) in

  match bij with
  | None => ltac1:(tpsf kf |- rel_apply (refines_couple_UT _ _ kf with tpsf) ) tpsf kf
  | Some bij => ltac1:(bij tpsf kf |- rel_apply (refines_couple_UT _ bij kf with tpsf) ) bij tpsf kf
  end
  (* ltac1:(tpsf kf |- rel_apply (refines_couple_UT _ _ kf with tpsf) ) tpsf kf *)
  ;
  rel_named_l name (fun () => ltac1:(tapes |- iIntros "!>" (?) tapes) (Ltac1.of_constr tapes))
    (fun i cs => ltac1:(tapes i cs |- iIntros "!>" (i) tapes) (Ltac1.of_constr tapes) i cs)
.

Tactic Notation "rel_couple_UT" constr(tapes) :=
  let f := ltac2:(tapes |- ired_rand_l (rel_couple_UT None (Option.get (Ltac1.to_constr tapes))))
  in f tapes.

Tactic Notation "rel_couple_UT" constr(tapes) open_constr(bij) :=
  let f := ltac2:(bij tapes |- ired_rand_l (rel_couple_UT (Some bij) (Option.get (Ltac1.to_constr tapes))))
  in f bij tapes.

Ltac2 rel_couple_TU bij tapes tm k name :=
  let kf := Ltac1.of_constr k in
  let tpsf := constr:(String.append "[ -$" (String.append $tapes " ]")) in
  let tpsf := Ltac1.of_constr (eval vm_compute in $tpsf) in

  match bij with
  | None =>
      ltac1:(tpsf kf |- rel_apply (refines_couple_TU _ _ kf with tpsf) ; [reflexivity|] ) tpsf kf
  | Some bij =>
      ltac1:(bij tpsf kf |- rel_apply (refines_couple_TU _ bij kf with tpsf) ; [reflexivity|] ) bij tpsf kf
  end
  ;
  rel_named_l name (fun () => ltac1:(tapes |- iIntros (?) tapes) (Ltac1.of_constr tapes))
    (fun i cs => ltac1:(tapes i cs |- iIntros (i) tapes) (Ltac1.of_constr tapes) i cs)
.

Tactic Notation "rel_couple_TU" constr(tapes) :=
  let f := ltac2:(tapes |- ired_rand_r (rel_couple_TU None (Option.get (Ltac1.to_constr tapes))))
  in f tapes.

Tactic Notation "rel_couple_TU" constr(tapes) open_constr(bij) :=
  let f := ltac2:(bij tapes |- ired_rand_r (rel_couple_TU (Some bij) (Option.get (Ltac1.to_constr tapes))))
  in f bij tapes.
