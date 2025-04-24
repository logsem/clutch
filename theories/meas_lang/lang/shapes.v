(* TODO: Clear imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From stdpp Require Import binders gmap countable.
From mathcomp Require Import functions classical_sets.
From mathcomp.analysis Require Import reals measure lebesgue_measure.
From mathcomp Require Import boolp choice.
From clutch.prelude Require Export base classical.
From clutch.meas_lang.lang Require Export prelude types.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

(** Shapes: Trees with Unit as leaves.
    Used to prove that functions in the expr algebra are measurable *)

Definition base_lit_shape : Type := @base_lit_pre () () () ().
Definition val_shape      : Type := @val_pre () () () ().
Definition expr_shape     : Type := @expr_pre () () () ().

(** Get the shape of an expression *)

Definition shape_base_lit {T1 T2 T3 T4} : @base_lit_pre T1 T2 T3 T4 -> base_lit_shape :=
 base_lit_pre_F (cst ()) (cst ()) (cst ()) (cst ()) (cst ()).

Definition shape_val {T1 T2 T3 T4} : @val_pre T1 T2 T3 T4 -> val_shape :=
 val_pre_F (cst ()) (cst ()) (cst ()) (cst ()) (cst ()).

Definition shape_expr {T1 T2 T3 T4} : @expr_pre T1 T2 T3 T4 -> expr_shape :=
 expr_pre_F (cst ()) (cst ()) (cst ()) (cst ()) (cst ()).


(** Get a generator for all expressions with a given shape *)

Definition gen_base_lit : base_lit_shape -> base_lit_S :=
 base_lit_pre_F (cst setT) (cst setT) (cst setT) (cst setT) (cst setT).

Definition gen_val : val_shape -> val_S :=
 val_pre_F (cst setT) (cst setT) (cst setT) (cst setT) (cst setT).

Definition gen_expr : expr_shape -> expr_S :=
 expr_pre_F (cst setT) (cst setT) (cst setT) (cst setT) (cst setT).


Lemma gen_base_lit_generator s : base_lit_ML (gen_base_lit s).
Proof.
  rewrite /base_lit_ML/gen_base_lit/base_lit_pre_F.
  destruct s; try done; by eapply @measurableT.
Qed.

(** gen-* are generators for their respective sigma algebras *)
Lemma gen_val_generator s : val_ML (gen_val s).
Proof.
  apply (val_pre_mut _ _ _ _ (fun s => expr_ML (gen_expr s)) (fun s => val_ML (gen_val s))).
  all: try by move=>*//=.
  by apply gen_base_lit_generator.
Qed.

Lemma gen_expr_generator s : expr_ML (gen_expr s).
Proof.
  apply (expr_pre_mut _ _ _ _ (fun s => expr_ML (gen_expr s)) (fun s => val_ML (gen_val s))).
  all: try by move=>*//=.
  by apply gen_base_lit_generator.
Qed.


(** The set of all expressions with a given shape is singly generated *)
Lemma base_lit_shape_cyl (s : base_lit_shape) : [set e | shape_base_lit e = s] = base_lit_ST (gen_base_lit s).
Proof.
  apply /predeqP =>b.
  destruct b; simpl.
  all: split; [ by move <-; rewrite //=; eexists _; eauto | ].
  all: move=> H.
  all: destruct s as [x|x| |x|x|x]; simpl in H.
  all: try done.
  all: try by destruct H as [? ?].
  all: by destruct x.
Qed.

Lemma expr_shape_cyl (s : expr_shape) : [set e | shape_expr e = s] = expr_ST (gen_expr s).
Proof.
  rewrite eqEsubset; split; intros e; simpl.
  - intros <-. revert e. fix FIX 1.
    intros [v|?|???|??|??|???|???|??|?|?|?|?|???|?|?|??|?|??| |?|?]; simpl. 
    { exists v; last done.
      revert v. fix FIX' 1.
      intros [l|f x e|v1 v2| | ]; simpl.
      - exists l; last done. rewrite -base_lit_shape_cyl/=. done.
      - eexists _; last done. apply FIX.
      - eexists _; last eexists _.
        + apply FIX'.
        + apply FIX'.
        + done. 
      - eexists _; last done. apply FIX'.
      - eexists _; last done. apply FIX'.
    }
    all: try done; eexists _; try done; try apply FIX.
    all: try eexists _; try done; try apply FIX.
    all: try eexists _; try done; apply FIX.
  - revert s e.
    fix FIX 1.
    intros s e.
    destruct s as [s| | | | | | | | | | | | | | | | | | | | ].
    (* val case *)
    { simpl.
      intros [v ?]; subst.
      revert s v H.
      fix FIX' 1.
      intros s v.
      destruct s as [l| | | |].
      - destruct l as [[]|[]| |[]|[]|[]]; simpl.
        + intros [?[?[]]]; by subst. 
        + intros [?[?[]]]; by subst. 
        + intros [??]; subst. by subst.
        + intros [?[?[]]]; by subst. 
        + intros [?[?[]]]; by subst.
        + intros [?[?[]]]; by subst.
      - simpl.
        intros [? ]; subst.
        rewrite /shape_expr. simpl. f_equal. f_equal.
        by apply FIX in H. 
      - simpl. intros [? H [? H']]; subst.
        apply FIX' in H. apply FIX' in H'.
        rewrite /shape_expr/= in H H' *. by simplify_eq.
      - intros [? H]; subst.
        apply FIX' in H. rewrite /shape_expr in H *. simpl in *. by simplify_eq.
      - intros [? H]; subst.
        apply FIX' in H. rewrite /shape_expr in H *. simpl in *. by simplify_eq.
    }
    all: simpl.
    all: try (intros [??]; subst; rewrite /shape_expr/=; f_equal; by apply FIX).
    all: try by intros ->.
    all: try (intros [??[]]; subst; rewrite /shape_expr/=; f_equal; by apply FIX).
    all: try (intros [??[??[]]]; subst; rewrite /shape_expr/=; f_equal; by apply FIX).
Qed.

Lemma val_shape_cyl (s : val_shape) : [set e | shape_val e = s] = val_ST (gen_val s).
Proof.
  rewrite eqEsubset; split; intros v; simpl.
  - intros <-. revert v. fix FIX 1.
      intros [l|f x e|v1 v2| | ]; simpl.
      + exists l; last done. rewrite -base_lit_shape_cyl/=. done.
      + eexists _; last done. rewrite <- expr_shape_cyl. done. 
      + eexists _; last eexists _; [apply FIX..|done].
      + eexists _; last done. apply FIX.
      + eexists _; last done. apply FIX.
  - revert s v. fix FIX 1.
    intros s v. destruct s as [l| | | |].
    + destruct l as [[]|[]| |[]|[]|[]]; simpl.
      * intros [?[]]; by subst. 
      * intros [?[]]; by subst. 
      * intros [??]; by subst.
      * intros [?[]]; by subst. 
      * intros [?[]]; by subst.
      * intros [?[]]; by subst.
    + simpl.
      intros [? H <-].
      rewrite <-expr_shape_cyl in H; simpl in *. by subst.
    + simpl. intros [? ?[]]; subst.
      rewrite /shape_val/=. f_equal; by apply FIX.
    + simpl. intros [??[]]. rewrite /shape_val/=; f_equal. by apply FIX.
    + simpl. intros [??[]]. rewrite /shape_val/=; f_equal. by apply FIX.
Qed.

(** Decompose the set of expressions into a countable union over expr_shape *)

Local Open Scope positive.
Global Program Instance bin_op_countable : countable.Countable <<discr bin_op>> :=
  {|
    encode x := match x with
                | PlusOp => 14 | MinusOp => 1| MultOp =>2| QuotOp =>3| RemOp=>4 (* Arithmetic *)
                | AndOp => 5| OrOp => 6| XorOp=> 7 (* Bitwise *)
                | ShiftLOp => 8| ShiftROp => 9(* Shifts *)
                | LeOp => 10| LtOp => 11| EqOp => 12(* Relations *)
                | OffsetOp => 13 end (* Pointer offset *);
    decode p := match p with 
  | 14 => Some PlusOp | 1 => Some MinusOp | 2 => Some MultOp | 3 => Some QuotOp | 4 => Some RemOp (* Arithmetic *)
  | 5 => Some AndOp | 6 => Some OrOp | 7 => Some XorOp (* Bitwise *)
  | 8 => Some ShiftLOp | 9 => Some ShiftROp (* Shifts *)
  | 10 => Some LeOp | 11 => Some LtOp | 12 => Some EqOp (* Relations *)
                | 13 => Some OffsetOp (* Pointer offset *)
  | _ => None end
  |}.
Next Obligation. done. Qed.
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. done. Qed.
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. done. Qed.
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. by intros []. Qed.

Global Program Instance un_op_countable : countable.Countable <<discr un_op>> :={|
    encode x := match x with
                | NegOp => 1 | MinusUnOp => 2 end (* Pointer offset *);
    decode p := match p with 
  | 1 => Some NegOp | 2 => Some MinusUnOp | _ => None end
                                                                                |}.
Next Obligation. done. Qed.
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. by intros []. Qed.
Global Program Instance base_lit_pre_countable : countable.Countable (@base_lit_pre () () () ()) :={|
    encode x := match x with
                | LitInt _ => 1 | LitBool _ => 2
                | LitUnit => 3 | LitLoc _ => 4
                | LitLbl _ => 5 | LitReal _ => 6
                end (* Pointer offset *);
    decode p := match p with 
                | 1 => Some (LitInt ())| 2 => Some (LitBool ())
                | 3 => Some (LitUnit)| 4 => Some (LitLoc ())
                | 5 => Some (LitLbl ())| 6 => Some (LitReal ())| _ => None end
                                                                                |}.
Next Obligation. done. Qed.
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. done. Qed. 
Next Obligation. by intros [[]|[]| |[]|[]|[]]. Qed.
Local Close Scope positive.

Definition expr_shape_encode :=
  fix go (e:expr_shape) :=
     match e with
     | Val v => GenNode 0 [gov v]
     | Var x => GenLeaf (inl (inl x))
     | Rec f x e => GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | App e1 e2 => GenNode 2 [go e1; go e2]
     | UnOp op e => GenNode 3 [GenLeaf (inr (inr (inl op))); go e]
     | BinOp op e1 e2 => GenNode 4 [GenLeaf (inr (inr (inr op))); go e1; go e2]
     | If e0 e1 e2 => GenNode 5 [go e0; go e1; go e2]
     | Pair e1 e2 => GenNode 6 [go e1; go e2]
     | Fst e => GenNode 7 [go e]
     | Snd e => GenNode 8 [go e]
     | InjL e => GenNode 9 [go e]
     | InjR e => GenNode 10 [go e]
     | Case e0 e1 e2 => GenNode 11 [go e0; go e1; go e2]
     | Alloc e => GenNode 12 [go e]
     | Load e => GenNode 13 [go e]
     | Store e1 e2 => GenNode 14 [go e1; go e2]
     | AllocTape e => GenNode 15 [go e]
     | Rand e1 e2 => GenNode 16 [go e1; go e2]
     | AllocUTape => GenNode 17 []
     | URand e => GenNode 18 [go e]
     | Tick e => GenNode 19 [go e]
     end
   with gov v :=
     match v with
     | LitV l => GenLeaf (inr (inl l))
     | RecV f x e =>
        GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
     | InjLV v => GenNode 2 [gov v]
     | InjRV v => GenNode 3 [gov v]
     end
       for go.
Definition expr_shape_decode : _->expr_shape:=
  fix go e : expr_shape :=
     match e with
     | GenNode 0 [v] => Val (gov v)
     | GenLeaf (inl (inl x)) => Var x
     | GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => Rec f x (go e)
     | GenNode 2 [e1; e2] => App (go e1) (go e2)
     | GenNode 3 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
     | GenNode 4 [GenLeaf (inr (inr (inr op))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 [e0; e1; e2] => If (go e0) (go e1) (go e2)
     | GenNode 6 [e1; e2] => Pair (go e1) (go e2)
     | GenNode 7 [e] => Fst (go e)
     | GenNode 8 [e] => Snd (go e)
     | GenNode 9 [e] => InjL (go e)
     | GenNode 10 [e] => InjR (go e)
     | GenNode 11 [e0; e1; e2] => Case (go e0) (go e1) (go e2)
     | GenNode 12 [e] => Alloc (go e)
     | GenNode 13 [e] => Load (go e)
     | GenNode 14 [e1; e2] => Store (go e1) (go e2)
     | GenNode 15 [e] => AllocTape (go e)
     | GenNode 16 [e1; e2] => Rand (go e1) (go e2)
     | GenNode 17 [] => AllocUTape 
     | GenNode 18 [e1] => URand (go e1) 
     | GenNode 19 [e] => Tick (go e)
     | _ => Val $ LitV LitUnit (* dummy *)
     end
   with gov v :val_shape :=
     match v with
     | GenLeaf (inr (inl l)) => LitV l
     | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => RecV f x (go e)
     | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
     | GenNode 2 [v] => InjLV (gov v)
     | GenNode 3 [v] => InjRV (gov v)
     | _ => LitV LitUnit (* dummy *)
     end
       for go.

Lemma expr_shape_decode_encode e: expr_shape_decode (expr_shape_encode e) = e.
Proof.
  revert e.
  rewrite {1}/expr_shape_decode{1}/expr_shape_encode/=.
 refine (fix go (e : expr_shape) {struct e} := _ with gov (v : val_shape) {struct v} := _ for go).
  - destruct e as [v| | | | | | | | | | | | | | | | | | | |  ]; simpl; f_equal; [exact (gov v)|done..].
  - destruct v; by f_equal.
Qed.

Definition val_shape_encode v := expr_shape_encode (Val v).
Definition val_shape_decode t:= match expr_shape_decode t with | Val v => v | _ => LitV LitUnit end.
Lemma val_shape_decode_encode v : val_shape_decode (val_shape_encode v) = v.
Proof.
  by rewrite /val_shape_decode/val_shape_encode expr_shape_decode_encode.
Qed.

Definition expr_shape_enum (n : nat) : expr_shape :=
  match decode_nat n with
  | Some x => expr_shape_decode x
  | _ => Val $ LitV $ LitUnit
  end.

Definition val_shape_enum (n : nat) : val_shape:=
  match expr_shape_decode <$> (decode_nat n) with
  | Some (Val v) =>v
  | _ => LitV LitUnit
  end. 

Definition base_lit_shape_enum (n : nat) : base_lit_shape :=
  match decode_nat n with
  | Some x => x
  | _ => LitUnit
  end.
(* I only need surjectivity to prove that I don't miss any trees, so I'll use a definition
   of surjectivity appropriate for that (not the HB one, it gives us nothing) *)

Lemma expr_shape_enum_surj (e : expr_shape) : exists n, expr_shape_enum n = e.
Proof.
  exists (encode_nat (expr_shape_encode e)).
  rewrite /expr_shape_enum.
  rewrite decode_encode_nat.
  apply expr_shape_decode_encode.
Qed.

Lemma val_shape_enum_surj (e : val_shape) : exists n, val_shape_enum n = e.
Proof.
  exists (encode_nat (expr_shape_encode (Val e))).
  rewrite /val_shape_enum decode_encode_nat.
  Local Opaque expr_shape_decode expr_shape_encode. simpl.
  by rewrite expr_shape_decode_encode.
Qed.

Lemma base_lit_shape_enum_surj (e : base_lit_shape) : exists n, base_lit_shape_enum n = e.
Proof.
  exists (encode_nat e).
  rewrite /base_lit_shape_enum.
  by rewrite decode_encode_nat.
Qed.

Lemma binder_enum_surj (e : binder) : exists n, binder_enum n = e.
Proof. by eexists (Pos.to_nat (encode e)); rewrite /binder_enum Pos2Nat.id decode_encode //=. Qed.

Lemma un_op_enum_surj (e : un_op) : exists n, un_op_enum n = e.
Proof. destruct e; by [ exists 0 | exists 1 ]. Qed.

Lemma bin_op_enum_surj (e : bin_op) : exists n, bin_op_enum n = e.
Proof.
  destruct e; by [ exists 0 | exists 1 | exists 2 | exists 3 | exists 4 |
                   exists 5 | exists 6 | exists 7 | exists 8 | exists 9 |
                   exists 10 | exists 11 | exists 12 | exists 13].
Qed.

Definition base_lit_seq : sequences.sequence (set base_lit) :=
  fun n => shape_base_lit @^-1` [set base_lit_shape_enum n].

Definition expr_seq : sequences.sequence (set expr) :=
  fun n => shape_expr @^-1` [set expr_shape_enum n].

Definition val_seq : sequences.sequence (set val) :=
  fun n => shape_val @^-1` [set val_shape_enum n].

Lemma base_lit_shape_decompT : (\bigcup_n base_lit_seq n) = setT.
Proof.
  rewrite <- subTset => e He.
  case (base_lit_shape_enum_surj (shape_base_lit e)) as [n Hn].
  exists n; [done|].
  by rewrite /base_lit_seq Hn //=.
Qed.

Lemma expr_shape_decompT: (\bigcup_n expr_seq n) = setT.
Proof.
  rewrite <- subTset => e He.
  case (expr_shape_enum_surj (shape_expr e)) as [n Hn].
  exists n; [done|].
  by rewrite /expr_seq Hn //=.
Qed.

Lemma val_shape_decompT : (\bigcup_n val_seq n) = setT.
Proof.
  rewrite <- subTset => e He.
  case (val_shape_enum_surj (shape_val e)) as [n Hn].
  exists n; [done|].
  by rewrite /val_seq Hn //=.
Qed.


Lemma base_lit_shape_decomp S : (\bigcup_n (S `&` base_lit_seq n)) = S.
Proof. by rewrite <- setI_bigcupr, base_lit_shape_decompT, setIT. Qed.

Lemma expr_shape_decomp S : (\bigcup_n (S `&` expr_seq n)) = S.
Proof. by rewrite <- setI_bigcupr, expr_shape_decompT, setIT. Qed.

Lemma val_shape_decomp S : (\bigcup_n (S `&` val_seq n)) = S.
Proof. by rewrite <- setI_bigcupr, val_shape_decompT, setIT. Qed.

(*
Check @discr_generated_by_singletons binder.
Check @discr_generated_by_singletons un_op.
Check @discr_generated_by_singletons bin_op.
*)


(**  Lemma about discrete spaces

TODO: Refactor code to use discr_generated_by_singletons instead (7 total usages) then delete.
 *)

Definition binder_singletons : set (set <<discr binder>>) := fun S => exists b, S = [set b].
Definition un_op_singletons : set (set <<discr un_op>>) := fun S => exists b, S = [set b].
Definition bin_op_singletons : set (set <<discr bin_op>>) := fun S => exists b, S = [set b].

Lemma binder_generated_by_singletons : binder.-discr.-measurable = <<s binder_singletons >>.
Proof.
  apply /predeqP =>y //=.
  simpl in *.
  split.
  - move=> _.
    have ->: y = \bigcup_i ([set (binder_enum i)] `&` y).
    { rewrite /bigcup//=.
      apply /predeqP =>z /=.
      split.
      - move=> ?.
        destruct (binder_enum_surj z) as [i ?].
        by exists i.
      - by move=> [i ?][-> ?].
    }
    apply sigma_algebra_bigcup.
    move=> i.
    destruct (ExcludedMiddle (y (binder_enum i))).
    + apply sub_sigma_algebra.
      rewrite /binder_singletons/setI //=.
      exists (binder_enum i).
      apply /predeqP =>z /=.
      split.
      * by move=> [? ?].
      * by move=>->.
    + have -> : ([set binder_enum i] `&` y) = set0.
      { rewrite /setI//=.
      apply /predeqP =>z /=.
      split.
      + by move=>[-> ?].
      + by move=>?. }
      apply sigma_algebra0.
  - move=> _. by rewrite /measurable/=/discr_measurable/=.
Qed.

Lemma un_op_generated_by_singletons : un_op.-discr.-measurable = <<s un_op_singletons >>.
Proof.
  apply /predeqP =>y //=.
  simpl in *.
  split.
  - move=> _.
    have ->: y = \bigcup_i ([set (un_op_enum i)] `&` y).
    { rewrite /bigcup//=.
      apply /predeqP =>z /=.
      split.
      - move=> ?.
        destruct (un_op_enum_surj z) as [i ?].
        by exists i.
      - by move=> [i ?][-> ?].
    }
    apply sigma_algebra_bigcup.
    move=> i.
    destruct (ExcludedMiddle (y (un_op_enum i))).
    + apply sub_sigma_algebra.
      rewrite /binder_singletons/setI //=.
      exists (un_op_enum i).
      apply /predeqP =>z /=.
      split.
      * by move=> [? ?].
      * by move=>->.
    + have -> : ([set un_op_enum i] `&` y) = set0.
      { rewrite /setI//=.
      apply /predeqP =>z /=.
      split.
      + by move=>[-> ?].
      + by move=>?. }
      apply sigma_algebra0.
  - move=> _. by rewrite /measurable/=/discr_measurable/=.
Qed.

Lemma bin_op_generated_by_singletons : bin_op.-discr.-measurable = <<s bin_op_singletons >>.
Proof.
  apply /predeqP =>y //=.
  simpl in *.
  split.
  - move=> _.
    have ->: y = \bigcup_i ([set (bin_op_enum i)] `&` y).
    { rewrite /bigcup//=.
      apply /predeqP =>z /=.
      split.
      - move=> ?.
        destruct (bin_op_enum_surj z) as [i ?].
        by exists i.
      - by move=> [i ?][-> ?].
    }
    apply sigma_algebra_bigcup.
    move=> i.
    destruct (ExcludedMiddle (y (bin_op_enum i))).
    + apply sub_sigma_algebra.
      rewrite /binder_singletons/setI //=.
      exists (bin_op_enum i).
      apply /predeqP =>z /=.
      split.
      * by move=> [? ?].
      * by move=>->.
    + have -> : ([set bin_op_enum i] `&` y) = set0.
      { rewrite /setI//=.
      apply /predeqP =>z /=.
      split.
      + by move=>[-> ?].
      + by move=>?. }
      apply sigma_algebra0.
  - move=> _. by rewrite /measurable/=/discr_measurable/=.
Qed.
