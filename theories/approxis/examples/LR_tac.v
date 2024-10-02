From clutch.approxis Require Import approxis option.
Set Default Proof Using "Type*".

From Ltac2 Require Ltac2 Printf Option List.

(* We define two extensible tactics for introducing and proving logical
     relations. *)

Import Ltac2 Printf Option List.

Module Basic.
  (* Importing LR_tac will provides a "batteries included" variant of the
    tactics that deals with some of the syntactic built-in types. The bare
    version ("without batteries") of the tactics can be accessed by importing
    LR_tac.Basic. *)
  Ltac2 mutable pattern_of_lr2 (lr : constr) (xs : constr list) : constr :=
    lazy_match! lr with
    | @lrel_unit _ => constr:("(->&->)")
    | lrel_int =>
        match xs with
        | [] => '"(%&->&->)"
        | x :: _ => let s := '(append "(%" ($x ++ "&->&->)")) in
                    eval vm_compute in $s
        end
    | _ => Control.zero (Tactic_failure (Some (fprintf "no pattern found for lrel %t" lr)))
    end.

  Ltac2 mutable lrintro_tacs () : (string , (constr -> constr list -> (constr -> constr list -> constr option) -> constr option)) FMap.t :=
    FMap.empty (FSet.Tags.string_tag).

  Ltac2 printst st :=
    printf "current state is:" ;
    List.iter (fun (s, f) => printf "%s, " s) st.

  Ltac2 lr_printst () :=
    let m := lrintro_tacs () in
    let st := FMap.bindings m in
    printst st.

  Ltac2 rec lr_intro typ xs :=
    printf "entering lr_intro, typ: %t" typ ;
    FMap.fold
      (fun name f finished =>
         match finished with
         | Some s => finished
         | None =>
             (printf "trying %s" name ;
              f typ xs lr_intro)
         end)
      (lrintro_tacs ())
      None.

  Ltac2 fmt_constr_opt () opt :=
    match opt with None => Message.of_string "None"
              | Some s => Message.concat (Message.of_string "Some ") (Message.of_constr s)
    end.

  Ltac2 Type progress := [ Progressed | Stuck ].

  Ltac2 mutable rel_val_tacs () : (string , (constr -> (constr -> progress) -> progress)) FMap.t :=
    FMap.empty (FSet.Tags.string_tag).

  Ltac2 rec f_rel_vals typ :=
    printf "entering lr_intro, typ: %t" typ ;
    FMap.fold
      (fun name f finished =>
         match finished with
         | Progressed => finished
         | Stuck =>
             (printf "trying %s" name ;
              f typ f_rel_vals)
         end)
      (rel_val_tacs ())
      Stuck.

  Ltac2 rel_vals (lr : constr) : unit :=
    let prog := f_rel_vals lr in
    ().

  (* Ltac2 mutable rel_vals (lr : constr) : unit :=
       lazy_match! lr with
       | @lrel_unit => eauto
       (* | _ => Control.zero (Tactic_failure (Some (fprintf "Don't know how to solve lrel %t" lr))) *)
       | _ => printf "Don't know how to solve lrel %t" lr
       end. *)

  Tactic Notation "lrintro" constr(x) :=
    let f :=
      ltac2val:
        (lr xs |-
           let pat :=
             (* pattern_of_lr2 *)
             (Option.get (lr_intro
                            (Option.get (Ltac1.to_constr lr))
                            [(Option.get (Ltac1.to_constr xs))])) in
           Ltac1.of_constr pat) in
    lazymatch goal with
    | |- environments.envs_entails _ (lrel_car ?A _ _ -∗ _) =>
        let x' := f A x in
        iIntros x'
    | |- environments.envs_entails _ (∀ (_ _ : val), lrel_car ?A _ _ -∗ _) =>
        let x' := f A x in
        iIntros (??) x'
    end.

  Tactic Notation "lrintro" := lrintro "".

  Ltac rel_vals' :=
    lazymatch goal with
    (* | |- environments.envs_entails _ (_ (InjRV _) (InjRV _)) =>
         iExists _,_ ; iRight ; iSplit ; [eauto|iSplit ; eauto]
     | |- environments.envs_entails _ (_ (InjLV _) (InjLV _)) =>
         iExists _,_ ; iLeft ; iSplit ; [eauto|iSplit ; eauto]
     | |- environments.envs_entails _ (_ (_ , _)%V (_ , _)%V) =>
         iExists _,_,_,_ ; iSplit ; [eauto|iSplit ; [eauto | iSplit]]
     | |- environments.envs_entails _ (_ _ (lrel_int_bounded _ _) _ _) =>
         iExists _ ; iPureIntro ; intuition lia
     | |- environments.envs_entails _ (_ _ lrel_input _ _) =>
         iExists _ ; iPureIntro ; intuition lia
     | |- environments.envs_entails _ (_ _ lrel_output _ _) =>
         iExists _ ; iPureIntro ; intuition lia *)
    | |- environments.envs_entails _ ?lr =>
        idtac "trying lr " lr ;
        let f := ltac2:(lr |- rel_vals (Option.get (Ltac1.to_constr lr))) in
        f lr
    | _ => fail "rel_vals: case not covered"
    end.
  Ltac rel_vals := try rel_values ; try iModIntro ; repeat rel_vals'.

End Basic.
Export Basic.

Ltac2 get_head_name xs := match xs with [] => '"" | x :: _ => x end.

Module LR_unit.
  Ltac2 unit_intro typ xs k :=
    printf "entering unit_intro, typ: %t" typ ;
    lazy_match! typ with
    | lrel_unit =>
        printf "found `lrel_unit`, done" ;
        Some '"(->&->)"
    | _ => None
    end.
  Ltac2 Set Basic.lrintro_tacs as prev := fun () => FMap.add "unit" unit_intro (prev ()).
End LR_unit.
Export LR_unit.

Module LR_prod.
  Ltac2 prod_val typ k :=
    printf "entering prod_val, typ: %t" typ ;
    lazy_match! typ with
    | (lrel_car lrel_prod ?v1 ?v2) =>
        printf "found `lrel_prod %t %t`, splitting" v1 v2 ;
        ltac1:(iExists _,_,_,_ ; iSplit ; [eauto|iSplit ; [eauto | iSplit]]) ; Progressed
    | (lrel_car _ (?v1 , ?v2)%V (?v3 , ?v4)%V) =>
        printf "found `_ (%t, %t) (%t, %t)`, splitting" v1 v2 v3 v4 ;
        ltac1:(iExists _,_,_,_ ; iSplit ; [eauto|iSplit ; [eauto | iSplit]]) ; Progressed
    | _ => Stuck
    end.
  Ltac2 Set Basic.rel_val_tacs as prev := fun () => FMap.add "prod" prod_val (prev ()).
End LR_prod.
Export LR_prod.

Module LR_int.
  Ltac2 int_intro typ xs k :=
    printf "entering int_intro, typ: %t" typ ;
    lazy_match! typ with
    | lrel_int =>
        printf "found `lrel_int`, done" ;
        match xs with
        | [] => Some '"(%&->&->)"
        | x :: _ => let s := '(append "(%" ($x ++ "&->&->)")) in
                    Some (eval vm_compute in $s)
        end
    | _ => None
    end.
  Ltac2 Set Basic.lrintro_tacs as prev := fun () => FMap.add "int" int_intro (prev ()).

  Ltac2 int_val typ k :=
    printf "entering int_val, typ: %t" typ ;
    lazy_match! typ with
    | (lrel_car lrel_int ?v1 ?v2) =>
        printf "found `lrel_int %t %t`, trying lia" v1 v2 ;
        ltac1:(iExists _ ; iPureIntro ; (intuition lia || eauto)) ; Progressed
    | _ => Stuck
    end.
  Ltac2 Set Basic.rel_val_tacs as prev := fun () => FMap.add "int" int_val (prev ()).
End LR_int.
Export LR_int.

Module LR_option.
  Ltac2 option_intro typ xs k :=
    printf "entering option_intro, typ: %t" typ ;
    lazy_match! typ with
    | lrel_option ?a =>
        printf "found `option %t`, continuing" a ;
        Option.bind
          (k a xs)
          (fun aa =>
             Option.bind (k 'lrel_unit [])
               (fun u =>
                  let s := '(append "#(%" (" " ++ "&% &[(->&->&" ++ $u ++ ") | (->&->&"++$aa++")])")) in
                  Option.ret (eval vm_compute in $s)))
    | _ => None
    end.
  Ltac2 Set Basic.lrintro_tacs as prev := fun () => FMap.add "option" option_intro (prev ()).

  (* Ltac2 Set pattern_of_lr2 as previous :=
       fun lr (xs : constr list) =>
         lazy_match! lr with
         | lrel_option ?a =>
             let aa := previous a xs in
             let u := previous 'lrel_unit xs in
             let s := '(append "#(%" (" " ++ "&% &[(->&->&" ++ $u ++ ") | (->&->&"++$aa++")])")) in
             eval vm_compute in $s
         | _ => previous lr xs
         end. *)

  Ltac2 option_val typ k :=
    printf "entering option_val, typ: %t" typ ;
    lazy_match! typ with
    | (lrel_car _ (InjLV _) (InjLV _)) =>
        printf "found `InjLV`, continuing left" ;
        ltac1:(iExists _,_ ; iLeft ; iSplit ; [eauto | iSplit ; eauto]) ; Progressed
    | (lrel_car _ (InjRV _) (InjRV _)) =>
        printf "found `InjRV`, continuing right" ;
        ltac1:(iExists _,_ ; iRight ; iSplit ; [eauto | iSplit ; eauto]) ; Progressed
    | _ => Stuck
    end.

  Ltac2 Set Basic.rel_val_tacs as prev := fun () => FMap.add "option" option_val (prev ()).

End LR_option.
Export LR_option.

Goal forall Σ, ⊢ ∀ v1 v2, @lrel_option Σ (@lrel_int Σ) v1 v2 -∗ ⌜v1 = v2⌝.
  ltac1:(iIntros (?) ; iStartProof ; lrintro "").
  1:ltac1:(done).
  lr_printst ().
  printf "%a" fmt_constr_opt (lr_intro '(lrel_int) ['"x"]).
  printf "%t" (pattern_of_lr2 'lrel_int ['"x"]).
  (* printf "%t" (pattern_of_lr2 '(lrel_option lrel_int) ['"x"]). *)
  printf "%a" fmt_constr_opt (lr_intro '(lrel_option lrel_int) ['"x"]).
  auto.
Abort.

Goal forall Σ, ⊢ @lrel_option Σ (@lrel_int Σ) (InjRV #(1/1/4/2)) (InjRV #(0+2)).
  ltac1:(iIntros (?) ; iStartProof).
  ltac1:(rel_vals).
  ltac1:(rel_vals).
Abort.

Goal forall Σ, ⊢ @lrel_option Σ (@lrel_int Σ) (InjLV #()) (InjLV #()).
  ltac1:(iIntros (?) ; iStartProof).
  ltac1:(rel_vals).
Qed.
