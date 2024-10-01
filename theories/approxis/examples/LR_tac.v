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

  Ltac2 mutable rel_vals (lr : constr) (* : unit *) :=
    lazy_match! lr with
    | @lrel_unit => eauto
    | _ => Control.zero (Tactic_failure (Some (fprintf "Don't know how to solve lrel %t" lr)))
    end.

  Tactic Notation "lrintro" constr(x) :=
    let f :=
      ltac2val:
        (lr xs |-
           let pat := pattern_of_lr2
                        (Option.get (Ltac1.to_constr lr))
                        [(Option.get (Ltac1.to_constr xs))] in
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
  Ltac rel_vals := try (rel_values ; iModIntro) ; rel_vals'.

End Basic.
Export Basic.

Ltac2 get_head_name xs := match xs with [] => '"" | x :: _ => x end.

Module LR_option.

  Ltac2 Set pattern_of_lr2 as previous :=
    fun lr (xs : constr list) =>
      lazy_match! lr with
      | lrel_option ?a =>
          let aa := previous a xs in
          let u := previous 'lrel_unit xs in
          let s := '(append "#(%" (" " ++ "&% &[(->&->&" ++ $u ++ ") | (->&->&"++$aa++")])")) in
          eval vm_compute in $s
      | _ => previous lr xs
      end.

  Ltac2 Set rel_vals as previous :=
    fun lr =>
      lazy_match! lr with
      | (lrel_car _ (InjRV _) (InjRV _)) =>
          ltac1:(iExists _,_ ; iRight ; iSplit ; [eauto | iSplit ; eauto])
      | (lrel_car _ (InjLV _) (InjLV _)) =>
          ltac1:(iExists _,_ ; iLeft ; iSplit ; [eauto | iSplit ; eauto])
      | _ => previous lr
      end.

End LR_option.
Export LR_option.
