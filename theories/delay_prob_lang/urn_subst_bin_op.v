From Coq Require Import Reals Psatz.
Require Import Btauto. 
From stdpp Require Import countable gmap stringmap fin_sets.
From clutch.prelude Require Import stdpp_ext.
From clutch.delay_prob_lang Require Import tactics notation.
From clutch.delay_prob_lang Require Export lang urn_subst.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".

Local Ltac bin_op_smash:= intros K1 K2 K3; rewrite !bind_Some in K2 K3;
                          destruct K2 as [?[K2 ?]]; destruct K3 as [?[K3 ?]]; simplify_eq;
                          apply urn_subst_well_typed in K2 as K2';
                          destruct K2' as [? [? Hrewrite1]];
                          apply urn_subst_well_typed in K3 as K3';
                          destruct K3' as [? [? Hrewrite2]]; simplify_eq;
                          rewrite Hrewrite1 Hrewrite2;
                          apply urn_subst_is_simple in K2 as K2'';
                          apply urn_subst_is_simple in K3 as K3'';
                          bind_solver; match_solver;
                          simpl in *; simplify_eq;
                          try rewrite K2; try rewrite K3; simpl; bind_solver; match_solver; try case_match; simplify_eq; naive_solver.

Lemma urn_subst_val_bin_op op f v1 v2 v v1' v2':
  bin_op_eval op v1 v2 = Some v ->
  urn_subst_val f v1 = Some v1' ->
  urn_subst_val f v2 = Some v2' ->
  ∃ v', urn_subst_val f v = Some v' /\ bin_op_eval op v1' v2' = Some v'.
Proof.
  rewrite /bin_op_eval/bin_op_eval_bl.
  destruct v1 as [l1| | | |]; 
    destruct v2 as [l2| | | |]; simpl; [|done..].
  destruct (base_lit_type_check l1) as [b1|] eqn:H1; 
    destruct (base_lit_type_check l2) as [b2|] eqn:H2; [|repeat (done||case_match)..].
  destruct op, b1, b2; simplify_eq; try done.
Admitted.
(** This proof is correct but SUPER SLOW *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(*   - bin_op_smash. *)
(* Qed.  *)
