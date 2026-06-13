(** Minimal tactic support for gen_prob_lang: the [head_step] hint database and
    [solve_red], ported from [prob_lang/tactics.v] (the generic, non-Laplace
    parts). [inv_head_step] is already provided by [lang.v]. *)
From Stdlib Require Import Reals Psatz.
From clutch.common Require Import ectx_language.
From clutch.prob Require Import distribution.
From clutch.gen_prob_lang Require Import lang.
From iris.proofmode Require Import environments proofmode.
From iris.prelude Require Import options.

#[local] Open Scope R.

(* Re-export the head_step_rel constructors into the [head_step] db (the in-file
   hint was section-local), and the generic reducibility bridges. *)
Global Hint Constructors head_step_rel : head_step.

Global Hint Extern 0 (head_reducible _ _) =>
  eexists (_, _); eapply head_step_support_equiv_rel : head_step.
Global Hint Extern 1 (head_step _ _ _ > 0) =>
  eapply head_step_support_equiv_rel; econstructor : head_step.
Global Hint Extern 2 (head_reducible _ _) =>
  by eauto with head_step : typeclass_instances.

(* [inv_head_step]/[solve_distr] are defined inside [lang.v]'s [Section semantics]
   for the metatheory proofs, but do not survive section close + [Export]; re-export
   them here (the bodies are S-independent). *)
Ltac inv_head_step :=
  repeat
    match goal with
    | H : context [@bool_decide ?P ?dec] |- _ =>
        try (rewrite bool_decide_eq_true_2 in H; [|done]);
        try (rewrite bool_decide_eq_false_2 in H; [|done]);
        destruct_decide (@bool_decide_reflect P dec); simplify_eq
    | _ => progress simplify_map_eq; simpl in *; inv_distr; repeat case_match; inv_distr
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : is_Some (_ !! _) |- _ => destruct H
    end.

Ltac solve_distr :=
  repeat
    match goal with
    | |- (dret _).(pmf) _ > 0 => rewrite dret_1_1 //; lra
    | |- (dret ?x).(pmf) ?x = 1 => by apply dret_1_1
    | |- (dbind _ _).(pmf) _ > 0 => apply dbind_pos; eexists; split
    | |- (dmap _ _).(pmf) _ > 0 =>
        apply dmap_pos; eexists; (split; [done|]); try done
    | |- (dunifP _).(pmf) _ > 0 => apply dunifP_pos
    | |- (dunifv _ _).(pmf) _ > 0 => apply dunifv_pos
    | |- (d_proj_Some _).(pmf) _ > 0 => rewrite d_proj_Some_pos
    end.

Ltac solve_red :=
  match goal with
  | |- (environments.envs_entails _ ( ⌜ _ ⌝ ∗ _)) =>
      iSplitR ; [ by (iPureIntro ; solve_red) | ]
  | |- (environments.envs_entails _ ( _ ∗ ⌜ _ ⌝)) =>
      iSplitL ; [ by (iPureIntro ; solve_red) | ]
  | |- reducible ((fill _ _), _) =>
      apply reducible_fill ; solve_red
  | |- reducible _ =>
      apply head_prim_reducible ; solve_red
  | |- (head_reducible _ _) =>
      by eauto with head_step
  end.
