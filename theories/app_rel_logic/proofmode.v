From clutch.prob_lang Require Import lang notation class_instances tactics.
From clutch.prob_lang Require Export wp_tactics.
From clutch.app_rel_logic Require Import app_weakestpre lifting primitive_laws derived_laws.
From iris.prelude Require Import options.


#[global] Program Instance app_rel_logic_wptactics_base `{!parisGS Σ} : GwpTacticsBase Σ unit wp.
Next Obligation. intros. by apply wp_value. Qed.
Next Obligation. intros. by apply wp_fupd. Qed.

#[global] Program Instance app_rel_logic_wptactics_bind `{!parisGS Σ} : GwpTacticsBind Σ unit wp.
Next Obligation. intros. by apply wp_bind. Qed.

#[global] Program Instance app_rel_logic_wptactics_pure `{!parisGS Σ} : GwpTacticsPure Σ unit true wp.
Next Obligation. intros. by eapply wp_pure_step_later. Qed.

#[global] Program Instance rel_logic_wptactics_heap `{!parisGS Σ} : GwpTacticsHeap Σ unit true wp :=
  Build_GwpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) (λ l q vs, (l ↦∗{q} vs)%I) _ _ _ _.
Next Obligation. intros. by apply wp_alloc. Qed.
Next Obligation. intros. by apply wp_allocN. Qed.
Next Obligation. intros. by apply wp_load. Qed.
Next Obligation. intros. by apply wp_store. Qed.


