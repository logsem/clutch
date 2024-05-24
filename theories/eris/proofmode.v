From clutch.prob_lang Require Import lang notation class_instances tactics.
From clutch.prob_lang Require Export wp_tactics.
From clutch.eris Require Import weakestpre primitive_laws derived_laws.
From clutch.eris Require Import total_weakestpre total_primitive_laws total_derived_laws.
From iris.prelude Require Import options.

#[global] Program Instance rel_logic_wptactics_base `{!erisGS Σ} : GwpTacticsBase Σ unit wp.
Next Obligation. intros. by apply ub_wp_value. Qed.
Next Obligation. intros. by apply ub_wp_fupd. Qed.

#[global] Program Instance rel_logic_wptactics_bind `{!erisGS Σ} : GwpTacticsBind Σ unit wp.
Next Obligation. intros. by apply ub_wp_bind. Qed.

#[global] Program Instance rel_logic_wptactics_pure `{!erisGS Σ} : GwpTacticsPure Σ unit true wp.
Next Obligation. intros. by eapply lifting.wp_pure_step_later. Qed.

#[global] Program Instance rel_logic_wptactics_heap `{!erisGS Σ} : GwpTacticsHeap Σ unit true wp :=
  Build_GwpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) (λ l q vs, (l ↦∗{q} vs)%I) _ _ _ _.
Next Obligation. intros. by apply wp_alloc. Qed.
Next Obligation. intros. by apply wp_allocN. Qed.
Next Obligation. intros. by apply wp_load. Qed.
Next Obligation. intros. by apply wp_store. Qed.

#[global] Program Instance rel_logic_twptactics_base `{!erisGS Σ} : GwpTacticsBase Σ unit twp.
Next Obligation. intros. by apply ub_twp_value. Qed.
Next Obligation. intros. by apply ub_twp_fupd. Qed.

#[global] Program Instance rel_logic_twptactics_bind `{!erisGS Σ} : GwpTacticsBind Σ unit twp.
Next Obligation. intros. by apply ub_twp_bind. Qed.

#[global] Program Instance rel_logic_twptactics_pure `{!erisGS Σ} : GwpTacticsPure Σ unit false twp.
Next Obligation. intros. by eapply total_lifting.twp_pure_step_fupd. Qed.

#[global] Program Instance rel_logic_twptactics_heap `{!erisGS Σ} : GwpTacticsHeap Σ unit false twp :=
  Build_GwpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) (λ l q vs, (l ↦∗{q} vs)%I) _ _ _ _.
Next Obligation. intros. by apply twp_alloc. Qed.
Next Obligation. intros. by apply twp_allocN. Qed.
Next Obligation. intros. iIntros ">H H2". iApply (twp_load with "[H //] [H2 //]"). Qed.
Next Obligation. intros. iIntros ">H H2". iApply (twp_store with "[H //] [H2 //]"). Qed.
