From clutch.prob_lang Require Import lang notation class_instances tactics.
From clutch.prob_lang Require Export wp_tactics.
From clutch.ub_logic Require Import ub_weakestpre primitive_laws derived_laws.
From clutch.ub_logic Require Import ub_total_weakestpre total_primitive_laws total_derived_laws.
From iris.prelude Require Import options.

#[global] Program Instance rel_logic_wptactics_base `{!ub_clutchGS Σ} : @GwpTacticsBase Σ unit _ _ wp.
Next Obligation. intros. by apply ub_wp_value. Qed.
Next Obligation. intros. by apply ub_wp_fupd. Qed.

#[global] Program Instance rel_logic_wptactics_bind `{!ub_clutchGS Σ} : @GwpTacticsBind Σ unit _ _ wp.
Next Obligation. intros. by apply ub_wp_bind. Qed.

#[global] Program Instance rel_logic_wptactics_pure `{!ub_clutchGS Σ} : @GwpTacticsPure Σ unit true wp.
Next Obligation. intros. by eapply lifting.wp_pure_step_later. Qed.

#[global] Program Instance rel_logic_wptactics_heap `{!ub_clutchGS Σ} : @GwpTacticsHeap Σ unit true wp :=
  Build_GwpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) (λ l q vs, (l ↦∗{q} vs)%I) _ _ _ _.
Next Obligation. intros. by apply wp_alloc. Qed.
Next Obligation. intros. by apply wp_allocN. Qed.
Next Obligation. intros. by apply wp_load. Qed.
Next Obligation. intros. by apply wp_store. Qed.

#[global] Program Instance rel_logic_twptactics_base `{!ub_clutchGS Σ} : @GwpTacticsBase Σ unit _ _ twp.
Next Obligation. intros. by apply ub_twp_value. Qed.
Next Obligation. intros. by apply ub_twp_fupd. Qed.

#[global] Program Instance rel_logic_twptactics_bind `{!ub_clutchGS Σ} : @GwpTacticsBind Σ unit _ _ twp.
Next Obligation. intros. by apply ub_twp_bind. Qed.

#[global] Program Instance rel_logic_twptactics_pure `{!ub_clutchGS Σ} : @GwpTacticsPure Σ unit false twp.
Next Obligation. intros. by eapply total_lifting.twp_pure_step_fupd. Qed.

#[global] Program Instance rel_logic_twptactics_heap `{!ub_clutchGS Σ} : @GwpTacticsHeap Σ unit false twp :=
  Build_GwpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) (λ l q vs, (l ↦∗{q} vs)%I) _ _ _ _.
Next Obligation. intros. by apply twp_alloc. Qed.
Next Obligation. intros. by apply twp_allocN. Qed.
Next Obligation. intros. iIntros ">H H2". iApply (twp_load with "[H //] [H2 //]"). Qed.
Next Obligation. intros. iIntros ">H H2". iApply (twp_store with "[H //] [H2 //]"). Qed.
