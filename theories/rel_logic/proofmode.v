From clutch.prob_lang Require Import lang notation class_instances tactics.
From clutch.prob_lang Require Export wp_tactics.
From clutch.rel_logic Require Import primitive_laws.
From iris.prelude Require Import options.

#[global] Program Instance rel_logic_wptactics_base `{!clutchGS Σ} : @WpTacticsBase Σ unit wp' _ _.
Next Obligation. intros. by apply wp_value. Qed.
Next Obligation. intros. by apply wp_fupd. Qed.
Next Obligation. intros. by apply wp_bind. Qed.

#[global] Program Instance rel_logic_wptactics_pure `{!clutchGS Σ} : @WpTacticsPure Σ unit wp' true.
Next Obligation. intros. by eapply lifting.wp_pure_step_later. Qed.

#[global] Program Instance rel_logic_wptactics_heap `{!clutchGS Σ} : @WpTacticsHeap Σ unit wp' true :=
  Build_WpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) _ _ _.
Next Obligation. intros. by apply wp_alloc. Qed.
Next Obligation. intros. by apply wp_load. Qed.
Next Obligation. intros. by apply wp_store. Qed.
