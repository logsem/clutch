From clutch.con_prob_lang Require Import lang notation class_instances tactics.
From clutch.con_prob_lang Require Export wp_tactics.
From clutch.coneris Require Import weakestpre primitive_laws derived_laws.
From iris.prelude Require Import options.

#[global] Program Instance rel_logic_wptactics_base `{!conerisGS Σ} : GwpTacticsBase Σ unit wp.
Next Obligation. intros. by apply pgl_wp_value. Qed.
Next Obligation. intros. by apply pgl_wp_fupd. Qed.

#[global] Program Instance rel_logic_wptactics_bind `{!conerisGS Σ} : GwpTacticsBind Σ unit wp.
Next Obligation. intros. by apply pgl_wp_bind. Qed.

#[global] Program Instance rel_logic_wptactics_pure `{!conerisGS Σ} : GwpTacticsPure Σ unit true wp.
Next Obligation. intros. by eapply lifting.wp_pure_step_later. Qed.

#[global] Program Instance rel_logic_wptactics_heap `{!conerisGS Σ} : GwpTacticsHeap Σ unit true wp :=
  Build_GwpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) (λ l q vs, (l ↦∗{q} vs)%I) _ _ _ _.
Next Obligation. intros. by apply wp_alloc. Qed.
Next Obligation. intros. by apply wp_allocN. Qed.
Next Obligation. intros. by apply wp_load. Qed.
Next Obligation. intros. by apply wp_store. Qed.
