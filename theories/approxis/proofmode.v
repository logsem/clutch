From clutch.prob_lang Require Import lang notation class_instances tactics.
From clutch.prob_lang Require Export wp_tactics.
From clutch.approxis Require Import app_weakestpre lifting primitive_laws derived_laws.
From iris.prelude Require Import options.


#[global] Program Instance approxis_wptactics_base `{!approxisGS Σ} : GwpTacticsBase Σ unit wp.
Next Obligation. intros. by apply wp_value. Qed.
Next Obligation. intros. by apply wp_fupd. Qed.

#[global] Program Instance approxis_wptactics_bind `{!approxisGS Σ} : GwpTacticsBind Σ unit wp.
Next Obligation. intros. by apply wp_bind. Qed.

#[global] Program Instance approxis_wptactics_pure `{!approxisGS Σ} : GwpTacticsPure Σ unit true wp.
Next Obligation. intros. by eapply wp_pure_step_later. Qed.

#[global] Program Instance rel_logic_wptactics_heap `{!approxisGS Σ} : GwpTacticsHeap Σ unit true wp :=
  Build_GwpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) (λ l q vs, (l ↦∗{q} vs)%I) _ _ _ _.
Next Obligation. intros. by apply wp_alloc. Qed.
Next Obligation. intros. by apply wp_allocN. Qed.
Next Obligation. intros. by apply wp_load. Qed.
Next Obligation. intros. by apply wp_store. Qed.


#[global] Program Instance rel_logic_wptactics_tape `{!approxisGS Σ} : GwpTacticsTapes Σ unit true wp :=
  Build_GwpTacticsTapes _ _ _ _ (λ l q N ns, (l ↪N ( N ; ns ))%I) _ _.
Next Obligation. intros. by apply wp_alloc_tape. Qed.
Next Obligation. intros. rewrite (bi.wand_curry (l↪N(N;ns))). by apply wp_rand_tape. Qed.

