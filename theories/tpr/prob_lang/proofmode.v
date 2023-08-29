From clutch.prob_lang Require Import lang notation class_instances tactics.
From clutch.prob_lang Require Export wp_tactics.
From clutch.tpr Require Import weakestpre primitive_laws.
From iris.prelude Require Import options.

#[local] Definition rwp' `{markov A B} `{!tprG A Σ} := (rwp' _ _ _ _ _ _ _ _ _).

#[global] Program Instance rel_logic_wptactics_base `{markov A B} `{!tprG A Σ} :
  @WpTacticsBase Σ unit rwp' _ _.
Next Obligation. intros. by apply: rwp_value. Qed.
Next Obligation. intros. by apply: rwp_fupd. Qed.
Next Obligation. intros. by apply: rwp_bind. Qed.

#[global] Program Instance rel_logic_wptactics_pure `{markov A B} `{!tprG A Σ} :
  @WpTacticsPure Σ unit rwp' false.
Next Obligation. intros. by eapply lifting.rwp_pure_step. Qed.

#[global] Program Instance rel_logic_wptactics_heap `{markov A B} `{!tprG A Σ}  :
  @WpTacticsHeap Σ unit rwp' false := Build_WpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) _ _ _.
Next Obligation. intros. by apply rwp_alloc. Qed.
Next Obligation. intros. by apply rwp_load. Qed.
Next Obligation. intros. by apply rwp_store. Qed.
