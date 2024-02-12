From clutch.prob_lang Require Import lang notation class_instances tactics.
From clutch.prob_lang Require Export wp_tactics.
From clutch.tpref_logic Require Import weakestpre primitive_laws derived_laws.
From iris.prelude Require Import options.


#[local] Definition rwp' `{!tprG δ Σ} := (rwp' _ _ _ _ _).

(*
#[local] Program Instance rwp' `{!spec δ Σ} `{!tprwpG prob_lang Σ} : Gwp (iProp Σ) (expr) (val ) () .
Next Obligation.
  intros δ Σ s lang.
  pose proof (rwp') as [wp ?]; [exact lang | exact s |].
  apply wp.
Defined.
Next Obligation.
  intros δ Σ s lang.
  pose proof (rwp') as [wp u]; [exact lang | exact s |].
  exact u.
Defined.
*)


#[global] Program Instance rel_logic_wptactics_base `{!tprG δ Σ} :
  @GwpTacticsBase Σ unit _ _ wp.
Next Obligation. intros. by apply rwp_value. Qed.
Next Obligation. intros. by apply rwp_fupd. Qed.
Next Obligation. intros. by apply rwp_bind. Qed.

#[global] Program Instance rel_logic_wptactics_pure `{!tprG δ Σ} :
  @GwpTacticsPure Σ unit false wp.
Next Obligation. intros. by eapply lifting.rwp_pure_step. Qed.

#[global] Program Instance rel_logic_wptactics_heap `{!tprG δ Σ}  :
  @GwpTacticsHeap Σ unit false wp := Build_GwpTacticsHeap _ _ _ _ (λ l q v, (l ↦{q} v)%I) (λ l q vs, (l ↦∗{q} vs)%I) _ _ _ _.
Next Obligation. intros. by apply rwp_alloc. Qed.
Next Obligation. intros. by apply rwp_allocN. Qed.
Next Obligation. intros. by apply rwp_load. Qed.
Next Obligation. intros. by apply rwp_store. Qed.
