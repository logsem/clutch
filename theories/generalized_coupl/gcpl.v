From Coq Require Export Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.

From clutch.bi Require Export weakestpre.
From clutch.prelude Require Import stdpp_ext iris_ext NNRbar.
From clutch.prob Require Export distribution graded_predicate_lifting countable_couplings.
From clutch.common Require Export language erasable.
From clutch.generalized_coupl Require Export convex.
From clutch.prob_lang Require Import erasure.

From clutch.clutch Require Import weakestpre.

Local Open Scope R.

Section gcoupl.
  Context {A : Type} {Σ : gFunctors} {Λ : language} `{invGS_gen HasNoLc Σ} (CC : conv_comb A). 

  Local Canonical Structure ARO := leibnizO A.

  Definition gscpl_pre E Z (Φ : state Λ * A → iProp Σ) : state Λ * A → iProp Σ :=
    (λ (x : state Λ * A),
      let '(σ1, a) := x in
      (Z σ1 a) ∨
      (∃ (S : state Λ → A → Prop) (n : nat) (μ1 : distr (state Λ)) (η : cdistr A),
         ⌜ARcouplC μ1 η S 0⌝ ∗
         ⌜CC a η⌝ ∗
         ⌜erasable μ1 σ1⌝ ∗ 
         ∀ σ2 a', ⌜S σ2 a'⌝ ={E}=∗ Φ (σ2, a')))%I. 

  #[local] Instance gscpl_pre_ne Z E Φ :
    NonExpansive (gscpl_pre E Z Φ).
  Proof.
    rewrite /gscpl_pre.
    intros ? (?&?) (?&?) ([=] & [=]). 
    by simplify_eq.
  Qed.

  #[local] Instance gscpl_pre_mono Z E : BiMonoPred (gscpl_pre Z E).
  Proof.
    split; [|apply _].
    iIntros (Φ Ψ HNEΦ HNEΨ) "#Hwand".
    iIntros ((σ1 & a)) "[H | (% & % & % & % & % & % & % & H)]".
    - iLeft. done.
    - iRight. 
      repeat iExists _.
      repeat (iSplit; [done|]).
      iIntros (???). iApply "Hwand". by iApply "H".
    Unshelve. auto.
  Qed.

  Definition gscpl' E Z := bi_least_fixpoint (gscpl_pre E Z).
  Definition gscpl E σ a Z := gscpl' E Z (σ, a).

  Definition gpcpl e σ a Z : iProp Σ :=
    ∃ (R : cfg Λ → A → Prop) (η : cdistr A),
        ⌜CC a η⌝ ∗
        ⌜reducible (e, σ)⌝ ∗
        ⌜ARcouplC (prim_step e σ) η R 0⌝ ∗
        ∀ e' σ' a, ⌜R (e', σ') a⌝ ={∅}=∗ Z e' σ' a.

End gcoupl.




Section clutch.
  

  

End clutch.