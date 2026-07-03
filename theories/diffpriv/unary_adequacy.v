From iris.proofmode Require Import base proofmode.
From iris.bi Require Export lib.fixpoint_mono big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Export language erasable exec.
From clutch.base_logic Require Import error_credits.
From clutch.diffpriv Require Import weakestpre primitive_laws.
From clutch.diffpriv Require Import adequacy.
From clutch.prob Require Import distribution.
Import uPred.


Lemma uwp_adequacy_exec_n Σ `{!diffprivGpreS Σ} (e : expr) (σ : state) n φ (δ : R) :
  0 <= δ ->
  (∀ `{diffprivGS Σ}, ⊢ ↯ δ -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (exec n (e, σ)) φ δ.
Proof.
  intros Hδ Hwp.
  eapply DPcoupl_to_UB.
  eapply (wp_adequacy_exec_n Σ e (Val #()) σ σ n (λ v _, φ v) 0 δ); [lra|done|].
  intros ?. iIntros "Hspec _ Hd".
  iPoseProof (Hwp with "Hd") as "He".
  iApply (wp_wand with "He").
  iIntros (v) "%". iExists _. by iFrame.
Qed.

Theorem uwp_adequacy Σ `{diffprivGpreS Σ} (e : expr) (σ : state) (δ : R) φ :
  0 <= δ ->
  (∀ `{diffprivGS Σ}, ⊢  ↯ δ -∗ WP e {{ v, ⌜φ v⌝ }} ) →
  pgl (lim_exec (e, σ)) φ δ.
Proof.
  intros Hδ Hwp.
  eapply DPcoupl_to_UB.
  eapply (wp_adequacy Σ e (Val #()) σ σ 0 δ); [lra|done|].
  intros ?. iIntros "Hspec _ Hd".
  iPoseProof (Hwp with "Hd") as "He".
  iApply (wp_wand with "He").
  iIntros (v) "%". iExists _. by iFrame.
Qed.
