From Coq Require Export Reals Psatz.

From iris.base_logic.lib Require Export fancy_updates own.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl auth.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob Require Export couplings distribution markov.

Set Default Proof Using "Type".

(** A [spec] is a Markov chain together with an interpretation in the logic  *)
Class spec (δ : markov) (Σ : gFunctors) := Spec {
  spec_interp : mstate δ → iProp Σ;
}.
Global Arguments Spec {_ _}.

Canonical Structure mstateO δ := leibnizO (mstate δ).

(** An "update"-modality for deterministic spec steps  *)
Section spec_update.
  Context `{spec δ Σ} `{invGS_gen hlc Σ}.
  Implicit Types a : mstate δ.

  Definition spec_update (n : nat) (E : coPset) (P : iProp Σ) : iProp Σ :=
    (∀ a, spec_interp a -∗ |={E}=> ∃ a', ⌜stepN n a a' = 1⌝ ∗ spec_interp a' ∗ P)%I.

  Lemma spec_update_bind n m E P Q :
    spec_update n E P ∗ (P -∗ spec_update m E Q) ⊢ spec_update (n + m) E Q.
  Proof.
    rewrite /spec_update. iIntros "[P PQ]" (a) "Ha".
    iMod ("P" $! a with "Ha") as (b Hab) "[Hb P]".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (c Hbc) "[Hc Q]".
    iModIntro. iExists _.
    assert (stepN (n + m) a c = 1) by by eapply stepN_det_trans.
    by iFrame.
  Qed.

  Lemma spec_update_mono_fupd n E P Q :
    spec_update n E P ∗ (P ={E}=∗ Q) ⊢ spec_update n E Q.
  Proof.
    iIntros "[HP PQ]". iIntros (a) "Hsrc".
    iMod ("HP" with "Hsrc") as (b Hstep) "[Hsrc P]".
    iMod ("PQ" with "P"). iFrame. iModIntro.
    iExists b. by iFrame.
  Qed.

  Lemma spec_update_mono n E P Q :
    spec_update n E P ∗ (P -∗ Q) ⊢ spec_update n E Q.
  Proof.
    iIntros "[Hupd HPQ]". iApply (spec_update_mono_fupd with "[$Hupd HPQ]").
    iIntros "P". iModIntro. by iApply "HPQ".
  Qed.

  Lemma fupd_spec_update n E P :
    (|={E}=> spec_update n E P) ⊢ spec_update n E P.
  Proof.
    iIntros "H". rewrite /spec_update. iIntros (e) "Hsrc".
    iMod "H". by iApply "H".
  Qed.

End spec_update.
