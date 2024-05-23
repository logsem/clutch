From Coq Require Export Reals Psatz.

From iris.base_logic.lib Require Export fancy_updates own.
From iris.proofmode Require Import base tactics classes.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob Require Export couplings distribution markov.

Set Default Proof Using "Type".

Class spec_updateGS (δ : markov) (Σ : gFunctors) := Spec_updateGS {
  spec_interp : mstate δ → iProp Σ;
}.
Global Arguments Spec_updateGS {_ _}.

Canonical Structure mstateO δ := leibnizO (mstate δ).

(** An "update"-modality for deterministic spec steps  *)
Section spec_update.
  Context `{spec_updateGS δ Σ, invGS_gen hl Σ}.
  Implicit Types a : mstate δ.

  Definition spec_updateN (n : nat) (E : coPset) (P : iProp Σ) : iProp Σ :=
    (∀ a, spec_interp a -∗ |={E}=> ∃ a', ⌜stepN n a a' = 1⌝ ∗ spec_interp a' ∗ P)%I.

  Definition spec_update (E : coPset) (P : iProp Σ) : iProp Σ :=
    (∀ a, spec_interp a -∗ |={E}=> ∃ a' n, ⌜stepN n a a' = 1⌝ ∗ spec_interp a' ∗ P)%I.

  Lemma spec_updateN_implies_spec_update n E P:
    spec_updateN n E P -∗ spec_update E P.
  Proof.
    rewrite /spec_updateN/spec_update.
    iIntros "H % Ha".
    iMod ("H" with "[$]") as "(%&%&?&?)". iModIntro.
    iExists _, _. iFrame. by iPureIntro.
  Qed.

  Lemma spec_updateN_ret E P :
    P ⊢ spec_updateN 0 E P.
  Proof.
    iIntros "HP" (a) "Ha !#".
    iExists _.
    rewrite stepN_O dret_1_1 //.
    by iFrame.
  Qed.

  Lemma spec_update_ret E P :
    P ⊢ spec_update E P.
  Proof.
    iIntros "HP" (a) "Ha !#".
    iExists a, O.
    rewrite stepN_O dret_1_1 //.
    by iFrame.
  Qed.

  Lemma spec_updateN_bind n m E1 E2 P Q :
    E1 ⊆ E2 →
    spec_updateN n E1 P ∗ (P -∗ spec_updateN m E2 Q) ⊢ spec_updateN (n + m) E2 Q.
  Proof.
    rewrite /spec_updateN. iIntros (?) "[P PQ] %a Ha".
    iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
    iMod ("P" $! a with "Ha") as (b Hab) "[Hb P]".
    iMod "Hclose" as "_".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (c Hbc) "[Hc Q]".
    iModIntro. iExists _.
    erewrite stepN_det_trans; [|done|done].
    by iFrame.
  Qed.

  Lemma spec_update_bind E1 E2 P Q :
    E1 ⊆ E2 →
    spec_update E1 P ∗ (P -∗ spec_update E2 Q) ⊢ spec_update E2 Q.
  Proof.
    rewrite /spec_update. iIntros (HE) "[P PQ] %a Ha".
    iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
    iMod ("P" $! a with "Ha") as (b n Hab) "[Hb P]".
    iMod "Hclose" as "_".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (c m Hbc) "[Hc Q]".
    iModIntro. iExists _, (n + m)%nat. iFrame.
    by erewrite stepN_det_trans.
  Qed.

  Lemma spec_updateN_mono_fupd n E P Q :
    spec_updateN n E P ∗ (P ={E}=∗ Q) ⊢ spec_updateN n E Q.
  Proof.
    iIntros "[HP PQ]". iIntros (a) "Hsrc".
    iMod ("HP" with "Hsrc") as (b Hstep) "[Hsrc P]".
    iMod ("PQ" with "P"). iFrame. iModIntro.
    iExists b. by iFrame.
  Qed.

  Lemma spec_update_mono_fupd E P Q :
    spec_update E P ∗ (P ={E}=∗ Q) ⊢ spec_update E Q.
  Proof.
    rewrite /spec_update.
    iIntros "[HP PQ]". iIntros (a) "Hsrc".
    iMod ("HP" with "Hsrc") as (b n Hstep) "[Hsrc P]".
    iMod ("PQ" with "P"). iFrame. iModIntro.
    iExists b, _. by iFrame.
  Qed.

  Lemma spec_updateN_mono n E P Q :
    spec_updateN n E P ∗ (P -∗ Q) ⊢ spec_updateN n E Q.
  Proof.
    iIntros "[Hupd HPQ]". iApply (spec_updateN_mono_fupd with "[$Hupd HPQ]").
    iIntros "P". iModIntro. by iApply "HPQ".
  Qed.

  Lemma spec_update_mono E P Q :
    spec_update E P ∗ (P -∗ Q) ⊢ spec_update E Q.
  Proof.
    rewrite /spec_update.
    iIntros "[Hupd HPQ]". iApply (spec_update_mono_fupd with "[$Hupd HPQ]").
    iIntros "P". iModIntro. by iApply "HPQ".
  Qed.

  Lemma fupd_spec_updateN n E P :
    (|={E}=> spec_updateN n E P) ⊢ spec_updateN n E P.
  Proof.
    iIntros "H". rewrite /spec_updateN. iIntros (e) "Hsrc".
    iMod "H". by iApply "H".
  Qed.

  Lemma fupd_spec_update E P :
    (|={E}=> spec_update E P) ⊢ spec_update E P.
  Proof.
    rewrite /spec_update.
    iIntros "H". rewrite /spec_updateN. iIntros (e) "Hsrc".
    iMod "H". by iApply "H".
  Qed.

  Global Instance from_modal_spec_update_spec_update P E :
    FromModal True modality_id (spec_update E P) (spec_update E P) P.
  Proof. iIntros (_) "HP /=". by iApply spec_update_ret. Qed.

  Global Instance elim_modal_spec_update_spec_update P Q E :
    ElimModal True false false (spec_update E P) P (spec_update E Q) (spec_update E Q).
  Proof. iIntros (?) "[HP Hcnt]". by iApply (spec_update_bind with "[$]"). Qed.

  Global Instance from_modal_spec_updateN_spec_updateN P E :
    FromModal True modality_id (spec_update E P) (spec_updateN 0 E P) P.
  Proof. iIntros (_) "HP /=". by iApply spec_updateN_ret. Qed.

  Global Instance elim_modal_spec_updateN_spec_updateN n m P Q E :
    ElimModal True false false (spec_updateN n E P) P (spec_updateN (n + m) E Q) (spec_updateN m E Q).
  Proof. iIntros (?) "[HP Hcnt]". by iApply (spec_updateN_bind with "[$]"). Qed.

End spec_update.
