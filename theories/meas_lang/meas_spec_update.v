From Coq Require Import Reals Psatz.

From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import base tactics classes.

(*  From clutch.prob Require Import distribution markov. *)

From clutch.prob.monad Require Import meas_markov.
From mathcomp.analysis Require Import measure.

Set Default Proof Using "Type".


Class meas_spec_updateGS (δ : meas_markov) (Σ : gFunctors) := MeasSpec_updateGS {
  spec_interp : mstate δ → iProp Σ;
}.
Global Arguments MeasSpec_updateGS {_ _}.

Canonical Structure mstateO δ := leibnizO (mstate δ).

(** An "update"-modality for deterministic spec steps  *)
Section spec_update.
  Context `{meas_spec_updateGS δ Σ, invGS_gen hl Σ}.
  Implicit Types a : mstate δ.


  Definition spec_updateN_def (n : nat) (E : coPset) (P : iProp Σ) : iProp Σ :=
    (∀ a, spec_interp a -∗ |={E}=> ∃ a', ⌜is_det (toPacked a') (stepN n a) ⌝ ∗ spec_interp a' ∗ P)%I.
  Local Definition spec_updateN_aux : seal (@spec_updateN_def). Proof. by eexists. Qed.
  Definition spec_updateN := spec_updateN_aux.(unseal).
  Lemma spec_updateN_unseal : spec_updateN = spec_updateN_def.
  Proof. rewrite -spec_updateN_aux.(seal_eq) //. Qed.

  Definition spec_update_def (E : coPset) (P : iProp Σ) : iProp Σ :=
    (∀ a, spec_interp a -∗ |={E}=> ∃ a' n, ⌜is_det (toPacked a') (stepN n a)⌝ ∗ spec_interp a' ∗ P)%I.
  Local Definition spec_update_aux : seal (@spec_update_def). Proof. by eexists. Qed.
  Definition spec_update := spec_update_aux.(unseal).
  Lemma spec_update_unseal : spec_update = spec_update_def.
  Proof. rewrite -spec_update_aux.(seal_eq) //. Qed.

  Lemma spec_updateN_implies_spec_update n E P:
    spec_updateN n E P -∗ spec_update E P.
  Proof.
    rewrite spec_updateN_unseal spec_update_unseal.
    iIntros "H % Ha".
    iMod ("H" with "[$]") as "(%&%&?&?)". iModIntro.
    iExists _, _. iFrame. by iPureIntro.
  Qed.


  Lemma spec_updateN_ret E P :
    P ⊢ spec_updateN 0 E P.
  Proof.
    rewrite spec_updateN_unseal.
    iIntros "HP" (a) "Ha !#".
    iExists a.
    iFrame.
    iPureIntro.
    by rewrite stepN_0 //.
  Qed.

  Lemma spec_update_ret E P :
    P ⊢ spec_update E P.
  Proof.
    rewrite spec_update_unseal.
    iIntros "HP" (a) "Ha !#".
    iExists a, O.
    iFrame.
    iPureIntro.
    rewrite stepN_0.
    by apply is_det_dret.
  Qed.

  Lemma spec_updateN_bind n m E1 E2 P Q :
    E1 ⊆ E2 →
    spec_updateN n E1 P ∗ (P -∗ spec_updateN m E2 Q) ⊢ spec_updateN (n + m) E2 Q.
  Proof.
    rewrite spec_updateN_unseal. iIntros (?) "[P PQ] %a Ha".
    iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
    iMod ("P" $! a with "Ha") as (b Hab) "[Hb P]".
    iMod "Hclose" as "_".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (c Hbc) "[Hc Q]".
    iModIntro. iExists c.
    iFrame.
    iPureIntro.
    by eapply stepN_is_det_trans.
  Qed.

  Lemma spec_update_bind E1 E2 P Q :
    E1 ⊆ E2 →
    spec_update E1 P ∗ (P -∗ spec_update E2 Q) ⊢ spec_update E2 Q.
  Proof.
    rewrite spec_update_unseal. iIntros (HE) "[P PQ] %a Ha".
    iMod (fupd_mask_subseteq E1) as "Hclose"; [done|].
    iMod ("P" $! a with "Ha") as (b n Hab) "[Hb P]".
    iMod "Hclose" as "_".
    iSpecialize ("PQ" with "P").
    iMod ("PQ" $! b with "Hb") as (c m Hbc) "[Hc Q]".
    iModIntro. iExists c, (n + m)%nat.
    iFrame.
    iPureIntro.
    by eapply stepN_is_det_trans.
  Qed.

  Lemma spec_updateN_mono_fupd n E P Q :
    spec_updateN n E P ∗ (P ={E}=∗ Q) ⊢ spec_updateN n E Q.
  Proof.
    rewrite spec_updateN_unseal.
    iIntros "[HP PQ] %a Hsrc".
    iMod ("HP" with "Hsrc") as (b Hstep) "[Hsrc P]".
    iMod ("PQ" with "P"). by iFrame. 
  Qed.

  Lemma spec_update_mono_fupd E P Q :
    spec_update E P ∗ (P ={E}=∗ Q) ⊢ spec_update E Q.
  Proof.
    rewrite spec_update_unseal.
    iIntros "[HP PQ] %a Hsrc".
    iMod ("HP" with "Hsrc") as (b n Hstep) "[Hsrc P]".
    iMod ("PQ" with "P"). iFrame. eauto. 
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
    iIntros "[Hupd HPQ]".
    iApply (spec_update_mono_fupd with "[$Hupd HPQ]").
    iIntros "P". iModIntro. by iApply "HPQ".
  Qed.

  Lemma fupd_spec_updateN n E P :
    (|={E}=> spec_updateN n E P) ⊢ spec_updateN n E P.
  Proof.
    rewrite spec_updateN_unseal.
    iIntros "H %e Hsrc".
    iMod "H".
    by iApply "H".
  Qed.

  Lemma fupd_spec_update E P :
    (|={E}=> spec_update E P) ⊢ spec_update E P.
  Proof.
    rewrite spec_update_unseal.
    iIntros "H %e Hsrc".
    iMod "H". by iApply "H".
  Qed.

  Lemma spec_updateN_frame_l R n E P :
    R ∗ spec_updateN n E P ⊢ spec_updateN n E (P ∗ R).
  Proof.
    iIntros "[HR H]".
    iApply spec_updateN_mono.
    iFrame; eauto.
  Qed.

  Lemma spec_update_frame_l R E P :
    R ∗ spec_update E P ⊢ spec_update E (P ∗ R).
  Proof.
    iIntros "[HR H]".
    iApply spec_update_mono.
    iFrame; eauto.
  Qed.

  Global Instance from_modal_spec_update_spec_update P E :
    FromModal True modality_id (spec_update E P) (spec_update E P) P.
  Proof. iIntros (_) "HP /=". by iApply spec_update_ret. Qed.

  Global Instance elim_modal_spec_update_spec_update P Q E :
    ElimModal True false false (spec_update E P) P (spec_update E Q) (spec_update E Q).
  Proof. iIntros (?) "[HP Hcnt]". by iApply (spec_update_bind with "[$]"). Qed.

  Global Instance frame_spec_update p E R P Q:
    Frame p R P Q → Frame p R (spec_update E P) (spec_update E Q).
  Proof.
    rewrite /Frame=> HR.
    rewrite spec_update_frame_l.
    iIntros "H".
    iApply spec_update_mono; iFrame.
    iIntros "[? ?]".
    iApply HR; iFrame.
  Qed.

  Global Instance from_pure_bupd b E P φ :
    FromPure b P φ → FromPure b (spec_update E P) φ.
  Proof.
    rewrite /FromPure=> HP.
    iIntros "H !>".
    by iApply HP.
  Qed.

  Global Instance into_wand_spec_update p q E R P Q :
    IntoWand false false R P Q → IntoWand p q (spec_update E R) (spec_update E P) (spec_update E Q).
  Proof.
    rewrite /IntoWand /= => HR.
    rewrite !bi.intuitionistically_if_elim.
    iIntros ">HR >HP !>". iApply (HR with "HR HP").
  Qed.

  Global Instance into_wand_bupd_persistent p q E R P Q :
    IntoWand false q R P Q → IntoWand p q (spec_update E R) P (spec_update E Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite bi.intuitionistically_if_elim.
    iIntros ">HR HP !>".
    iApply (HR with "HR HP").
  Qed.

  Global Instance into_wand_bupd_args p q E R P Q :
    IntoWand p false R P Q → IntoWand' p q R (spec_update E P) (spec_update E Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    rewrite bi.intuitionistically_if_elim.
    iIntros "Hw HP".
    iApply spec_update_mono; iFrame.
  Qed.

  Global Instance from_sep_bupd E P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (spec_update E P) (spec_update E Q1) (spec_update E Q2).
  Proof.
    rewrite /FromSep=> HP.
    iIntros "[>HQ1 >HQ2] !>".
    iApply HP. iFrame.
  Qed.

  Global Instance elim_modal_fupd_wp p E P Q :
    ElimModal True p false (|={E}=> P) P (spec_update E Q) (spec_update E Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim => _.
    iIntros "[Hu Hw]".
    iApply fupd_spec_update.
    iMod "Hu".
    iApply ("Hw" with "Hu").
  Qed.

  Global Instance from_exist_spec_update {B} P E (Φ : B → iProp Σ) :
    FromExist P Φ → FromExist (spec_update E P) (λ b, spec_update E (Φ b))%I.
  Proof.
    rewrite /FromExist => HP.
    iIntros "[%x >Hx] !>".
    iApply HP. eauto.
  Qed.

  Global Instance into_forall_spec_update {B} P E (Φ : B → iProp Σ) :
    IntoForall P Φ → IntoForall (spec_update E P) (λ b, spec_update E (Φ b))%I.
  Proof.
    rewrite /IntoForall=>HP.
    iIntros "> H" (b) "!>".
    iApply (HP with "H").
  Qed.

  Global Instance from_assumption_spec_update p E P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (spec_update E Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply spec_update_ret. Qed.

  Global Instance from_modal_spec_updateN_spec_updateN P E :
    FromModal True modality_id (spec_update E P) (spec_updateN 0 E P) P.
  Proof. iIntros (_) "HP /=". by iApply spec_updateN_ret. Qed.

  Global Instance elim_modal_spec_updateN_spec_updateN n m P Q E :
    ElimModal True false false (spec_updateN n E P) P (spec_updateN (n + m) E Q) (spec_updateN m E Q).
  Proof. iIntros (?) "[HP Hcnt]". by iApply (spec_updateN_bind with "[$]"). Qed.

  Global Instance frame_spec_updateN p E n R P Q:
    Frame p R P Q → Frame p R (spec_updateN n E P) (spec_updateN n E Q).
  Proof.
    rewrite /Frame=> HR.
    rewrite spec_updateN_frame_l.
    iIntros "H".
    iApply spec_updateN_mono; iFrame.
    iIntros "[? ?]".
    iApply HR; iFrame.
  Qed.

  Global Instance from_assumption_spec_updateN p E P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (spec_updateN 0 E Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply spec_updateN_ret. Qed.

End spec_update.

