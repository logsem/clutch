From iris.base_logic.lib Require Export fancy_updates invariants.
From iris.proofmode Require Import base tactics classes.
From clutch.coneris Require Import weakestpre primitive_laws.

(** A [wp_update] modality for Coneris that captures propositions that can be elimnated against an
    arbitrary weakest precondition. This includes, e.g., state steps.

    The definition generilizable to any [WP] (modulo elminiating [fupd]). The [TCEq (to_val e) None]
    could be lifted for logics like Approxis that do not require this to do, e.g. state steps. *)

Section wp_update.
  Context `{!conerisGS Σ}.

  Definition wp_update_def (E : coPset) (P : iProp Σ) : iProp Σ :=
    ∀ e Φ, (P -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}.
  Local Definition wp_update_aux : seal (@wp_update_def). Proof. by eexists. Qed.
  Definition wp_update := wp_update_aux.(unseal).
  Lemma wp_update_unseal : wp_update = wp_update_def.
  Proof. rewrite -wp_update_aux.(seal_eq) //. Qed.

  Global Instance elim_modal_wp_update_wp p e E P Φ :
    ElimModal (True) p false (wp_update E P) P (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim => Hv.
    rewrite wp_update_unseal.
    iIntros "[Hu Hw]".
    by iApply "Hu". 
  Qed.

  Lemma wp_update_ret E P :
    P ⊢ wp_update E P.
  Proof.
    rewrite wp_update_unseal.
    iIntros "HP" (e Φ) "Hwp".
    iApply ("Hwp" with "HP").
  Qed.

  Lemma wp_update_bind E P Q :
    wp_update E P ∗ (P -∗ wp_update E Q) ⊢ wp_update E Q.
  Proof.
    rewrite {3}wp_update_unseal.
    iIntros "[HP HQ]" (e Φ) "Hwp".
    iMod "HP".
    iMod ("HQ" with "HP") as "HQ".
    by iApply "Hwp".
  Qed.

  Lemma wp_update_mono_fupd E P Q :
    wp_update E P ∗ (P ={E}=∗ Q) ⊢ wp_update E Q.
  Proof.
    rewrite {2}wp_update_unseal.
    iIntros "[HP Hwand]" (e Φ) "Hwp".
    iMod "HP".
    iMod ("Hwand" with "HP") as "HQ".
    by iApply "Hwp".
  Qed.

  Lemma wp_update_mono E P Q :
    wp_update E P ∗ (P -∗ Q) ⊢ wp_update E Q.
  Proof.
    iIntros "[Hupd HPQ]".
    iApply (wp_update_mono_fupd with "[$Hupd HPQ]").
    iIntros "P". iModIntro. by iApply "HPQ".
  Qed.

  Lemma fupd_wp_update E P :
    (|={E}=> wp_update E P) ⊢ wp_update E P.
  Proof.
    rewrite wp_update_unseal.
    iIntros "H" (e Φ) "Hwp".
    iMod "H". by iApply "H".
  Qed.

  Lemma wp_update_frame_l R E P :
    R ∗ wp_update E P ⊢ wp_update E (P ∗ R).
  Proof.
    iIntros "[HR H]".
    iApply wp_update_mono.
    iFrame. eauto.
  Qed.

  Lemma wp_update_unfold E (P:iProp Σ):
     wp_update E P ⊣⊢
     (∀ e Φ, (P -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}).
  Proof.
    by rewrite wp_update_unseal.
  Qed.

  Lemma wp_update_state_step_coupl P E:
    (∀ σ1 ε1, state_interp σ1 ∗ err_interp ε1 ={E, ∅}=∗
            state_step_coupl σ1 ε1
              (λ σ2 ε2, |={∅, E}=> state_interp σ2 ∗ err_interp ε2 ∗ P))
    -∗ wp_update E P.
  Proof.
    iIntros "H".
    rewrite wp_update_unseal/wp_update_def.
    iIntros (??) "H'".
    iApply state_step_coupl_pgl_wp.
    iIntros (??) "[??]".
    iMod ("H" with "[$]") as "H".
    iModIntro.
    iApply (state_step_coupl_bind with "[H']"); last done.
    simpl.
    iIntros (??) "H".
    iApply state_step_coupl_ret.
    iMod "H" as "(?&?&?)".
    iFrame.
    by iApply "H'".
  Qed.

  Lemma wp_update_epsilon_err E:
    ⊢ wp_update E (∃ ε, ⌜(0<ε)%R⌝ ∗ ↯ ε).
  Proof.
    iApply wp_update_state_step_coupl.
    iIntros (? ε) "[Hstate Herr]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply state_step_coupl_ampl'.
    iIntros (ε' ?).
    iApply state_step_coupl_ret.
    assert (ε<=ε')%R as H' by lra.
    pose (diff :=((ε' - ε) H')%NNR).
    replace (ε') with (ε + diff)%NNR; last (apply nnreal_ext; rewrite /diff; simpl; lra).
    iMod (ec_supply_increase _ diff with "[$]") as "[??]".
    { rewrite /diff. simpl. lra. }
    iFrame. iMod "Hclose". iPureIntro.
    rewrite /diff.
    simpl.
    lra.
  Qed.
  
  Global Instance from_modal_wp_update_wp_update P E :
    FromModal True modality_id (wp_update E P) (wp_update E P) P.
  Proof. iIntros (_) "HP /=". by iApply wp_update_ret. Qed.

  Global Instance elim_modal_wp_update_wp_update P Q E :
    ElimModal True false false (wp_update E P) P (wp_update E Q) (wp_update E Q).
  Proof. iIntros (?) "[HP Hcnt]". by iApply (wp_update_bind with "[$]"). Qed.

  Global Instance frame_wp_update p E R P Q:
    Frame p R P Q → Frame p R (wp_update E P) (wp_update E Q).
  Proof.
    rewrite /Frame=> HR.
    rewrite wp_update_frame_l.
    iIntros "H".
    iApply wp_update_mono; iFrame.
    iIntros "[? ?]".
    iApply HR; iFrame.
  Qed.

  Global Instance from_pure_bupd b E P φ :
    FromPure b P φ → FromPure b (wp_update E P) φ.
  Proof.
    rewrite /FromPure=> HP.
    iIntros "H !>".
    by iApply HP.
  Qed.

  Global Instance into_wand_wp_update p q E R P Q :
    IntoWand false false R P Q → IntoWand p q (wp_update E R) (wp_update E P) (wp_update E Q).
  Proof.
    rewrite /IntoWand /= => HR.
    rewrite !bi.intuitionistically_if_elim.
    iIntros ">HR >HP !>". iApply (HR with "HR HP").
  Qed.

  Global Instance into_wand_bupd_persistent p q E R P Q :
    IntoWand false q R P Q → IntoWand p q (wp_update E R) P (wp_update E Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite bi.intuitionistically_if_elim.
    iIntros ">HR HP !>".
    iApply (HR with "HR HP").
  Qed.

  Global Instance into_wand_bupd_args p q E R P Q :
    IntoWand p false R P Q → IntoWand' p q R (wp_update E P) (wp_update E Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    rewrite bi.intuitionistically_if_elim.
    iIntros "Hw HP".
    iApply wp_update_mono; iFrame.
  Qed.

  Global Instance from_sep_bupd E P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (wp_update E P) (wp_update E Q1) (wp_update E Q2).
  Proof.
    rewrite /FromSep=> HP.
    iIntros "[>HQ1 >HQ2] !>".
    iApply HP. iFrame.
  Qed.

  Global Instance elim_modal_fupd_wp p E P Q :
    ElimModal True p false (|={E}=> P) P (wp_update E Q) (wp_update E Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim => _.
    iIntros "[Hu Hw]".
    iApply fupd_wp_update.
    iMod "Hu".
    iApply ("Hw" with "Hu").
  Qed.

  Global Instance from_exist_wp_update {B} P E (Φ : B → iProp Σ) :
    FromExist P Φ → FromExist (wp_update E P) (λ b, wp_update E (Φ b))%I.
  Proof.
    rewrite /FromExist => HP.
    iIntros "[%x >Hx] !>".
    iApply HP. eauto.
  Qed.

  Global Instance into_forall_wp_update {B} P E (Φ : B → iProp Σ) :
    IntoForall P Φ → IntoForall (wp_update E P) (λ b, wp_update E (Φ b))%I.
  Proof.
    rewrite /IntoForall=>HP.
    iIntros "> H" (b) "!>".
    iApply (HP with "H").
  Qed.

  Global Instance from_assumption_wp_update p E P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (wp_update E Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply wp_update_ret. Qed.

End wp_update.

