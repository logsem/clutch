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

  Lemma fupd_wp_update_ret E P:
    (|={E}=> P) ⊢ wp_update E P.
  Proof.
    iIntros "H".
    iApply fupd_wp_update.
    by iApply wp_update_ret.
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

  Global Instance elim_modal_wp_update_wp_update b P Q E :
    ElimModal True b false (wp_update E P) P (wp_update E Q) (wp_update E Q).
  Proof. iIntros (?) "[HP Hcnt]".
         destruct b.
         - iApply (wp_update_bind); iFrame.
           by iApply bi.intuitionistically_elim.
         - by iApply (wp_update_bind with "[$]"). Qed.

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

  Global Instance is_except_0_wp_update E Q : IsExcept0 (wp_update E Q).
  Proof.
    by rewrite /IsExcept0 -{2}fupd_wp_update -except_0_fupd -fupd_intro.
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

Section state_update.
  Context `{!conerisGS Σ}.
  Definition state_update_def E1 E2 P:=
    (∀ σ1 ε1,
       state_interp σ1 ∗ err_interp ε1 ={E1, ∅}=∗
       state_step_coupl σ1 ε1 (λ σ2 ε2,
                                 |={∅, E2}=> state_interp σ2 ∗ err_interp ε2 ∗ P
         )
    )%I.
  
  Local Definition state_update_aux : seal (@state_update_def). Proof. by eexists. Qed.
  Definition state_update := state_update_aux.(unseal).
  Lemma state_update_unseal : state_update = state_update_def.
  Proof. rewrite -state_update_aux.(seal_eq) //. Qed.

  Lemma wp_update_state_update E P:
    state_update E E P -∗ wp_update E P.
  Proof.
    rewrite state_update_unseal/state_update_def.
    iIntros.
    by iApply wp_update_state_step_coupl.
  Qed.

  Lemma state_update_ret E P:
    P -∗ state_update E E P.
  Proof. 
    rewrite state_update_unseal/state_update_def.
    iIntros.
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply state_step_coupl_ret.
    iMod "Hclose".
    iFrame. by iModIntro.
  Qed.

  Global Instance from_modal_state_update_state_update P E :
    FromModal True modality_id (state_update E E P) (state_update E E P) P.
  Proof. iIntros (_) "HP /=". by iApply state_update_ret. Qed.
    
  Lemma state_update_mono_fupd E1 E2 E3 P:
    E1 ⊆ E2 -> (|={E2,E1}=> state_update E1 E3 P) -∗ state_update E2 E3 P.
  Proof.
    rewrite state_update_unseal/state_update_def.
    iIntros (Hsubseteq) "Hvs".
    iIntros (σ1 ε1) "[H1 H2]".
    iMod ("Hvs" with "[$]") as ">?".
    iModIntro.
    iApply (state_step_coupl_mono with "[][$]").
    iIntros (??) ">(?&?&?)". by iFrame.
  Qed.

  
  Lemma state_update_mono E1 E2 P Q:
    (P={E2}=∗Q) -∗ state_update E1 E2 P -∗ state_update E1 E2 Q.
  Proof.
    rewrite state_update_unseal/state_update_def.
    iIntros "Hvs H".
    iIntros (σ1 ε1) "[H1 H2]".
    iMod ("H" with "[$]") as "?".
    iModIntro.
    iApply (state_step_coupl_mono with "[Hvs][$]").
    iIntros (??) ">(?&?&?)".
    iFrame.
    by iApply "Hvs".
  Qed.
  
  Lemma state_update_mono_fupd' E1 E2 P:
    E1 ⊆ E2 -> (state_update E1 E1 P) -∗ state_update E2 E2 P.
  Proof.
    iIntros (?) "H".
    iApply state_update_mono_fupd; first done.
    iApply fupd_mask_intro; first done.
    iIntros "Hclose".
    rewrite state_update_unseal/state_update_def.
    iIntros.
    iMod ("H" with "[$]") as "H".
    iModIntro.
    iApply (state_step_coupl_bind with "[Hclose][$]").
    iIntros (??) "H". iApply state_step_coupl_ret.
    iMod "H".
    by iMod "Hclose".
  Qed.
  
  Lemma state_update_fupd E1 E2 P:
    (|={E1}=> state_update E1 E2 P) -∗ state_update E1 E2 P.
  Proof.
    iIntros "H".
    iApply state_update_mono_fupd; first done.
    iMod "H".
    iApply state_update_mono; last done.
    by iIntros.
  Qed.

  
  Lemma state_update_epsilon_err E:
    ⊢ state_update E E (∃ ε, ⌜(0<ε)%R⌝ ∗ ↯ ε).
  Proof.
    rewrite state_update_unseal/state_update_def.
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
  
  Lemma state_update_fupd_change E1 E2 E3 P Q:
    (|={E1, E2}=> P) -∗ (P-∗ state_update E2 E3 Q) -∗ state_update E1 E3 Q.
  Proof.
    iIntros "H1 H2".
    rewrite state_update_unseal/state_update_def.
    iIntros (??) "[??]".
    iMod "H1".
    iMod ("H2" with "[$][$]") as "H2".
    iModIntro.
    iApply state_step_coupl_mono; last done.
    simpl.
    iIntros (??) ">(?&?&?)".
    by iFrame.
  Qed.

  Global Instance elim_modal_bupd_state_update p E1 E2 P Q :
    ElimModal True p false (|==> P) P (state_update E1 E2 Q) (state_update E1 E2 Q).
  Proof.
    intros ?.
    rewrite bi.intuitionistically_if_elim/=.
    iIntros "[H1 H2]".
    iApply state_update_fupd.
    iMod "H1".
    iModIntro.
    by iApply "H2".
  Qed.
  
  Global Instance elim_modal_fupd_state_update p E1 E2 E3 P Q :
    ElimModal (True) p false
            (|={E1,E2}=> P) P
            (state_update E1 E3 Q) (state_update E2 E3 Q).
  Proof.
    intros ?.
    rewrite bi.intuitionistically_if_elim/=.
    iIntros "[??]".
    iApply (state_update_fupd_change with "[$][$]").
  Qed.
  
  Lemma state_update_bind E1 E2 E3 P Q:
    state_update E1 E2 P ∗ (P -∗ state_update E2 E3 Q) ⊢ state_update E1 E3 Q.
  Proof.
    rewrite state_update_unseal/state_update_def.
    iIntros "[H1 H2]" (??) "[??]".
    iMod ("H1" with "[$]") as "H1".
    iModIntro.
    iApply (state_step_coupl_bind with "[H2][$]").
    iIntros (??) "H1".
    iApply fupd_state_step_coupl.
    iMod "H1" as "(?&?&?)".
    by iMod ("H2" with "[$][$]").
  Qed.

  Global Instance elim_modal_state_update_state_update p E1 E2 E3 P Q :
    ElimModal (True) p false (state_update E1 E2 Q) Q (state_update E1 E3 P) (state_update E2 E3 P).
  Proof.
    iIntros (_) "[H1 H2]".
    rewrite bi.intuitionistically_if_elim.
    iApply state_update_mono_fupd; first exact.
    iApply fupd_mask_intro; first exact; iIntros "Hclose".
    iApply state_update_bind; iFrame.
  Qed.
 
  Global Instance elim_modal_state_update_wp_update p E1 E2 P Q :
    ElimModal (E1 ⊆ E2) p false (state_update E1 E1 Q) Q (wp_update E2 P) (wp_update E2 P).
  Proof.
    (* rewrite state_update_unseal/state_update_def. *)
    iIntros (?) "[H1 H2]".
    iApply (wp_update_bind).
    iFrame.
    iApply wp_update_state_update.
    iIntros.
    iApply state_update_mono_fupd; first exact.
    iApply fupd_mask_intro; first done.
    iIntros "Hclose".
    destruct p; simpl.
    - iDestruct (bi.intuitionistically_elim with "[$]") as "H1".
      iMod "H1".
      iMod "Hclose" as "_".
      by iModIntro.
    - iMod "H1".
      iMod "Hclose" as "_".
      by iModIntro.
  Qed.
  
  Global Instance elim_modal_state_update_wp e Φ p E1 E2 P :
    ElimModal (E1 ⊆ E2) p false (state_update E1 E1 P) P (WP e @ E2 {{ Φ }}) (WP e @ E2 {{ Φ }}).
  Proof.
    destruct p.
    all: iIntros (?); simpl; iIntros "[H1 H2]".
    1: iDestruct (bi.intuitionistically_elim with "[$]") as "H1".
    all: iDestruct (state_update_mono_fupd with "[H1]") as "H1"; first exact;
      last (iDestruct (wp_update_state_update with "[$]") as "H1"; iMod "H1"; by iApply "H2").
    all: iApply fupd_mask_intro; first exact; iIntros "Hclose"; iMod "H1"; iMod "Hclose"; by iModIntro.
  Qed.

  Lemma state_update_wp E P e Φ:
    (state_update E E P) -∗ (P -∗ WP e @ E {{Φ}}) -∗ WP e @ E {{Φ}}.
  Proof.
    iIntros ">? H".
    by iApply "H".
  Qed.

  Global Instance is_except_0_state_update E1 E2 Q : IsExcept0 (state_update E1 E2 Q).
  Proof.
    rewrite /IsExcept0.
    iIntros.
    iApply (state_update_fupd E1 E2 Q). by rewrite -except_0_fupd -fupd_intro.
  Qed.

  Lemma state_update_frame_l R E1 E2 P :
    R ∗ state_update E1 E2 P ⊢ state_update E1 E2 (P ∗ R).
  Proof.
    iIntros "[HR H]".
    iMod "H".
    iModIntro.
    iFrame. 
  Qed.

  Global Instance frame_state_update p E R P Q:
    Frame p R P Q → Frame p R (state_update E E P) (state_update E E Q).
  Proof.
    rewrite /Frame=> HR.
    rewrite state_update_frame_l.
    iIntros ">[??]".
    iModIntro.
    iApply HR; iFrame.
  Qed.

  Global Instance from_pure_bupd_state_update b E P φ :
    FromPure b P φ → FromPure b (state_update E E P) φ.
  Proof.
    rewrite /FromPure=> HP.
    iIntros "H !>".
    by iApply HP.
  Qed.

  Global Instance into_wand_state_update p q E R P Q :
    IntoWand false false R P Q → IntoWand p q (state_update E E R) (state_update E E P) (state_update E E Q).
  Proof.
    rewrite /IntoWand /= => HR.
    rewrite !bi.intuitionistically_if_elim.
    iIntros ">HR >HP !>". iApply (HR with "HR HP").
  Qed.

  Global Instance into_wand_bupd_persistent_state_update p q E R P Q :
    IntoWand false q R P Q → IntoWand p q (state_update E E R) P (state_update E E Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite bi.intuitionistically_if_elim.
    iIntros ">HR HP !>".
    iApply (HR with "HR HP").
  Qed.

  Global Instance into_wand_bupd_args_state_update p q E R P Q :
    IntoWand p false R P Q → IntoWand' p q R (state_update E E P) (state_update E E Q). 
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    rewrite bi.intuitionistically_if_elim.
    iIntros "Hw HP".
    iMod "HP".
    iModIntro.
    by iApply "Hw".
  Qed.

  Global Instance from_sep_bupd_state_update E P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (state_update E E P) (state_update E E Q1) (state_update E E Q2).
  Proof.
    rewrite /FromSep=> HP.
    iIntros "[>HQ1 >HQ2] !>".
    iApply HP. iFrame.
  Qed.

  Global Instance from_exist_state_update {B} P E (Φ : B → iProp Σ) :
    FromExist P Φ → FromExist (state_update E E P) (λ b, state_update E E (Φ b))%I.
  Proof.
    rewrite /FromExist => HP.
    iIntros "[%x >Hx] !>".
    iApply HP. eauto.
  Qed.

  Global Instance into_forall_state_update {B} P E (Φ : B → iProp Σ) :
    IntoForall P Φ → IntoForall (state_update E E P) (λ b, state_update E E (Φ b))%I.
  Proof.
    rewrite /IntoForall=>HP.
    iIntros "> H" (b) "!>".
    iApply (HP with "H").
  Qed.

  Global Instance from_assumption_state_update p E P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (state_update E E Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. iApply state_update_ret. Qed.

  Lemma pgl_wp_state_update Φ E e:
    WP e @ E {{ λ x, state_update E E (Φ x) }} ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros.
    rewrite state_update_unseal/state_update_def.
    iApply (pgl_wp_strong_mono with "[$]"); first done.
    iIntros (???) "(?&?&H)". 
    iMod ("H" with "[$]").
    by iModIntro.
  Qed.
  
  (** state_update works for allocation of invariants and ghost resources *)
  Lemma state_update_inv_alloc E P N:
    ▷ P -∗ state_update E E (inv N P).
  Proof.
    iIntros "HP".
    by iMod (inv_alloc with "[$]").
  Qed.

  Lemma state_update_inv_acc P E I N:
    ↑N ⊆ E -> inv N I -∗ (▷I -∗ state_update (E∖↑N) (E∖↑N) (P∗▷I)) -∗ state_update E E P.
  Proof.
    iIntros (Hsubset) "#Hinv H".
    iInv "Hinv" as "?" "Hclose".
    iMod ("H" with "[$]") as "[??]".
    iFrame. by iMod ("Hclose" with "[$]") as "_".
  Qed.
  
  Context {A : cmra} `{i : inG Σ A}.
  Lemma state_update_ra_alloc E (a:A):
    ✓ a -> ⊢ state_update E E (∃ γ, own γ a).
  Proof.
    iIntros "%H".
    by iMod (own_alloc).
  Qed.
  
End state_update.
