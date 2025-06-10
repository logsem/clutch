From iris.base_logic.lib Require Export fancy_updates invariants.
From iris.proofmode Require Import base tactics classes.
From clutch.con_prob_lang Require Import lang.
From clutch.foxtrot Require Import weakestpre.

Section pupd.
  Context `{H:!foxtrotWpGS con_prob_lang Σ}.
  Definition pupd_def E1 E2 P:=
    (∀ σ1 ρ1 ε1,
       state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E1, ∅}=∗
       spec_coupl σ1 ρ1 ε1 (λ σ2 ρ2 ε2,
                                 |={∅, E2}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗ P
         )
    )%I.
  
  Local Definition pupd_aux : seal (@pupd_def). Proof. by eexists. Qed.
  Definition pupd := pupd_aux.(unseal).
  Lemma pupd_unseal : pupd = pupd_def.
  Proof. rewrite -pupd_aux.(seal_eq) //. Qed.

  Lemma pupd_ret E P:
    P -∗ pupd E E P.
  Proof. 
    rewrite pupd_unseal/pupd_def.
    iIntros.
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iApply spec_coupl_ret.
    iMod "Hclose".
    iFrame. by iModIntro.
  Qed.

  Global Instance from_modal_pupd_pupd P E :
    FromModal True modality_id (pupd E E P) (pupd E E P) P.
  Proof. iIntros (_) "HP /=". by iApply pupd_ret. Qed.
    
  Lemma pupd_mono_fupd E1 E2 E3 P:
    E1 ⊆ E2 -> (|={E2,E1}=> pupd E1 E3 P) -∗ pupd E2 E3 P.
  Proof.
    rewrite pupd_unseal/pupd_def.
    iIntros (Hsubseteq) "Hvs".
    iIntros (σ1 ρ1 ε1) "(H1 & H2 & H3)".
    iMod ("Hvs" with "[$]") as ">?".
    iModIntro.
    iApply (spec_coupl_mono with "[][$]").
    iIntros (???) ">(?&?&?)". by iFrame.
  Qed.
  
  Lemma pupd_mono E1 E2 P Q:
    (P={E2}=∗Q) -∗ pupd E1 E2 P -∗ pupd E1 E2 Q.
  Proof.
    rewrite pupd_unseal/pupd_def.
    iIntros "Hvs H".
    iIntros (σ1 ρ1 ε1) "(H1 & H2 & H3)".
    iMod ("H" with "[$]") as "?".
    iModIntro.
    iApply (spec_coupl_mono with "[Hvs][$]").
    iIntros (???) ">(?&?&?&?)".
    iFrame.
    by iApply "Hvs".
  Qed.
  
  Lemma pupd_mono_fupd' E1 E2 P:
    E1 ⊆ E2 -> (pupd E1 E1 P) -∗ pupd E2 E2 P.
  Proof.
    iIntros (?) "H".
    iApply pupd_mono_fupd; first done.
    iApply fupd_mask_intro; first done.
    iIntros "Hclose".
    rewrite pupd_unseal/pupd_def.
    iIntros.
    iMod ("H" with "[$]") as "H".
    iModIntro.
    iApply (spec_coupl_bind with "[Hclose][$]").
    iIntros (???) "H". iApply spec_coupl_ret.
    iMod "H".
    by iMod "Hclose".
  Qed.
  
  Lemma pupd_fupd E1 E2 P:
    (|={E1}=> pupd E1 E2 P) -∗ pupd E1 E2 P.
  Proof.
    iIntros "H".
    iApply pupd_mono_fupd; first done.
    iMod "H".
    iApply pupd_mono; last done.
    by iIntros.
  Qed.
  
  Lemma pupd_fupd_change E1 E2 E3 P Q:
    (|={E1, E2}=> P) -∗ (P-∗ pupd E2 E3 Q) -∗ pupd E1 E3 Q.
  Proof.
    iIntros "H1 H2".
    rewrite pupd_unseal/pupd_def.
    iIntros (???) "(?&?&?)".
    iMod "H1".
    iMod ("H2" with "[$][$]") as "H2".
    iModIntro.
    iApply spec_coupl_mono; last done.
    simpl.
    iIntros (???) ">(?&?&?&?)".
    by iFrame.
  Qed.

  Global Instance elim_modal_bupd_pupd p E1 E2 P Q :
    ElimModal True p false (|==> P) P (pupd E1 E2 Q) (pupd E1 E2 Q).
  Proof.
    intros ?.
    rewrite bi.intuitionistically_if_elim/=.
    iIntros "[H1 H2]".
    iApply pupd_fupd.
    iMod "H1".
    iModIntro.
    by iApply "H2".
  Qed.
  
  Global Instance elim_modal_fupd_pupd p E1 E2 E3 P Q :
    ElimModal (True) p false
            (|={E1,E2}=> P) P
            (pupd E1 E3 Q) (pupd E2 E3 Q).
  Proof.
    intros ?.
    rewrite bi.intuitionistically_if_elim/=.
    iIntros "[??]".
    iApply (pupd_fupd_change with "[$][$]").
  Qed.

  
  Lemma pupd_mask_intro E1 E2 P:
    E2 ⊆ E1 -> (pupd E2 E1 emp -∗ P) -∗ pupd E1 E2 P.
  Proof.
    iIntros (?) "H".
    iApply pupd_mono_fupd; first exact.
    iApply fupd_mask_intro; first done.
    iIntros "K".
    iModIntro.
    iApply "H".
    iMod "K".
    by iModIntro.
  Qed.
  
  Lemma pupd_bind E1 E2 E3 P Q:
    pupd E1 E2 P ∗ (P -∗ pupd E2 E3 Q) ⊢ pupd E1 E3 Q.
  Proof.
    rewrite pupd_unseal/pupd_def.
    iIntros "[H1 H2]" (???) "(?&?&?)".
    iMod ("H1" with "[$]") as "H1".
    iModIntro.
    iApply (spec_coupl_bind with "[H2][$]").
    iIntros (???) "H1".
    iApply fupd_spec_coupl.
    iMod "H1" as "(?&?&?&?)".
    by iMod ("H2" with "[$][$]").
  Qed.

  Global Instance elim_modal_pupd_pupd p E1 E2 E3 P Q :
    ElimModal (True) p false (pupd E1 E2 Q) Q (pupd E1 E3 P) (pupd E2 E3 P).
  Proof.
    iIntros (_) "[H1 H2]".
    rewrite bi.intuitionistically_if_elim.
    iApply pupd_mono_fupd; first exact.
    iApply fupd_mask_intro; first exact; iIntros "Hclose".
    iApply pupd_bind; iFrame.
  Qed.
   
  Global Instance elim_modal_pupd_wp e Φ p E1 E2 P :
    ElimModal (E1 ⊆ E2) p false (pupd E1 E1 P) P (WP e @ E2 {{ Φ }}) (WP e @ E2 {{ Φ }}).
  Proof.
    destruct p.
    all: iIntros (?); simpl; iIntros "[H1 H2]".
    1: iDestruct (bi.intuitionistically_elim with "[$]") as "H1".
    all: iDestruct (pupd_mono_fupd with "[H1]") as "H1"; first exact;
      last first.
    - iApply spec_coupl_wp.
      rewrite -/(pupd_def _ _ _).
      rewrite -pupd_unseal.
      iMod "H1".
      iModIntro.
      iApply "H2".
      iApply "H1".
    - iApply fupd_mask_intro; first exact; iIntros "Hclose"; iMod "H1"; iMod "Hclose"; by iModIntro.
    - iApply spec_coupl_wp.
      rewrite -/(pupd_def _ _ _).
      rewrite -pupd_unseal.
      iMod "H1".
      iModIntro.
      iApply "H2".
      iApply "H1".
    - iApply fupd_mask_intro; first exact; iIntros "Hclose"; iMod "H1"; iMod "Hclose"; by iModIntro.
  Qed.

  Global Instance is_except_0_pupd E1 E2 Q : IsExcept0 (pupd E1 E2 Q).
  Proof.
    rewrite /IsExcept0.
    iIntros.
    iApply (pupd_fupd E1 E2 Q). by rewrite -except_0_fupd -fupd_intro.
  Qed.

  Lemma pupd_frame_l R E1 E2 P :
    R ∗ pupd E1 E2 P ⊢ pupd E1 E2 (P ∗ R).
  Proof.
    iIntros "[HR H]".
    iMod "H".
    iModIntro.
    iFrame. 
  Qed.

  Global Instance frame_pupd p E R P Q:
    Frame p R P Q → Frame p R (pupd E E P) (pupd E E Q).
  Proof.
    rewrite /Frame=> HR.
    rewrite pupd_frame_l.
    iIntros ">[??]".
    iModIntro.
    iApply HR; iFrame.
  Qed.

  Global Instance from_pure_bupd_pupd b E P φ :
    FromPure b P φ → FromPure b (pupd E E P) φ.
  Proof.
    rewrite /FromPure=> HP.
    iIntros "H !>".
    by iApply HP.
  Qed.

  Global Instance into_wand_pupd p q E R P Q :
    IntoWand false false R P Q → IntoWand p q (pupd E E R) (pupd E E P) (pupd E E Q).
  Proof.
    rewrite /IntoWand /= => HR.
    rewrite !bi.intuitionistically_if_elim.
    iIntros ">HR >HP !>". iApply (HR with "HR HP").
  Qed.

  Global Instance into_wand_bupd_persistent_pupd p q E R P Q :
    IntoWand false q R P Q → IntoWand p q (pupd E E R) P (pupd E E Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite bi.intuitionistically_if_elim.
    iIntros ">HR HP !>".
    iApply (HR with "HR HP").
  Qed.

  Global Instance into_wand_bupd_args_pupd p q E R P Q :
    IntoWand p false R P Q → IntoWand' p q R (pupd E E P) (pupd E E Q). 
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    rewrite bi.intuitionistically_if_elim.
    iIntros "Hw HP".
    iMod "HP".
    iModIntro.
    by iApply "Hw".
  Qed.

  Global Instance from_sep_bupd_pupd E P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (pupd E E P) (pupd E E Q1) (pupd E E Q2).
  Proof.
    rewrite /FromSep=> HP.
    iIntros "[>HQ1 >HQ2] !>".
    iApply HP. iFrame.
  Qed.

  Global Instance from_exist_pupd {B} P E (Φ : B → iProp Σ) :
    FromExist P Φ → FromExist (pupd E E P) (λ b, pupd E E (Φ b))%I.
  Proof.
    rewrite /FromExist => HP.
    iIntros "[%x >Hx] !>".
    iApply HP. eauto.
  Qed.

  Global Instance into_forall_pupd {B} P E (Φ : B → iProp Σ) :
    IntoForall P Φ → IntoForall (pupd E E P) (λ b, pupd E E (Φ b))%I.
  Proof.
    rewrite /IntoForall=>HP.
    iIntros "> H" (b) "!>".
    iApply (HP with "H").
  Qed.

  Global Instance from_assumption_pupd p E P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (pupd E E Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. iApply pupd_ret. Qed.

  Lemma wp_pupd Φ E e:
    WP e @ E {{ λ x, pupd E E (Φ x) }} ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros.
    rewrite pupd_unseal/pupd_def.
    iApply (wp_strong_mono with "[$]"); first done.
    iIntros (????) "(?&?&?&H)".
    iMod ("H" with "[$]").
    by iModIntro.
  Qed.
  
  (** pupd works for allocation of invariants and ghost resources *)
  Lemma pupd_inv_alloc E P N:
    ▷ P -∗ pupd E E (inv N P).
  Proof.
    iIntros "HP".
    by iMod (inv_alloc with "[$]").
  Qed.

  Lemma pupd_inv_acc P E I N:
    ↑N ⊆ E -> inv N I -∗ (▷I -∗ pupd (E∖↑N) (E∖↑N) (P∗▷I)) -∗ pupd E E P.
  Proof.
    iIntros (Hsubset) "#Hinv H".
    iInv "Hinv" as "?" "Hclose".
    iMod ("H" with "[$]") as "[??]".
    iFrame. by iMod ("Hclose" with "[$]") as "_".
  Qed.

  Lemma pupd_inv_acc' E I N:
    ↑N ⊆ E -> inv N I -∗ pupd E (E ∖↑N) (▷ I ∗ (▷ I -∗ pupd (E∖↑N) E True)).
  Proof.
    iIntros (Hsubset) "#Hinv".
    iDestruct (inv_acc with "[$]") as ">(H&Hvs)"; first exact.
    iModIntro. iFrame.
    iIntros.
    by iMod ("Hvs" with "[$]").
  Qed.
  
  Context {A : cmra} `{i : inG Σ A}.
  Lemma pupd_ra_alloc E (a:A):
    ✓ a -> ⊢ pupd E E (∃ γ, own γ a).
  Proof.
    iIntros "%".
    by iMod (own_alloc).
  Qed.
  
End pupd.

