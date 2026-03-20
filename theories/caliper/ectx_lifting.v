(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import proofmode.

From clutch.common Require Export ectx_language.
From clutch.caliper Require Export weakestpre lifting.
Set Default Proof Using "Type".

#[local] Open Scope R. 

Section rwp.
Context {Λ : ectxLanguage} `{!spec_updateGS δ Σ, !caliperWpG δ Λ Σ}.

Implicit Types P Q : iProp Σ.
Implicit Types a : mstate δ.
Implicit Types b : bool.
Implicit Types Φ : val Λ → iProp Σ.
Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Hint Resolve head_stuck_stuck : core.

Lemma rwp_lift_head_step_fupd {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1 a1, state_interp σ1 ∗ spec_interp a1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2,
      ⌜head_step e1 σ1 (e2, σ2) > 0%R⌝ ={∅,E}=∗
      state_interp σ2 ∗ spec_interp a1 ∗
      WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply rwp_lift_step_fupd=>//. iIntros (σ1 a) "Hσ".
  iMod ("H" with "Hσ") as "[%Hred H]".  iModIntro.
  iSplit.
  { iPureIntro. by eapply head_prim_reducible. }
  iIntros (e2 σ2 ?) "!>".
  iApply "H". eauto.
Qed.

Lemma rwp_lift_atomic_head_step_fupd {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1 a1, state_interp σ1 ∗ spec_interp a1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0%R⌝ ={E}=∗
      state_interp σ2 ∗
      spec_interp a1 ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply rwp_lift_atomic_step_fupd; [done|].
  iIntros (σ1 a) "H'".
  iMod ("H"  with "H'") as "[%Hred H]".
  iModIntro.
  iSplit.
  { iPureIntro. by eapply head_prim_reducible. }
  iIntros (e2 σ2 Hstep).
  iApply "H". eauto.
Qed.

Lemma rwp_lift_pure_head_step `{!Inhabited (state Λ)} E Φ e1 s :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2 σ2, head_step e1 σ1 (e2, σ2) > 0%R → σ2 = σ1) →
  (∀ e2 σ, ⌜head_step e1 σ (e2, σ) > 0%R⌝ → WP e2 @ s; E {{ Φ }})%I
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros Hsafe Hstep.
  iIntros "H". iApply rwp_lift_head_step_fupd; auto.
  { by eapply (to_final_None_1 (e1, inhabitant)), reducible_not_final, head_prim_reducible.  }
  iIntros (σ1 a) "[Ha Hσ]". iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
  iModIntro. iSplit; auto.
  iIntros (e2 σ2 H').
  pose proof (Hstep _ _ _ H'). subst.
  iMod "Hclose" as "_". iModIntro.
  iDestruct ("H" with "[//]") as "H". iFrame.
Qed.

Lemma rwp_lift_pure_det_head_step `{!Inhabited (state Λ)} {E Φ} e1 e2 s :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2,
    head_step e1 σ1 (e2', σ2) > 0%R → σ2 = σ1 ∧ e2' = e2) →
  (WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros H2 Hstep Hpuredet.
  iIntros "H". iApply rwp_lift_pure_head_step; auto.
  { naive_solver. }
  by iIntros (e' σ (_&->)%Hpuredet).
Qed.

(** * RSWP *)
Lemma rswp_lift_head_step_fupd {k E Φ} e1 s :
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    |={∅}[∅]▷=>^k ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0%R⌝ ={∅,E}=∗
      state_interp σ2 ∗
      WP e2 @ s; E {{ Φ }})
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply rswp_lift_step_fupd=>//. iIntros (σ1) "Hσ".
  iMod ("H" with "Hσ") as "H". iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "[% H]".
  iSplit.
  { iPureIntro. by eapply head_prim_reducible. }
  iIntros (e2 σ2 ?).
  iApply "H"; eauto.
Qed.

Lemma rswp_lift_atomic_head_step_fupd {k E Φ} e1 s :
  (∀ σ1, state_interp σ1 ={E}=∗
    |={E}[E]▷=>^k ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0%R⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply rswp_lift_atomic_step_fupd; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "H"; iModIntro.
  iApply (step_fupdN_wand with "H"); iIntros "[% H]".
  iSplit.
  { iPureIntro. by eapply head_prim_reducible. }
  iIntros (e2 σ2 Hstep).
  iApply "H"; eauto.
Qed.

Lemma rswp_lift_atomic_head_step {k E Φ} e1 s :
  (∀ σ1, state_interp σ1 ={E}=∗
    ▷^k (⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0%R⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2)))
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply rswp_lift_atomic_head_step_fupd; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "H"; iModIntro.
  by iApply step_fupdN_intro.
Qed.

Lemma rswp_lift_pure_head_step_fupd k E Φ e1 s :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2 σ2, head_step e1 σ1 (e2, σ2) > 0%R → σ2 = σ1) →
  (|={E}[E]▷=>^k ∀ e2 σ, ⌜head_step e1 σ (e2, σ) > 0%R⌝ → WP e2 @ s; E {{ Φ }})%I
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  intros Hsafe Hstep.
  iIntros "H". iApply rswp_lift_pure_step.
  { intros. by eapply head_prim_reducible. }
  { eauto. }
  iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "H" (e2 σ Hs).
  iApply "H"; eauto. iPureIntro.
  apply (head_reducible_prim_step _ σ); eauto.
Qed.

Lemma rswp_lift_pure_head_step k E Φ e1 s :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2 σ2, head_step e1 σ1 (e2, σ2) > 0%R → σ2 = σ1) →
  (▷^k ∀ e2 σ, ⌜head_step e1 σ (e2, σ) > 0%R⌝ → WP e2 @ s; E {{ Φ }})%I
  ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (Hsafe Hstep) "H".
  iApply rswp_lift_pure_head_step_fupd; eauto.
  by iApply step_fupdN_intro.
Qed.

Lemma rswp_lift_pure_det_head_step_fupd {k E Φ} e1 e2 s :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2,
    head_step e1 σ1 (e2', σ2) > 0%R → σ2 = σ1 ∧ e2' = e2) →
  (|={E}[E]▷=>^k WP e2 @ s; E {{ Φ }}) ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (Hstep Hdet) "H". iApply rswp_lift_pure_head_step_fupd; eauto.
  { naive_solver. }
  iApply (step_fupdN_wand with "H"); by iIntros "H" (e2' σ (_&->)%Hdet).
Qed.

Lemma rswp_lift_pure_det_head_step {k E Φ} e1 e2 s :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2,
    head_step e1 σ1 (e2', σ2) > 0%R → σ2 = σ1 ∧ e2' = e2) →
  (▷^k WP e2 @ s; E {{ Φ }}) ⊢ RSWP e1 at k @ s; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (Hsafe Hstep) "H". iApply rswp_lift_pure_det_head_step_fupd; eauto.
  by iApply step_fupdN_intro.
Qed.
End rwp.
