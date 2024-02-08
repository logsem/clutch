From iris.proofmode Require Import tactics.

From clutch.prelude Require Import iris_ext.
From clutch.tpref_logic Require Export weakestpre.
Set Default Proof Using "Type".

Section lifting.
Context `{spec δ Σ} `{!tprwpG Λ Σ}.

(** * RWP *)
Lemma rwp_lift_step_fupd_coupl E Φ e1 a :
  to_val e1 = None →
  (∀ σ1 a1,
      state_interp σ1 ∗ spec_interp a1 ={E,∅}=∗
      rwp_coupl e1 σ1 a1 (λ '(e2, σ2) a2,
        |={∅,E}=> state_interp σ2 ∗ spec_interp a2 ∗ WP e2 @ a; E {{ Φ }}))
  ⊢ WP e1 @ a; E {{ Φ }}.
Proof. by rewrite rwp_unfold /rwp_pre=>->. Qed.

Lemma rwp_lift_step_fupd E Φ e1 a :
  to_val e1 = None →
  (∀ σ1 a1,
      state_interp σ1 ∗ spec_interp a1 ={E,∅}=∗
      ⌜reducible (e1, σ1)⌝ ∗
      ∀ e2 σ2,
        ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗ |={∅,E}=>
        state_interp σ2 ∗ spec_interp a1 ∗ WP e2 @ a; E {{ Φ }})
  ⊢ WP e1 @ a; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply rwp_lift_step_fupd_coupl; [done|].
  iIntros (σ1 a1) "[Hσ1 Ha1]".
  iMod ("H" with "[$]") as "[%Hred H]".
  iModIntro.
  iApply rwp_coupl_prim_step_l; [done| |].
  { eapply refRcoupl_pos_R, refRcoupl_trivial. rewrite prim_step_mass //. }
  iIntros ([e2 σ2] (_ & _ & Hstep)).
  iMod ("H" with "[//]") as "H".
  by iIntros "!>".
Qed.

Lemma rwp_lift_pure_step `{!Inhabited (state Λ)} E Φ e1 a :
  (∀ σ1, reducible (e1, σ1)) →
  (∀ σ1 e2 σ2, prim_step e1 σ1 (e2, σ2) > 0 → σ2 = σ1) →
  (∀ e2 σ, ⌜prim_step e1 σ (e2, σ) > 0⌝ → WP e2 @ a; E {{ Φ }})
  ⊢ WP e1 @ a; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply rwp_lift_step_fupd.
  { specialize (Hsafe inhabitant).
    by eapply (to_final_None_1 (_, _)), reducible_not_final. }
  iIntros (σ1 a1) "Hσ".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit; [done|].
  iIntros (e2 σ2 Hprim).
  destruct (Hstep _ _ _ Hprim).
  iModIntro.
  iMod "Hclose" as "_".
  iModIntro.
  iDestruct ("H" with "[//]") as "H".
  iFrame.
Qed.

Lemma rwp_lift_atomic_step_fupd {E Φ} e1 a :
  to_val e1 = None →
  (∀ σ1 a1, state_interp σ1 ∗ spec_interp a1 ={E}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
      state_interp σ2 ∗ spec_interp a1 ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ a; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (rwp_lift_step_fupd E _ e1)=>//; iIntros (σ1 a1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (e2 σ2 Hs). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 with "[#]") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iMod "Hclose" as "_". iDestruct "H" as "($ & $ & HQ)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply rwp_value; [|done]. by apply of_to_val.
Qed.

Lemma rwp_lift_pure_det_step `{!Inhabited (state Λ)} {E Φ} e1 e2 a :
  (∀ σ1, reducible (e1, σ1)) →
  (∀ σ1 e2' σ2, prim_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  WP e2 @ a; E {{ Φ }} ⊢ WP e1 @ a; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (rwp_lift_pure_step E); try done.
  { naive_solver. }
  by iIntros (?? (?&->)%Hpuredet).
Qed.

Lemma rwp_pure_step `{!Inhabited (state Λ)} E e1 e2 φ n Φ a :
  PureExec φ n e1 e2 →
  φ →
  WP e2 @ a; E {{ Φ }} ⊢ WP e1 @ a; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply rwp_lift_pure_det_step; [done| |].
  - intros σ1 e2' σ2 Hpstep.
    by injection (pmf_1_supp_eq _ _ _ (pure_step_det σ1) Hpstep).
  - by iApply "IH".
Qed.

(** * RSWP  *)
Lemma rswp_lift_step_fupd k E Φ e1 a :
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    |={∅}▷=>^k ⌜reducible (e1, σ1)⌝ ∗
     ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0%R⌝ ={∅,E}=∗
      state_interp σ2  ∗
      WP e2 @ a; E {{ Φ }})
  ⊢ RSWP e1 at k @ a; E ⟨⟨ Φ ⟩⟩.
Proof.
  rewrite rswp_unfold /rswp_step.
  iIntros "H" (σ1 ?) "(Hσ & Ha)".
  iMod ("H" with "Hσ") as "H". iModIntro.
  iApply (step_fupdN_wand with "H").
  iIntros "(% & H)".
  iSplit; [done|].
  iExists _.
  iSplit.
  { iPureIntro.
    eapply refRcoupl_pos_R, refRcoupl_trivial.
    rewrite prim_step_mass //. }
  iIntros (?? (?&?&?)).
  iMod ("H" with "[//]") as "[$ H]".
  by iFrame.
Qed.

Lemma rswp_lift_step k E Φ e1 a :
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ▷^k (⌜reducible (e1, σ1)⌝ ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0%R⌝ ={∅,E}=∗
      state_interp σ2  ∗
      WP e2 @ a; E {{ Φ }}))
  ⊢ RSWP e1 at k @ a; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply rswp_lift_step_fupd. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "H". iIntros "!>". by iApply step_fupdN_intro.
Qed.

Lemma rswp_lift_pure_step k E E' Φ e1 a :
  (∀ σ1, reducible (e1, σ1)) →
  (∀ σ1 e2 σ2, prim_step e1 σ1 (e2, σ2) > 0 → σ2 = σ1) →
  (|={E}=> |={E}[E']▷=>^k ∀ e2 σ, ⌜prim_step e1 σ (e2, σ) > 0%R⌝ → WP e2 @ a; E {{ Φ }})
  ⊢ RSWP e1 at k @ a; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (Hsafe Hstep) "H". iApply rswp_lift_step_fupd.
  iIntros (σ1) "Hσ". iMod "H".
  iApply fupd_mask_intro; [by set_solver|].
  iIntros "Hclose".
  iApply (step_fupdN_wand with "[Hclose H]").
  { iApply (step_fupdN_mask_comm _ _ E E'); [set_solver|set_solver|].
    iMod "Hclose". by iModIntro. }
  iIntros "H". iSplit; [done|].
  iIntros (e2 σ2 Hstep'). iMod "H"; iModIntro.
  pose proof (Hstep σ1 e2 σ2 Hstep'); subst.
  iFrame. by iApply "H".
Qed.

Lemma rswp_lift_atomic_step_fupd e1 k E1 Φ a :
  (∀ σ1, state_interp σ1 ={E1}=∗
  |={E1}[E1]▷=>^k ⌜reducible (e1, σ1)⌝ ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0%R⌝ ={E1}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ RSWP e1 at k @ a; E1 ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H".
  iApply (rswp_lift_step_fupd k E1 _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "H".
  iApply step_fupdN_mask_comm'; [set_solver|].
  iApply (step_fupdN_wand with "H"); iIntros "[% H]".
  iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|].
  iModIntro; iSplit; auto.
  iIntros (e2 σ2 Hstep). iMod "Hclose".
  iMod ("H" with "[//]") as "($ & H)".
  destruct (to_val e2) eqn:?; [|by iExFalso].
  iApply rwp_value; [|done]. by apply of_to_val.
Qed.

Lemma rswp_lift_atomic_step e1 k E Φ a :
  (∀ σ1, state_interp σ1 ={E}=∗
    ▷^k (⌜reducible (e1, σ1)⌝ ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0%R⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2)))
  ⊢ RSWP e1 at k @ a; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros "H". iApply rswp_lift_atomic_step_fupd.
  iIntros (?) "?". iMod ("H" with "[$]") as "H".
  iIntros "!>". by iApply step_fupdN_intro.
Qed.

Lemma rswp_lift_pure_det_step e1 e2 k E E' Φ a :
  (∀ σ1, reducible (e1, σ1)) →
  (∀ σ1 e2' σ2 , prim_step e1 σ1 (e2', σ2) > 0%R → σ2 = σ1 ∧ e2' = e2) →
  (|={E}[E']▷=>^k WP e2 @ a; E {{ Φ }}) ⊢ RSWP e1 at k @ a; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (? Hpuredet) "H". iApply (rswp_lift_pure_step k E).
  { done. }
  { naive_solver. }
  iModIntro. iApply (step_fupdN_wand with "H"); iIntros "H".
  by iIntros (e' σ [_ ->]%Hpuredet).
Qed.

Lemma rswp_pure_step_fupd k E E' e1 e2 φ Φ `{!Inhabited (state Λ)} a :
  PureExec φ 1 e1 e2 →
  φ →
  (|={E}[E']▷=>^k WP e2 @ a; E {{ Φ }}) ⊢ RSWP e1 at k @ a; E ⟨⟨ Φ ⟩⟩.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  inversion Hexec as [|n' ? e1' ? Hstep Hrest]; subst.
  iApply rswp_lift_pure_det_step.
  - intros σ. by eapply pure_step_safe.
  - intros σ1 e2' σ2 Hpstep.
    destruct Hstep.
    by injection (pmf_1_supp_eq _ _ _ (pure_step_det σ1) Hpstep).
  - inversion Hrest; subst; eauto.
Qed.

Lemma rswp_pure_step_later `{!Inhabited (state Λ)} k E e1 e2 φ Φ a :
  PureExec φ 1 e1 e2 →
  φ →
  ▷^k WP e2 @ a; E {{ Φ }} ⊢ RSWP e1 at k @ a; E ⟨⟨ Φ ⟩⟩.
Proof.
  intros Hexec ?. rewrite -rswp_pure_step_fupd //.
  iIntros "H".
  by iApply step_fupdN_intro.
Qed.

End lifting.
