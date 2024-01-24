(** Total lifting lemmas for the ub logic*)
From clutch.ub_logic Require Import ub_total_weakestpre.
From iris.proofmode Require Import tactics.
From clutch.prelude Require Import NNRbar.

Section total_lifting.
  Context `{!irisGS Λ Σ}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Local Open Scope R.

  Lemma twp_lift_step_fupd_exec_ub E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ε,
    state_interp σ1 ∗ err_interp ε
    ={E,∅}=∗
    exec_ub e1 σ1 (λ ε2 '(e2, σ2),
                      |={∅,E}=> state_interp σ2 ∗ err_interp ε2 ∗ WP e2 @ E [{ Φ }]) ε)
  ⊢ WP e1 @ E [{ Φ }].
  Proof.
    by rewrite ub_twp_unfold /ub_twp_pre =>->.
  Qed.

  Lemma twp_lift_step_fupd E Φ e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1
     ={E,∅}=∗
    ⌜reducible e1 σ1⌝ ∗
     ∀ e2 σ2,
      ⌜prim_step e1 σ1 (e2, σ2) > 0 ⌝ ={∅}=∗ |={∅,E}=>
      state_interp σ2 ∗ WP e2 @ E [{ Φ }])
  ⊢ WP e1 @ E [{ Φ }].
  Proof.
    intros Hval.
    iIntros "H".
    iApply twp_lift_step_fupd_exec_ub; [done|].
    iIntros (σ1 ε) "[Hσ Hε]".
    iMod ("H" with "Hσ") as "[%Hs H]". iModIntro.
    iApply (exec_ub_prim_step e1 σ1).
    iExists _.
    iExists nnreal_zero.
    iExists ε.
    iSplit.
    { iPureIntro. simpl. done. }
    iSplit.
    { iPureIntro. simpl. lra. }
    iSplit.
    { iPureIntro.
      eapply ub_lift_pos_R, ub_lift_trivial.
      simpl; lra.
    }
    iIntros ([e2 σ2] (?&?)).
    iMod ("H" with "[//]")as "H".
    iModIntro. iMod "H". iModIntro. iFrame. done.
  Qed.

  (** Derived lifting lemmas. *)
  Lemma twp_lift_step E Φ e1 :
    to_val e1 = None →
    (∀ σ1, state_interp σ1 ={E,∅}=∗
           ⌜reducible e1 σ1⌝ ∗
           ∀ e2 σ2,
       ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅,E}=∗
       state_interp σ2 ∗
       WP e2 @ E [{ Φ }])
    ⊢ WP e1 @ E [{ Φ }].
  Proof.
    iIntros (?) "H". iApply twp_lift_step_fupd; [done|]. iIntros (?) "Hσ".
    iMod ("H" with "Hσ") as "[$ H]". iIntros "!>" (???) "!>" . iMod ("H" with "[]"); first done.
    iModIntro; done.
  Qed.

  Lemma twp_lift_pure_step `{!Inhabited (state Λ)} E Φ e1 :
    (∀ σ1, reducible e1 σ1) →
    (∀ σ1 e2 σ2, prim_step e1 σ1 (e2, σ2) > 0 → σ2 = σ1) →
    (|={E}=> ∀ e2 σ, ⌜prim_step e1 σ (e2, σ) > 0⌝ → WP e2 @ E [{ Φ }])
    ⊢ WP e1 @ E [{ Φ }].
  Proof.
    iIntros (Hsafe Hstep) "H". iApply twp_lift_step.
    { specialize (Hsafe inhabitant). eauto using reducible_not_val. }
    iIntros (σ1) "Hσ". iMod "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; [done|].
    iIntros (e2 σ2 Hprim).
    destruct (Hstep _ _ _ Hprim).
    iMod "Hclose" as "_". iModIntro.
    iDestruct ("H" with "[//]") as "H". simpl. by iFrame.
  Qed.

  Lemma twp_lift_atomic_step_fupd {E1 Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜reducible e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E1}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ E1 [{ Φ }].
  Proof.
    iIntros (?) "H".
    iApply (twp_lift_step_fupd E1 _ e1)=>//; iIntros (σ1) "Hσ1".
    iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose" (e2 σ2 Hs). iMod "Hclose" as "_".
    iMod ("H" $! e2 σ2 with "[#]") as "[Hs ?]"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iMod "Hclose" as "_". iModIntro. 
    destruct (to_val e2) eqn:?; last (simpl; by iExFalso).
    iFrame.
    iApply ub_twp_value; last done. by apply of_to_val.
  Qed.

  Lemma twp_lift_atomic_step {E Φ} e1 :
    to_val e1 = None →
    (∀ σ1, state_interp σ1 ={E}=∗
           ⌜reducible e1 σ1⌝ ∗
          ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
                    state_interp σ2 ∗
                    from_option Φ False (to_val e2))
  ⊢ WP e1 @ E [{ Φ }].
  Proof.
    iIntros (?) "H". iApply twp_lift_atomic_step_fupd; [done|].
    iIntros (?) "?". iMod ("H" with "[$]") as "[$ H]".
    iIntros "!> *". iIntros (Hstep).
    by iApply "H".
  Qed.

  Lemma twp_lift_pure_det_step `{!Inhabited (state Λ)} {E Φ} e1 e2 :
    (∀ σ1, reducible e1 σ1) →
    (∀ σ1 e2' σ2, prim_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
    (|={E}=> WP e2 @ E [{ Φ }]) ⊢ WP e1 @ E [{ Φ }].
  Proof.
    iIntros (? Hpuredet) "H". iApply (twp_lift_pure_step E); try done.
    { naive_solver. }
    iMod "H". iModIntro.
    iIntros (e' σ (?&->)%Hpuredet); auto.
  Qed.

  Lemma twp_pure_step_fupd `{!Inhabited (state Λ)} E e1 e2 φ n Φ :
    PureExec φ n e1 e2 →
    φ →
    WP e2 @ E [{ Φ }] ⊢ WP e1 @ E [{ Φ }].
  Proof.
    iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
    iApply twp_lift_pure_det_step.
    - intros σ1 e2' σ2 Hpstep.
      by injection (pmf_1_supp_eq _ _ _ (pure_step_det σ1) Hpstep).
    - iModIntro. iApply "IH". iApply "Hwp". 
  Qed.
  
End total_lifting.
