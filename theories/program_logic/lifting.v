(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)
From Coq Require Import Reals Psatz.
From iris.proofmode Require Import tactics.
From self.prob Require Import couplings.
From self.program_logic Require Export weakestpre exec.
From iris.prelude Require Import options.

Section lifting.
Context `{!irisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

#[local] Open Scope R.

Lemma wp_lift_step_fupd_couple s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ρ, state_interp σ1 ∗ spec_interp ρ ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∃ ξ ξ' R,
      ⌜SchedulerWf ξ (e1, σ1)⌝ ∗
      ⌜Rcoupl (exec ξ (e1, σ1)) (exec ξ' ρ) R⌝ ∗
      ∀ e2 σ2 ρ',
        ⌜R (e2, σ2) ρ'⌝ ={∅}=∗ ▷ |={∅,E}=>
        state_interp σ2 ∗ spec_interp ρ' ∗ WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. by rewrite wp_unfold /wp_pre=>->. Qed.

Lemma wp_lift_step_fupd s E Φ e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2,
      ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗ ▷ |={∅,E}=>
      state_interp σ2 ∗ WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply wp_lift_step_fupd_couple; [done|].
  iIntros (σ1 ρ) "[Hσ Hρ]".
  iMod ("H" with "Hσ") as "[%Hs H]". iModIntro.
  iSplit; [done|].
  iExists (prim_step_sch (e1, σ1)), [], _.
  iSplit; [iPureIntro; by apply prim_step_sch_wf|].
  iSplit.
  { iPureIntro. eapply Rcoupl_pos_R, Rcoupl_trivial. }
  iIntros (???). rewrite exec_prim_step_sch_pmf exec_nil.
  iIntros "(_ & %Hstep & %Hρ')".
  apply dret_pos in Hρ'; subst.
  iMod ("H" with "[//]") as "H".
  iIntros "!> !>". by iFrame.
Qed.

Lemma wp_lift_stuck E Φ e :
  to_val e = None →
  (∀ σ ρ, state_interp σ ∗ spec_interp ρ ={E,∅}=∗ ⌜stuck e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->. iIntros "H" (σ1 ρ) "Hσ".
  iMod ("H" with "Hσ") as %[? Hirr]. iModIntro. iSplit; first done.
  iExists (prim_step_sch (e, σ1)), [], _.
  iSplit; [iPureIntro; by apply prim_step_sch_wf|].
  iSplit.
  { iPureIntro. eapply Rcoupl_pos_R, Rcoupl_trivial. }
  simpl.
  iIntros (e2 σ2 ρ' (_ & Hexec & ?)).
  rewrite exec_prim_step_sch_pmf in Hexec.
  destruct (Hirr (e2, σ2)); lra.
Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_step s E Φ e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2,
     ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅,E}=∗
      state_interp σ2 ∗
      WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]". iIntros "!>" (???) "!>!>" . by iApply "H".
Qed.

Lemma wp_lift_pure_step `{!Inhabited (state Λ)} s E E' Φ e1 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 e2 σ2, prim_step e1 σ1 (e2, σ2) > 0 → σ2 = σ1) →
  (|={E}[E']▷=> ∀ e2 σ, ⌜prim_step e1 σ (e2, σ) > 0⌝ → WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
  iIntros (σ1) "Hσ". iMod "H".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e2 σ2 Hprim).
  destruct (Hstep _ _ _ Hprim).
  iMod "Hclose" as "_". iMod "H".
  iDestruct ("H" with "[//]") as "H". simpl. by iFrame.
Qed.

Lemma wp_lift_pure_stuck `{!Inhabited (state Λ)} E Φ e :
  (∀ σ, stuck e σ) →
  True ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply wp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case: (Hstuck inhabitant).
  - iIntros (σ ρ) "_". iApply fupd_mask_intro; auto with set_solver.
Qed.

(* Atomic steps don't need any mask-changing business here, one can *)
(* use the generic lemmas here. *)
Lemma wp_lift_atomic_step_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E1}[E2]▷=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E1 _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (e2 σ2 Hs). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 with "[#]") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as "($ & HQ)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply wp_value; last done. by apply of_to_val.
Qed.

Lemma wp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2, ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (?) "?". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!> *". iIntros (Hstep) "!> !>".
  by iApply "H".
Qed.

Lemma wp_lift_pure_det_step `{!Inhabited (state Λ)} {s E E' Φ} e1 e2 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 e2' σ2, prim_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  (|={E}[E']▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step s E E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (e' σ (?&->)%Hpuredet); auto.
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E E' e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (|={E}[E']▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply wp_lift_pure_det_step.
  - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_val.
  - intros σ1 e2' σ2 Hpstep.
    by injection (pmf_1_supp_eq _ _ _ (pure_step_det σ1) Hpstep).
  - by iApply (step_fupd_wand with "Hwp").
Qed.

Lemma wp_pure_step_later `{!Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
End lifting.
