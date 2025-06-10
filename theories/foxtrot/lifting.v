(** The "lifting lemmas" in this file serve to lift the rules of the operational
    semantics to the program logic. *)
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.
From clutch.prelude Require Import NNRbar.
From clutch.con_prob_lang Require Import lang erasure.
From clutch.foxtrot Require Import weakestpre.

Section lifting.
Context `{!foxtrotWpGS con_prob_lang Σ}.
Implicit Types v : val con_prob_lang.
Implicit Types e : expr con_prob_lang.
Implicit Types σ : state con_prob_lang.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val con_prob_lang → iProp Σ.

#[local] Open Scope R.

Lemma wp_lift_step_couple E Φ e1 s :
  (∀ σ1 ρ1 ε1,
      state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E, ∅}=∗
      spec_coupl σ1 ρ1 ε1 (λ σ2 ρ2 ε2,
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗ Φ v
        | None =>
            prog_coupl e1 σ2 ρ2 ε2 (λ e3 σ3 efs ρ3 ε3,
                ▷ spec_coupl σ3 ρ3 ε3 (λ σ4 ρ4 ε4,
                   |={∅, E}=> state_interp σ4 ∗ spec_interp ρ4 ∗ err_interp ε4 ∗
                             WP e3 @ s ; E {{ Φ }} ∗
                                         [∗ list] ef ∈efs, WP ef @ s ; ⊤ {{fork_post}}))
      end))%I
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. rewrite wp_unfold /wp_pre //. Qed.

Lemma wp_lift_step_spec_couple E Φ e1 s :
  (∀ σ1 ρ1 ε1,
      state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E, ∅}=∗
      spec_coupl σ1 ρ1 ε1 (λ σ2 ρ2 ε2,
        |={∅, E}=> state_interp σ2 ∗ spec_interp ρ2 ∗
                   err_interp ε2 ∗ WP e1 @ s; E {{ Φ }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iApply spec_coupl_wp.
Qed.

Lemma wp_lift_step_prog_couple E Φ e1 s :
  to_val e1 = None →
  (∀ σ1 ρ1 ε1,
      state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E, ∅}=∗
      prog_coupl e1 σ1 ρ1 ε1 (λ e2 σ2 efs ρ2 ε2,
        ▷ |={∅, E}=> state_interp σ2 ∗ spec_interp ρ2 ∗
                     err_interp ε2 ∗ WP e2 @ s; E {{ Φ }} ∗
                                         [∗ list] ef ∈efs, WP ef @ s ; ⊤ {{fork_post}}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hv) "H".
  iApply wp_lift_step_couple.
  iIntros (???) "Hs".
  iMod ("H" with "[$]") as "H".
  iApply spec_coupl_ret.
  iModIntro. rewrite Hv.
  iApply (prog_coupl_mono with "[] H").
  iIntros (?????) "H !>".
  by iApply spec_coupl_ret.
Qed.

Lemma wp_lift_step_later E Φ e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
     ⌜reducible e1 σ1⌝ ∗
     ∀ e2 σ2 efs,
      ⌜prim_step e1 σ1 (e2, σ2, efs) > 0⌝ ={∅}=∗ ▷ |={∅,E}=>
      state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗
                                   [∗ list] ef ∈efs, WP ef @ s ; ⊤ {{fork_post}})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply wp_lift_step_prog_couple; [done|].
  iIntros (σ1 ρ1 ε1) "(Hσ & Hρ & Hε)".
  iMod ("H" with "Hσ") as "[%Hs H]". iModIntro.
  iApply prog_coupl_step_l; [done|].
  iIntros (????).
  iMod ("H" with "[//]") as "H".
  iIntros "!> !>".
  iMod "H" as "($ & $)".
  by iFrame.
Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_step E Φ e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs,
     ⌜prim_step e1 σ1 (e2, σ2, efs) > 0⌝ ={∅,E}=∗
      state_interp σ2 ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈efs, WP ef @ s ; ⊤ {{fork_post}})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_later; [done|]. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]". iIntros "!>" (????) "!>" . by iApply "H".
Qed.

Lemma wp_lift_pure_step_no_fork E E' Φ e1 s :
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2 efs, prim_step e1 σ1 (e2, σ2, efs) > 0 → σ2 = σ1 /\ efs = []) →
  (|={E}[E']▷=> ∀ e2 σ efs, ⌜prim_step e1 σ (e2, σ, efs) > 0⌝ → WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant) as Hsafe'.
    rewrite /reducible in Hsafe'.
    destruct Hsafe' as [].
    by eapply val_stuck. }
  iIntros (σ1) "Hσ". iMod "H".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit; [done|].
  iNext. iIntros (e2 σ2 efs Hprim).
  destruct (Hstep _ _ _ _ Hprim).
  iMod "Hclose" as "_". iMod "H". subst.
  iDestruct ("H" with "[//]") as "H". simpl. by iFrame.
Qed.

(* Atomic steps don't need any mask-changing business here, one can *)
(* use the generic lemmas here. *)
Lemma wp_lift_atomic_step_fupd {E1 E2 Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 (e2, σ2, efs) > 0⌝ ={E1}[E2]▷=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }}
  )
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_later E1 _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (e2 σ2 efs Hs). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 with "[#]") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as "($ & HQ & $)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply wp_value; last done. by apply of_to_val.
Qed.

Lemma wp_lift_atomic_step {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 (e2, σ2, efs) > 0⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2)∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (?) "?". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!> *". iIntros (Hstep) "!> !>".
  by iApply "H".
Qed.

Lemma wp_lift_pure_det_step_no_fork {E E' Φ} e1 e2 s :
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs, prim_step e1 σ1 (e2', σ2, efs) > 0 → σ2 = σ1 ∧ e2' = e2 /\ efs = []) →
  (|={E}[E']▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step_no_fork E E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (e' σ efs (?&->&->)%Hpuredet); auto.
Qed.

Lemma wp_pure_step_fupd E E' e1 e2 φ n Φ s :
  PureExec φ n e1 e2 →
  φ →
  (|={E}[E']▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply wp_lift_pure_det_step_no_fork.
  - eauto.
  - intros σ1 e2' σ2 efs Hpstep.
    by injection (pmf_1_supp_eq _ _ _ (pure_step_det σ1) Hpstep).
  - by iApply (step_fupd_wand with "Hwp").
Qed.

Lemma wp_pure_step_later E e1 e2 φ n Φ s :
  PureExec φ n e1 e2 →
  φ →
  ▷^n WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
End lifting.
