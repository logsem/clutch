(** The "lifting lemmas" in this file serve to lift the rules of the operational
    semantics to the program logic. *)
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.
From clutch.prelude Require Import NNRbar.
From mathcomp.analysis Require Import measure.
From clutch.bi Require Import weakestpre.
From clutch.micrometer Require Import app_weakestpre.

Section lifting.
Context `{!meas_spec_updateGS (meas_lang_markov Λ) Σ, !micrometerWpGS Λ Σ}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

#[local] Open Scope R.

Lemma wp_lift_step_couple E Φ e1 (s : ()) :
  (∀ σ1 e1' σ1' ε1 ,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ={E, ∅}=∗
      meas_spec_coupl ∅ σ1 e1' σ1' ε1 (λ σ2 e2' σ2' ε2 ,
        match to_val e1 with
        | Some v => |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗
                               err_interp ε2 ∗ Φ v
        | None =>
            meas_prog_coupl e1 σ2 e2' σ2' ε2 (λ e3 σ3 e3' σ3' ε3,
                ▷ meas_spec_coupl ∅ σ3 e3' σ3' ε3 (λ σ4 e4' σ4' ε4,
                    |={∅, E}=> state_interp σ4 ∗ spec_interp (e4', σ4') ∗
                               err_interp ε4 ∗ WP e3 @ s; E {{ Φ }}))
        end))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. rewrite wp_unfold /wp_pre //. Qed.

Lemma wp_lift_step_spec_couple E Φ e1 s :
  (∀ σ1 e1' σ1' ε1,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ={E, ∅}=∗
      meas_spec_coupl ∅ σ1 e1' σ1' ε1 (λ σ2 e2' σ2' ε2,
        |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗
                   err_interp ε2 ∗ WP e1 @ s; E {{ Φ }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros "H".
  iApply wp_lift_step_couple.
  iIntros (????) "Hs".
  iMod ("H" with "[$]") as "H".
  iModIntro.
  iApply (meas_spec_coupl_bind with "[] H"); [done|].
  iIntros (????) "H".
  iApply fupd_meas_spec_coupl.
  iMod "H" as "(?&?&?&H)".
  rewrite wp_unfold /wp_pre.
  iApply ("H" with "[$]").
Qed.

Lemma wp_lift_step_meas_prog_couple E Φ e1 s :
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε1,
      state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ={E, ∅}=∗
      meas_prog_coupl e1 σ1 e1' σ1' ε1 (λ e2 σ2 e2' σ2' ε2,
        ▷ |={∅, E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗
                     err_interp ε2 ∗ WP e2 @ s; E {{ Φ }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hv) "H".
  iApply wp_lift_step_couple.
  iIntros (????) "Hs".
  iMod ("H" with "[$]") as "H".
  iApply meas_spec_coupl_ret.
  iModIntro. rewrite Hv.
  iApply (meas_prog_coupl_mono with "[] H").
  iIntros (?????) "H !>".
  by iApply meas_spec_coupl_ret.
Qed.

Lemma wp_lift_step_later E Φ e1 s :
  to_val e1 = None ->
  (∀ σ1, state_interp σ1 ={E,∅}=∗
      ⌜reducible (e1, σ1) ⌝ ∗
      EXSM
        (fun ρ => True ={∅}=∗ ▷ |={∅,E}=> state_interp ρ.2 ∗ WP ρ.1  @ s; E {{ Φ }})
        (prim_step (e1, σ1)))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply wp_lift_step_meas_prog_couple; [done|].
  iIntros (σ1 e1' σ1' ε1) "(Hσ & Hρ & Hε)".
  iMod ("H" with "Hσ") as "[%Hs [%S [%HS1 [%HS2 H3]]]]". iModIntro.
  iApply meas_prog_coupl_step_l; [done|].
  iExists S.
  do 2 (iSplitR; [done|]).
  iIntros (ρ Hρ).
  iMod ("H3" $! ρ Hρ with "[//]") as "H".
  iIntros "!> !>".
  iMod "H" as "($ & $)".
  by iFrame.
Qed.


(** Derived lifting lemmas. *)
Lemma wp_lift_step E Φ e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    EXSM (λ ρ, ▷ |={∅,E}=> state_interp ρ.2 ∗ WP ρ.1 @ s; E {{ Φ }}) (prim_step (e1, σ1)))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_later; [done|]. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "[$ [%S [% [% H]]]]".
  iIntros "!>".
  iExists S. do 2 (iSplitR; [done|]).
  iIntros (???) "!>" .
  by iApply "H".
Qed.

Lemma wp_lift_pure_step `{!Inhabited (state Λ)} E E' Φ e1 s :
  (∀ σ1, reducible (e1, σ1)) →
  (∀ σ1 e2 σ2, is_det σ1 (gMap' snd (prim_step (e1, σ1)))) ->
  (|={E}[E']▷=> ∀ σ, EXSM (fun e => WP e @ s; E {{ Φ }}) (gMap' fst (prim_step (e1, σ))))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant). by eapply (to_final_None_1 (e1, _)), reducible_not_final. }
  iIntros (σ1) "Hσ". iMod "H".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iSplit; [done|].

Admitted. (*  Not sure. Can I commute a later out of an EXSM?
  iNext. iIntros (e2 σ2 Hprim).
  destruct (Hstep _ _ _ Hprim).
  iMod "Hclose" as "_". iMod "H".
  iDestruct ("H" with "[//]") as "H". simpl. by iFrame.
Qed. *)

(* Atomic steps don't need any mask-changing business here, one can *)
(* use the generic lemmas here. *)
Lemma wp_lift_atomic_step_fupd {E1 E2 Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    EXSM
      (fun ρ => True ={E1}[E2]▷=∗  state_interp ρ.2 ∗ from_option Φ False (to_val ρ.1))
      (prim_step (e1, σ1)))
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_later E1 _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ [%S [%[% H]]]]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iExists S.
  do 2 (iSplitR; [done|]).
  iIntros (ρ HS).
  destruct ρ as [e2 σ2].
  iMod "Hclose" as "_".
  iMod ("H" $! (e2, σ2) HS with "[]") as "H"; [done|].
  iIntros (_).
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as "($ & HQ)".
  destruct (to_val e2) eqn:?; last by rewrite Heqo //=.
  rewrite //= Heqo //=.
  iApply wp_value; last done.
  by apply of_to_val.
Qed.

Lemma wp_lift_atomic_step {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜reducible (e1, σ1)⌝ ∗
    EXSM (fun ρ => ▷ True ={E}=∗ state_interp ρ.2 ∗ from_option Φ False (to_val ρ.1)) (prim_step (e1, σ1)))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (?) "?". iMod ("H" with "[$]") as "[$ [%S [%[% H]]]]".
  iIntros "!> *".
  iExists S.
  do 2 (iSplitR; [done|]).
  iIntros (ρ Hρ).
  iSpecialize ("H" $! ρ Hρ).
  iIntros (_) "!> !>".
  by iApply "H".
Qed.

(** UNSURE (figure out wp_lift_pure_step first to get statement right *)
(*
Lemma wp_lift_pure_det_step `{!Inhabited (state Λ)} {E E' Φ} e1 e2 s :
  (∀ σ1, reducible (e1, σ1)) →
  (∀ σ1 e2' σ2, prim_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  (|={E}[E']▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step E E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (e' σ (?&->)%Hpuredet); auto.
Qed.

*)

(** Statement shouldn't change as even if lemma statements do *)
Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} E E' e1 e2 φ n Φ s :
  PureExec φ n e1 e2 →
  φ →
  (|={E}[E']▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof. Admitted.
(*

  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
Admitted.
(*
  iApply wp_lift_pure_det_step.
  - eauto.
  - intros σ1 e2' σ2 Hpstep.
    by injection (pmf_1_supp_eq _ _ _ (pure_step_det σ1) Hpstep).
  - by iApply (step_fupd_wand with "Hwp").
Qed. *) *)

(** Statement shouldn't change as even if lemma statements do *)
Lemma wp_pure_step_later `{!Inhabited (state Λ)} E e1 e2 φ n Φ s :
  PureExec φ n e1 e2 →
  φ →
  ▷^n WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof. Admitted.
(*
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed. *)

End lifting.
