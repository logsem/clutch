(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import proofmode.
From clutch.program_logic Require Import ectx_language weakestpre lifting.
From iris.prelude Require Import options.

Local Open Scope R.

Section wp.
Context {Λ : ectxLanguage} `{!irisGS Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Local Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Local Definition reducible_not_val_inhabitant e := reducible_not_val e inhabitant.
Local Hint Resolve reducible_not_val_inhabitant : core.
Local Hint Resolve head_stuck_stuck : core.

Lemma wp_lift_head_step_fupd_couple {E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 e1' σ1',
    state_interp σ1 ∗ spec_interp (e1', σ1') ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    exec_coupl e1 σ1 e1' σ1' (λ '(e2, σ2) '(e2', σ2'),
      ▷ |={∅,E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ WP e2 @ E {{ Φ }}))
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd_couple; [done|].
  iIntros (σ1 e1' σ1') "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  done.
Qed.

Lemma wp_lift_head_step {E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ E {{ Φ }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit; [by eauto|].
  iIntros (???) "!> !>". iApply "H"; auto.
Qed.

(* Lemma wp_lift_head_stuck E Φ e : *)
(*   to_val e = None → *)
(*   sub_redexes_are_values e → *)
(*   (∀ σ ρ, state_interp σ ∗ spec_interp ρ ={E,∅}=∗ ⌜head_stuck e σ⌝) *)
(*   ⊢ WP e @ E ?{{ Φ }}. *)
(* Proof. *)
(*   iIntros (??) "H". iApply wp_lift_stuck; first done. *)
(*   iIntros (σ ρ) "Hσ". iMod ("H" with "Hσ") as "%". by auto. *)
(* Qed. *)

(* Lemma wp_lift_pure_head_stuck E Φ e : *)
(*   to_val e = None → *)
(*   sub_redexes_are_values e → *)
(*   (∀ σ, head_stuck e σ) → *)
(*   ⊢ WP e @ E ?{{ Φ }}. *)
(* Proof using Hinh. *)
(*   iIntros (?? Hstuck). iApply wp_lift_head_stuck; [done|done|]. *)
(*   iIntros (σ ρ) "_". iApply fupd_mask_intro; by auto with set_solver. *)
(* Qed. *)

Lemma wp_lift_atomic_head_step_fupd {E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={E1}[E2]▷=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by auto. iIntros (e2 σ2 Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step {E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; [by auto|]. iNext. iIntros (e2 σ2 Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_pure_det_head_step {E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2,
    head_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  (|={E}[E']▷=> WP e2 @ E {{ Φ }}) ⊢ WP e1 @ E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step e1 e2); eauto.
Qed.

Lemma wp_lift_pure_det_head_step' {E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2,
    head_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  ▷ WP e2 @ E {{ Φ }} ⊢ WP e1 @ E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(WP e1 @ _ {{ _ }})%I]wp_lift_pure_det_head_step //.
  rewrite -step_fupd_intro //.
Qed.
End wp.
