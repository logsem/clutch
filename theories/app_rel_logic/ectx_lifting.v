(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import proofmode.
From clutch.common Require Import ectx_language.
From clutch.app_rel_logic Require Export app_weakestpre lifting.
From iris.prelude Require Import options.

Local Open Scope R.

Section wp.
Context {Λ : ectxLanguage} `{!irisGS Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Local Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Local Hint Resolve head_stuck_stuck : core.

Lemma wp_lift_head_step_fupd_couple {E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε,
    state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    (exec_coupl e1 σ1 e1' σ1' (λ '(e2, σ2) '(e2', σ2') ε2,
      ▷ |={∅,E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 ∗ WP e2 @ E {{ Φ }}) ε ))
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd_couple; [done |].
  iIntros (σ1 e1' σ1' ε) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit; [|done].
  iPureIntro. by apply head_prim_reducible.
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
  iSplit.
  { iPureIntro. by apply head_prim_reducible. }
  iIntros (???) "!> !>". iApply "H"; auto.
Qed.

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
  iSplit.
  { iPureIntro. by apply head_prim_reducible. }
  iIntros (e2 σ2 Hstep).
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
  iSplit.
  { iPureIntro. by apply head_prim_reducible. }
  iNext. iIntros (e2 σ2 Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_pure_det_head_step {E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2,
    head_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  (|={E}[E']▷=> WP e2 @ E {{ Φ }}) ⊢ WP e1 @ E {{ Φ }}.
Proof using Hinh.
  intros. erewrite !(wp_lift_pure_det_step e1 e2); eauto.
  intros. by apply head_prim_reducible.
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
