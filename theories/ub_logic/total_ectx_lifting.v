From iris.proofmode Require Import proofmode.
From clutch.common Require Import ectx_language.
From clutch.ub_logic Require Import ub_total_weakestpre total_lifting.

Local Open Scope R.

Section twp.
Context {Λ : ectxLanguage} `{!irisGS Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Local Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Local Hint Resolve head_stuck_stuck : core.

Lemma twp_lift_head_step_exec_ub {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1 ε1,
    state_interp σ1 ∗ err_interp ε1
    ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    exec_ub e1 σ1 ε1 (λ ε2 '(e2, σ2),
      |={∅,E}=> state_interp σ2 ∗ err_interp ε2 ∗ WP e2 @ s; E [{ Φ }]))
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (?) "H". iApply twp_lift_step_fupd_exec_ub; [done|].
  iIntros (σ1 ε1) "Hσε".
  iMod ("H" with "Hσε") as "[% H]"; iModIntro; auto.
Qed.

Lemma twp_lift_head_step {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
     ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ s; E [{ Φ }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (?) "H". iApply twp_lift_step_fupd; [done|]. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit.
  { iPureIntro. by apply head_prim_reducible. }
  iIntros (???) "!>". iApply "H"; auto.
Qed.

Lemma twp_lift_atomic_head_step_fupd {E1 Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={E1}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E1 [{ Φ }].
Proof.
  iIntros (?) "H". iApply twp_lift_atomic_step_fupd; [done|].
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit.
  { iPureIntro. by apply head_prim_reducible. }
  iIntros (e2 σ2 Hstep).
  iApply "H"; eauto.
Qed.

Lemma twp_lift_atomic_head_step {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
     ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (?) "H". iApply twp_lift_atomic_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit.
  { iPureIntro. by apply head_prim_reducible. }
  iIntros (e2 σ2 Hstep).
  iApply "H"; eauto.
Qed.

Lemma twp_lift_pure_det_head_step {E Φ} e1 e2 s :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2,
    head_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  (|={E}=> WP e2 @ s; E [{ Φ }]) ⊢ WP e1 @ s; E [{ Φ }].
Proof using Hinh.
  intros. erewrite !(twp_lift_pure_det_step e1 e2); eauto.
  all: intros. all: by apply head_prim_reducible.
Qed.

Lemma twp_lift_pure_det_head_step' {E Φ} e1 e2 s :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2,
    head_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
   WP e2 @ s; E [{ Φ }] ⊢ WP e1 @ s; E [{ Φ }].
Proof using Hinh.
  intros. rewrite -[(WP e1 @ _; _ [{ _ }])%I] twp_lift_pure_det_head_step //.
  iIntros. by iModIntro.
Qed.


End twp.
