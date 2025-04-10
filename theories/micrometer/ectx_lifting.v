(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import proofmode.
From clutch.meas_lang Require Import ectx_language.
From clutch.micrometer Require Export app_weakestpre lifting.
From iris.prelude Require Import options.
From mathcomp.analysis Require Import measure.

Local Open Scope R.

(*
Section ectx_lifting.
Context
  {Λ : meas_ectxLanguage} {Hinh : Inhabited (state Λ)}
 `{!meas_spec_updateGS (meas_lang_markov Λ) Σ, !micrometerWpGS Λ Σ}.

Implicit Types P : iProp Σ.
Implicit Types Φ : Measurable.sort (val Λ) → iProp Σ.
Implicit Types v : Measurable.sort (val Λ).
Implicit Types e : Measurable.sort (expr Λ).
(*
Local Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Local Hint Resolve head_stuck_stuck : core.
*)

Lemma wp_lift_head_step_meas_prog_couple {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1 e1' σ1' ε1,
    state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    meas_prog_coupl e1 σ1 e1' σ1' ε1 (λ e2 σ2 e2' σ2' ε2,
      ▷ |={∅,E}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗
                  err_interp ε2 ∗ WP e2 @ s; E {{ Φ }}))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_meas_prog_couple; [done|].
  iIntros (σ1 e1' σ1' ε1) "Hσ".
  by iMod ("H" with "Hσ") as "[% H]".
Qed.

Lemma wp_lift_head_step {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    EXSM (fun ρ => ▷ (True ={∅,E}=∗ state_interp ρ.2 ∗ WP ρ.1 @ s; E {{ Φ }})) (head_step (e1, σ1)))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_later; [done|]. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "[% [%S [%[% H]]]]"; iModIntro.
  iSplit.
  { iPureIntro. admit. (* by apply head_prim_reducible. *) }
  iExists S.
  iSplitR; [done|].
  iSplitR.
  { (* head step and prim step *) admit. }
  iIntros (ρ Hρ _).
  iSpecialize ("H" $! ρ Hρ).
  iIntros "!>".
  iNext.
  by iApply "H".
Admitted.

Lemma wp_lift_atomic_head_step_fupd {E1 E2 Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    EXSM (fun ρ => True ={E1}[E2]▷=∗ state_interp ρ.2 ∗ from_option Φ False (to_val ρ.1)) (head_step (e1, σ1)))
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% [%S[%[% H]]]]"; iModIntro.
  iSplit.
  { iPureIntro. (* by apply head_prim_reducible. *) admit. }
  iExists S.
  iSplitR; [done|].
  iSplitR. { (* head step and prim ste *) admit. }
  iIntros (e2 σ2 Hstep).
  iApply "H"; eauto.
Admitted.

Lemma wp_lift_atomic_head_step {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    EXSM (fun ρ => ▷ (True  ={E}=∗ state_interp ρ.2 ∗ from_option Φ False (to_val ρ.1)))
            (head_step (e1, σ1)))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplitR.
  { iPureIntro. (* Head reducible reducible *) admit. }
  iDestruct "H" as "[%S [%H1 [%H2 H4]]]".
  iExists S.
  iSplitR; [done|].
  iSplitR.
  { (* head step prim step *) admit. }
  done.
Admitted.

Lemma wp_lift_pure_det_head_step {E E' Φ} e1 e2 s :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ : state Λ, is_det (e2, σ) (head_step (e1, σ))) ->
  (|={E}[E']▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros. erewrite !(wp_lift_pure_det_step e1 e2); first done.
  { (* head reducuble reducible *) admit. }
  { (* prim step head step *) admit. }
Admitted.

Lemma wp_lift_pure_det_head_step' {E Φ} e1 e2 s :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ : state Λ, is_det (e2, σ) (head_step (e1, σ))) ->
  ▷ WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(WP e1 @ _ ; _ {{ _ }})%I]wp_lift_pure_det_head_step //.
  rewrite -step_fupd_intro //.
Qed.

End ectx_lifting.
*)
