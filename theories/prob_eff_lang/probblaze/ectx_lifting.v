(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import proofmode.
From clutch.approxis Require Export app_weakestpre lifting.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics.
From iris.prelude Require Import options.

Local Open Scope R.

Section ectx_lifting.
Context
  {Hinh : Inhabited (syntax.state)}
 `{!spec_updateGS (lang_markov blaze_prob_lang) Σ, !approxisWpGS blaze_prob_lang Σ}.

Implicit Types P : iProp Σ.
Implicit Types Φ : syntax.val → iProp Σ.
Implicit Types v : syntax.val.
Implicit Types e : syntax.expr.
(* Local Hint Resolve head_prim_reducible head_reducible_prim_step : core.
   Local Hint Resolve head_stuck_stuck : core. *)

Lemma wp_lift_atomic_head_step {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit.
  { iPureIntro. unfold reducible. inversion H0. exists x. simpl. rewrite head_prim_step_pmf_eq. done. }
  iNext. iIntros (e2 σ2 Hstep).
  iApply "H"; eauto.
  iPureIntro. rewrite -head_prim_step_pmf_eq. done.
Qed.

Lemma wp_lift_head_step {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_later; [done|]. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit.
  { iPureIntro. unfold reducible. inversion H0. exists x. simpl. rewrite head_prim_step_pmf_eq. done. }
  iIntros (???) "!> !>". iApply "H"; auto.
  iPureIntro. rewrite -head_prim_step_pmf_eq. done.
Qed.

End ectx_lifting.
