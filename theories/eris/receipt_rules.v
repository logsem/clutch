From stdpp Require Import namespaces finite.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext.
From clutch.prob_lang Require Import notation tactics metatheory.
From clutch.prob_lang Require Export lang.
From clutch.eris Require Export lifting proofmode ectx_lifting primitive_laws seq_amplification.

Section receipt_rules.
Context `{!erisGS Σ}.

Definition steps_left k : iProp Σ :=
  ∃ n, @mono_nat_lb_own _ erisGS_steps erisGS_steps_name n ∗ ⌜ (erisGS_max_step <= n + k)%nat ⌝.

Lemma steps_left_0 s E e Φ :
  to_val e = None →
  steps_left 0 ⊢ WP e @ s ; E {{ Φ }}.
Proof.
  iIntros (?) "Hstep0". rewrite -wp_lift_step_fupd_glm_max_step //.
  iIntros (n σ ?) "([Hh [Ht Hs]]&?)".
  rewrite /steps_auth.
  iDestruct "Hstep0" as (n') "(Hlb&%Hle)".
  iDestruct (mono_nat_lb_own_valid with "[$] [$]")as "(?&%Hle')".
  iApply fupd_mask_intro; [set_solver|]. iIntros "_".
  iLeft. iPureIntro.
  rewrite /max_step//=.
  lia.
Qed.

Lemma steps_left_intro s E e Φ :
  to_val e = None →
  (∀ k, steps_left k -∗ WP e @ s ; E {{ Φ }}) ⊢ WP e @ s ; E {{ Φ }}.
Proof.
  iIntros (Hnval) "Hk".
  iEval (rewrite !pgl_wp_unfold /pgl_wp_pre /=).
  rewrite Hnval.
  iIntros (n σ ?) "([Hh [Ht Hs]]&?)".
  iDestruct (mono_nat_lb_own_get with "Hs") as "#Hlb".
  iSpecialize ("Hk" $! (@erisGS_max_step _ erisGS0 - n) with "[]").
  { iExists n. iFrame "#". iPureIntro. lia. }
  rewrite !pgl_wp_unfold /pgl_wp_pre /= Hnval.
  iApply "Hk".
  iFrame.
Qed.

Lemma steps_left_decr s E e (Φ : val → iProp Σ) k :
  to_val e = None →
  steps_left (S k) -∗ WP e @ s ; E {{ v, steps_left k -∗ Φ v}} -∗ WP e @ s ; E {{ v , Φ v }}.
Proof.
  iIntros (Hnval).
  rewrite !pgl_wp_unfold /pgl_wp_pre /= Hnval.
  iIntros "Hsteps Hwp".
  iIntros (n σ1 ?) "([Hh [Ht Hs]]&?)".
  iDestruct "Hsteps" as (n') "(Hlb&%Hpure)".
  iDestruct (mono_nat_lb_own_valid with "[$] [$]")as "#(_&%Hle')".
  iMod ("Hwp" with "[$]") as "[Hl|Hwp]".
  { iModIntro; iLeft. auto. }
  iModIntro. iRight.
  iApply (glm_mono_pred with "[Hlb] Hwp").
  iIntros ([e2 σ2] ?) "H".
  iNext.
  iMod "H" as "(Hσ & Hρ & H)".
  iDestruct "Hσ" as "[Hh [Ht Hs]]".
  iDestruct (mono_nat_lb_own_get with "Hs") as "#Hlb'".
  iFrame. iModIntro.
  iApply (pgl_wp_wand with "H").
  iIntros (?) "H". iApply "H".
  iExists _. iFrame "Hlb'".
  iPureIntro. lia.
Qed.

End receipt_rules.
