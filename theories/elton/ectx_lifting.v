(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import proofmode.
From clutch.common Require Import con_ectx_language.
From clutch.delay_prob_lang Require Import lang.
From clutch.elton Require Import weakestpre lifting.
From iris.prelude Require Import options.

Local Open Scope R.

Section wp.
Context `{!eltonWpGS d_prob_lang Σ} {Hinh : Inhabited (state d_prob_lang)}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val d_prob_lang → iProp Σ.
Implicit Types v : val d_prob_lang.
Implicit Types e : expr d_prob_lang.
Local Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Local Hint Resolve head_stuck_stuck : core.

Lemma wp_lift_head_step_fupd {E Φ} e1 s :
  (∀ σ1 ε1,
    state_interp σ1 ∗ err_interp ε1
    ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    state_step_coupl σ1 ε1
       (λ σ2 ε2,
          match to_val e1 with
          | Some v => |={∅, E}=> state_interp σ2 ∗ err_interp ε2 ∗ Φ v
          | None => prog_coupl e1 σ2 ε2
                     (λ e3 σ3 ε3,
                        ▷ state_step_coupl σ3 ε3
                          (λ σ4 ε4, |={∅, E}=> state_interp σ4 ∗ err_interp ε4 ∗ WP e3 @ s ; E {{Φ}} 
                          )
                     )
          end
       )
  )
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros "H". iApply wp_lift_step_fupd_glm.
  iIntros (σ1 ε) "Hσε".
  iMod ("H" with "Hσε") as "[% H]"; iModIntro; auto.
Qed.

Lemma wp_lift_head_step {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={∅,E}=∗
                   state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} 
  )
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (?) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit.
  { iPureIntro. by eapply head_prim_reducible. }
  iIntros (???) "!> !>". iApply "H"; auto.
Qed.

Lemma wp_lift_atomic_head_step_fupd {E1 E2 Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={E1}[E2]▷=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2) 
  )
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit.
  { iPureIntro. by apply head_prim_reducible. }
  iIntros (e2 σ2 Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step {E Φ} e1 s :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2, ⌜head_step e1 σ1 (e2, σ2) > 0⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_val e2) 
  )
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit.
  { iPureIntro. by apply head_prim_reducible. }
  iNext. iIntros (e2 σ2 Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_pure_det_head_step {E E' Φ} e1 e2 s :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2,
    head_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  (|={E}[E']▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros. erewrite !(wp_lift_pure_det_step e1 e2); eauto.
  all: intros. all: by apply head_prim_reducible.
Qed.

Lemma wp_lift_pure_det_head_step' {E Φ} e1 e2 s :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2,
    head_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2) →
  ▷ WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(WP e1 @ _; _ {{ _ }})%I]wp_lift_pure_det_head_step //.
  rewrite -step_fupd_intro //.
Qed.

End wp.
