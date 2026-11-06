(* The group-mask secure channel in factory form, multi-session: the
   environment gets [λ<>, R_CHAN] and may start any number of sessions.  The
   security is perfect, so this follows from the session-level relations of
   [sec_channel_prf]. *)

From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup adequacy mode.
From clutch.prob_eff_lang.probblaze.typing Require Import types interp fundamental.
From clutch.prob_eff_lang.probblaze Require Import sec_channel_def sec_channel_prf mask advantage_schan factory_advantage.

Import fingroup.
Import fingroup.fingroup.

Section adv_schan_factory.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {msk : Mask vgG vgval}.
  Context {M : ∀ `{probblazeRGS Σ}, Mask_struc}.

  Import valgroup_notation.

  Lemma adv_SCHAN_f A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A ((𝟙 → τ_CHAN) → 𝔹)%T) →
    (advantage A (λ: <>, R_CHAN)%V (λ: <>, CHAN_SIM_lazy ∘f F_CHAN)%V #true <= 0)%R.
  Proof using All.
    intros HA. apply (advantage_zero_f _ _ _ _ (λ _, τ_CHAN)); [exact HA| |]; intros Hrgs.
    - by unshelve eapply R_I_SCHAN.
    - by unshelve eapply I_R_SCHAN.
  Qed.

  Lemma T_CHAN_f_bool_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ (interp._ty η μ δ ((() ⇾ T_CHAN) ⇾ 𝔹) ξ)%T ≤ₜ ((𝟙 → τ_CHAN) → 𝔹)%T.
  Proof using All.
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply T_CHAN_subtype].
  Qed.

  Lemma adv_SCHAN_f_typed A :
    ⊢ᵥ A : ((() ⇾ T_CHAN) ⇾ TBool) →
    (advantage A (λ: <>, R_CHAN)%V (λ: <>, CHAN_SIM_lazy ∘f F_CHAN)%V #true <= 0)%R.
  Proof using All.
    intros HAtyped. apply adv_SCHAN_f.
    intros HRGS.
    apply (@fundamental_val Σ HRGS) in HAtyped.
    iPoseProof HAtyped as "Hadv".
    unfold bin_log_val_related.
    iSpecialize ("Hadv" $! [] [] ∅ []).
    iModIntro. iApply (T_CHAN_f_bool_subtype [] [] ∅ []).
    by rewrite /sem_val_typed /=.
  Qed.

End adv_schan_factory.
