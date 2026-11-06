(* The DHKE + secure-channel composition of [advantage_comp] in factory form,
   multi-session: the same chain of hybrids, each given as a factory.  The
   perfect steps are the session-level relations of [new_composition]; the
   DDH step is a β-step ([advantage_reduction_f]). *)

From clutch.prob_eff_lang.probblaze Require Import advantage.
From clutch.prob_eff_lang.probblaze.typing Require Import types fundamental interp.
From clutch.prob_eff_lang.probblaze Require Import comp_operators sem_types sem_row sem_judgement syntax semantics metatheory proofmode valgroup adequacy mode.
From clutch.prob_eff_lang.probblaze.examples Require Import
  new_composition mask sec_channel_def new_composition_defs dhke_common advantage_comp factory_advantage.
From Stdlib Require Import Reals Psatz.

Import fingroup.
Import fingroup.fingroup.

#[local] Open Scope R_scope.

Section adv_comp_factory.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context `{Hpre :probblazeRGpreS Σ}.
  Context {msk : @Mask (@vgG vg) vgval}.
  Context {M : ∀ `{probblazeRGS Σ}, Mask_struc}.

  (* A perfect step between factories, from the two session-level relations. *)
  Local Tactic Notation "zero_step" uconstr(L) uconstr(R) :=
    apply (advantage_zero_f _ _ _ _ (λ _, τ)); [assumption| |]; intros ?; [by eapply L|by eapply R].

  Theorem adv_composition_f A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A ((𝟙 → τ) → 𝔹)%T) →
    advantage A (λ: <>, REAL_CHAN_DHKE)%V (λ: <>, SIMSIMFCHAN)%V #true <=
      advantage (λ: "d", A (λ: <>, REAL_CHAN_DH_RED "d"))%V DH_real DH_rand #true.
  Proof using All.
    intros HA.
    set (ε := advantage (λ: "d", A (λ: <>, REAL_CHAN_DH_RED "d"))%V DH_real DH_rand #true).
    assert (is_closed_expr ∅ REAL_CHAN_DH_RED) as HRc by is_closed.
    eapply (advantage_triangle _ _ (λ: <>, REAL_CHAN_DH_REAL)%V _ _ 0 ε); [| |lra].
    { zero_step F_OAUTH_DHKE_C_REAL C_REAL_DHKE_F_OAUTH. }
    eapply (advantage_triangle _ _ (λ: <>, REAL_CHAN_DH_RED_REAL)%V _ _ 0 ε); [| |lra].
    { zero_step REAL_DHKE_DH_RED_REAL REAL_DHKE_DH_RED_REAL'. }
    eapply (advantage_triangle _ _ (λ: <>, REAL_CHAN_DH_RED_RAND)%V _ _ ε 0); [| |lra].
    { apply (advantage_reduction_f A "d" (REAL_CHAN_DH_RED "d") _ _ DH_real DH_rand).
      - change (App (val_subst "d" DH_real REAL_CHAN_DH_RED) (Val DH_real) = REAL_CHAN_DH_RED_REAL).
        by rewrite (subst_is_closed ∅ _ "d" DH_real HRc (not_elem_of_empty _)).
      - change (App (val_subst "d" DH_rand REAL_CHAN_DH_RED) (Val DH_rand) = REAL_CHAN_DH_RED_RAND).
        by rewrite (subst_is_closed ∅ _ "d" DH_rand HRc (not_elem_of_empty _)). }
    eapply (advantage_triangle _ _ (λ: <>, REAL_CHAN_DH_RAND)%V _ _ 0 0); [| |lra].
    { zero_step REAL_DHKE_DH_RED_RAND' REAL_DHKE_DH_RED_RAND. }
    eapply (advantage_triangle _ _ (λ: <>, DHSIM_FKE_CHAN1)%V _ _ 0 0); [| |lra].
    { zero_step REAL_CHAN_DH_RAND_DHSIM_FKE_CHAN1 DHSIM_FKE_CHAN1_REAL_CHAN_DH_RAND. }
    eapply (advantage_triangle _ _ (λ: <>, DHSIM_FKE_CHAN2)%V _ _ 0 0); [| |lra].
    { zero_step DHSIM_FKE_CHAN1_DHSIM_FKE_CHAN2 DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN1. }
    eapply (advantage_triangle _ _ (λ: <>, DHSIM_FKE_CHAN3)%V _ _ 0 0); [| |lra].
    { zero_step DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN3 DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN2. }
    eapply (advantage_triangle _ _ (λ: <>, DHSIM_FKE_CHAN4)%V _ _ 0 0); [| |lra].
    { zero_step DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4 DHSIM_FKE_CHAN4_DHSIM_FKE_CHAN3. }
    zero_step DHSIM_FKE_CHAN4_SIMFCHAN SIMFCHAN_DHSIM_FKE_CHAN4.
  Qed.

  Lemma T_f_bool_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ (interp._ty η μ δ ((() ⇾ T) ⇾ 𝔹) ξ)%T ≤ₜ ((𝟙 → τ) → 𝔹)%T.
  Proof using All.
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply T_subtype].
  Qed.

  Lemma adv_composition_f_typed A :
    ⊢ᵥ A : ((() ⇾ T) ⇾ TBool) →
    advantage A (λ: <>, REAL_CHAN_DHKE)%V (λ: <>, SIMSIMFCHAN)%V #true <=
      advantage (λ: "d", A (λ: <>, REAL_CHAN_DH_RED "d"))%V DH_real DH_rand #true.
  Proof using All.
    intros HAtyped. apply adv_composition_f.
    intros HRGS.
    apply (@fundamental_val Σ HRGS) in HAtyped.
    iPoseProof HAtyped as "Hadv".
    unfold bin_log_val_related.
    iSpecialize ("Hadv" $! [] [] ∅ []).
    iModIntro. iApply (T_f_bool_subtype [] [] ∅ []).
    by rewrite /sem_val_typed /=.
  Qed.

End adv_comp_factory.
