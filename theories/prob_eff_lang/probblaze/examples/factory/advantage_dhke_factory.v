(* DHKE in factory form: the environment gets [λ<>, F_AUTH ∘f DH_KE] and may
   start any number of sessions.  The DDH reduction is the factory
   [λ<>, F_AUTH ∘f C_lazy d] around the DDH oracle [d]; it calls [d] once per
   session. *)

From clutch.prob_eff_lang.probblaze.typing Require Import types interp fundamental.
From clutch.prob_eff_lang.probblaze Require Import advantage.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_judgement sem_row syntax semantics metatheory proofmode mode.
From clutch.prob_eff_lang.probblaze Require Import
  dhke_channel_lazy_results dhke_common dhke_closed adequacy comp_operators
  advantage_dhke_lazy factory_advantage.
From Stdlib Require Import Reals Psatz.

#[local] Open Scope R_scope.

Section adv_dhke_factory.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.

  Import valgroup_notation.

  Definition DHKE_f : val := λ: <>, F_AUTH ∘f DH_KE.
  Definition DHKE_SIM_f : val := λ: <>, F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice).

  Theorem adv_DHKE_f A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A ((𝟙 → τ_DH) → 𝔹)%T) →
    advantage A DHKE_f DHKE_SIM_f #true <=
      advantage (λ: "d", A (λ: <>, F_AUTH ∘f (C_lazy "d")))%V DH_real DH_rand #true.
  Proof using All.
    intros HA. rewrite /DHKE_f /DHKE_SIM_f.
    assert (is_closed_expr ∅ F_AUTH) as HFc by is_closed.
    eapply (advantage_triangle _ _ (λ: <>, F_AUTH ∘f C_DH_real)%V _ _ 0).
    { apply (advantage_zero_f _ _ _ _ (λ _, τ_DH)); [exact HA| |]; intros HRGS.
      - iApply F_AUTH_DH_KE_FAUTH_C_DH_real.
      - iApply F_AUTH_C_DH_real_FAUTH_DH_KE. }
    2: { rewrite Rplus_0_l. reflexivity. }
    eapply (advantage_triangle _ _ (λ: <>, F_AUTH ∘f C_DH_rand)%V _ _ _ 0).
    - apply (advantage_reduction_f A "d" (F_AUTH ∘f (C_lazy "d")) _ _ DH_real DH_rand).
      + change ((func_comp (val_subst "d" DH_real F_AUTH) (C_lazy DH_real))%E = (F_AUTH ∘f C_DH_real)%E).
        by rewrite (subst_is_closed ∅ F_AUTH "d" DH_real HFc (not_elem_of_empty _)).
      + change ((func_comp (val_subst "d" DH_rand F_AUTH) (C_lazy DH_rand))%E = (F_AUTH ∘f C_DH_rand)%E).
        by rewrite (subst_is_closed ∅ F_AUTH "d" DH_rand HFc (not_elem_of_empty _)).
    - apply (advantage_zero_f _ _ _ _ (λ _, τ_DH)); [exact HA| |]; intros HRGS.
      + iApply F_AUTH_C_DH_rand_FAUTH_DH_SIM_F_KE.
      + iApply F_AUTH_DH_SIM_F_KE_FAUTH_C_DH_rand.
    - rewrite Rplus_0_r. reflexivity.
  Qed.

  Lemma T_DH_f_bool_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ (interp._ty η μ δ ((() ⇾ T_DH) ⇾ 𝔹) ξ)%T ≤ₜ ((𝟙 → τ_DH) → 𝔹)%T.
  Proof using All.
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply T_DH_subtype].
  Qed.

  Lemma adv_DHKE_f_typed A :
    ⊢ᵥ A : ((() ⇾ T_DH) ⇾ TBool) →
    advantage A DHKE_f DHKE_SIM_f #true <=
      advantage (λ: "d", A (λ: <>, F_AUTH ∘f (C_lazy "d")))%V DH_real DH_rand #true.
  Proof using All.
    intros HAtyped. apply adv_DHKE_f.
    intros HRGS.
    apply (@fundamental_val Σ HRGS) in HAtyped.
    iPoseProof HAtyped as "Hadv".
    unfold bin_log_val_related.
    iSpecialize ("Hadv" $! [] [] ∅ []).
    iModIntro. iApply (T_DH_f_bool_subtype [] [] ∅ []).
    by rewrite /sem_val_typed /=.
  Qed.

End adv_dhke_factory.
