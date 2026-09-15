From clutch.prob_eff_lang.probblaze.typing Require Import types interp fundamental.
From Coq.Logic Require Import FunctionalExtensionality.
From clutch.prob_eff_lang.probblaze Require Import advantage.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_judgement sem_row syntax semantics proofmode mode.
From clutch.prob_eff_lang.probblaze Require Import 
  dhke_channel_lazy_results
  dhke_channel_authchan_new
  dhke_common adequacy.

Section adv_dhke.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.

  Import valgroup_notation.
  Import valgroup_tactics.
  
  Definition T_DH : type :=
    (∀R:
       ((∀R: (((() + ()) -{ RVar 0%nat }-> (() + τG)) -{ RVar 0%nat ∪ᵣ RVar 1%nat }-∘ ()))
        -∘
        (∀R: ((((τG * (() + ())) -{ RVar 0%nat }-> ()) * ((() + ()) -{ RVar 0%nat }-> (() + TNat))) -{ RVar 0%nat ∪ᵣ RVar 1%nat }-∘ ()))))%ty.

  Lemma T_DH_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ τ_DH ≤ₜ (interp._ty η μ δ T_DH ξ).
  Proof using All. 
    rewrite /T_DH /τ_DH /sem_ty_option /=. 
    iApply ty_le_row_forall. iIntros (?).
    iApply ty_le_arr; first iApply row_le_refl.
    - iApply ty_le_row_forall; iIntros (?).
      iApply ty_le_arr; [iApply row_le_refl | | iApply ty_le_refl].
      iApply ty_le_mbang_comp; first iApply mode_le_refl.
      iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|].
      iApply ty_le_sum; first iApply ty_le_refl.
      iIntros (??) "!#". iApply τG_subtype.
    - iApply ty_le_row_forall; iIntros (?).
      iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
      iApply ty_le_prod; last iApply ty_le_refl.
      iApply ty_le_mbang_comp; first iApply mode_le_refl.
      iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
      iApply ty_le_prod; last iApply ty_le_refl.
      iIntros (??) "!#". iApply τG_subtype.
  Qed. 

  Lemma T_DH_bool_subtype  `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ (interp._ty η μ δ (T_DH ⇾ 𝔹) ξ)%T ≤ₜ (τ_DH → 𝔹)%T.
  Proof using All. 
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl|iApply T_DH_subtype |iApply ty_le_refl].
  Qed. 

  Lemma adv_DHKE_DH_real  A :
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    nonneg (advantage A (λ: "f", F_AUTH (DH_KE "f"))%V ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_real) #true) = 0%R.
  Proof using inG2 inG1 inG0 H G.
    intros HA. eapply sem_typed_advantage; first apply HA. split.
    - intros Hrgs. apply DHKE_RED. 
    - intros Hrgs. apply RED_DHKE. 
  Qed. 

  Lemma adv_DH_rand_FKE  A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    nonneg (advantage A ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_rand) (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V  #true) = 0%R.
  Proof using H inG0 inG1 inG2 G.
    intros HA. eapply sem_typed_advantage; first apply HA. split.
    - intros Hrgs. apply RED_DHSIM. 
    - intros Hrgs. apply DHSIM_RED.
  Qed. 

  Theorem adv_DHKE A (ε : R) :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    advantage A ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_real) ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_rand) #true <= ε →
    advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V #true <= ε.
  Proof using H inG0 inG1 inG2 G.
    intros HA HAadv.
    eapply advantage_triangle.
    - right. by apply adv_DHKE_DH_real.
    - eapply advantage_triangle. 
      + apply HAadv.
      + right. by apply adv_DH_rand_FKE.
      + done.
    - lra.
  Qed.

  Corollary adv_DHKE_no_epsilon  A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V #true 
    <= advantage A ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_real) ((λ: "DH" "f", F_AUTH (C_lazy "DH" "f"))%V DH_rand) #true.
  Proof using H inG0 inG1 inG2 G.
    intros. eapply adv_DHKE; eauto; lra.
  Qed.
 
  Theorem adv_DHKE_real A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V #true <=
      advantage (λ: "v", A (((λ: "DH", (λ: "f", F_AUTH (C_lazy "DH" "f")))%V "v")))%V DH_real DH_rand #true.
  Proof using H inG0 inG1 inG2 G.
    intros HA.
    etrans.
    - apply adv_DHKE_no_epsilon; eauto.
    - eapply advantage_reduction.
      intros HRGS. exists (𝟙 ⊸ (𝔾 × 𝔾 × 𝔾))%T, τ_DH.
      split; [apply HA | split].
      + apply red_self.
      + split; [apply DH_real_self | apply DH_rand_self].
  Qed.
 
  Lemma adv_DHKE_typed A :
   ⊢ᵥ A : (T_DH ⇾ TBool) →
          advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V #true <=
            advantage (λ: "v", A (((λ: "DH", (λ: "f", F_AUTH (C_lazy "DH" "f")))%V "v")))%V DH_real DH_rand #true.
  Proof using All.
    intros HAtyped. apply adv_DHKE_real. 
    intros HRGS.
    apply (@fundamental_val Σ HRGS) in HAtyped.
    iPoseProof HAtyped as "Hadv".
    unfold bin_log_val_related.
    iSpecialize ("Hadv" $! [] [] ∅ []). 
    iModIntro. iApply T_DH_bool_subtype. 
    by rewrite /sem_val_typed /=. 
  Qed. 

End adv_dhke.

Print Assumptions adv_DHKE_real.
