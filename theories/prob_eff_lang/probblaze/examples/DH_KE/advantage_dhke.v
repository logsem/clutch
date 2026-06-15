From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup.
From clutch.prob_eff_lang.probblaze Require Import dhke_channel def_dhke adequacy. 

Section adv_dhke.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {la1 la2 : label}.     (* can be removed once dhke_channel.v has been cleaned up *)

  Definition τ_DH `{!probblazeRGS Σ}
    := (∀ᵣ θ__L, (∀ᵣ θₕ, ((sem_ty_sum 𝟙 𝟙) -{ θₕ }-> (Option sem_ty_group)) -{ sem_row_union θₕ θ__L }-> 𝟙)%T 
                 ⊸ ((∀ᵣ θₗ, (((⊤ × (𝟙 + 𝟙)) -{ θₗ }-> 𝟙) × ((𝟙 + 𝟙) -{ θₗ }-> Option ⊤)) 
                            -{ sem_row_union θₗ θ__L }-∘ 𝟙)))%T.

  Lemma adv_DHKE_DH_real  A :
    (∀ `{!probblazeRGS Σ}, 
       ⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    nonneg (advantage A (λ: "f", F_AUTH (DH_KE "f"))%V ((λ: "DH" "f", F_AUTH (C "DH" "f"))%V DH_real) #true) = 0%R.
  Proof using H inG0 inG1 inG2 la2 G. (* also debris from dhke_channel *)
    intros. eapply sem_typed_advantage; eauto. split.
    - intros Hrgs. apply DHKE_RED; eauto. 
    - intros Hrgs. apply RED_DHKE; eauto.
  Qed. 

  Lemma adv_DH_rand_FKE  A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    nonneg (advantage A ((λ: "DH" "f", F_AUTH (C "DH" "f"))%V DH_rand) (λ: "f", F_AUTH (DH_SIM (F_KE "f")))%V  #true) = 0%R.
  Proof using H inG0 inG1 inG2 G la2. 
    intros. eapply sem_typed_advantage; eauto. split.
    - intros Hrgs. apply RED_DHSIM; eauto.
    - intros Hrgs. apply DHSIM_RED; eauto.
  Qed. 

  Theorem adv_DHKE A (ε : R) :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    advantage A ((λ: "DH" "f", F_AUTH (C "DH" "f"))%V DH_real) ((λ: "DH" "f", F_AUTH (C "DH" "f"))%V DH_rand) #true <= ε →
    advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE "f")))%V #true <= ε.
  Proof using H inG0 inG1 inG2 G la2. 
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
    advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE "f")))%V #true 
    <= advantage A ((λ: "DH" "f", F_AUTH (C "DH" "f"))%V DH_real) ((λ: "DH" "f", F_AUTH (C "DH" "f"))%V DH_rand) #true.
  Proof using H inG0 inG1 inG2 G la2. 
    intros. eapply adv_DHKE; eauto; lra.
  Qed.
    
  Theorem adv_DHKE_real A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ_DH → 𝔹)%T) →
    advantage A (λ: "f", F_AUTH (DH_KE "f"))%V (λ: "f", F_AUTH (DH_SIM (F_KE "f")))%V #true <=
      advantage (λ: "v", A (((λ: "DH", (λ: "f", F_AUTH (C "DH" "f")))%V "v")))%V DH_real DH_rand #true.
  Proof using H inG0 inG1 inG2 G la2.  
    intros.
    etrans. 
    - apply adv_DHKE_no_epsilon; eauto.
    - eapply advantage_reduction. 
      intros ?. eexists _,_.
      split; try done.
      split.
      + admit.                  (* F_AUTH ∘ C is well-typed *)
      + admit.                  (* DH_real and DH_rand are well-typed *)
  Admitted. 

End adv_dhke.
