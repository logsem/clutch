From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sec_channel_def p_composition sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup adequacy.
From clutch.prob_eff_lang.probblaze Require Import new_composition xor new_composition_defs def_dhke.

Section adv_comp.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.  
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context `{Hpre :probblazeRGpreS Σ}.
  Let Key := S (S n'').
  Let Support := S (S n'').
  Variable xor_struct : XOR (Key := Key) (Support := Support).
  Context `{X : ∀ `{!probblazeRGS Σ}, XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}.


  Theorem adv_composition A :
     (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ → 𝔹)%T) →
    advantage A
      (REAL_CHAN_DHKE xor_struct)
      SIMSIMFCHAN #true
    <= advantage A 
                 (REAL_CHAN_DH_REAL xor_struct)
                 (REAL_CHAN_DH_RAND xor_struct) #true.
  Proof using G Hpre Key Support X cg inG0 inG1 inG2 vg vgg xor_struct Σ. 
    intros Hadv.
    eapply (advantage_triangle _ _ _ _ _ 0); last (rewrite Rplus_0_l; apply Rle_refl).
    - right. eapply sem_val_typed_advantage; first apply Hadv.
      split.
      + intros H. apply F_OAUTH_DHKE_C_REAL; try done.
      + intros H. apply C_REAL_DHKE_F_OAUTH; try done.
    - eapply (advantage_triangle _ _ _ _ _ _ 0); [apply Rle_refl| | (rewrite Rplus_0_r; apply Rle_refl)].
      eapply (advantage_triangle _ _ _ _ _ 0 0); last lra.
      { right. eapply sem_val_typed_advantage; first apply Hadv.
        split. 
        - intros H. by apply REAL_CHAN_DH_RAND_DHSIM_FKE_CHAN1. 
        - intros H. by apply DHSIM_FKE_CHAN1_REAL_CHAN_DH_RAND. }
      eapply (advantage_triangle _ _ _ _ _ 0 0); last lra.
      { right. eapply sem_val_typed_advantage; first apply Hadv.
        split. 
        - intros H. by apply DHSIM_FKE_CHAN1_DHSIM_FKE_CHAN2.
        - intros H. by apply DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN1. }
      eapply (advantage_triangle _ _ _ _ _ 0 0); last lra.
      { right. eapply sem_val_typed_advantage; first apply Hadv.
        split. 
        - intros H. by apply DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN3.
        - intros H. by apply DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN2. }
      eapply (advantage_triangle _ _ _ _ _ 0 0); last lra.
      { right. eapply sem_val_typed_advantage; first apply Hadv.
        split. 
        - intros H. by apply DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4.
        - intros H. by apply DHSIM_FKE_CHAN4_DHSIM_FKE_CHAN3. }
      right. eapply sem_val_typed_advantage; first apply Hadv.
      split.
      + intros H. by apply DHSIM_FKE_CHAN4_SIMFCHAN.
      + intros H. by apply SIMFCHAN_DHSIM_FKE_CHAN4. 
  Qed. 

  Theorem adv_composition_real A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ → 𝔹)%T) →
    advantage A (REAL_CHAN_DHKE xor_struct) SIMSIMFCHAN #true <=
      advantage (λ: "v", A (((λ: "DH", λ: "f", (((λ: "f", F_AUTH (C_lazy "DH" "f")))%V ||ᵣ F_OAUTH) "f") "v")))%V DH_real DH_rand #true.
  Proof using G Hpre Key Support X cg inG0 inG1 inG2 vg vgg xor_struct Σ. 
    intros.
    etrans. 
    - apply adv_composition; eauto.
    -                           (* A lemma relating REAL_CHAN_DH_REAL and REAL_CHAN_DH_RAND is needed, where they first take DDH as arguments *)
(* eapply advantage_reduction. 
         intros ?. eexists _,_.
         split; try done.
         split.
         + admit.
         + admit.
     Admitted.  *)
  Admitted. 

Section adv_comp.
