From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import sec_channel_def p_composition sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup adequacy.
From clutch.prob_eff_lang.probblaze Require Import new_composition xor new_composition_defs def_dhke.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import advantage_dhke_lazy.

Section adv_comp.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.  
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context `{Hpre :probblazeRGpreS Σ}.
  Let Key := S (S n'').
  Let Support := S (S n'').
  Context {xor_struct : XOR (Key := Key) (Support := Support)}.
  Context `{X : ∀ `{!probblazeRGS Σ}, XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}.


  Theorem adv_composition A :
     (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ → 𝔹)%T) →
     advantage A REAL_CHAN_DHKE SIMSIMFCHAN #true
    <=
      advantage A REAL_CHAN_DH_REAL REAL_CHAN_DH_RAND #true.
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


  Lemma REAL_DHKE_DH_RED_RAND_adv (A : val) (b : bool) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (τ → 𝔹)%T) →
    nonneg $ advantage A REAL_CHAN_DH_RED_RAND REAL_CHAN_DH_RAND #b = 0.
  Proof using All.
    intros Aty.
    eapply sem_typed_advantage.
    1: apply Aty.
    split ; intros.
    - by eapply REAL_DHKE_DH_RED_RAND'.
    - simpl. by eapply REAL_DHKE_DH_RED_RAND.
  Qed.

  Lemma REAL_DHKE_DH_RED_REAL_adv (A : val) (b : bool) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (τ → 𝔹)%T) →
    nonneg $ advantage A REAL_CHAN_DH_RED_REAL REAL_CHAN_DH_REAL #b = 0.
  Proof using All.
    intros Aty.
    eapply sem_typed_advantage.
    1: apply Aty.
    split ; intros.
    - by eapply REAL_DHKE_DH_RED_REAL'.
    - simpl. by eapply REAL_DHKE_DH_RED_REAL.
  Qed.

  Theorem adv_composition_real A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ → 𝔹)%T) →
    advantage A REAL_CHAN_DHKE SIMSIMFCHAN #true <=
      advantage (λ: "v", A ((REAL_CHAN_DH_RED "v")))%V DH_real DH_rand #true.
  Proof using G Hpre Key Support X cg inG0 inG1 inG2 vg vgg xor_struct Σ. 
    intros Aty.
    etrans. 
    - apply adv_composition; eauto.
    - eapply (advantage_triangle _ _ _ _ _ 0 _); last try lra.
      3: rewrite Rplus_0_l ; reflexivity.
      2: eapply (advantage_triangle _ _ _ _ _ _ 0); last try lra.
      4: rewrite Rplus_0_r ; reflexivity.
      { right. rewrite advantage_sym.
        apply REAL_DHKE_DH_RED_REAL_adv. done. }
      2: { right. apply REAL_DHKE_DH_RED_RAND_adv. done. }
      apply (advantage_reduction A REAL_CHAN_DH_RED DH_real DH_rand true).
      intros. eexists _,_. split ; [|split].
      1: apply Aty.
      2:{ split.
          - by unshelve eapply DH_real_self.
          - by unshelve eapply DH_rand_self. }
      apply REAL_CHAN_DH_RED_sem_typed.
  Qed.

Section adv_comp.
