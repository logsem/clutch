From iris.proofmode Require Import base proofmode classes. 
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra class_instances.
From clutch.prob_eff_lang.probblaze Require Import tactics.
From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Export def_dhke.
From clutch.prob_eff_lang.probblaze Require Export sec_channel_def xor.
From clutch.prob_eff_lang.probblaze Require Export sec_channel_prf.
From clutch.prob_eff_lang.probblaze Require Export dhke_channel_lazy_results dhke_channel_lazy_authchan.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_judgement sem_def.

Import fingroup.
Import fingroup.fingroup.



Import valgroup_tactics.

Section new_comp_verification.
  Context `{probblazeRGS Σ}.
  Context (channel leaksec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 keyleak1 keyleak2 schannel1 schannel2 l1 l2 l2': label).
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.
  (* Context {Key Support : nat}. *)
  Let Key := S (S n'').
  Let Support := S (S n'').
  Variable xor_struct : XOR (Key := Key) (Support := Support).
  Variable bij_group_xor_sem : vgG -> vgG -> vgG.
  Hypothesis Bij_xor_sem : ∀ g1 g2 : vgG, bij_group_xor_sem (bij_group_xor_sem g1 g2) g2 = g1.
  Context `{!XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}. 

  Notation "'𝔾'" := sem_ty_group.
  Definition τ := (* the type should match the program. Look carefully at the order of the incoming effects *)
        (* the type of the client needs to change to a linear function *)
        (∀ᵣ θ__L ,(∀ᵣ θₕ, ((𝔾 -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> (Option 𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)
                  (* the product needs to be under a bang, since the effects can be used multiple times *)
                   ⊸ (∀ᵣ θ₁,∀ᵣ θ2, ((((𝔾 × (𝟙 + 𝟙))) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙)) 
                    ⊸ (((𝔾 × (𝟙 + 𝟙)) -{ θ2 }-> 𝟙) × ((𝟙 + 𝟙) -{ θ2 }-> Option 𝔾)) -{ sem_row_union θ₁ (sem_row_union θ2 θ__L) }-∘ 𝟙))%T.

  Definition REAL_CHAN_DHKE : val :=
    λ: "f", ((λ: "f", F_AUTH (DH_KE "f"))%V ||ᵣ F_OAUTH) (CHAN xor "f").

  Definition REAL_CHAN_DH_REAL : val :=
    λ: "f", ( (λ: "f", F_AUTH (C_lazy DH_real "f"))%V ||ᵣ F_OAUTH) (CHAN xor "f").

  Definition REAL_CHAN_DH_RAND : val :=
    λ: "f", ((λ: "f", F_AUTH (C_lazy DH_rand "f"))%V ||ᵣ F_OAUTH) (CHAN xor "f").
  
   (* F_OAUTH[ F_AUTH [DH_KE [CHAN []]]] ≤ F_OAUTH[ F_AUTH [C[DH_real][CHAN []]]] *)
  (*---------------------------------------------------------------------------*)
  Lemma F_OAUTH_DHKE_C_REAL :
    ⊢ sem_val_typed REAL_CHAN_DHKE REAL_CHAN_DH_REAL τ.
  Proof. 
    iApply func_comp_left.
    - admit.                    (* closed expressions *)
    - admit.                    (* closed expressions *)
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. unshelve iApply F_AUTH_DH_KE_FAUTH_C_DH_real; try done. 
      + admit.                  (* F_OAUTH well-typed *)
    - admit.                    (* CHAN well-typed *)
  Admitted. 
   

  Lemma C_REAL_DHKE_F_OAUTH :
     ⊢ sem_val_typed REAL_CHAN_DH_REAL REAL_CHAN_DHKE τ.
  Proof. 
    iApply func_comp_left.
    - admit.                    (* closed expressions *)
    - admit.                    (* closed expressions *)
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. iApply F_AUTH_C_DH_real_FAUTH_DH_KE; try done.
      + admit.                  (* F_OAUTH well-typed *)
    - admit.                    (* CHAN well-typed *)
  Admitted. 

 
  Definition DHSIM_FKE_CHAN1 : val :=
    (λ: "f", ((λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V ||ᵣ F_OAUTH) (CHAN xor "f")). 

  Definition DHSIM_FKE_CHAN2 : val :=
    (λ: "f", ((λ: "f", (λ: "f", F_AUTH (DH_SIM "f"))%V (F_KE_lazy_alice "f"))%V ||ᵣ F_OAUTH) (CHAN xor "f")). 

  Definition DHSIM_FKE_CHAN3 : val :=
    ((F_AUTH ∘f DH_SIM) ∘F (F_KE_lazy_alice ||ᵣ F_OAUTH)%V)%V ∘f (CHAN xor).
    (* (λ: "f", (λ: "f" "rF" "rH", (λ: "f", F_AUTH (DH_SIM "f"))%V (λ: "rG", (F_KE ||ᵣ F_OAUTH)%V "f" "rH" "rG") "rF") (CHAN xor "f")). *)

  Definition DHSIM_FKE_CHAN4 : val :=
    (F_AUTH ∘f DH_SIM) ∘F (R_CHAN xor_struct).
    (* (λ: "f" "rF" "rH", (λ: "f", F_AUTH (DH_SIM "f"))%V (λ: "rG", (λ: "f", (F_KE ||ᵣ F_OAUTH)%V (CHAN xor "f")) "f" "rH" "rG") "rF").  *)

  Lemma REAL_CHAN_DH_RAND_DHSIM_FKE_CHAN1 : 
    ⊢ sem_val_typed REAL_CHAN_DH_RAND DHSIM_FKE_CHAN1 τ.
  Proof.
    iApply func_comp_left.
    - admit.
    - admit.
    - iIntros (θ). iApply parallel_comp_right. 
      + iApply F_AUTH_C_DH_rand_FAUTH_DH_SIM_F_KE; try done.
      + admit.
    - admit.
  Admitted. 

  Lemma DHSIM_FKE_CHAN1_REAL_CHAN_DH_RAND : 
    ⊢ sem_val_typed DHSIM_FKE_CHAN1 REAL_CHAN_DH_RAND τ.
  Proof.
    iApply func_comp_left.
    - admit.
    - admit.
    - iIntros (θ). iApply parallel_comp_right.
      + iApply F_AUTH_DH_SIM_F_KE_FAUTH_C_DH_rand; try done. 
      + admit.
    -  admit.
  Admitted. 

  Lemma DHSIM_FKE_CHAN1_DHSIM_FKE_CHAN2 : 
    ⊢ sem_val_typed  DHSIM_FKE_CHAN1 DHSIM_FKE_CHAN2 τ.
  Proof.
    iApply func_comp_left.
    - admit.
    - admit.
    - iIntros (θ). iApply parallel_comp_right.
      + unfold τ__F. iApply func_comp_assoc.
        * admit.
        * admit.
        * admit.
      + admit.
    - admit.
  Admitted. 

  Lemma DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN1 : 
    ⊢ sem_val_typed DHSIM_FKE_CHAN2 DHSIM_FKE_CHAN1 τ.
  Proof.
    iApply func_comp_left.
    - admit.
    - admit.
    - iIntros (θ). iApply parallel_comp_right.
      + iApply func_comp_assoc_rev.
        * admit.
        * admit.
        * admit.
      + admit.
    - admit.
  Admitted. 
        
  Lemma DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN3 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN2 DHSIM_FKE_CHAN3 τ.
  Proof.
    (* All admits are well-typedness *)
    iApply func_comp_left.
    - admit.                    (* closed expr *)
    - admit.                    (* closed expr *)
    - iIntros (θ). iApply func_comp_parallel_comp_assoc; try done.
      + admit.
      + admit.
      + admit.
    - admit.
  Admitted.

  Lemma DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN2 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN3 DHSIM_FKE_CHAN2 τ.
  Proof.
    iApply func_comp_left.
    - admit.
    - admit.
    - iIntros (θ). iApply func_comp_parallel_comp_assoc_rev; try done.
      + admit.
      + admit.
      + admit.
    - admit.
  Admitted. 
   
  Lemma DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN3 DHSIM_FKE_CHAN4 τ.
  Proof. 
    iApply functionality_comp_func_comp_assoc; first done.  
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
Admitted. 

  Lemma DHSIM_FKE_CHAN4_DHSIM_FKE_CHAN3 :
    ⊢ sem_val_typed DHSIM_FKE_CHAN4 DHSIM_FKE_CHAN3 τ.
  Proof. 
    iApply functionality_comp_func_comp_assoc_rev; first done. 
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted. 
 

  Definition SIMSIMFCHAN : val :=
    (F_AUTH ∘f DH_SIM) ∘F (CHAN_SIM_lazy ∘f F_CHAN).
    (* (λ: "f" "rF" "rH", (λ: "f", F_AUTH (DH_SIM "f"))%V (λ: "rG", (λ: "f", CHAN_SIM (F_CHAN "f"))%V "f" "rH" "rG") "rF").  *)

  Lemma DHSIM_FKE_CHAN4_SIMFCHAN :
    ⊢ sem_val_typed DHSIM_FKE_CHAN4 SIMSIMFCHAN τ.
  Proof.           
    iApply functionality_comp_cong. 
    - admit.                    (* closed *)
    - admit.                    (* closed *)
    - admit.                    (* closed *)
    - unshelve iApply R_I_SCHAN; done.                    (* security of secure channel  *)
    - admit.                    (* well-typedness *)
  Admitted. 


  Lemma SIMFCHAN_DHSIM_FKE_CHAN4 :
    ⊢ sem_val_typed SIMSIMFCHAN DHSIM_FKE_CHAN4 τ.
  Proof.           
    iApply functionality_comp_cong.
    - admit.
    - admit.
    - admit.
    - unshelve iApply I_R_SCHAN; done.                    (* security of secure channel *)
    - admit.
  Admitted. 

End new_comp_verification.
