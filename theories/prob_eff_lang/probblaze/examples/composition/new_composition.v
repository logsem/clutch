From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import
  primitive_laws proofmode
  spec_rules spec_ra class_instances tactics notation 
  sem_row sem_sig.
From clutch.prob_eff_lang.probblaze.typing Require Import fundamental.
From clutch.prob_eff_lang.probblaze.examples Require Import
  dhke_common sec_channel_def xor sec_channel_prf dhke_channel_lazy_results dhke_channel_authchan_new
  new_composition_defs new_composition_closed new_composition_typing.
 
Import fingroup.
Import fingroup.fingroup.

Import valgroup_tactics.

(* Top-level semantic-typing results: each composite program is related to
   itself (or to the next in the chain) at the target type [τ].  The proofs
   are complete modulo the building-block typing lemmas admitted in
   [new_composition_typing.v]. *)

Section new_comp_verification.
  Context `{probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.
  Context {msk : @Mask (@vgG vg) vgval}.
  Context `{!Mask_struc}.
 

 Lemma REAL_DHKE_DH_RED_REAL :
    ⊢ sem_typed [] REAL_CHAN_DH_REAL REAL_CHAN_DH_RED_REAL ⊥ τ [].
  Proof using All.
    unfold REAL_CHAN_DH_REAL, C_DH_real, REAL_CHAN_DH_RED_REAL, REAL_CHAN_DH_RED.
    assert ((((F_AUTH ∘f (λ: "f", C_lazy DH_real "f")) ||ᵣ F_OAUTH) ∘f CHAN)%E = val_subst' "DH" DH_real (((F_AUTH ∘f (λ: "f", C_lazy "DH" "f") ||ᵣ F_OAUTH)) ∘f CHAN)%E) as -> by done.
    iApply sem_typed_eta_expansion_l. 
    1,2 : rewrite sem_env.env_dom_nil; apply not_elem_of_nil.
    - iApply REAL_CHAN_DH_RED_unfolded_typed. 
    - iApply DH_real_self.
  Qed. 

  Lemma REAL_DHKE_DH_RED_REAL' :
    ⊢ sem_typed [] REAL_CHAN_DH_RED_REAL REAL_CHAN_DH_REAL ⊥ τ [].
  Proof using All.
    unfold REAL_CHAN_DH_REAL, C_DH_real, REAL_CHAN_DH_RED_REAL, REAL_CHAN_DH_RED.
    assert ((((F_AUTH ∘f (λ: "f", C_lazy DH_real "f")) ||ᵣ F_OAUTH) ∘f CHAN)%E = val_subst' "DH" DH_real (((F_AUTH ∘f (λ: "f", C_lazy "DH" "f") ||ᵣ F_OAUTH)) ∘f CHAN)%E) as -> by done.
    iApply sem_typed_eta_expansion_r. 
    1,2 : rewrite sem_env.env_dom_nil; apply not_elem_of_nil.
    - iApply REAL_CHAN_DH_RED_unfolded_typed.
    - iApply DH_real_self.
  Qed. 

  Lemma REAL_DHKE_DH_RED_RAND :
    ⊢ sem_typed [] REAL_CHAN_DH_RAND REAL_CHAN_DH_RED_RAND ⊥ τ [].
  Proof using All.
    unfold REAL_CHAN_DH_RAND, C_DH_rand, REAL_CHAN_DH_RED_RAND, REAL_CHAN_DH_RED.
    assert ((((F_AUTH ∘f (λ: "f", C_lazy DH_rand "f")) ||ᵣ F_OAUTH) ∘f CHAN)%E = val_subst' "DH" DH_rand (((F_AUTH ∘f (λ: "f", C_lazy "DH" "f") ||ᵣ F_OAUTH)) ∘f CHAN)%E) as -> by done.
    iApply sem_typed_eta_expansion_l. 
    1,2 : rewrite sem_env.env_dom_nil; apply not_elem_of_nil.
    - iApply REAL_CHAN_DH_RED_unfolded_typed.
    - iApply DH_rand_self.
  Qed. 
    
  Lemma REAL_DHKE_DH_RED_RAND' :
    ⊢ sem_typed [] REAL_CHAN_DH_RED_RAND REAL_CHAN_DH_RAND ⊥ τ [].
  Proof using All.
    unfold REAL_CHAN_DH_RAND, C_DH_rand, REAL_CHAN_DH_RED_RAND, REAL_CHAN_DH_RED.
    assert ((((F_AUTH ∘f (λ: "f", C_lazy DH_rand "f")) ||ᵣ F_OAUTH) ∘f CHAN)%E = val_subst' "DH" DH_rand (((F_AUTH ∘f (λ: "f", C_lazy "DH" "f") ||ᵣ F_OAUTH)) ∘f CHAN)%E) as -> by done.
    iApply sem_typed_eta_expansion_r. 
    1,2 : rewrite sem_env.env_dom_nil; apply not_elem_of_nil.
    - iApply REAL_CHAN_DH_RED_unfolded_typed.
    - iApply DH_rand_self.
  Qed. 

  (* F_OAUTH[ F_AUTH [DH_KE [CHAN []]]] ≤ F_OAUTH[ F_AUTH [C[DH_real][CHAN []]]] *)
  (*---------------------------------------------------------------------------*)
  Lemma F_OAUTH_DHKE_C_REAL :
    ⊢ sem_typed [] REAL_CHAN_DHKE REAL_CHAN_DH_REAL ⊥ τ [].
  Proof using All.
    iApply func_comp_left.
    - apply F_AUTH_DHKE_FOAUTH_closed. 
    - apply F_AUTH_C_DDH_real_FOAUTH_closed.
    - apply CHAN_closed.
    - iApply parallel_comp_right.
      + apply F_AUTH_DHKE_closed.
      + apply F_AUTH_C_DH_real_closed. 
      + apply F_OAUTH_closed.
      + iApply F_AUTH_DH_KE_FAUTH_C_DH_real.
      + iApply F_OAUTH_typed.   
    - iApply CHAN_typed.        
  Qed. 

  Lemma C_REAL_DHKE_F_OAUTH :
     ⊢ sem_typed [] REAL_CHAN_DH_REAL REAL_CHAN_DHKE ⊥ τ [].
  Proof using All.
    iApply func_comp_left.
    - apply F_AUTH_C_DDH_real_FOAUTH_closed.
    - apply F_AUTH_DHKE_FOAUTH_closed.
    - apply CHAN_closed.
    - iApply parallel_comp_right.
      + apply F_AUTH_C_DH_real_closed.
      + apply F_AUTH_DHKE_closed.
      + apply F_OAUTH_closed.
      + iApply F_AUTH_C_DH_real_FAUTH_DH_KE.
      + iApply F_OAUTH_typed.   
    - iApply CHAN_typed.
  Qed. 

  Lemma REAL_CHAN_DH_RAND_DHSIM_FKE_CHAN1 :
    ⊢ sem_typed [] REAL_CHAN_DH_RAND DHSIM_FKE_CHAN1 ⊥ τ [].
  Proof using All.
    iApply func_comp_left.
    - apply F_AUTH_C_DDH_rand_FOAUTH_closed.
    - apply DHSIM_FKE_CHAN1_closed.
    - apply CHAN_closed.
    - iApply parallel_comp_right.
      + apply F_AUTH_C_DH_rand_closed. 
      + apply F_AUTH_DHSIM_FKE_closed. 
      + apply F_OAUTH_closed.
      + iApply F_AUTH_C_DH_rand_FAUTH_DH_SIM_F_KE.
      + iApply F_OAUTH_typed.   
    - iApply CHAN_typed.
  Qed. 

  Lemma DHSIM_FKE_CHAN1_REAL_CHAN_DH_RAND :
    ⊢ sem_typed [] DHSIM_FKE_CHAN1 REAL_CHAN_DH_RAND ⊥ τ [].
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN1_closed.
    - apply F_AUTH_C_DDH_rand_FOAUTH_closed.
    - apply CHAN_closed.
    - iApply parallel_comp_right.
      + apply F_AUTH_DHSIM_FKE_closed.
      + apply F_AUTH_C_DH_rand_closed.
      + apply F_OAUTH_closed.
      + iApply F_AUTH_DH_SIM_F_KE_FAUTH_C_DH_rand.
      + iApply F_OAUTH_typed.   
    - iApply CHAN_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN1_DHSIM_FKE_CHAN2 :
    ⊢ sem_typed [] DHSIM_FKE_CHAN1 DHSIM_FKE_CHAN2 ⊥ τ [].
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN1_closed.
    - apply DHSIM_FKE_CHAN2_closed.
    - apply CHAN_closed.
    - iApply parallel_comp_right.
      + apply F_AUTH_DHSIM_FKE_closed.
      + apply F_AUTH_DHSIM_FKE_assoc_closed.
      + apply F_OAUTH_closed.
      + iApply func_comp_assoc.
        * apply F_AUTH_closed. 
        * apply DH_SIM_closed.
        * apply FKE_closed. 
        * iApply F_AUTH_typed. 
        * iApply DH_SIM_typed. 
        * iApply F_KE_lazy_alice_typed. 
      + iApply F_OAUTH_typed. 
    - iApply CHAN_typed.
  Qed. 

  Lemma DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN1 :
    ⊢ sem_typed [] DHSIM_FKE_CHAN2 DHSIM_FKE_CHAN1 ⊥ τ [].
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN2_closed.
    - apply DHSIM_FKE_CHAN1_closed.
    - apply CHAN_closed.
    - iApply parallel_comp_right.
      + apply F_AUTH_DHSIM_FKE_assoc_closed.
      + apply F_AUTH_DHSIM_FKE_closed.
      + apply F_OAUTH_closed.
      + iApply func_comp_assoc_rev.
        * apply F_AUTH_closed. 
        * apply DH_SIM_closed.
        * apply FKE_closed. 
        * iApply F_AUTH_typed. 
        * iApply DH_SIM_typed. 
        * iApply F_KE_lazy_alice_typed.
      + iApply F_OAUTH_typed.
    - iApply CHAN_typed.
  Qed.

  Lemma DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN3 :
    ⊢ sem_typed [] DHSIM_FKE_CHAN2 DHSIM_FKE_CHAN3 ⊥ τ [].
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN2_closed.
    - apply DHSIM_FKE_CHAN3_closed.
    - apply CHAN_closed.
    - iApply func_comp_parallel_comp_assoc; first done.
      + apply F_AUTH_DHSIM_closed. 
      + apply F_OAUTH_closed.
      + iApply F_AUTH_DH_SIM_FO_typed. 
      + iApply F_KE_body_typed. 
      + iApply F_OAUTH_typed. 
    - iApply CHAN_typed. 
  Qed. 

  Lemma DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN2 :
    ⊢ sem_typed [] DHSIM_FKE_CHAN3 DHSIM_FKE_CHAN2 ⊥ τ [].
  Proof using All.
    iApply func_comp_left.
    - apply DHSIM_FKE_CHAN3_closed.
    - apply DHSIM_FKE_CHAN2_closed.
    - apply CHAN_closed.
    - iApply func_comp_parallel_comp_assoc_rev; first done.
      + apply F_AUTH_DHSIM_closed. 
      + apply F_OAUTH_closed.
      + iApply F_AUTH_DH_SIM_FO_typed. 
      + iApply F_KE_body_typed. 
      + iApply F_OAUTH_typed. 
    - iApply CHAN_typed. 
  Qed. 

  
  Lemma DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4 :
    ⊢ sem_typed [] DHSIM_FKE_CHAN3 DHSIM_FKE_CHAN4 ⊥ τ [].
  Proof using All.
    unfold DHSIM_FKE_CHAN3, DHSIM_FKE_CHAN4, R_CHAN, τ.
    set (τJ θ1 θ2 := (chan θ1 × gk θ2)%T).
   
    
    iApply (functionality_comp_func_comp_assoc_gen _ _ _ "f" "effs" _ _ _ τJ _); first done. 
    - apply F_AUTH_DH_SIM_closed.
    - apply F_KE_lazy_alice_F_OAUTH_closed.
    - iApply F_AUTH_DH_SIM_FO_typed.
    - unfold τJ.
      iApply F_KE_F_OAUTH_typed.
    -  iIntros (???). iApply CHAN_body_typed.
  Qed. 

  Lemma DHSIM_FKE_CHAN4_DHSIM_FKE_CHAN3 :
    ⊢ sem_typed [] DHSIM_FKE_CHAN4 DHSIM_FKE_CHAN3 ⊥ τ [].
  Proof using All.
     set (τJ θ1 θ2 := (chan θ1 × gk θ2)%T).
     iApply (functionality_comp_func_comp_assoc_gen_rev _ _ _ _ _ _ _ _ τJ); first done.
       - apply F_AUTH_DH_SIM_closed.
       - apply F_KE_lazy_alice_F_OAUTH_closed.
       - iApply F_AUTH_DH_SIM_FO_typed.
       - iApply F_KE_F_OAUTH_typed.
       - iIntros (???). iApply CHAN_body_typed.
     Qed.

  Lemma DHSIM_FKE_CHAN4_SIMFCHAN :
    ⊢ sem_typed [] DHSIM_FKE_CHAN4 SIMSIMFCHAN ⊥ τ [].
  Proof using All.
    iApply functionality_comp_cong.
    - apply F_AUTH_DH_SIM_closed.
    - apply R_CHAN_closed.
    - apply CHAN_SIM_lazy_F_CHAN_closed.
    - iApply R_I_SCHAN. 
    - iApply F_AUTH_DH_SIM_FO_typed.
  Qed.

  Lemma SIMFCHAN_DHSIM_FKE_CHAN4 :
    ⊢ sem_typed [] SIMSIMFCHAN DHSIM_FKE_CHAN4 ⊥ τ [].
  Proof using All.
    iApply functionality_comp_cong.
    - apply F_AUTH_DH_SIM_closed.
    - apply CHAN_SIM_lazy_F_CHAN_closed.
    - apply R_CHAN_closed.
    - iApply I_R_SCHAN. 
    - iApply F_AUTH_DH_SIM_FO_typed.
  Qed.

End new_comp_verification.

