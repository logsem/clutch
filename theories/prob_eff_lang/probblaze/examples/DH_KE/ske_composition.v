From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import
  primitive_laws proofmode
  spec_rules spec_ra class_instances tactics notation metatheory
  sem_sig.
From clutch.prob_eff_lang.probblaze.typing Require Import fundamental.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import
  dhke_common ske_sec_chan_prf ske_sec_chan_ideal_prf dhke_channel_lazy_results dhke_channel_authchan_new
  ske_composition_defs ske_composition_closed ske_composition_typing.
 
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
  (* message and cipher spaces: abstract *)
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  (* key space is valgroup *)
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.
  (* the semantic side of the scheme: the key space is [vg_fv], the message and
     cipher spaces are abstract.  [enc_sem]/[dec_sem] take and return VALUES of
     those spaces, so nothing below ever decodes a key or a message. *)
  Context {msg : @fin_val Σ _ mt ms} {cipher : @fin_val Σ _ ct cs}.
  Context {SKE : @SYM Σ _ vg_fvt mt ct vg_fvts ms cs vg_fv msg cipher ske}.

  Let τ := (@τ _ _ _ mt ct ms cs msg cipher).


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
       + iApply (F_OAUTH_typed (SKE := SKE)).
    - iApply (CHAN_typed (SKE := SKE)).
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
     + iApply (F_OAUTH_typed (SKE := SKE)).
    - iApply (CHAN_typed (SKE := SKE)).
  Qed.

  Lemma REAL_DHKE_DH_RED_REAL :
    ⊢ sem_typed [] REAL_CHAN_DH_REAL REAL_CHAN_DH_RED_REAL ⊥ τ [].
  Proof using All.
    unfold REAL_CHAN_DH_REAL, C_DH_real, REAL_CHAN_DH_RED_REAL, REAL_CHAN_DH_RED.
    assert ((((F_AUTH ∘f (λ: "f", C_lazy DH_real "f")) ||ᵣ F_OAUTH) ∘f CHAN)%E = val_subst' "DH" DH_real (((F_AUTH ∘f (λ: "f", C_lazy "DH" "f") ||ᵣ F_OAUTH)) ∘f CHAN)%E) as -> by done.
    iApply sem_typed_eta_expansion_l. 
    1,2 : rewrite sem_env.env_dom_nil; apply not_elem_of_nil.
    - iApply (REAL_CHAN_DH_RED_unfolded_typed (SKE := SKE)). 
    - iApply DH_real_self.
  Qed. 

  Lemma REAL_DHKE_DH_RED_REAL' :
    ⊢ sem_typed [] REAL_CHAN_DH_RED_REAL REAL_CHAN_DH_REAL ⊥ τ [].
  Proof using All.
    unfold REAL_CHAN_DH_REAL, C_DH_real, REAL_CHAN_DH_RED_REAL, REAL_CHAN_DH_RED.
    assert ((((F_AUTH ∘f (λ: "f", C_lazy DH_real "f")) ||ᵣ F_OAUTH) ∘f CHAN)%E = val_subst' "DH" DH_real (((F_AUTH ∘f (λ: "f", C_lazy "DH" "f") ||ᵣ F_OAUTH)) ∘f CHAN)%E) as -> by done.
    iApply sem_typed_eta_expansion_r. 
    1,2 : rewrite sem_env.env_dom_nil; apply not_elem_of_nil.
    - iApply (REAL_CHAN_DH_RED_unfolded_typed (SKE := SKE)).
    - iApply DH_real_self.
  Qed. 

  Lemma REAL_DHKE_DH_RED_RAND :
    ⊢ sem_typed [] REAL_CHAN_DH_RAND REAL_CHAN_DH_RED_RAND ⊥ τ [].
  Proof using All.
    unfold REAL_CHAN_DH_RAND, C_DH_rand, REAL_CHAN_DH_RED_RAND, REAL_CHAN_DH_RED.
    assert ((((F_AUTH ∘f (λ: "f", C_lazy DH_rand "f")) ||ᵣ F_OAUTH) ∘f CHAN)%E = val_subst' "DH" DH_rand (((F_AUTH ∘f (λ: "f", C_lazy "DH" "f") ||ᵣ F_OAUTH)) ∘f CHAN)%E) as -> by done.
    iApply sem_typed_eta_expansion_l. 
    1,2 : rewrite sem_env.env_dom_nil; apply not_elem_of_nil.
    - iApply (REAL_CHAN_DH_RED_unfolded_typed (SKE := SKE)).
    - iApply DH_rand_self.
  Qed. 
  
  Lemma REAL_DHKE_DH_RED_RAND' :
    ⊢ sem_typed [] REAL_CHAN_DH_RED_RAND REAL_CHAN_DH_RAND ⊥ τ [].
  Proof using All.
    unfold REAL_CHAN_DH_RAND, C_DH_rand, REAL_CHAN_DH_RED_RAND, REAL_CHAN_DH_RED.
    assert ((((F_AUTH ∘f (λ: "f", C_lazy DH_rand "f")) ||ᵣ F_OAUTH) ∘f CHAN)%E = val_subst' "DH" DH_rand (((F_AUTH ∘f (λ: "f", C_lazy "DH" "f") ||ᵣ F_OAUTH)) ∘f CHAN)%E) as -> by done.
    iApply sem_typed_eta_expansion_r. 
    1,2 : rewrite sem_env.env_dom_nil; apply not_elem_of_nil.
    - iApply (REAL_CHAN_DH_RED_unfolded_typed (SKE := SKE)).
    - iApply DH_rand_self.
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
      + iApply (F_OAUTH_typed (SKE := SKE)).
    - iApply (CHAN_typed (SKE := SKE)).
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
      + iApply (F_OAUTH_typed (SKE := SKE)).
    - iApply (CHAN_typed (SKE := SKE)).
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
        * iApply (F_AUTH_typed (SKE := SKE)).
        * iApply (DH_SIM_typed (SKE := SKE)).
        * iApply (F_KE_lazy_alice_typed (SKE := SKE)).
      + iApply (F_OAUTH_typed (SKE := SKE)).
    - iApply (CHAN_typed (SKE := SKE)).
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
        * iApply (F_AUTH_typed (SKE := SKE)).
        * iApply (DH_SIM_typed (SKE := SKE)).
        * iApply (F_KE_lazy_alice_typed (SKE := SKE)).
      + iApply (F_OAUTH_typed (SKE := SKE)).
    - iApply (CHAN_typed (SKE := SKE)).
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
      + iApply (F_AUTH_DH_SIM_FO_typed (SKE := SKE)).
      + iApply (F_KE_body_typed (SKE := SKE)).
      + iApply (F_OAUTH_typed (SKE := SKE)).
    - iApply (CHAN_typed (SKE := SKE)).
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
      + iApply (F_AUTH_DH_SIM_FO_typed (SKE := SKE)).
      + iApply (F_KE_body_typed (SKE := SKE)).
      + iApply (F_OAUTH_typed (SKE := SKE)).
    - iApply (CHAN_typed (SKE := SKE)).
  Qed.
  
  Lemma DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4 :
    ⊢ sem_typed [] DHSIM_FKE_CHAN3 DHSIM_FKE_CHAN4 ⊥ τ [].
  Proof using All.
    iApply functionality_comp_func_comp_assoc_gen; first done.
    - apply F_AUTH_DHSIM_closed.
    - apply F_KE_lazy_alice_F_OAUTH_closed.
    - iApply (F_AUTH_DH_SIM_FO_typed (SKE := SKE)).
    - iApply (F_KE_F_OAUTH_typed (SKE := SKE)).
    - iIntros (???); iApply (CHAN_body_typed (SKE := SKE)).
  Qed.
  
  Lemma DHSIM_FKE_CHAN4_DHSIM_FKE_CHAN3 :
    ⊢ sem_typed [] DHSIM_FKE_CHAN4 DHSIM_FKE_CHAN3 ⊥ τ [].
  Proof using All.
    iApply functionality_comp_func_comp_assoc_gen_rev; first done.
    - apply F_AUTH_DHSIM_closed.
    - apply F_KE_lazy_alice_F_OAUTH_closed.
    - iApply (F_AUTH_DH_SIM_FO_typed (SKE := SKE)).
    - iApply (F_KE_F_OAUTH_typed (SKE := SKE)).
    - iIntros (???); iApply (CHAN_body_typed (SKE := SKE)).
  Qed.
  
  Lemma DHSIM_FKE_CHAN4_GAME1 :
    ⊢ sem_typed [] DHSIM_FKE_CHAN4 DHSIM_FKE_GAME1 ⊥ τ [].
  Proof using All.
    iApply functionality_comp_cong.
    - apply F_AUTH_DHSIM_closed.
    - apply sc_real_closed.
    - apply game1_closed.
    - iApply (@sc_real_game1 _ _ _ _ _ _ mt ct ms cs).  
    - iApply (F_AUTH_DH_SIM_FO_typed (SKE := SKE)).
  Qed.
  
  Lemma GAME1_DHSIM_FKE_CHAN4 :
    ⊢ sem_typed [] DHSIM_FKE_GAME1 DHSIM_FKE_CHAN4 ⊥ τ [].
  Proof using All.
    iApply functionality_comp_cong.
    - apply F_AUTH_DHSIM_closed. 
    - apply game1_closed.
    - apply sc_real_closed.
    - iApply (@game1_sc_real _ _ _ _ _ _ mt ct ms cs).  
    - iApply (F_AUTH_DH_SIM_FO_typed (SKE := SKE)).
  Qed.


  (* Change the game to be initialized in the beginning and make the game a thunk *)
  Lemma GAME1_RED :
    ⊢ sem_typed [] DHSIM_FKE_GAME1 DHSIM_FKE_RED_ENC_REAL ⊥ τ [].
  Proof using All.
    unfold DHSIM_FKE_GAME1, game1, DHSIM_FKE_RED_ENC_REAL, DHSIM_FKE_RED.
    assert (((F_AUTH ∘f DH_SIM) ∘F (@reduction _ _ _ mt ms (enc_real_tape ske)))%E 
            = val_subst' "enc" (enc_real_tape ske) ((F_AUTH ∘f DH_SIM) ∘F ((@reduction _ _ _ mt ms) "enc"))%E) as -> by done.
    iApply sem_typed_eta_expansion_l. 
    1,2 : rewrite sem_env.env_dom_nil; apply not_elem_of_nil.
    - iApply (DHSIM_FKE_RED_unfolded_typed (SKE := SKE)).
    - iApply (enc_real_tape_val_typed (SKE := SKE)).
  Qed.

  Lemma RED_GAME1 :
    ⊢ sem_typed [] DHSIM_FKE_RED_ENC_REAL DHSIM_FKE_GAME1 ⊥ τ [].
  Proof using All.
    unfold DHSIM_FKE_GAME1, game1, DHSIM_FKE_RED_ENC_REAL, DHSIM_FKE_RED.
    assert (((F_AUTH ∘f DH_SIM) ∘F (@reduction _ _ _ mt ms (enc_real_tape ske)))%E 
            = val_subst' "enc" (enc_real_tape ske) ((F_AUTH ∘f DH_SIM) ∘F ((@reduction _ _ _ mt ms) "enc"))%E) as -> by done.
    iApply sem_typed_eta_expansion_r. 
    1,2 : rewrite sem_env.env_dom_nil; apply not_elem_of_nil.
    - iApply (DHSIM_FKE_RED_unfolded_typed (SKE := SKE)).
    - iApply (enc_real_tape_val_typed (SKE := SKE)).
  Qed.

  (* Change the game to be initialized in the beginning and make the game a thunk *)
  Lemma GAME2_RED :
    ⊢ sem_typed [] DHSIM_FKE_GAME2 DHSIM_FKE_RED_ENC_IDEAL ⊥ τ [].
  Proof using All.
    unfold DHSIM_FKE_GAME2, game2, DHSIM_FKE_RED_ENC_IDEAL, DHSIM_FKE_RED.
    assert (((F_AUTH ∘f DH_SIM) ∘F (@reduction _ _ _ mt ms (enc_ideal ske)))%E 
            = val_subst' "enc" (enc_ideal ske) ((F_AUTH ∘f DH_SIM) ∘F ((@reduction _ _ _ mt ms) "enc"))%E) as -> by done.
    iApply sem_typed_eta_expansion_l. 
    1,2 : rewrite sem_env.env_dom_nil; apply not_elem_of_nil.
    - iApply (DHSIM_FKE_RED_unfolded_typed (SKE := SKE)).
    - iApply (enc_ideal_val_typed (SKE := SKE)).
  Qed.

  Lemma RED_GAME2 :
    ⊢ sem_typed [] DHSIM_FKE_RED_ENC_IDEAL DHSIM_FKE_GAME2 ⊥ τ [].
  Proof using All.
    unfold DHSIM_FKE_GAME2, game2, DHSIM_FKE_RED_ENC_IDEAL, DHSIM_FKE_RED.
    assert (((F_AUTH ∘f DH_SIM) ∘F (@reduction _ _ _ mt ms (enc_ideal ske)))%E 
            = val_subst' "enc" (enc_ideal ske) ((F_AUTH ∘f DH_SIM) ∘F ((@reduction _ _ _ mt ms) "enc"))%E) as -> by done.
    iApply sem_typed_eta_expansion_r. 
    1,2 : rewrite sem_env.env_dom_nil; apply not_elem_of_nil.
    - iApply (DHSIM_FKE_RED_unfolded_typed (SKE := SKE)).
    - iApply (enc_ideal_val_typed (SKE := SKE)).
  Qed.

  Lemma DHSIM_FKE_GAME2_IDEAL :
    ⊢ sem_typed [] DHSIM_FKE_GAME2 SIMSIMFCHAN ⊥  τ [].
  Proof using All.
    iApply functionality_comp_cong.
    - apply F_AUTH_DHSIM_closed.
    - apply game2_closed. 
    - apply sc_ideal_closed.
    - iApply (@game2_sc_ideal _ _ _ _ _ _ mt ct ms cs).
    - iApply (F_AUTH_DH_SIM_FO_typed (SKE := SKE)).
  Qed.

  Lemma IDEAL_DHSIM_FKE_GAME2 :
    ⊢ sem_typed [] SIMSIMFCHAN DHSIM_FKE_GAME2 ⊥ τ [].
  Proof using All.
    iApply functionality_comp_cong.
    - apply F_AUTH_DHSIM_closed.
    - apply sc_ideal_closed. 
    - apply game2_closed.
    - iApply (@sc_ideal_game2 _ _ _ _ _ _ mt ct ms cs).
    - iApply (F_AUTH_DH_SIM_FO_typed (SKE := SKE)).
  Qed.

End new_comp_verification.

