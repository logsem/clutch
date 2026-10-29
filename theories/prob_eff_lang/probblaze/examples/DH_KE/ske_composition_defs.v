From clutch.prob_eff_lang.probblaze Require Import logic sem_types sem_def sem_row.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Export valgroup def_dhke ske_sec_chan_def.

Import fingroup.

(* The programs (functionality composites) verified in [new_composition.v],
   together with the top-level target type [τ].  Split out so the slow
   [is_closed] proofs and the semantic-typing content can be compiled
   separately. *)

Section new_comp_verification.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.
  #[local] Notation n := (S n'').
  (* message and cipher spaces: abstract *)
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  (* key space is valgroup *)
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.

  Definition REAL_CHAN_DHKE : expr :=
    ((F_AUTH ∘f DH_KE) ||ᵣ F_OAUTH) ∘f CHAN.

  Definition REAL_CHAN_DH_REAL : expr :=
    ((F_AUTH ∘f C_DH_real) ||ᵣ F_OAUTH) ∘f CHAN.

  Definition REAL_CHAN_DH_RED : expr :=
    λ:"DH", ((F_AUTH ∘f (C_lazy "DH")) ||ᵣ F_OAUTH) ∘f CHAN.

  Definition REAL_CHAN_DH_RED_REAL : expr := REAL_CHAN_DH_RED DH_real.
  Definition REAL_CHAN_DH_RED_RAND : expr := REAL_CHAN_DH_RED DH_rand.

  Definition REAL_CHAN_DH_RAND : expr :=
    ((F_AUTH ∘f (C_DH_rand)) ||ᵣ F_OAUTH) ∘f CHAN.

  Definition DHSIM_FKE_CHAN1 : expr :=
    ((F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)) ||ᵣ F_OAUTH) ∘f CHAN.

  Definition DHSIM_FKE_CHAN2 : expr :=
    (((F_AUTH ∘f DH_SIM) ∘f F_KE_lazy_alice) ||ᵣ F_OAUTH) ∘f CHAN.

  Definition DHSIM_FKE_CHAN3 : expr :=
    ((F_AUTH ∘f DH_SIM) ∘F (F_KE_lazy_alice ||ᵣ F_OAUTH)) ∘f CHAN.

  Definition DHSIM_FKE_CHAN4 : expr :=
    (F_AUTH ∘f DH_SIM) ∘F sc_real.

  Definition DHSIM_FKE_GAME1 : expr := 
    (F_AUTH ∘f DH_SIM) ∘F game1.

  Definition DHSIM_FKE_RED : expr := 
    λ: "enc", (F_AUTH ∘f DH_SIM) ∘F (@reduction _ _ _ mt ms "enc").
  
  Definition DHSIM_FKE_RED_ENC_REAL : expr :=
    DHSIM_FKE_RED (enc_real_tape ske).

  Definition DHSIM_FKE_RED_ENC_IDEAL : expr :=
    DHSIM_FKE_RED (enc_ideal ske).

  Definition DHSIM_FKE_GAME2 : expr := 
    (F_AUTH ∘f DH_SIM) ∘F game2.

  Definition SIMSIMFCHAN : expr :=
    (F_AUTH ∘f DH_SIM) ∘F sc_ideal.

End new_comp_verification.

Section type.
  Context `{!probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  (* message and cipher spaces: abstract *)
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  (* key space is valgroup *)
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.
  Context {msg : @fin_val Σ _ mt ms} {cipher : @fin_val Σ _ ct cs}.
  Context {SKE : @SYM Σ _ vg_fvt mt ct vg_fvts ms cs vg_fv msg cipher ske}.

  
  Import valgroup_notation.

  Definition τ := (* the type should match the program. Look carefully at the order of the incoming effects *)
        (* the type of the client needs to change to a linear function *)
        (∀ᵣ θ__L ,(∀ᵣ θₕ, ((ℕ -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> (Option (msg.(sem_τFT))))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)
                  (* the product needs to be under a bang, since the effects can be used multiple times *)
                   ⊸ (∀ᵣ θ1,∀ᵣ θ2, (((((cipher.(sem_τFT) × (𝟙 + 𝟙))) -{ θ1 }-> 𝟙) × ((𝟙 + 𝟙) -{ θ1 }-> Option 𝟙))
                    × (((𝔾 × (𝟙 + 𝟙)) -{ θ2 }-> 𝟙) × ((𝟙 + 𝟙) -{ θ2 }-> Option ℕ))) -{ sem_row_union (¡θ1)%R (sem_row_union (¡θ2)%R θ__L) }-∘ 𝟙))%T.
End type.
