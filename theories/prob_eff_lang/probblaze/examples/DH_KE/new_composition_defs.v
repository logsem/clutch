From clutch.prob_eff_lang.probblaze Require Import logic sem_types sem_def sem_row.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import valgroup def_dhke sec_channel_def sec_channel_prf xor.


(* The programs (functionality composites) verified in [new_composition.v],
   together with the top-level target type [τ].  Split out so the slow
   [is_closed] proofs and the semantic-typing content can be compiled
   separately. *)

Section new_comp_verification.
  Context `{probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.
  Let Key := (S n'').
  Let Support := (S n'').
  Context {xor_struct : XOR (Key := Key) (Support := Support)}.
  Context `{!XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}.

  Import valgroup_notation.

  Definition τ := (* the type should match the program. Look carefully at the order of the incoming effects *)
        (* the type of the client needs to change to a linear function *)
        (∀ᵣ θ__L ,(∀ᵣ θₕ, ((ℕ -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> (Option 𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)
                  (* the product needs to be under a bang, since the effects can be used multiple times *)
                   ⊸ (∀ᵣ θ₁,∀ᵣ θ2, ((((𝔾 × (𝟙 + 𝟙))) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙))
                    ⊸ (((𝔾 × (𝟙 + 𝟙)) -{ θ2 }-> 𝟙) × ((𝟙 + 𝟙) -{ θ2 }-> Option ℕ)) -{ sem_row_union θ₁ (sem_row_union θ2 θ__L) }-∘ 𝟙))%T.

  Definition REAL_CHAN_DHKE : val :=
    λ: "f", ((λ: "f", F_AUTH (DH_KE "f"))%V ||ᵣ F_OAUTH) (CHAN xor "f").

  Definition REAL_CHAN_DH_REAL : val :=
    λ: "f", ( (λ: "f", F_AUTH (C_lazy DH_real "f"))%V ||ᵣ F_OAUTH) (CHAN xor "f").

  Definition REAL_CHAN_DH_RED : val :=
    λ:"DH", λ: "f", ( (λ: "f", F_AUTH (C_lazy "DH" "f")) ||ᵣ F_OAUTH) (CHAN xor "f").

  Definition REAL_CHAN_DH_RED_REAL : expr := REAL_CHAN_DH_RED DH_real.
  Definition REAL_CHAN_DH_RED_RAND : expr := REAL_CHAN_DH_RED DH_rand.

  Definition REAL_CHAN_DH_RAND : val :=
    λ: "f", ((λ: "f", F_AUTH (C_lazy DH_rand "f"))%V ||ᵣ F_OAUTH) (CHAN xor "f").

  Definition DHSIM_FKE_CHAN1 : val :=
    (λ: "f", ((λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V ||ᵣ F_OAUTH) (CHAN xor "f")).

  Definition DHSIM_FKE_CHAN2 : val :=
    (λ: "f", ((λ: "f", (λ: "f", F_AUTH (DH_SIM "f"))%V (F_KE_lazy_alice "f"))%V ||ᵣ F_OAUTH) (CHAN xor "f")).

  Definition DHSIM_FKE_CHAN3 : val :=
    ((F_AUTH ∘f DH_SIM) ∘F (F_KE_lazy_alice ||ᵣ F_OAUTH)%V)%V ∘f (CHAN xor).

  Definition DHSIM_FKE_CHAN4 : val :=
    (F_AUTH ∘f DH_SIM) ∘F (R_CHAN xor_struct).

  Definition SIMSIMFCHAN : val :=
    (F_AUTH ∘f DH_SIM) ∘F (CHAN_SIM_lazy ∘f F_CHAN).

End new_comp_verification.
