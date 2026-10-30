From clutch.prob_eff_lang.probblaze Require Import logic.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup def_dhke sec_channel_def sec_channel_prf mask.
(* Syntactic closedness of the composite programs.  These [is_closed]
   proofs are slow, so they live in their own file. *)
Import fingroup.

Section new_comp_verification.
  Context `{probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context {msk : Mask vgG vgval}.
  Context `{!Mask_struc}.

  (* [is_closed] discharges its leaves with [auto]; make the XOR operation's
     closedness (a field of the [XOR] class) available to it. *)
  #[local] Hint Resolve mask_closed : core.

  Lemma F_OAUTH_closed : is_closed_expr ∅ F_OAUTH.
  Proof. is_closed. Qed. 
  Lemma F_AUTH_closed : is_closed_expr ∅ F_AUTH.
  Proof. is_closed. Qed. 
  Lemma DH_SIM_closed : is_closed_expr ∅ DH_SIM.
  Proof. is_closed. Qed.
  Lemma FKE_closed : is_closed_expr ∅ F_KE_lazy_alice.
  Proof. is_closed. Qed.
  Lemma CHAN_closed : is_closed_expr ∅ CHAN.
  Proof. is_closed. Qed.

  Lemma F_AUTH_DHKE_FOAUTH_closed : is_closed_expr ∅ ((F_AUTH ∘f DH_KE) ||ᵣ F_OAUTH).
  Proof. is_closed. Qed.
  Lemma F_AUTH_DHKE_closed : is_closed_expr ∅ (F_AUTH ∘f DH_KE).
  Proof. is_closed. Qed.
  Lemma F_AUTH_DHSIM_closed : is_closed_expr ∅ (F_AUTH ∘f DH_SIM).
  Proof. is_closed. Qed.

  Lemma F_AUTH_C_DH_real_closed : is_closed_expr ∅ (F_AUTH ∘f C_DH_real).
  Proof. is_closed. Qed.
  Lemma F_AUTH_C_DH_rand_closed : is_closed_expr ∅ (F_AUTH ∘f C_DH_rand).
  Proof. is_closed. Qed.
  Lemma F_AUTH_C_DDH_real_FOAUTH_closed : is_closed_expr ∅ ((F_AUTH ∘f C_DH_real) ||ᵣ F_OAUTH).
  Proof. is_closed. Qed.
  Lemma F_AUTH_C_DDH_rand_FOAUTH_closed : is_closed_expr ∅ ((F_AUTH ∘f C_DH_rand) ||ᵣ F_OAUTH).
  Proof. is_closed. Qed.
  Lemma F_AUTH_DHSIM_FKE_closed : is_closed_expr ∅ (F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)).
  Proof. is_closed. Qed.
  Lemma F_AUTH_DHSIM_FKE_assoc_closed : is_closed_expr ∅ ((F_AUTH ∘f DH_SIM) ∘f F_KE_lazy_alice).
  Proof. is_closed. Qed.


  Lemma DHSIM_FKE_CHAN1_closed : is_closed_expr ∅ ((F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)) ||ᵣ F_OAUTH).
  Proof. is_closed. Qed.

  Lemma DHSIM_FKE_CHAN2_closed : is_closed_expr ∅ (((F_AUTH ∘f DH_SIM) ∘f F_KE_lazy_alice) ||ᵣ F_OAUTH).
  Proof. is_closed. Qed.

  Lemma DHSIM_FKE_CHAN3_closed : is_closed_expr ∅ ((F_AUTH ∘f DH_SIM) ∘F (F_KE_lazy_alice ||ᵣ F_OAUTH)).
  Proof. is_closed. Qed.

  Lemma F_AUTH_DH_SIM_closed : is_closed_expr ∅ (F_AUTH ∘f DH_SIM).
  Proof. is_closed. Qed.

  Lemma F_KE_lazy_alice_F_OAUTH_closed : is_closed_expr ∅ (F_KE_lazy_alice ||ᵣ F_OAUTH).
  Proof. is_closed. Qed.

  Lemma R_CHAN_closed : is_closed_expr ∅ R_CHAN.
  Proof. is_closed. Qed.

  Lemma CHAN_SIM_lazy_F_CHAN_closed : is_closed_expr ∅ (CHAN_SIM_lazy ∘f F_CHAN).
  Proof. is_closed. Qed.

End new_comp_verification.
