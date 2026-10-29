From clutch.prob_eff_lang.probblaze Require Import logic.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import valgroup def_dhke ske_sec_chan_def.
Import fingroup.

Create HintDb ske_comp_closed discriminated.

Section ske_comp_closed.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {vgg: @val_group_generator vg}.
  (* message and cipher spaces: abstract *)
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  (* key space is valgroup *)
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.

  Lemma F_OAUTH_closed : is_closed_expr ∅ F_OAUTH.
  Proof. is_closed. Qed.
  Lemma F_AUTH_closed : is_closed_expr ∅ F_AUTH.
  Proof. is_closed. Qed.
  Lemma DH_SIM_closed : is_closed_expr ∅ DH_SIM.
  Proof. is_closed. Qed.
  Lemma FKE_closed : is_closed_expr ∅ F_KE_lazy_alice.
  Proof. is_closed. Qed.
  Lemma DH_KE_closed : is_closed_expr ∅ DH_KE.
  Proof. is_closed. Qed.
  Lemma C_DH_real_closed : is_closed_expr ∅ C_DH_real.
  Proof. is_closed. Qed.
  Lemma C_DH_rand_closed : is_closed_expr ∅ C_DH_rand.
  Proof. is_closed. Qed.
  (* [is_closed] leaves the closedness of the scheme's [enc]/[dec] open. *)
  Lemma CHAN_closed : is_closed_expr ∅ CHAN.
  Proof. is_closed. Qed.
  Lemma func_comp_closed : is_closed_expr ∅ func_comp.
  Proof. is_closed. Qed.
  Lemma right_composition_closed : is_closed_expr ∅ right_composition.
  Proof. is_closed. Qed.
  Lemma functionality_composition_closed : is_closed_expr ∅ functionality_composition.
  Proof. is_closed. Qed.

  #[local] Opaque F_OAUTH F_AUTH DH_SIM F_KE_lazy_alice DH_KE C_DH_real C_DH_rand CHAN
    func_comp right_composition functionality_composition.
  #[local] Hint Constants Opaque : ske_comp_closed.
  #[local] Hint Resolve F_OAUTH_closed F_AUTH_closed DH_SIM_closed FKE_closed DH_KE_closed
    C_DH_real_closed C_DH_rand_closed CHAN_closed func_comp_closed right_composition_closed
    functionality_composition_closed : ske_comp_closed.
  #[local] Hint Extern 1 (Is_true (is_closed_val ?v)) =>
    change (Is_true (is_closed_expr ∅ (Val v))) : ske_comp_closed.

  Local Ltac is_closed_hint :=
    cbn; repeat match goal with |- Is_true (_ && _) => apply andb_prop_intro; split end;
    solve [typeclasses eauto with ske_comp_closed | apply bool_decide_pack; set_solver | auto].

  Lemma F_AUTH_DHKE_FOAUTH_closed : is_closed_expr ∅ ((F_AUTH ∘f DH_KE) ||ᵣ F_OAUTH).
  Proof. is_closed_hint. Qed.
  Lemma F_AUTH_DHKE_closed : is_closed_expr ∅ (F_AUTH ∘f DH_KE).
  Proof. is_closed_hint. Qed.
  Lemma F_AUTH_DHSIM_closed : is_closed_expr ∅ (F_AUTH ∘f DH_SIM).
  Proof. is_closed_hint. Qed.

  Lemma F_AUTH_C_DH_real_closed : is_closed_expr ∅ (F_AUTH ∘f C_DH_real).
  Proof. is_closed_hint. Qed.
  Lemma F_AUTH_C_DH_rand_closed : is_closed_expr ∅ (F_AUTH ∘f C_DH_rand).
  Proof. is_closed_hint. Qed.
  Lemma F_AUTH_C_DDH_real_FOAUTH_closed : is_closed_expr ∅ ((F_AUTH ∘f C_DH_real) ||ᵣ F_OAUTH).
  Proof. is_closed_hint. Qed.
  Lemma F_AUTH_C_DDH_rand_FOAUTH_closed : is_closed_expr ∅ ((F_AUTH ∘f C_DH_rand) ||ᵣ F_OAUTH).
  Proof. is_closed_hint. Qed.
  Lemma F_AUTH_DHSIM_FKE_closed : is_closed_expr ∅ (F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)).
  Proof. is_closed_hint. Qed.
  Lemma F_AUTH_DHSIM_FKE_assoc_closed : is_closed_expr ∅ ((F_AUTH ∘f DH_SIM) ∘f F_KE_lazy_alice).
  Proof. is_closed_hint. Qed.

  Lemma DHSIM_FKE_CHAN1_closed : is_closed_expr ∅ ((F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)) ||ᵣ F_OAUTH).
  Proof. is_closed_hint. Qed.

  Lemma DHSIM_FKE_CHAN2_closed : is_closed_expr ∅ (((F_AUTH ∘f DH_SIM) ∘f F_KE_lazy_alice) ||ᵣ F_OAUTH).
  Proof. is_closed_hint. Qed.

  Lemma DHSIM_FKE_CHAN3_closed : is_closed_expr ∅ ((F_AUTH ∘f DH_SIM) ∘F (F_KE_lazy_alice ||ᵣ F_OAUTH)).
  Proof. is_closed_hint. Qed.

  Lemma F_KE_lazy_alice_F_OAUTH_closed : is_closed_expr ∅ (F_KE_lazy_alice ||ᵣ F_OAUTH).
  Proof. is_closed_hint. Qed.

  Lemma game2_closed : is_closed_expr ∅ game2.
  Proof. is_closed_hint. Qed.
  Lemma sc_ideal_closed : is_closed_expr ∅ sc_ideal.
  Proof. is_closed_hint. Qed.

  Lemma sc_real_closed : is_closed_expr ∅ sc_real.
  Proof. is_closed_hint. Qed.
  Lemma game1_closed : is_closed_expr ∅ game1.
  Proof. is_closed. Admitted.

End ske_comp_closed.
