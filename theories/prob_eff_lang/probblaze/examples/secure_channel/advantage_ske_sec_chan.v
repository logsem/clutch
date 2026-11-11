(* The one-message secure channel over a symmetric encryption scheme, as
   factories ([ske_sec_chan_def]):
     F_OAUTH   the one-shot authenticated channel (leaks the ciphertext)
     CHAN      the protocol: encrypt with the DHKE key, send over F_OAUTH,
               in the (F_KE_lazy_alice ||ᵣ F_OAUTH)-hybrid world
     F_CHAN    the ideal secure channel
     CHAN_SIM  the simulator
   The standalone result, at both modes [m], reduces to the encryption scheme:

     advantage A REAL_SKE (SIM_SKE ∘f IDEAL_SKE)
       ≤ advantage (RED_SKE A) (enc_real ske) (enc_ideal ske)

   for environments [A : fac m τsc → 𝔹], through the hybrids GAME1 and
   GAME2 (the protocol with the encryption replaced by the real, resp. ideal,
   oracle; the four relations are in [ske_sec_chan_prf] and
   [ske_sec_chan_ideal_prf]). *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze.typing Require Import types.
From clutch.prob_eff_lang.probblaze.typing Require interp.
From clutch.prob_eff_lang.probblaze.typing Require Import bridge.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory mode adequacy.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage comp_operators.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems uc_advantage uc_theorem.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_typed.
From clutch.prob_eff_lang.probblaze.examples Require Import fin_val_type ske ske_sec_chan_def ske_sec_chan_common ske_sec_chan_typing.
From clutch.prob_eff_lang.probblaze.examples Require Import ske_sec_chan_prf ske_sec_chan_ideal_prf.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic.
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_common dhke_typing.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def advantage_dhke.
From Stdlib Require Import Reals Psatz.


#[local] Open Scope R_scope.
#[local] Open Scope factory_scope.
#[local] Set Default Proof Using "All".

(* ------------------------------------------------------------------ *)
(* Typing.                                                             *)
(* ------------------------------------------------------------------ *)

Section ske_typing_f.
  Context `{probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.
  Context {msg : @fin_val Σ _ mt ms} {cipher : @fin_val Σ _ ct cs}.
  Context {SKE : @SYM Σ _ vg_fvt mt ct vg_fvts ms cs vg_fv msg cipher ske}.

  #[local] Notation Msg := (@sem_τFT Σ _ mt ms msg).
  #[local] Notation Cph := (@sem_τFT Σ _ ct cs cipher).

  Import valgroup_notation.
  Import typed_hint_modes.
  #[local] Existing Instance multi_ty_group.
  #[local] Existing Instance multi_ty_fvt.

  (* An encryption oracle: a thunk of mode [m] returning an encryption function. *)
  Definition τ_ENC (m : mode) : sem_ty Σ := (𝟙 -{ ⟨⟩ }-[ m ]-> (Msg -{ ⊥ }-> Cph))%T.

  (* The interface of the channel, in the shape the composition theorem
     expects: a channel client, taken any number of times, over the
     authenticated-channel leakage and the key-exchange leakage ([τsc] of
     [ske_sec_chan_common], unfolded). *)
  Definition τ_SKE : sem_ty Σ := (∀ᵣ θ, hdl (cli msg) θ → τ__f θ (oaleak cipher) leakI)%T.

  Lemma τsc_le_τ_SKE : ⊢ τsc (msg) (cipher) ≤ₜ τ_SKE.
  Proof using Type*. iApply ty_le_row_forall. iIntros (θ). iApply ty_le_refl. Qed.

  (* The hybrid world of the channel. *)
  Lemma F_KE_F_OAUTH_typed_f m :
    ⊢ ⊨ᵥ (F_KE_lazy_alice ||ᵣ F_OAUTH) ≤ (F_KE_lazy_alice ||ᵣ F_OAUTH) :
        fac m (∀ᵣ θ, τ__f θ (cchan cipher) gk → τ__f θ (oaleak cipher) leakI).
  Proof using All.
    iApply parallel_comp_f_typed; [iApply (F_KE_lazy_alice_typed (G := G))|iApply (F_OAUTH_typed (G := G) (SKE := SKE))].
  Qed.

  (* The reduction: an oracle of mode [m] gives a factory of mode [m]. *)
  Lemma RED_CHAN_typed_f m :
    ⊢ ⊨ᵥ (RED_CHAN ms) ≤ (RED_CHAN ms) : (τ_ENC m → fac m (∀ᵣ θ, hdl (cli msg) θ → τ__f θ (cchan cipher) gk))%T.
  Proof using All.
    rewrite /RED_CHAN /τ_ENC. iApply (sem_typed_closure _ _ _ BAnon "enc" _ _ MS); first done. simpl.
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_]).
    destruct m.
    - iApplyT (sem_oval_typed_afun 𝟙%T ⟨⟩%R _ BAnon). simpl.
      iApplyT sem_typed_app_nil; last first.
      { iApplyT sem_typed_sub_ty; [iApply ty_le_mbang_elim|typed_var]. }
      iApply sem_typed_val. iApply (RED_CHAN_val_typed (G := G) (SKE := SKE)).
    - iApplyT (sem_oval_typed_ufun 𝟙%T ⟨⟩%R _ _ BAnon BAnon). simpl.
      iApplyT sem_typed_app_nil; last first.
      { iApplyT sem_typed_sub_ty; [iApply ty_le_mbang_elim|typed_var]. }
      iApply sem_typed_val. iApply (RED_CHAN_val_typed (G := G) (SKE := SKE)).
    Unshelve. all: solve_typed_side.
  Qed.

  (* The reduction environment is an environment for the encryption oracles. *)
  Lemma RED_SKE_typed m (A : val) :
    ⊢ sem_val_typed A A (fac m τ_SKE → 𝔹)%T -∗
      sem_val_typed (RED_SKE ms A) (RED_SKE ms A) (τ_ENC m → 𝔹)%T.
  Proof using All.
    iIntros "#HA". rewrite /RED_SKE.
    change ((F_KE_lazy_alice ||ᵣ F_OAUTH) ∘fₚ (RED_CHAN ms "v"))%fac
      with (fill [AppRCtx (fac_app func_comp (F_KE_lazy_alice ||ᵣ F_OAUTH)); AppRCtx (RED_CHAN ms)] "v").
    iApply ctx_adv_typed; first iApply "HA". simpl. rewrite /τ_SKE.
    iApplyT sem_typed_app_nil; last first.
    { iApplyT sem_typed_app_nil; last typed_var.
      iApply sem_typed_val. iApply sem_val_typed_sub; [iApply (ty_le_mbang_elim MS)|iApply RED_CHAN_typed_f]. }
    iApplyT sem_typed_app_nil; last (iApply sem_typed_val; iApply F_KE_F_OAUTH_typed_f).
    iApply sem_typed_val.
    iApply (func_comp_app_typed_gen m (λ θ, hdl (cli msg) θ) (λ θ, τ__f θ (cchan cipher) gk) (λ θ, τ__f θ (oaleak cipher) leakI)).
    intros θ. apply eta_ty_τf.
    Unshelve. all: solve_typed_side.
  Qed.

End ske_typing_f.

#[global] Arguments τ_ENC {Σ H mt ct ms cs} msg cipher m.
#[global] Arguments τ_SKE {Σ H mt ct ms cs} msg cipher.

(* ------------------------------------------------------------------ *)
(* The taped and the untaped real oracle, as thunks of either mode.    *)
(* ------------------------------------------------------------------ *)

Section enc_oracles.
  Context `{ske : SYM}.

  (* The equivalence of [ske] is between persistent thunks. *)
  Lemma enc_real_tape_enc_real_MS :
    ⊢ sem_typed [] (enc_real_tape ske) (enc_real ske) ⊥ (𝟙 -{ ⟨⟩ }-[ MS ]-> (msg.(sem_τFT) → cipher.(sem_τFT)))%T [].
  Proof using Type*.
    apply (EQ_sem_typed _ _ _ _ enc_real_tape_EQ Fwd).
  Qed.

  Lemma enc_real_enc_real_tape_MS :
    ⊢ sem_typed [] (enc_real ske) (enc_real_tape ske) ⊥ (𝟙 -{ ⟨⟩ }-[ MS ]-> (msg.(sem_τFT) → cipher.(sem_τFT)))%T [].
  Proof using Type*.
    apply (EQ_sem_typed _ _ _ _ enc_real_tape_EQ Bwd).
  Qed.

  Lemma enc_real_tape_enc_real_f m :
    ⊢ sem_typed [] (enc_real_tape ske) (enc_real ske) ⊥ (𝟙 -{ ⟨⟩ }-[ m ]-> (msg.(sem_τFT) → cipher.(sem_τFT)))%T [].
  Proof using Type*.
    iApply sem_typed_sub_ty; last iApply enc_real_tape_enc_real_MS.
    destruct m; [iApply (ty_le_mbang_elim MS)|iApply ty_le_refl].
  Qed.

  Lemma enc_real_enc_real_tape_f m :
    ⊢ sem_typed [] (enc_real ske) (enc_real_tape ske) ⊥ (𝟙 -{ ⟨⟩ }-[ m ]-> (msg.(sem_τFT) → cipher.(sem_τFT)))%T [].
  Proof using Type*.
    iApply sem_typed_sub_ty; last iApply enc_real_enc_real_tape_MS.
    destruct m; [iApply (ty_le_mbang_elim MS)|iApply ty_le_refl].
  Qed.

End enc_oracles.

(* ------------------------------------------------------------------ *)
(* Pure steps of the reduction.                                        *)
(* ------------------------------------------------------------------ *)

Section pure.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.

  Lemma RED_CHAN_pure (d : val) : rtc pure_step (RED_CHAN ms d) (λ: <>, RED_CHAN_sess ms d)%V.
  Proof.
    rewrite /RED_CHAN.
    eapply rtc_l.
    { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
    simpl.
    eapply rtc_l.
    { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
    done.
  Qed.

  (* The reduction context applied to an oracle evaluates to a composite. *)
  Lemma RED_pure (d : val) :
    rtc pure_step (fill [AppRCtx (fac_app func_comp (F_KE_lazy_alice ||ᵣ F_OAUTH)); AppRCtx (RED_CHAN ms)] d)
      ((F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f (λ: <>, RED_CHAN_sess ms d)%V)%fac.
  Proof.
    etrans.
    { apply (rtc_congruence (R := pure_step) (fill [AppRCtx (fac_app func_comp (F_KE_lazy_alice ||ᵣ F_OAUTH))]) pure_step
               (RED_CHAN ms d) (λ: <>, RED_CHAN_sess ms d)%V).
      - intros ???. by apply (@language.pure_step_ctx _ _
          (fill_ctx_no_handler [AppRCtx (fac_app func_comp (F_KE_lazy_alice ||ᵣ F_OAUTH))] eq_refl)).
      - apply RED_CHAN_pure. }
    apply fac_app_pure.
  Qed.

End pure.

(* ------------------------------------------------------------------ *)
(* The advantage bound: reduction to the encryption scheme.            *)
(* ------------------------------------------------------------------ *)

Section ske_advantage.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context {vgg : @val_group_generator vg}.
  Context `{probblazeRGpreS Σ}.
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.
  Context {msg : ∀ `(!probblazeRGS Σ), @fin_val Σ _ mt ms} {cipher : ∀ `(!probblazeRGS Σ), @fin_val Σ _ ct cs}.
  Context {SKE : ∀ `{H : !probblazeRGS Σ}, @SYM Σ _ vg_fvt mt ct vg_fvts ms cs (vg_fv (Σ := Σ) (H := H)) (msg H) (cipher H) ske}.

  Import valgroup_notation.

  Theorem adv_SKE (m : mode) (A : val) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m (τ_SKE (msg _) (cipher _)) → 𝔹)%T) →
    advantage A REAL_SKE (SIM_SKE ∘f (IDEAL_SKE ms)) #true <=
      advantage (RED_SKE ms A) (enc_real ske) (enc_ideal ske) #true.
  Proof using All.
    intros HA. rewrite /RED_SKE.
    (*   REAL_SKE  ≃  GAME1                                                  *)
    eapply (advantage_triangle _ _ GAME1 _ _ 0); first last.
    { rewrite Rplus_0_l. reflexivity. }
    2: { apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, fac m (τ_SKE (msg _) (cipher _)))); [exact HA| |]; intros HRGS.
         - iApply sem_typed_sub_ty; [iApply ty_le_trans; [iApply fac_MS_le|iApply fac_le; iApply (τsc_le_τ_SKE (msg := msg HRGS) (cipher := cipher HRGS))]|iApply (REAL_SKE_GAME1_MS (G := G _ _) (SKE := SKE _))].
         - iApply sem_typed_sub_ty; [iApply ty_le_trans; [iApply fac_MS_le|iApply fac_le; iApply (τsc_le_τ_SKE (msg := msg HRGS) (cipher := cipher HRGS))]|iApply (GAME1_REAL_SKE_MS (G := G _ _) (SKE := SKE _))]. }
    (*   GAME2  ≃  SIM_SKE ∘f IDEAL_SKE                                      *)
    eapply (advantage_triangle _ _ GAME2 _ _ _ 0); first last.
    { rewrite Rplus_0_r. reflexivity. }
    1: { apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, fac m (τ_SKE (msg _) (cipher _)))); [exact HA| |]; intros HRGS.
         - iApply sem_typed_sub_ty; [iApply ty_le_trans; [iApply fac_MS_le|iApply fac_le; iApply (τsc_le_τ_SKE (msg := msg HRGS) (cipher := cipher HRGS))]|iApply (GAME2_IDEAL_SKE_MS (G := G _ _) (SKE := SKE _))].
         - iApply sem_typed_sub_ty; [iApply ty_le_trans; [iApply fac_MS_le|iApply fac_le; iApply (τsc_le_τ_SKE (msg := msg HRGS) (cipher := cipher HRGS))]|iApply (IDEAL_SKE_GAME2_MS (G := G _ _) (SKE := SKE _))]. }
    (*   GAME1  vs  GAME2: the encryption step, through the reduction
         [λ enc, A ((F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f RED_CHAN ms enc)]            *)
    etrans; first apply (advantage_pure_r_rev _ [] _ (fill [AppRCtx (fac_app func_comp (F_KE_lazy_alice ||ᵣ F_OAUTH)); AppRCtx (RED_CHAN ms)] (enc_ideal ske)) _);
      [done|apply RED_pure|].
    etrans; first apply (advantage_pure_l_rev _ [] (fill [AppRCtx (fac_app func_comp (F_KE_lazy_alice ||ᵣ F_OAUTH)); AppRCtx (RED_CHAN ms)] (enc_real_tape ske)) _ _);
      [done|apply RED_pure|].
    etrans; first apply (advantage_reduction_ctx A [AppRCtx (fac_app func_comp (F_KE_lazy_alice ||ᵣ F_OAUTH)); AppRCtx (RED_CHAN ms)]);
      [done|intros vs w Hw; simpl; by rewrite Hw|].
    (*   the taped real oracle  ≃  the real oracle                            *)
    eapply (advantage_triangle _ _ (enc_real ske) _ _ 0); first last.
    { rewrite Rplus_0_l. reflexivity. }
    2: { apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, τ_ENC (msg H) (cipher H) m)).
         - intros HRGS. iApply (RED_SKE_typed (G := G _ _) (SKE := SKE _)). iApply HA.
         - intros HRGS. iApply (enc_real_tape_enc_real_f (ske := SKE _)).
         - intros HRGS. iApply (enc_real_enc_real_tape_f (ske := SKE _)). }
    reflexivity.
  Qed.

  (** Syntactically typed environments *)

  (* [τ_SKE], syntactically. *)
  Definition T_SKE : type :=
    (∀R:
      (∀R: ((ℕ -{ RVar 0%nat }-> ()) * (() -{ RVar 0%nat }-> (() + ms.(τFT))))
             -{ RVar 0%nat ∪ᵣ RVar 1%nat }-∘ ()) ⇾
      (∀R: ∀R: ((((cs.(τFT) * (() + ())) -{ RVar 1%nat }-> ()) * ((() + ()) -{ RVar 1%nat }-> (() + ())))
                 * (((() + ()) -{ RVar 0%nat }-> ()) * ((() + ()) -{ RVar 0%nat }-> (() + ()))))
             -{ (RFlip OS (RVar 1%nat)) ∪ᵣ ((RFlip OS (RVar 0%nat)) ∪ᵣ RVar 2%nat) }-∘ ()))%ty.

  Lemma T_SKE_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ τ_SKE (msg _) (cipher _) ≤ₜ interp.interp._ty η μ δ T_SKE ξ.
  Proof using msg cipher.
    sem_ty_le_struct using
      (first [ iApply (τFT_subtype (fin_val := msg _))
             | iApply (τFT_subtype (fin_val := cipher _)) ]).
  Qed.

  Corollary adv_SKE_typed A :
    ⊢ᵥ A : ((() -∘ T_SKE) ⇾ TBool)%ty →
    advantage A REAL_SKE (SIM_SKE ∘f (IDEAL_SKE ms)) #true <=
      advantage (RED_SKE ms A) (enc_real ske) (enc_ideal ske) #true.
  Proof using All.
    intros HA. apply (adv_SKE OS), (typed_env_fac A T_SKE (λ _, τ_SKE (msg _) (cipher _))); last done.
    intros. apply T_SKE_subtype.
  Qed.

End ske_advantage.
