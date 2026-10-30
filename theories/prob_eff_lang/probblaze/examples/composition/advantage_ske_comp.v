From clutch.prob_eff_lang.probblaze Require Import advantage.
From clutch.prob_eff_lang.probblaze.typing Require Import types fundamental interp.
From clutch.prob_eff_lang.probblaze Require Import p_composition sem_row syntax semantics proofmode valgroup adequacy mode.
From clutch.prob_eff_lang.probblaze.examples Require Import ske_composition ske_composition_defs dhke_common ske_typing ske_composition_typing.

Import fingroup.
Import fingroup.fingroup.

Section adv_comp.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.  
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context `{Hpre :probblazeRGpreS Σ}.
  (* message and cipher spaces: abstract *)
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  (* key space is valgroup *)
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.
  (* the semantic side of the scheme: the key space is [vg_fv], the message and
     cipher spaces are abstract.  [enc_sem]/[dec_sem] take and return VALUES of
     those spaces, so nothing below ever decodes a key or a message. *)
  Context {msg : ∀ `(!probblazeRGS Σ), @fin_val Σ _ mt ms} {cipher : ∀ `(!probblazeRGS Σ), @fin_val Σ _ ct cs}.
  Context {SKE : ∀ `{H : !probblazeRGS Σ}, @SYM Σ _ vg_fvt mt ct vg_fvts ms cs (vg_fv (Σ := Σ) (H := H)) (msg H) (cipher H) ske}.
  
  Let τ `{H : !probblazeRGS Σ} := (τ (ms := ms) (cs := cs) (msg := msg H) (cipher := cipher H) (mt := mt) (ct := ct)).

  Theorem adv_composition A :
     (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ → 𝔹)%T) →
     advantage A REAL_CHAN_DHKE SIMSIMFCHAN #true
    <=
      advantage A REAL_CHAN_DH_REAL REAL_CHAN_DH_RAND #true
      + advantage A DHSIM_FKE_RED_ENC_REAL DHSIM_FKE_RED_ENC_IDEAL #true.
  Proof using All.
    intros Hadv. unfold τ.
    eapply (advantage_triangle _ _ _ _ _ 0); last (rewrite Rplus_0_l; apply Rle_refl).
    - right. eapply sem_typed_advantage; first apply Hadv.
      split; unfold τ.
      + intros H. eapply F_OAUTH_DHKE_C_REAL; try done.
      + intros H. eapply C_REAL_DHKE_F_OAUTH; try done.
    - eapply advantage_triangle; [apply Rle_refl| |apply Rle_refl].
      eapply (advantage_triangle _ _ _ _ _ 0); last (rewrite Rplus_0_l; apply Rle_refl).
      { right. eapply sem_typed_advantage; first apply Hadv. unfold τ.
        split. 
        - intros H. by eapply REAL_CHAN_DH_RAND_DHSIM_FKE_CHAN1.
        - intros H. by eapply DHSIM_FKE_CHAN1_REAL_CHAN_DH_RAND. }
      eapply (advantage_triangle _ _ _ _ _ 0); last (rewrite Rplus_0_l; apply Rle_refl).
      { right. eapply sem_typed_advantage; first apply Hadv. unfold τ.
        split. 
        - intros H. by eapply DHSIM_FKE_CHAN1_DHSIM_FKE_CHAN2.
        - intros H. by eapply DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN1. }
      eapply (advantage_triangle _ _ _ _ _ 0); last (rewrite Rplus_0_l; apply Rle_refl).
      { right. eapply sem_typed_advantage; first apply Hadv. unfold τ.
        split. 
        - intros H. by eapply DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN3.
        - intros H. by eapply DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN2. }
      eapply (advantage_triangle _ _ _ _ _ 0); last (rewrite Rplus_0_l; apply Rle_refl).
      { right. eapply sem_typed_advantage; first apply Hadv. unfold τ.
        split. 
        - intros H. by eapply DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4.
        - intros H. by eapply DHSIM_FKE_CHAN4_DHSIM_FKE_CHAN3. }
      eapply (advantage_triangle _ _ _ _ _ 0); last (rewrite Rplus_0_l; apply Rle_refl).
      { right. eapply sem_typed_advantage; first apply Hadv. unfold τ.
        split. 
        - intros H. by eapply DHSIM_FKE_CHAN4_GAME1.
        - intros H. by eapply GAME1_DHSIM_FKE_CHAN4. }
      eapply (advantage_triangle _ _ _ _ _ 0); last (rewrite Rplus_0_l; apply Rle_refl).
      { right. eapply sem_typed_advantage; first apply Hadv. unfold τ.
        split. 
        - intros H. by eapply GAME1_RED.
        - intros H. by eapply RED_GAME1. }
      eapply (advantage_triangle _ _ _ _ _ _ 0); [apply Rle_refl| |(rewrite Rplus_0_r; apply Rle_refl)].
      eapply (advantage_triangle _ _ _ _ _ 0 0); last lra.
      { right. eapply sem_typed_advantage; first apply Hadv. unfold τ.
        split. 
        - intros H. by eapply RED_GAME2.
        - intros H. by eapply GAME2_RED. }
      right. eapply sem_typed_advantage; first apply Hadv. unfold τ.
      split.
      + intros H. by eapply DHSIM_FKE_GAME2_IDEAL.
      + intros H. by eapply IDEAL_DHSIM_FKE_GAME2.
  Qed. 


  Lemma REAL_DHKE_DH_RED_RAND_adv (A : val) (b : bool) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (τ → 𝔹)%T) →
    nonneg $ advantage A REAL_CHAN_DH_RED_RAND REAL_CHAN_DH_RAND #b = 0.
  Proof using All.
    intros Aty.
    eapply sem_typed_advantage.
    1: apply Aty.
    split ; intros.
    - unfold τ. by eapply REAL_DHKE_DH_RED_RAND'.
    - unfold τ. by eapply REAL_DHKE_DH_RED_RAND.
  Qed.
  
  Lemma REAL_DHKE_DH_RED_REAL_adv (A : val) (b : bool) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (τ → 𝔹)%T) →
    nonneg $ advantage A REAL_CHAN_DH_RED_REAL REAL_CHAN_DH_REAL #b = 0.
  Proof using All.
    intros Aty.
    eapply sem_typed_advantage.
    1: apply Aty.
    split ; intros.
    - unfold τ. by eapply REAL_DHKE_DH_RED_REAL'.
    - unfold τ. by eapply REAL_DHKE_DH_RED_REAL.
  Qed.

  Lemma enc_real_tape_enc_real_adv (A : expr) (b : bool) : 
    (∀ H : probblazeRGS Σ, ⊢ sem_typed [] A A ⊥ ((𝟙 ⊸ (msg H).(sem_τFT) → (cipher H).(sem_τFT)) → 𝔹)%T []) → 
    nonneg $ advantage A (enc_real_tape ske) (enc_real ske) #b = 0.
  Proof using All.
    intros Aty.
    eapply sem_typed_advantage_expr; last first.
    - split; intros H.
      + apply (enc_real_tape_enc_real (ske := SKE H)).
      + apply (enc_real_enc_real_tape (ske := SKE H)).
    - apply Aty.
  Qed. 
  
  Lemma enc_real_tape_enc_ideal (A : expr) (b : bool) : 
    (∀ H : probblazeRGS Σ, ⊢ sem_typed [] A A ⊥ ((𝟙 ⊸ (msg H).(sem_τFT) → (cipher H).(sem_τFT)) → 𝔹)%T []) → 
    nonneg $ advantage A (enc_real_tape ske) (enc_ideal ske) #b <= nonneg $ advantage A (enc_real ske) (enc_ideal ske) #b.
  Proof using All. 
    intros Aty.
    eapply advantage_triangle. 
    - right; eapply enc_real_tape_enc_real_adv; done.
    - apply Rle_refl.
    - lra.
  Qed.

  Theorem adv_composition_real A :
    (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ → 𝔹)%T) →
    advantage A REAL_CHAN_DHKE SIMSIMFCHAN #true <=
      advantage (λ: "v", A ((REAL_CHAN_DH_RED "v"))) DH_real DH_rand #true
      + advantage (λ: "v", A (((DHSIM_FKE_RED (mt := mt) (ms := ms)) "v"))) (enc_real ske) (enc_ideal ske) #true.
  Proof using All.
    intros Aty.
    etrans. 
    - apply adv_composition; eauto.
    - apply Rplus_le_compat.
      + eapply (advantage_triangle _ _ _ _ _ 0 _); last try lra.
        3: rewrite Rplus_0_l ; reflexivity.
        2: eapply (advantage_triangle _ _ _ _ _ _ 0); last try lra.
        4: rewrite Rplus_0_r ; reflexivity.
        { right. rewrite advantage_sym.
          apply REAL_DHKE_DH_RED_REAL_adv. done. }
        2: { right. apply REAL_DHKE_DH_RED_RAND_adv. done. }
        apply (advantage_reduction_expr_expr _ A REAL_CHAN_DH_RED DH_real DH_rand true).
        1 : { intros. apply (subst_is_closed ∅); first is_closed. done. }
        intros. eexists _,_. split ; [|split].
        1: apply Aty.
        2:{ split; iApply compatibility.sem_typed_val.
            - by iApply DH_real_self.
            - by iApply DH_rand_self. }
        unfold τ. by apply ske_composition_typing.REAL_CHAN_DH_RED_typed.
      + etrans; last first.
        * eapply enc_real_tape_enc_ideal. 
          intros H.
          iApply sem_typed_adv_red_expr; first iApply Aty.
          iApply (DHSIM_FKE_RED_typed (ske := ske)).
        * apply advantage_reduction_expr_expr.
          1 : { intros. apply (subst_is_closed ∅); first is_closed. done. }
          intros. eexists _,_. split ; [apply Aty|split].
          -- iApply (DHSIM_FKE_RED_typed (ske := ske)).
          -- split; iApply compatibility.sem_typed_val.
             ++ iApply (ske_typing.enc_real_tape_val_typed (SKE := SKE H)).
             ++ iApply (ske_typing.enc_ideal_val_typed (SKE := SKE H)).
  Qed.

  Definition T : type :=
    (∀R: 
   (∀R:  ((ℕ -{ RVar 0%nat }-> ()) * (() -{ RVar 0%nat }-> () + (ms.(τFT)))) -{ RUnion (RVar 0%nat) (RVar 1%nat) }-∘ ())
   -∘ ∀R:
     (∀R:
      ((((((cs.(τFT)) * (() + ())) -{ RVar 1%nat }-> ()) * ((() + ()) -{ RVar 1%nat }-> () + ())))
      * ((((τG * (() + ())) -{ RVar 0%nat }-> ()) * ((() + ()) -{ (RVar 0%nat) }-> () + ℕ)))) -{ RUnion (RFlip OS (RVar 1%nat)) (RUnion (RFlip OS (RVar 0%nat)) (RVar 2%nat)) }-∘ ())).
  
  Lemma T_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ τ ≤ₜ interp._ty η μ δ T ξ.
  Proof using All.
    rewrite /T /τ /sem_ty_option /=. 
    iApply ty_le_row_forall. iIntros (?).
    iApply ty_le_arr; first iApply row_le_refl.
    - iApply ty_le_row_forall; iIntros (?).
      iApply ty_le_arr; [iApply row_le_refl | | iApply ty_le_refl].
      iApply ty_le_prod; first iApply ty_le_refl.
      iApply ty_le_mbang_comp; first iApply mode_le_refl.
      iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|].
      iApply ty_le_sum; first iApply ty_le_refl.
      iIntros (??) "!#". iApply (msg probblazeRGS0).(τFT_subtype).
    - iApply ty_le_row_forall; iIntros (?).
      iApply ty_le_row_forall; iIntros (?). 
      iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
      iApply ty_le_prod.
      + iApply ty_le_prod; last iApply ty_le_refl.
        iApply ty_le_mbang_comp; first iApply mode_le_refl.
        iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
        iApply ty_le_prod; last iApply ty_le_refl.
        iIntros (??) "!#". iApply (cipher probblazeRGS0).(τFT_subtype).
      + iApply ty_le_prod; last iApply ty_le_refl.
        iApply ty_le_mbang_comp; first iApply mode_le_refl.
        iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
        iApply ty_le_prod; last iApply ty_le_refl.
        iIntros (??) "!#". iApply τG_subtype.
  Qed. 
  
  Lemma T_bool_subtype  `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ (interp._ty η μ δ (T ⇾ 𝔹) ξ)%T ≤ₜ (τ → 𝔹)%T.
  Proof using All. 
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl|iApply T_subtype |iApply ty_le_refl].
  Qed. 
  
  Lemma adv_composition_typed A :
   ⊢ᵥ A : (T ⇾ TBool) →
    advantage A REAL_CHAN_DHKE SIMSIMFCHAN #true <=
      advantage (λ: "v", A ((REAL_CHAN_DH_RED "v"))) DH_real DH_rand #true
      + advantage (λ: "v", A ((DHSIM_FKE_RED (mt := mt) (ms := ms) "v"))) (enc_real ske) (enc_ideal ske) #true.
  Proof using All.
    intros HAtyped. apply adv_composition_real. 
    intros HRGS.
    apply (@fundamental_val Σ HRGS) in HAtyped.
    iPoseProof HAtyped as "Hadv".
    unfold bin_log_val_related.
    iSpecialize ("Hadv" $! [] [] ∅ []). 
    iModIntro. iApply T_bool_subtype. 
    by rewrite /sem_val_typed /=. 
  Qed.

End adv_comp.
