From clutch.prob_eff_lang.probblaze Require Import advantage.
From iris.algebra Require Import excl.
From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze.typing Require Import types fundamental interp.
From clutch.prob_eff_lang.probblaze Require Import p_composition sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup adequacy mode.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import new_composition xor def_dhke sec_channel_def new_composition_defs.


Import fingroup.
Import fingroup.fingroup.

Section adv_comp.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.  
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context `{Hpre :probblazeRGpreS Σ}.
  Let Key := S (S n'').
  Let Support := S (S n'').
  Context {xor_struct : XOR (Key := Key) (Support := Support)}.
  Context `{X : ∀ `{!probblazeRGS Σ}, XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}.

  Variable group_xor_sem : vgG -> vgG -> vgG.
  (* actual BITWISE xor has both left and right inverse, so this assumption is a valid spec.*)
  Hypothesis Bij_xor_sem : ∀ g1 g2 : vgG, group_xor_sem (group_xor_sem g1 g2) g2 = g1.
  Hypothesis Bij_xor_sem_l : ∀ g1 g2 : vgG, group_xor_sem g1 (group_xor_sem g1 g2) = g2.
  Hypothesis vg_int_xor_sem : ∀ `{!probblazeRGS Σ}, ∀ g1 g2 : vgG, vg_of_int_sem (xor_sem (int_of_vg_sem g1) (int_of_vg_sem g2)) = Some (group_xor_sem g1 g2 ).
  Variable log__g : vgG -> fin (S (S n'')).
  Hypothesis Val_log : ∀ x : vgG, (g ^+(log__g x))%g = x.
  Hypothesis Bij_log : forall m : vgG, @Bij (fin (S (S n''))) (fin (S (S n''))) (λ n, log__g (group_xor_sem m (g ^+n))).
  Hypothesis Bdd_int_vg : ∀ `{!probblazeRGS Σ}, ∀ g : vgG, (int_of_vg_sem g < S (S (S n'')))%nat.


  Theorem adv_composition A :
     (∀ `{!probblazeRGS Σ},⊢ sem_val_typed A A (τ → 𝔹)%T) →
     advantage A REAL_CHAN_DHKE SIMSIMFCHAN #true
    <=
      advantage A REAL_CHAN_DH_REAL REAL_CHAN_DH_RAND #true.
  Proof using All.
    intros Hadv.
    eapply (advantage_triangle _ _ _ _ _ 0); last (rewrite Rplus_0_l; apply Rle_refl).
    - right. eapply sem_val_typed_advantage; first apply Hadv.
      split.
      + intros H. eapply F_OAUTH_DHKE_C_REAL; try done.
      + intros H. eapply C_REAL_DHKE_F_OAUTH; try done.
    - eapply (advantage_triangle _ _ _ _ _ _ 0); [apply Rle_refl| | (rewrite Rplus_0_r; apply Rle_refl)].
      eapply (advantage_triangle _ _ _ _ _ 0 0); last lra.
      { right. eapply sem_val_typed_advantage; first apply Hadv.
        split. 
        - intros H. by eapply REAL_CHAN_DH_RAND_DHSIM_FKE_CHAN1.
        - intros H. by eapply DHSIM_FKE_CHAN1_REAL_CHAN_DH_RAND. }
      eapply (advantage_triangle _ _ _ _ _ 0 0); last lra.
      { right. eapply sem_val_typed_advantage; first apply Hadv.
        split. 
        - intros H. by eapply DHSIM_FKE_CHAN1_DHSIM_FKE_CHAN2.
        - intros H. by eapply DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN1. }
      eapply (advantage_triangle _ _ _ _ _ 0 0); last lra.
      { right. eapply sem_val_typed_advantage; first apply Hadv.
        split. 
        - intros H. by eapply DHSIM_FKE_CHAN2_DHSIM_FKE_CHAN3.
        - intros H. by eapply DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN2. }
      eapply (advantage_triangle _ _ _ _ _ 0 0); last lra.
      { right. eapply sem_val_typed_advantage; first apply Hadv.
        split. 
        - intros H. by eapply DHSIM_FKE_CHAN3_DHSIM_FKE_CHAN4.
        - intros H. by eapply DHSIM_FKE_CHAN4_DHSIM_FKE_CHAN3. }
      right. eapply sem_val_typed_advantage; first apply Hadv.
      split.
      + intros H. by eapply DHSIM_FKE_CHAN4_SIMFCHAN.
      + intros H. by eapply SIMFCHAN_DHSIM_FKE_CHAN4.
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
  Proof using All.
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
      by apply new_composition_typing.REAL_CHAN_DH_RED_sem_typed.
  Qed.

  Definition T : type :=
    (∀R: 
   (∀R:  ((ℕ -{ RVar 0%nat }-> ()) * (() -{ RVar 0%nat }-> () + τG)) -{ RUnion (RVar 0%nat) (RVar 1%nat) }-∘ ())
   -∘ ∀R:
     (∀R:
      (((τG * (() + ())) -{ RVar 1%nat }-> ()) * ((() + ()) -{ RVar 1%nat }-> () + ()))
      -∘ (((τG * (() + ())) -{ RVar 0%nat }-> ()) * ((() + ()) -{ (RVar 0%nat) }-> () + ℕ)) -{ RUnion (RVar 1%nat) (RUnion (RVar 0%nat) (RVar 2%nat)) }-∘ ())).

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
      iIntros (??) "!#". iApply τG_subtype.
    - iApply ty_le_row_forall; iIntros (?).
      iApply ty_le_row_forall; iIntros (?).
      iApply ty_le_arr; [iApply row_le_refl| |].
      + iApply ty_le_prod; last iApply ty_le_refl.
        iApply ty_le_mbang_comp; first iApply mode_le_refl.
        iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
        iApply ty_le_prod; last iApply ty_le_refl.
        iIntros (??) "!#". iApply τG_subtype.
      + iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
        iApply ty_le_prod; last iApply ty_le_refl.
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
      advantage (λ: "v", A ((REAL_CHAN_DH_RED "v")))%V DH_real DH_rand #true.
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
