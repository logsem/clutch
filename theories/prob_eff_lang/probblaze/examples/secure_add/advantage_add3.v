From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze Require Import advantage.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup adequacy mode.
From clutch.prob_eff_lang.probblaze.typing Require Import types interp fundamental.
From clutch.prob_eff_lang.probblaze.examples.secure_add Require Import add3_def add3_prf add3_prf_rev.

Import fingroup.
Import fingroup.fingroup.

(** No well-typed environment can distinguish the real three-party addition
    protocol, with party [c] passively corrupted, from the ideal
    functionality with the simulator. *)

Section adv_add3.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (dfrac_agreeR valO)}.
  Context (c : nat) (Hc : (c < 3)%nat).

  Import valgroup_notation.

  (* [τ_ADD3], syntactically.  Under [∀T: ∀R:], [TVar 0] is the client's
     result type and [RVar 0] the environment's row [θ_L]; under the inner
     [∀R:], [RVar 0] is the client's (resp. the environment's operations')
     row. *)
  Definition T_ADD3 : type :=
    ![MS] (∀T: ∀R:
      (∀R: (((ℕ -{ RVar 0%nat }-> (() + τG)) * (ℕ -{ RVar 0%nat }-> (() + τG)))
            * (ℕ -{ RVar 0%nat }-> (() + τG)))
             -{ RVar 0%nat ∪ᵣ RVar 1%nat }-∘ TVar 0%nat) -∘
      (∀R: (((τG + ((ℤ * ℤ) * τG)) -{ RVar 0%nat }-> ())
            * ((((ℤ * ℤ) * ℤ) -{ RVar 0%nat }-> ()) * (((ℤ * ℤ) * ℤ) -{ RVar 0%nat }-> ())))
             -{ (RFlip OS (RVar 0%nat)) ∪ᵣ RVar 1%nat }-∘ TVar 0%nat))%ty.

  Lemma T_ADD3_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ τ_ADD3 ≤ₜ (interp._ty η μ δ T_ADD3 ξ).
  Proof using All.
    rewrite /T_ADD3 /τ_ADD3 /τ_port /τ_envops /τ_view /τ_hdr /sem_ty_option /=.
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_type_forall; iIntros (α).
    iApply ty_le_row_forall; iIntros (θL).
    iApply ty_le_arr; first iApply row_le_refl.
    - (* the client: its ports return group elements *)
      iApply ty_le_row_forall; iIntros (θh).
      iApply ty_le_arr; [iApply row_le_refl | | iApply ty_le_refl].
      iApply ty_le_prod; [iApply ty_le_prod |];
        (iApply ty_le_mbang_comp; first iApply mode_le_refl);
        (iApply ty_le_arr; [iApply row_le_refl | iApply ty_le_refl |]);
        (iApply ty_le_sum; first iApply ty_le_refl);
        iIntros (??) "!#"; iApply τG_subtype.
    - (* the environment's operations: the leak takes group elements *)
      iApply ty_le_row_forall; iIntros (θ1).
      iApply ty_le_arr; [iApply row_le_refl | | iApply ty_le_refl].
      iApply ty_le_prod; [| iApply ty_le_prod; iApply ty_le_refl].
      iApply ty_le_mbang_comp; first iApply mode_le_refl.
      iApply ty_le_arr; [iApply row_le_refl | | iApply ty_le_refl].
      iApply ty_le_sum; [iIntros (??) "!#"; iApply τG_subtype |].
      iApply ty_le_prod; [iApply ty_le_refl | iIntros (??) "!#"; iApply τG_subtype].
  Qed.

  Lemma T_ADD3_bool_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ (interp._ty η μ δ (T_ADD3 ⇾ 𝔹) ξ)%T ≤ₜ (τ_ADD3 → 𝔹)%T.
  Proof using All.
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl | iApply T_ADD3_subtype | iApply ty_le_refl].
  Qed.

  Lemma adv_ADD3 A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (τ_ADD3 → 𝔹)%T) →
    nonneg (advantage A (R_ADD3 c) (I_ADD3 c) #true) = 0%R.
  Proof using All.
    intros HA.
    eapply (sem_typed_advantage A (R_ADD3 c) (I_ADD3 c) (λ HRGS, @τ_ADD3 Σ HRGS vg));
      first apply HA.
    split.
    - intros Hrgs. by unshelve eapply (R_ADD3_I_ADD3 c Hc).
    - intros Hrgs. by unshelve eapply (I_ADD3_R_ADD3 c Hc).
  Qed.

  Theorem adv_ADD3_typed A :
    ⊢ᵥ A : (T_ADD3 ⇾ TBool) →
    nonneg (advantage A (R_ADD3 c) (I_ADD3 c) #true) = 0%R.
  Proof using All.
    intros HAtyped. apply adv_ADD3.
    intros HRGS.
    apply (@fundamental_val Σ HRGS) in HAtyped.
    iPoseProof HAtyped as "Hadv".
    unfold bin_log_val_related.
    iSpecialize ("Hadv" $! [] [] ∅ []).
    iModIntro. iApply T_ADD3_bool_subtype.
    by rewrite /sem_val_typed /=.
  Qed.

End adv_add3.
