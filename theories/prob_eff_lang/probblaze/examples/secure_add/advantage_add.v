From clutch.prob_eff_lang.probblaze Require Import advantage.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup adequacy mode.
From clutch.prob_eff_lang.probblaze.typing Require Import types interp fundamental.
From clutch.prob_eff_lang.probblaze.examples.secure_add Require Import add_def add_prf.

Import fingroup.
Import fingroup.fingroup.

(** No well-typed environment -- in particular no aggregator -- can
    distinguish the real two-party addition protocol from the ideal
    functionality with the simulator. *)

Section adv_add.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.

  Import valgroup_notation.

  Definition T_ADD : type :=
    (∀R: (∀R: ((ℕ -{ RVar 0%nat }-> ()) * (ℕ -{ RVar 0%nat }-> ())) -{ RVar 0%nat ∪ᵣ (RVar 1%nat) }-∘ ()) -∘
       (∀R: ((((τG -{ RVar 0%nat }-> ()) * (τG -{ RVar 0%nat }-> ()))
              * ((((() + ()) -{ RVar 0%nat }-> ())) * ((() + ()) -{ RVar 0%nat }-> (() + ()))))
               -{ (RFlip OS (RVar 0%nat)) ∪ᵣ (RVar 1%nat) }-∘ ()))).

  Lemma T_ADD_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ τ_ADD ≤ₜ (interp._ty η μ δ T_ADD ξ).
  Proof using All.
    rewrite /T_ADD /τ_ADD /sem_ty_option /=.
    iApply ty_le_row_forall; iIntros (?).
    iApply ty_le_arr; first iApply row_le_refl.
    - iApply ty_le_refl.
    - iApply ty_le_row_forall; iIntros (?).
      iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
      iApply ty_le_prod; last iApply ty_le_refl.
      iApply ty_le_prod;
        (iApply ty_le_mbang_comp; first iApply mode_le_refl);
        (iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl]);
        iIntros (??) "!#"; iApply τG_subtype.
  Qed.

  Lemma T_ADD_bool_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ (interp._ty η μ δ (T_ADD ⇾ 𝔹) ξ)%T ≤ₜ (τ_ADD → 𝔹)%T.
  Proof using All.
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl|iApply T_ADD_subtype |iApply ty_le_refl].
  Qed.

  Lemma adv_ADD A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (τ_ADD → 𝔹)%T) →
    nonneg (advantage A R_ADD I_ADD #true) = 0%R.
  Proof using All.
    intros HA. eapply (sem_typed_advantage A R_ADD I_ADD (λ HRGS, @τ_ADD Σ HRGS vg)); first apply HA. split.
    - intros Hrgs. by unshelve eapply R_ADD_I_ADD.
    - intros Hrgs. by unshelve eapply I_ADD_R_ADD.
  Qed.

  Theorem adv_ADD_typed A :
    ⊢ᵥ A : (T_ADD ⇾ TBool) →
    nonneg (advantage A R_ADD I_ADD #true) = 0%R.
  Proof using All.
    intros HAtyped. apply adv_ADD.
    intros HRGS.
    apply (@fundamental_val Σ HRGS) in HAtyped.
    iPoseProof HAtyped as "Hadv".
    unfold bin_log_val_related.
    iSpecialize ("Hadv" $! [] [] ∅ []).
    iModIntro. iApply T_ADD_bool_subtype.
    by rewrite /sem_val_typed /=.
  Qed.

End adv_add.
