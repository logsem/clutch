From iris.algebra.lib Require Import dfrac_agree.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup adequacy mode compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems uc_advantage.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_typed.
From clutch.prob_eff_lang.probblaze.typing Require Import types interp fundamental.
From clutch.prob_eff_lang.probblaze.typing Require Import bridge.
From clutch.prob_eff_lang.probblaze.examples.secure_add3 Require Import add3_def add3_prf.

Import fingroup.
Import fingroup.fingroup.

(** No well-typed environment can distinguish the real three-party addition
    protocol, with party [c] passively corrupted, from the ideal
    functionality with the simulator. *)

#[local] Open Scope R_scope.
#[local] Open Scope factory_scope.

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
    (∀T: ∀R:
      (∀R: (((ℕ -{ RVar 0%nat }-> (() + τG)) * (ℕ -{ RVar 0%nat }-> (() + τG)))
            * (ℕ -{ RVar 0%nat }-> (() + τG)))
             -{ RVar 0%nat ∪ᵣ RVar 1%nat }-∘ TVar 0%nat) ⇾
      (∀R: (((τG + ((ℤ * ℤ) * τG)) -{ RVar 0%nat }-> ())
            * ((((ℤ * ℤ) * ℤ) -{ RVar 0%nat }-> ()) * (((ℤ * ℤ) * ℤ) -{ RVar 0%nat }-> ())))
             -{ (RFlip OS (RVar 0%nat)) ∪ᵣ RVar 1%nat }-∘ TVar 0%nat))%ty.

  Lemma T_ADD3_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ τ_ADD3 ≤ₜ (interp._ty η μ δ T_ADD3 ξ).
  Proof using All.
    sem_ty_le_struct using (iApply τG_subtype).
  Qed.

  Theorem adv_ADD3 (m : mode) (A : val) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m τ_ADD3 → 𝔹)%T) →
    advantage A (REAL_ADD3 c) ((SIM_ADD3 c) ∘f (IDEAL_ADD3 c)) #true <= 0.
  Proof using All.
    intros HA.
    apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, fac m τ_ADD3)); [exact HA| |]; intros HRGS;
      (iApply sem_typed_sub_ty; first iApply fac_MS_le);
      [iApply (REAL_ADD3_IDEAL_MS c Hc)|iApply (IDEAL_REAL_ADD3_MS c Hc)].
  Qed.

  Corollary adv_ADD3_typed A :
    ⊢ᵥ A : ((() -∘ T_ADD3) ⇾ TBool) →
    advantage A (REAL_ADD3 c) ((SIM_ADD3 c) ∘f (IDEAL_ADD3 c)) #true <= 0.
  Proof using All.
    intros HA. apply (adv_ADD3 OS), (typed_env_fac A T_ADD3 (λ _, τ_ADD3)); last done.
    intros. apply T_ADD3_subtype.
  Qed.

End adv_add3.
