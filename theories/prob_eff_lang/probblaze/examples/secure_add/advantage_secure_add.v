From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode valgroup adequacy mode compatibility.
From clutch.prob_eff_lang.probblaze.typing Require Import types interp fundamental.
From clutch.prob_eff_lang.probblaze.typing Require Import bridge.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems uc_advantage.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_typed.
From clutch.prob_eff_lang.probblaze.examples.secure_add Require Import secure_add_def secure_add_prf.

Import fingroup.
Import fingroup.fingroup.

#[local] Open Scope R_scope.
#[local] Open Scope factory_scope.

(** No well-typed environment -- in particular no aggregator -- can
    distinguish the real two-party addition protocol from the ideal
    functionality with the simulator, at either mode. *)

Section adv_add.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{probblazeRGpreS Σ}.

  Import valgroup_notation.

  Theorem adv_ADD (m : mode) (A : val) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m τ_ADD → 𝔹)%T) →
    advantage A REAL_ADD (SIM_ADD ∘f IDEAL_ADD) #true <= 0.
  Proof using All.
    intros HA.
    apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, fac m τ_ADD)); [exact HA| |]; intros HRGS;
      (iApply sem_typed_sub_ty; first iApply fac_MS_le);
      [iApply (REAL_ADD_IDEAL_MS (G := G _ _))|iApply (IDEAL_REAL_ADD_MS (G := G _ _))].
  Qed.

  (* The same for syntactically typed environments, through the fundamental
     lemma: the environment takes a single-session factory of the scenario. *)
  Definition T_ADD : type :=
    (∀R: (∀R: ((ℕ -{ RVar 0%nat }-> ()) * (ℕ -{ RVar 0%nat }-> ())) -{ RVar 0%nat ∪ᵣ (RVar 1%nat) }-∘ ()) ⇾
       (∀R: ((((τG -{ RVar 0%nat }-> ()) * (τG -{ RVar 0%nat }-> ()))
              * ((((() + ()) -{ RVar 0%nat }-> ())) * ((() + ()) -{ RVar 0%nat }-> (() + ()))))
               -{ (RFlip OS (RVar 0%nat)) ∪ᵣ (RVar 1%nat) }-∘ ()))).

  Lemma T_ADD_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ τ_ADD ≤ₜ (interp._ty η μ δ T_ADD ξ).
  Proof using All.
    sem_ty_le_struct using (iApply τG_subtype).
  Qed.

  Corollary adv_ADD_typed A :
    ⊢ᵥ A : ((() -∘ T_ADD) ⇾ TBool) →
    advantage A REAL_ADD (SIM_ADD ∘f IDEAL_ADD) #true <= 0.
  Proof using All.
    intros HA. apply (adv_ADD OS), (typed_env_fac A T_ADD (λ _, τ_ADD)); last done.
    intros. apply T_ADD_subtype.
  Qed.

End adv_add.
