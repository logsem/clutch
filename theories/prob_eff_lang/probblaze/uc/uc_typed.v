(** * Syntactically typed environments

    The advantage bounds are stated for environments [A] that are
    semantically typed at [fac m τ → 𝔹].  A syntactically typed environment
    [⊢ᵥ A : (() -∘ T) ⇾ 𝔹] is one at [m = OS], as soon as the semantic
    interface [τ] is a subtype of the interpretation of [T]; the syntactic
    versions of the bounds are corollaries of [typed_env_fac]. *)
From clutch.prob_eff_lang.probblaze.typing Require Import types interp fundamental.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_judgement sem_row syntax semantics proofmode mode adequacy.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems.

Section uc_typed.
  Context `{probblazeRGpreS Σ}.

  Lemma fac_bool_subtype `{!probblazeRGS Σ} η μ δ ξ (T : type) (τ : sem_ty Σ) :
    (⊢ τ ≤ₜ interp._ty η μ δ T ξ) →
    ⊢ (interp._ty η μ δ ((() -∘ T) ⇾ 𝔹)%ty ξ)%T ≤ₜ (fac OS τ → 𝔹)%T.
  Proof.
    iIntros (Hτ).
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
    iApply ty_le_trans; first iApply (ty_le_mbang_elim OS).
    iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply Hτ].
  Qed.

  (* A syntactically typed environment, at a semantic interface [τ] below the
     interpretation of its syntactic interface [T]. *)
  Lemma typed_env_fac (A : val) (T : type) (τ : ∀ `{!probblazeRGS Σ}, sem_ty Σ) :
    (∀ `{!probblazeRGS Σ} η μ δ ξ, ⊢ τ ≤ₜ interp._ty η μ δ T ξ) →
    ⊢ᵥ A : ((() -∘ T) ⇾ TBool)%ty →
    ∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (fac OS τ → 𝔹)%T.
  Proof.
    intros Hτ HAtyped HRGS.
    apply (@fundamental_val Σ HRGS) in HAtyped.
    iPoseProof HAtyped as "Hadv".
    unfold bin_log_val_related.
    iSpecialize ("Hadv" $! [] [] ∅ []).
    iModIntro. iApply fac_bool_subtype; first apply Hτ.
    by rewrite /sem_val_typed /=.
  Qed.
End uc_typed.

