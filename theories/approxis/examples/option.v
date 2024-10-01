From clutch.prob_lang.typing Require Import tychk.
From clutch.approxis Require Import approxis.
Set Default Proof Using "Type*".

Definition TOption (T : type) : type := (TUnit + T)%ty.
Definition lrel_option {Σ} (A : lrel Σ) := (() + A)%lrel.

Definition opt_mult : val :=
  λ:"opt",
    match: "opt" with
    | NONE => NONE
    | SOME "vopt" =>
        match: "vopt" with
        | NONE => NONE
        | SOME "v" => SOME "v"
        end
    end.

Fact opt_mult_typed (A : type) : (⊢ᵥ opt_mult : (TOption (TOption A) → TOption A)%ty).
Proof.
  rewrite /opt_mult. tychk.
Qed.

Definition opt_mult_poly : val :=
  Λ: λ:"opt",
    match: "opt" with
    | NONE => NONE
    | SOME "vopt" =>
        match: "vopt" with
        | NONE => NONE
        | SOME "v" => SOME "v"
        end
    end.

Fact opt_mult_poly_typed : (⊢ᵥ opt_mult_poly : ∀: (TOption (TOption #0) → TOption #0)%ty).
Proof.
  rewrite /opt_mult_poly. constructor. tychk.
Qed.

Fact opt_mult_poly_sem_typed `{!approxisRGS Σ} :
  ⊢ (∀ A : lrel Σ, lrel_option (lrel_option A) → lrel_option A)%lrel
      opt_mult_poly opt_mult_poly.
Proof.
  replace (∀ A : lrel Σ, lrel_option (lrel_option A) → lrel_option A)%lrel
    with (interp (∀: TOption (TOption #0) → TOption #0) []) by easy.
  iApply fundamental_val.
  rewrite /opt_mult_poly. constructor. tychk.
Qed.
