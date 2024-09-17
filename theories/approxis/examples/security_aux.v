From clutch.prob_lang.typing Require Import tychk.
From clutch.approxis Require Import approxis map list.
(* From clutch.approxis.examples Require Import prf symmetric prf_cpa. *)
Set Default Proof Using "Type*".

Definition TOption (T : type) : type := (TUnit + T)%ty.

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
