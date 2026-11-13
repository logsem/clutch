From Autosubst Require Import Autosubst.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics notation logic.
From clutch.prob_eff_lang.probblaze.typing Require Import types interp fundamental.

(** * Hand-written derivations for copyable references

    A test of the syntactic rules [AllocC_typed], [LoadC_typed] and
    [StoreC_typed] for [refᶜ τ] (PLAN.md, section 2): a derivation written
    by hand, before any automation exists.  The program allocates an empty
    option cell, reads it, and fills it if it was empty.  The reference is
    used twice (by the load and by the store), so it is copied with
    [Contraction_typed]; [refᶜ τ] is [MultiT] by [TBangRefC_le]. *)

Ltac solve_fresh :=
  first [ done | intros []
        | unfold ctx_dom; simpl; unfold elem_of, elem_binder_string; set_solver ].

Local Notation optZ := (() + ℤ)%ty.

(* [() + ℤ] is copyable: bang both summands, then pull the bang out. *)
Lemma optZ_multi : le.MultiT optZ.
Proof.
  eapply le.TTrans_le; [|apply le.TBangSum1_le].
  apply le.TSum_le; [apply le.TBangUnit_le|apply le.TBangInt_le].
Qed.

(* Every copyable reference is copyable, whatever its payload. *)
Lemma refc_multi τ : le.MultiT (refᶜ τ).
Proof. apply le.TBangRefC_le. Qed.

Definition refc_test : expr :=
  let: "r" := ref NONE in
  match: ! "r" with
    NONE => "r" <- SOME #1
  | SOME "x" => #()%V
  end.

Lemma refc_test_typed : ∅ .| [] ⊢ₜ refc_test : RNil : () ⊣ [].
Proof.
  unfold refc_test.
  apply (Let_typed _ [] [] [] "r" _ _ RNil (refᶜ optZ)%ty); [solve_fresh|solve_fresh| |].
  - (* ref NONE *)
    apply AllocC_typed, InjL_typed, Val_typed, Unit_val_typed.
  - (* Copy "r": one copy for the load, one for the store. *)
    apply (Contraction_typed _ [] _ _ _ _ "r" (refᶜ optZ)%ty (refc_multi _)).
    apply (Match_typed _ _ [("r", (refᶜ optZ)%ty)] [] _ _ _ BAnon "x" RNil TUnit TInt TUnit);
      [solve_fresh|solve_fresh|solve_fresh|solve_fresh| | |].
    + (* ! "r" consumes the first copy. *)
      apply LoadC_typed; [apply optZ_multi|]. apply Var_typed.
    + (* NONE => "r" <- SOME #1 consumes the second copy. *)
      apply (StoreC_typed _ _ [("r", (refᶜ optZ)%ty)] [] _ _ _ optZ).
      * apply le.Multi_le, optZ_multi.
      * apply Var_typed.
      * apply InjR_typed, Val_typed, Int_val_typed.
    + (* SOME "x" => #() drops "x" and the second copy of "r". *)
      apply (Weakening_typed _ [("r", (refᶜ optZ)%ty)] _ _ _ _ "x" TInt).
      apply (Weakening_typed _ [] _ _ _ _ "r" (refᶜ optZ)%ty).
      apply Val_typed, Unit_val_typed.
Qed.

(* The fundamental lemma turns the derivation into a semantic typing. *)
Lemma refc_test_sem `{!probblazeRGS Σ} :
  ⊢ 〈∅; []〉 ⊨ₜ refc_test ≤log≤ refc_test : RNil : () ⫤ [].
Proof. apply fundamental, refc_test_typed. Qed.
