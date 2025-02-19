(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

Definition state_loadC : (<<discr loc>> * state)%type -> val :=
  of_option (ssrfun.comp gl_evalC $ mProd fst (ssrfun.comp heap snd)).

Definition auxcov_load_ok : set (<<discr loc>> * state)%type :=
  [set x | ∃ w, heap x.2 !! x.1 = Some w ].

Definition auxcov_load_stuck : set (<<discr loc>> * state)%type :=
  [set x | heap x.2 !! x.1 = None ].

Lemma auxcov_load_ok_meas : measurable auxcov_load_ok.
Proof. Admitted.
Hint Resolve auxcov_load_ok_meas : measlang.

Lemma auxcov_load_stuck_meas : measurable auxcov_load_stuck.
Proof. Admitted.
Hint Resolve auxcov_load_stuck_meas : measlang.

Lemma state_loadC_meas : measurable_fun auxcov_load_ok state_loadC.
Proof.
Admitted.
Hint Resolve state_loadC_meas : measlang.


(*
    | AllocN (Val (LitV (LitInt N))) (Val v) =>
        if bool_decide (0 < Z.to_nat N)%nat
          then
            let ℓ := fresh_loc σ1.(heap) in
            giryM_ret R ((Val $ LitV $ LitLoc ℓ, state_upd_heap_N ℓ (Z.to_nat N) v σ1) : cfg)
          else giryM_zero
*)

Locate fresh_loc.

(* AllocN: the state part of the result *)
Definition state_allocNCS (x : (<<discr Z>> * val * state)%type) : state. Admitted.
(*
  state_upd_heap_N (fresh_loc x.2.(heap)) (Z.to_nat x.1.1) x.1.2 x.2.
*)
(* AllocN: the state part of the result *)
Definition state_allocNCE (x : (<<discr Z>> * val * state)%type) : <<discr loc>>. Admitted.
(*   (fresh_loc x.2.(heap)).  *)


Definition auxcov_allocN_ok : set (<<discr Z>> * val * state)%type :=
  [set x | (0 < Z.to_nat x.1.1)%nat].

Definition auxcov_allocN_stuck: set (<<discr Z>> * val * state)%type :=
  [set x | (0 >= Z.to_nat x.1.1)%nat].

Lemma auxcov_allocN_ok_meas : measurable auxcov_allocN_ok.
Proof. Admitted.
Hint Resolve auxcov_allocN_ok_meas : measlang.

Lemma auxcov_allocN_stuck_meas : measurable auxcov_allocN_stuck.
Proof. Admitted.
Hint Resolve auxcov_allocN_stuck_meas : measlang.

Lemma state_allocNCE_meas : measurable_fun auxcov_allocN_ok state_allocNCE.
Proof.
Admitted.
Hint Resolve state_allocNCE_meas : measlang.

Lemma state_allocNCS_meas : measurable_fun auxcov_allocN_ok state_allocNCS.
Proof.
Admitted.
Hint Resolve state_allocNCS_meas : measlang.


(*
    | Store (Val (LitV (LitLoc l))) (Val w) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val $ LitV LitUnit, state_upd_heap <[l:=w]> σ1) : cfg)
          | None => giryM_zero
        end
 *)


(* store: the state part of the result *)
Program Definition state_storeS (x : (<<discr loc>> * val * state)%type) : state. Admitted.
(*  state_upd_heap <[x.1.1:=x.1.2]> x.2. *)

(* store: the expression part of the result *)
Definition state_storeE (x : (<<discr loc>> * val * state)%type) : expr :=
  ValU $ LitV $ LitUnit.

Definition auxcov_store_ok : set (<<discr loc>> * val * state)%type :=
  [set x | ∃ w, heap x.2 !! x.1.1 = Some w ].

Definition auxcov_store_stuck : set (<<discr loc>> * val * state)%type :=
  [set x | heap x.2 !! x.1.1 = None ].

Lemma auxcov_store_ok_meas : measurable auxcov_store_ok.
Proof. Admitted.
Hint Resolve auxcov_store_ok_meas : measlang.

Lemma auxcov_store_stuck_meas : measurable auxcov_store_stuck.
Proof. Admitted.
Hint Resolve auxcov_store_stuck_meas : measlang.

Lemma state_storeS_meas : measurable_fun auxcov_store_ok state_storeS.
Proof.
Admitted.
Hint Resolve state_storeS_meas : measlang.

Lemma state_storeE_meas : measurable_fun auxcov_store_ok state_storeE.
Proof.
Admitted.
Hint Resolve state_storeE_meas : measlang.
