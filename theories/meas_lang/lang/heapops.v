(* TODO cleanup imports *)
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
From clutch.prob.monad Require Export laws extras.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state.

Local Open Scope classical_set_scope.

Definition state_loadC (x : (<<discr loc>> * state)%type) : val :=
  match (x.2.(heap) !! x.1)  with
  | Some v => v
  | None => inhabitant
  end.

Definition auxcov_load_ok : set (<<discr loc>> * state)%type :=
  [set x | ∃ w, x.2.(heap) !! x.1 = Some w ].

Definition auxcov_load_stuck : set (<<discr loc>> * state)%type :=
  [set x | x.2.(heap) !! x.1 = None ].

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

(* AllocN: the state part of the result *)
Definition state_allocNCS (x : (<<discr Z>> * val * state)%type) : state :=
  state_upd_heap_N (fresh_loc x.2.(heap)) (Z.to_nat x.1.1) x.1.2 x.2.

(* AllocN: the state part of the result *)
Definition state_allocNCE (x : (<<discr Z>> * val * state)%type) : <<discr loc>> :=
  (fresh_loc x.2.(heap)).


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
