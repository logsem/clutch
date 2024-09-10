(** Zero distibution *)
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types.

Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

Section giryM_zero.
  Context {d} {T : measurableType d}.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Local Open Scope classical_set_scope.

  Local Definition giryM_zero_def : giryM T := mzero.

End giryM_zero.


(** Public definition for the zero function *)
Definition giryM_zero {R : realType} {d} {T : measurableType d} : @giryM R _ T :=
  giryM_zero_def.

(** Public equality for the zero function *)
Definition giryM_zero_eval {R : realType} {d} {T : measurableType d} :
    forall t : set T, @giryM_zero R _ _ t = 0%R.
Proof. done. Qed.
