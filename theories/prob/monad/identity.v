(** Identity function measurable map *)
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

Section MeasurableMap_id.
  Context {d} {T : measurableType d}.
  Local Open Scope classical_set_scope.

  Local Definition m_id_def : T -> T := id.

  Local Lemma m_id_def_measurable :
    @measurable_fun _ _ T T setT m_id_def.
  Proof. apply measurable_id. Qed.

  HB.instance Definition _ :=
    isMeasurableMap.Build _ _ T T m_id_def m_id_def_measurable.
End MeasurableMap_id.


(** Public definition for identity function *)
Definition m_id {d} {T : measurableType d} : measurable_map T T :=
  m_id_def.

(** Public equality for id *)
Definition m_id_eval {d} {T : measurableType d} :
    forall t : T, m_id t = t.
Proof. done. Qed.
