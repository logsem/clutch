(** Constant function measurable map *)
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

Section MeasurableMap_const.
  Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
  Local Open Scope classical_set_scope.

  Local Definition m_cst_def (t : T2) : T1 -> T2 := cst t.

  Local Lemma m_cst_def_measurable (t : T2):
    @measurable_fun _ _ T1 T2 setT (m_cst_def t).
  Proof. apply measurable_cst. Qed.

  HB.instance Definition _ (t : T2) :=
    isMeasurableMap.Build _ _ T1 T2 (m_cst_def t) (m_cst_def_measurable t).
End MeasurableMap_const.


(** Public definition for constant function *)
Definition m_cst {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (v : T2) : measurable_map T1 T2 :=
  m_cst_def v.

(** Public equality for cst *)
Definition m_cst_eval {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (v : T2) :
    forall t : T1, m_cst v t = cst v t.
Proof. done. Qed.
