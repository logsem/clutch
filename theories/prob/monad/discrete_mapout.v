(** A function from a discrete space is a measurable map *)
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

Section discrete_space_mapout.
  Context {d2} {T1 : pointedType} {T2 : measurableType d2}.
  Local Open Scope classical_set_scope.

  Local Definition m_discr (f : T1 -> T2) : <<discr T1>> -> T2 := f.

  Lemma m_discr_measurable (f : T1 -> T2) : (measurable_fun setT (m_discr f)).
  Proof. rewrite /measurable_fun. intros. by rewrite /measurable/=/discr_meas/=. Qed.

  Definition m_discr_eval (f : T1 -> T2) : forall t : T1, m_discr f t = f t.
  Proof. done. Qed.

End discrete_space_mapout.
