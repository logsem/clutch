(** A function from a discrete space is a measurable map *)
#[warning="-notation-incompatible-prefix -hiding-delimiting-key"]
  From mathcomp Require Import all_boot all_algebra finmap.
#[warning="-notation-incompatible-prefix"]
From mathcomp Require Import mathcomp_extra boolp classical_sets functions reals interval_inference.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import ereal normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types.

From Stdlib.Logic Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

Section discrete_space_mapout.
  Context {d2} {T1 : pointedType} {T2 : measurableType d2}.
  Local Open Scope classical_set_scope.

  Local Definition m_mapout_def (f : T1 -> T2) : <<discr T1>> -> T2 := f.

  Lemma discr_mapout_measurable (f : T1 -> T2) : (measurable_fun setT (m_mapout_def f)).
  Proof. rewrite /measurable_fun. intros. by rewrite /measurable/=/discr_meas/=. Qed.

  HB.instance Definition  _ (f : T1 -> T2) :=
    isMeasurableMap.Build _ _ <<discr T1>> T2 (m_mapout_def f) (discr_mapout_measurable f).
End discrete_space_mapout.

(** Public definition for identity function *)
Local Open Scope classical_set_scope.
Definition m_discr {d} {T1 : pointedType} {T2 : measurableType d} (f : T1 -> T2) : measurable_map <<discr T1>> T2 :=
  m_mapout_def f.

(** Public equality for id *)
Definition m_discr_eval {d} {T1 : pointedType} {T2 : measurableType d} (f : T1 -> T2) :
    forall t : T1, m_discr f t = f t.
Proof. done. Qed.
