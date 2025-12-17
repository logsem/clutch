(** Composition of measurable maps *)
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

Section MeasurableMap_compose.
  Context {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}.
  Local Open Scope classical_set_scope.

  Local Definition m_cmp_def (f : measurable_map T2 T3) (g : measurable_map T1 T2) := comp f g.

  Lemma m_cmp_def_measurable (f : measurable_map T2 T3) (g : measurable_map T1 T2) :
    @measurable_fun _ _ T1 T3 setT (m_cmp_def f g).
  Proof.
    apply (@measurable_comp _ _ _ _ _ _ setT).
    - apply (@measurableT _ T2).
    - apply subsetT.
    - apply measurable_mapP.
    - apply measurable_mapP.
  Qed.

  HB.instance Definition _ (f : measurable_map T2 T3) (g : measurable_map T1 T2) :=
    isMeasurableMap.Build _ _ T1 T3 (m_cmp_def f g) (m_cmp_def_measurable f g).

End MeasurableMap_compose.


(** Public definition for composed function *)
Definition m_cmp {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
                 (f : measurable_map T2 T3) (g : measurable_map T1 T2) : measurable_map T1 T3 :=
  m_cmp_def f g.

(** Public equality for composition *)
Definition m_cmp_eval {d1 d2 d3} {T1 : measurableType d1} {T2 : measurableType d2} {T3 : measurableType d3}
                 (f : measurable_map T2 T3) (g : measurable_map T1 T2) : forall t : T1, m_cmp f g t = (comp f g) t.
Proof. done. Qed.
