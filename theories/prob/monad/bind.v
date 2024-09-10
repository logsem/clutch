(** Bind *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types compose join map.

Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".



Definition giryM_bind {R : realType} {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
                      (f : measurable_map T1 (giryM T2)) : measurable_map (@giryM R _ T1) (@giryM R _ T2)
  := m_cmp giryM_join (giryM_map f).
