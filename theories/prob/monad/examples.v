(** Examples *)

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

(* Check giryM. *)

(** ********** 2. Test: Examples of measuring sets *)
Section giry_space_example.
  Context {d : measure_display} (T : measurableType d).

  (*

  (* Example: Measuring sets in the Giry space *)
  Example test_giry_measures_0 : T.-giry.-measurable (set0 : set (giryM T)).
  Proof. by apply measurable0. Qed.

  Example test_giry_measures_T : T.-giry.-measurable [set: giryM T].
  Proof. by eapply @measurableT. Qed.

  (* giryM is also a measurable type, so can be nested. *)
  Example test_giry_measures_0' : (giryM T).-giry.-measurable (set0 : set (giryM (giryM T))).
  Proof. by apply measurable0. Qed.
   *)

End giry_space_example.
