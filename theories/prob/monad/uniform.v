(** uniform *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types eval compose integrate.

Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".


(*


Section unif_fin_space.
  Local Open Scope ereal_scope.
  Context {R : realType}.
  Variable (m : nat).

  Program Definition Ism_inhabitant : 'I_(S m). eapply (@Ordinal _), leqnn. Defined.

  HB.instance Definition _ := gen_eqMixin ('I_m).
  HB.instance Definition _ := gen_choiceMixin ('I_m).
  HB.instance Definition _ N := isPointed.Build ('I_(S m)) Ism_inhabitant.

  Definition unifM (X : set (discrType 'I_(S m))) : \bar R
    :=  if `[< finite_set X >] then ((#|` fset_set X |)%:R / (S m)%:R)%:E else +oo.

  Lemma unifM0 : unifM set0 = 0. Proof. Admitted.
  Lemma unifM_ge0 (A : set (discrType 'I_(S m))) : 0 <= unifM A. Proof. Admitted.
  Lemma unifM_sigma_additive : semi_sigma_additive unifM. Proof. Admitted.

  HB.instance Definition _ :=
    isMeasure.Build _ _ _ unifM unifM0 unifM_ge0 unifM_sigma_additive.

  Lemma unifM_T : unifM setT <= 1%E. Proof. Admitted.

  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ unifM unifM_T.

  (* Check (unifM : subprobability _ _).
  Check (unifM : giryType R (discrType ('I_(S m)))).

  Check (discrType ('I_(S m)) : measurableType _). (* Okay so this works *)
  Check (unifM : giryM R (discrType ('I_(S m)))). (* And this works too.... what does wrong withcfg? *) *)

End unif_fin_space.

(* Instead, we may consider restructing the semantics to use 'I_m instead of (fin m) *)
Definition fin_of_Im (m : nat) : 'I_m -> fin m.
Admitted.

*)
