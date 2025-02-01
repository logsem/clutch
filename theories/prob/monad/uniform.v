(** uniform spaces on finite types *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types eval integrate.

Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

Section unif_fin_space.
  Local Open Scope ereal_scope.
  Local Open Scope classical_set_scope.
  Context {R : realType}.
  Variable (m : nat).

  (* The finite type of > 0 elements is inhabited *)
  Program Definition Ism_inhabitant : 'I_(S m). eapply (@Ordinal _), leqnn. Defined.

  HB.instance Definition _ := gen_eqMixin ('I_m).
  HB.instance Definition _ := gen_choiceMixin ('I_m).
  HB.instance Definition _ N := isPointed.Build ('I_(S m)) Ism_inhabitant.

  Definition giryM_unif_def (X : set <<discr 'I_(S m)>>) : \bar R
    :=  if `[< finite_set X >] then ((#|` fset_set X |)%:R / (S m)%:R)%:E else +oo.

  Lemma unifM0 : giryM_unif_def set0 = 0.
  Proof. Admitted.

  Lemma unifM_ge0 (A : set <<discr 'I_(S m)>>) : 0 <= giryM_unif_def A.
  Proof. Admitted.

  Lemma unifM_sigma_additive : semi_sigma_additive giryM_unif_def.
  Proof. Admitted.

  HB.instance Definition _ :=
    isMeasure.Build _ _ _ giryM_unif_def unifM0 unifM_ge0 unifM_sigma_additive.

  Lemma unifM_T : giryM_unif_def setT <= 1%E.
  Proof. Admitted.

  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ giryM_unif_def unifM_T.

End unif_fin_space.

Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Public definition for the zero function *)
Definition giryM_unif {R : realType} (m : nat) : @giryM R _ <<discr ('I_(S m))>> :=
  @giryM_unif_def R m.

(** Public equality for the zero function *)
Definition giryM_unif_eval {R : realType} (m : nat) :
    forall X : set <<discr ('I_(S m))>>,
      (@giryM_unif R m) X =  if `[< finite_set X >] then ((#|` fset_set X |)%:R / (S m)%:R)%:E else +oo.
Proof. done. Qed.
