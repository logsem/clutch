(** Examples *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types eval ret.

Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

(** ********** Test: Examples of measuring sets *)
Section giry_space_example.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d : measure_display} (T : measurableType d).


  (* Example: Measuring sets in the Giry space *)
  Example test_giry_measures_0 : measurable (set0 : set (giryM T)).
  Proof. by apply measurable0. Qed.

  Example test_giry_measures_T : measurable [set: giryM T].
  Proof. by eapply @measurableT. Qed.

  (* giryM is also a measurable type, so can be nested. *)
  Example test_giry_measures_0' : measurable (set0 : set (giryM (giryM T))).
  Proof. by apply measurable0. Qed.

End giry_space_example.


(** ********** Test: Examples of integrals *)
Section giry_integral_example.
  Context {d : measure_display} (T : measurableType d).
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).

  Variable (μ_target : giryM T).  (* Some point in the space of measures on T*)

  (* The dirac measure using that point *)
  Example giry_ret_μ : giryM (giryM T) := @dirac _ _ μ_target _.

  Example int_zero_over_dirac : (\int[giry_ret_μ]_x cst 0%:E x)%E = 0%:E.
  Proof. apply integral0. Qed.

  Example int_one_over_dirac : (\int[giry_ret_μ]_x cst 1%:E x)%E = 1%:E.
  Proof.
    rewrite integral_cst /=.
    - by rewrite diracT mul1e.
    - rewrite -setC0.
      apply (@measurableC _ (giryM _)).
      by apply measurable0.
  Qed.
End giry_integral_example.



(** ********** Test: sealing *)
Section seal_example.
  Context {d : measure_display} (T : measurableType d).
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).

  Lemma X (S : set T) (HS : measurable S) : giryM_eval R HS = giryM_eval R HS.
  Proof.
    unfold giryM_eval.
    Fail unfold giryM_eval_def.
    (* Restart.
    Check giryM_eval R HS. *)
    (* TODO: Should be able to prove the equality of measurable maps using funext *)

    (* apply giryM_ext. *)
    (* rewrite giryM_eval_aux. *)
  Abort.


  Lemma X (v : T) : giryM_ret R v = giryM_ret R v.
  Proof.
    rewrite /giryM_ret.
    Fail unfold giryM_ret_def.
    rewrite giryM_ret_aux.
  Abort.

End seal_example.
