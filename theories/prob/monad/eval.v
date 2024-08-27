(** Definition of eval; characterization of A -> G B measurability *)

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

Section giryM_eval.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Local Definition giryM_eval_def (S : set T) (HS : measurable S) : giryM T -> borelER := (fun μ => μ S).

  Local Lemma giryM_eval_def_measurable (S : set T) (HS : measurable S) : measurable_fun setT (giryM_eval_def HS).
  Proof.
    apply (@measurability _ _ _ _ _ (giryM_eval_def HS) ereal_borel_subbase); first by simpl.
    rewrite /measurable/=.
    rewrite {2}/giry_subbase/=.
    apply  (@subset_trans _ (giry_subbase (T:=T))); last by apply sub_gen_smallest.
    rewrite /subset/=.
    intros X.
    rewrite /preimage_class/=.
    intros [Y HY <-].
    rewrite {1}/giry_subbase/=.
    exists S, HS.
    rewrite /preimage_class_of_measures/preimage_class/=.
    exists Y.
    { apply sub_gen_smallest.
      rewrite /ereal_borel_subbase/= in HY.
      done. }
    done.
  Qed.

  HB.instance Definition _ (S : set T) (HS : measurable S) :=
    isMeasurableMap.Build _ _ (giryM T) borelER (giryM_eval_def HS) (giryM_eval_def_measurable HS).

End giryM_eval.

(** Public definition for eval *)
Definition giryM_eval (R : realType) {d} {T : measurableType d} {S : set T} (HS : measurable S) :
    measurable_map (giryM T) borelER :=
  (@giryM_eval_def R _ T S HS).

(** Public equality for eval *)
Lemma giryM_eval_aux (R : realType) {d} {T : measurableType d} {S : set T} (HS : measurable S) :
  forall μ, giryM_eval R HS μ = μ S.
Proof. done. Qed.
