(** return *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types eval.

Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".


Section giry_ret.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Definition giryM_ret : T -> giryM T := fun t0 => @dirac _ T t0 _.

  Lemma giry_ret_measurable : @measurable_fun _ _ T (giryM T) setT giryM_ret.
  Proof.
    apply measurable_evals_iff_measurable.
    rewrite /measurable_evaluations.
    intros S SMeas.
    rewrite /measurable_fun/= .
    intros ? Y HY.
    (* NOTE: Since its using 'measurable, it seems that Borel or Lebesgue doesn't matter here.  *)
    remember (fun x : T => (\d_x)%R S) as f.
    rewrite /dirac in Heqf.
    have W : f = (comp EFin (indic S)).
    { apply functional_extensionality. intro. by rewrite Heqf/=. }
    rewrite W.
    rewrite setTI.
    rewrite comp_preimage.
    rewrite preimage_indic.
    remember (in_mem GRing.zero (mem (preimage EFin Y))) as B1; rewrite -HeqB1.
    remember (in_mem (GRing.one R) (mem (preimage EFin Y))) as B2; rewrite -HeqB2.
    destruct B1; destruct B2; simpl.
    - apply H.
    - apply measurableC, SMeas.
    - apply SMeas.
    - apply measurable0.
  Qed.

  (** Public equality for ret *)
  Lemma giryM_ret_eval (t : T) : forall z, giryM_ret t z = dirac t z.
  Proof. auto. Qed.

End giry_ret.
