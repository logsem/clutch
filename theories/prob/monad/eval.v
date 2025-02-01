(** Definition of eval; characterization of A -> G B measurability *)

From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed (* topology *) normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types extras.

Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".

Section giryM_eval.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Context (S : set T).
  Context (HS : measurable S).

  Definition giryM_eval : giryM T -> \bar R := (fun μ => μ S).

  Lemma giryM_eval_meas : measurable_fun setT giryM_eval.
  Proof using HS R S T d. by apply base_eval_measurable. Qed.

  (** Public equality for eval *)
  Lemma giryM_eval_eval : forall μ, giryM_eval μ = μ S.
  Proof. done. Qed.

  (** Eval is nonnegative *)
  Lemma giryM_eval_nonneg : forall x : giryM T, (0%R <= giryM_eval x)%E.
  Proof.
    intro μ.
    rewrite /giryM_eval_eval.
    apply (measure_ge0 μ S).
  Qed.

End giryM_eval.





Section giryM_eval_char.
  (** Characterize measurability of A -> giryM B functions using evaluations *)
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).

  Local Open Scope classical_set_scope.

  Context {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}.
  Variable (f : T1 -> giryM T2).

  (** f has measurable_evaluations when:
      for all measurable sets S, evaluating f by S is a measurable function.
   *)
  Definition measurable_evaluations {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> giryM T2) : Prop
    := forall (S : set T2), d2.-measurable S -> (measurable_fun setT ((f ^~ S) : T1 -> \bar R)).

  Lemma measurable_evals_if_measurable : measurable_fun setT f -> measurable_evaluations f.
  Proof.
    intros Hm.
    rewrite /measurable_evaluations.
    intros S HS.
    replace (fun x : T1 => f x S) with ((@^~ S) \o f); last by apply functional_extensionality.

    apply (@measurable_comp _ _ _ _ _ _ setT (@^~ S : giryM T2 -> \bar R)); auto.
    { apply subsetT. }
    apply (giryM_eval_meas HS).
  Qed.


  Lemma measurable_if_measurable_evals : measurable_evaluations f -> measurable_fun setT f.
  Proof.
    intro Hm.
    rewrite /measurable_evaluations/measurable_fun/= in Hm.

    apply (@measurable_if_pushfowrard_subset _ _ _ _ f).
    rewrite {1}/measurable/=.
    apply smallest_sub.
    { rewrite /sigma_algebra.
      constructor.
      - rewrite /= preimage_set0.
        apply measurable0.
      - intros ?.
        simpl.
        intro HA.
        rewrite setTD.
        rewrite -preimage_setC.
        apply measurableC.
        apply HA.
      - simpl.
        intros S MS.
        rewrite preimage_bigcup.
        apply bigcup_measurable.
        intros k _.
        apply MS.
    }
    rewrite /giry_subbase/subset/=.
    intros X [Y [HY HX]].

    have G1 : d1.-measurable [set: T1] by auto.
    specialize (Hm Y HY G1).
    rewrite /salgebraType/= in Hm.
    clear G1.

    rewrite /preimage_class_of_measures/preimage_class/= in HX.
    destruct HX as [B HB HBf].
    rewrite setTI in HBf.

    specialize (Hm B HB).
    rewrite setTI in Hm.

    rewrite <- HBf.
    rewrite <- comp_preimage.
    simpl.

    have HF : (fun x : T1 => f x Y) = ((SubProbability.sort (R:=R))^~ Y \o f).
    { apply functional_extensionality.
      intro x.
      by simpl.
    }

    rewrite HF in Hm.
    apply Hm.
  Qed.

  (** A function A -> giryM B is measurable iff its evaluation function at every S is measurable. *)
  Lemma measurable_evals_iff_measurable : measurable_evaluations f <-> measurable_fun setT f.
  Proof. split; [apply measurable_if_measurable_evals | apply measurable_evals_if_measurable]. Qed.

End giryM_eval_char.
