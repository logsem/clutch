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
Lemma giryM_eval_eval (R : realType) {d} {T : measurableType d} {S : set T} (HS : measurable S) :
  forall μ, giryM_eval R HS μ = μ S.
Proof. done. Qed.


(** Eval is nonnegative *)
Lemma giryM_eval_nonneg (R : realType) {d} {T : measurableType d} {S : set T} (HS : measurable S) :
  forall x : giryM T, (0%R <= giryM_eval R HS x)%E.
Proof. Admitted.






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
    := forall (S : set T2), d2.-measurable S -> (measurable_fun setT ((f ^~ S) : T1 -> borelER)).

  Lemma measurable_evals_if_measurable : measurable_fun setT f -> measurable_evaluations f.
  Proof.
    intros Hm.
    rewrite /measurable_evaluations.
    intros S HS.
    replace (fun x : T1 => f x S) with ((@^~ S) \o f); last by apply functional_extensionality.

    apply (@measurable_comp _ _ _ _ _ _ setT (@^~ S : giryM T2 -> borelER)); auto.
    { apply subsetT. }
    apply (giryM_eval_def_measurable HS).
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


(* TODO: Fix whatever is happening here, so that we can build measurable maps of type
   A -> giryM R B by building measurable evals .*)
(*
HB.factory Record GiryMeasurableEvals {R : realType} {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : T1 -> giryM R T2) :=
  { meas_evaluationsP : measurable_evaluations f }.
*)

    (* Probably want to use measurable_evaluations as a builder for measuable_fun now, so I can
       instansiate THAT and get the measurable fun hierarchy bit automatically (by this lemma) *)

    (* I don't think we ever care about measruable_evaluations as a class (still useful as a lemma
       so I won't add a mixin + factory going the other direction )*)

    (* FIXME: Needs to be done outside of a section. Uncomment below (it works) and reorganize. *)


(*

HB.builders Context R d1 d2 T1 T2 f of @GiryMeasurableEvals R d1 d2 T1 T2 f.
  Lemma measurable_subproof: measurable_fun setT f.
  Proof. apply measurable_evals_iff_measurable, meas_evaluationsP. Qed.

  HB.instance Definition _ :=
      isMeasurableMap.Build _ _ T1 (giryM R T2) f measurable_subproof.

HB.end.

*)
