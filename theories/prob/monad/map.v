(** Giry monad map *)

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



Section giryM_map_definition.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}.

  Local Open Scope classical_set_scope.

  Context (f : T1 -> T2).
  Context (Hf : measurable_fun setT f).
  Context (m : giryM T1).

  Local Definition giryM_map_def : set T2 -> \bar R :=
    fun A => m (f @^-1` A).

  Local Lemma giryM_map_def_pushforward_equiv (S : set T2) :
      giryM_map_def S = pushforward m Hf S.
  Proof. by rewrite /pushforward/giryM_map_def. Qed.

  Local Lemma giryM_map_def_0 : giryM_map_def set0 = 0%E.
  Proof using Hf R T1 T2 d1 d2 f m.
    rewrite giryM_map_def_pushforward_equiv.
    apply (measure0 (pushforward m Hf)).
  Qed.

  Local Lemma giryM_map_def_ge0 A : (0 <= giryM_map_def A)%E.
  Proof using Hf R T1 T2 d1 d2 f m.
    rewrite giryM_map_def_pushforward_equiv.
    apply (measure_ge0 (pushforward m Hf)).
  Qed.

  Local Lemma giryM_map_def_semi_additive : semi_sigma_additive giryM_map_def.
  Proof using Hf R T1 T2 d1 d2 f m.
    rewrite (functional_extensionality _ _ giryM_map_def_pushforward_equiv).
    apply (@measure_semi_sigma_additive _ _ _ (pushforward m Hf)).
  Qed.

  Local Lemma giryM_map_def_setT : (giryM_map_def setT <= 1)%E.
  Proof using Hf R T1 T2 d1 d2 f m.
    rewrite giryM_map_def_pushforward_equiv.
    rewrite /pushforward.
    rewrite preimage_setT.
    apply sprobability_setT.
  Qed.

  HB.instance Definition _
    := isMeasure.Build _ _ R
         (giryM_map_def )
         (giryM_map_def_0 )
         (giryM_map_def_ge0 )
         (@giryM_map_def_semi_additive ).

  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ giryM_map_def giryM_map_def_setT.

  Definition giryM_map : giryM T2 := giryM_map_def.

  (*
  Local Lemma giryM_map_def_is_measurable (f : measurable_map T1 T2) :
    @measurable_fun _ _ (giryM T1) (giryM T2) setT (giryM_map_def f).
  Proof.
    apply measurable_if_measurable_evals.
    rewrite /measurable_evaluations.
    (* Check pushforward. *)

    intros S HS.
    apply measurable_if_pushfowrard_subset.
    intros Y HY.
    simpl.

    (*

    have HM := @measurable_mapP _ _ _ _ f.
    apply measurable_if_pushfowrard_subset.
    rewrite /giryM_map_def.
    intros S SM.
    simpl.
    rewrite /pushforward.
    simpl.*)


    (* rewrite /giryM_map_def/measurable_fun.
    intros ? Y YMeas.
    rewrite setTI.
    rewrite /pushforward.
    rewrite /preimage.*)
  Admitted.
  *)


End giryM_map_definition.



Section giryM_map.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}.

  Axiom giryM_map_meas :
    forall (f : T1 -> T2) (Hf : measurable_fun setT f), @measurable_fun _ _ (giryM T1) (giryM T2) setT (giryM_map Hf).

    (*
    apply measurable_if_measurable_evals.
    rewrite /measurable_evaluations.
    intros S HS.
    rewrite /giryM_map_def'.
    erewrite functional_extensionality.
    2: {
      intro m.
      rewrite /= giryM_map_def_pushforward_equiv.
      reflexivity.
    }
    simpl.

*)

    (*
    apply measurable_if_pushfowrard_subset.
    Check (@measurability _ _ _ _ setT _ ereal_borel_subbase _).
    Search subset smallest.
    rewrite /subset.
    intros Rs HRs.
    simpl.
    rewrite /pushforward.
    rewrite /preimage.
     *)
  Local Open Scope classical_set_scope.
 (*

  Definition giryM_mapU : (<<discr (MeasurableMapT T1 T2)>> * (giryM T1))%type -> (giryM T2) :=
    fun x => giryM_map x.1.(f_meas) x.2.

  Lemma MyTest (S : set (<<discr (MeasurableMapT T1 T2)>> * (giryM T1))%type) :
    measurable (image S snd) -> measurable S.
  Proof.
    intro X.
    rewrite /measurable//=/preimage_classes//=.
  Abort.

  Lemma giryM_mapU_meas : measurable_fun setT giryM_mapU.
  Proof.
    intros _ Y HY.
    rewrite //= setTI.
    rewrite /preimage/giryM_mapU//=.
    rewrite /measurable//=/preimage_classes//=.
  Admitted.
*)


  (** Public equality for giryM_map *)
  Lemma giryM_map_eval  (f : T1 -> T2) (Hf : measurable_fun setT f) :
    forall μ S, (@giryM_map R _ _ _ _ f Hf μ) S = pushforward μ Hf S.
  Proof.
    intros μ S.
    rewrite /giryM_map/giryM_map_def.
    rewrite -giryM_map_def_pushforward_equiv.
    simpl.
    done.
  Qed.

End giryM_map.

Global Arguments giryM_map {_} {_} {_} {_} {_} _.
