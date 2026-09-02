(** Giry monad map *)

#[warning="-notation-incompatible-prefix -hiding-delimiting-key"]
  From mathcomp Require Import all_boot all_algebra finmap.
#[warning="-notation-incompatible-prefix"]
From mathcomp Require Import mathcomp_extra boolp classical_sets functions reals interval_inference.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import ereal normedtype esum numfun measure lebesgue_measure lebesgue_integral.
From HB Require Import structures.

From clutch.prob.monad Require Export types eval.

From Stdlib.Logic Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Default Proof Using "Type".



Section giryM_map_definition.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2}.

  Local Open Scope classical_set_scope.

  (* FIXME: This is an attempt to eliminate a reverse coercion. Delete or rename once done *)
  (* Speficially, this function takes in a measurable_map instead of a measurable_fun *)
  (* Local Definition giryM_map_def (f : measurable_map T1 T2) (m : giryM T1) : set T2 -> \bar R := *)
  (*   fun A => m (f @^-1` A). *)

  (* Local Lemma giryM_map_def_pushforward_equiv (f : measurable_map T1 T2) (m : giryM T1) (S : set T2) : *)
  (*   giryM_map_def f m S = pushforward m (@measurable_mapP _ _ _ _ f) S. *)
  (* Proof. by rewrite /pushforward/giryM_map_def. Qed. *)

  (* Local Lemma giryM_map_def_0 (f : measurable_map T1 T2) (m : giryM T1) : giryM_map_def f m set0 = 0%E. *)
  (* Proof. *)
  (*   rewrite giryM_map_def_pushforward_equiv. *)
  (*   apply (measure0 (pushforward m (@measurable_mapP _ _ _ _ f))). *)
  (* Qed. *)

  (* Local Lemma giryM_map_def_ge0 (f : measurable_map T1 T2) (m : giryM T1) A : (0 <= giryM_map_def f m A)%E. *)
  (* Proof. *)
  (*   rewrite giryM_map_def_pushforward_equiv. *)
  (*   apply (measure_ge0 (pushforward m (@measurable_mapP _ _ _ _ f))). *)
  (* Qed. *)

  (* Local Lemma giryM_map_def_semi_additive (f : measurable_map T1 T2) (m : giryM T1) : semi_sigma_additive (giryM_map_def f m). *)
  (* Proof. *)
  (*   rewrite (functional_extensionality _ _ (giryM_map_def_pushforward_equiv f m)). *)
  (*   apply (@measure_semi_sigma_additive _ _ _ (pushforward m (@measurable_mapP _ _ _ _ f))). *)
  (* Qed. *)

  (* Local Lemma giryM_map_def_setT  (f : measurable_map T1 T2) (m : giryM T1) : *)
  (*   (giryM_map_def f m setT <= 1)%E. *)
  (* Proof. *)
  (*   rewrite giryM_map_def_pushforward_equiv. *)
  (*   rewrite /pushforward. *)
  (*   rewrite preimage_setT. *)
  (*   apply sprobability_setT. *)
  (* Qed. *)

  (* HB.instance Definition _  (f : measurable_map T1 T2) (m : giryM T1) *)
  (*   := isMeasure.Build _ _ R *)
  (*        (giryM_map_def f m) *)
  (*        (giryM_map_def_0 f m) *)
  (*        (giryM_map_def_ge0 f m) *)
  (*        (@giryM_map_def_semi_additive f m). *)

  (* HB.instance Definition _ (f : measurable_map T1 T2) (m : giryM T1) := *)
  (*   Measure_isSubProbability.Build _ _ _ (giryM_map_def f m) (giryM_map_def_setT f m). *)


  (* FIXME: I have to define this again because of https://github.com/math-comp/hierarchy-builder/issues/419 *)
  (*    Can't use the partially applied giryM_map_def in the instance for measurable_map. *)
  (* Local Definition giryM_map_def' (f : measurable_map T1 T2) (m : giryM T1) : giryM T2 := *)
  (*   giryM_map_def f m. *)

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



  (* Local Lemma giryM_map_def'_is_measurable (f : measurable_map T1 T2) : *)
  (*   @measurable_fun _ _ (giryM T1) (giryM T2) setT (giryM_map_def' f). *)
  (* Proof. *)
  (*   apply measurable_if_measurable_evals. *)
  (*   rewrite /measurable_evaluations. *)
  (*   intros S HS. *)
  (*   rewrite /giryM_map_def'. *)
  (*   erewrite functional_extensionality. *)
  (*   2: { *)
  (*     intro m. *)
  (*     rewrite /= giryM_map_def_pushforward_equiv. *)
  (*     reflexivity. *)
  (*   } *)
  (*   simpl. *)



  (*   (* *)
  (*   apply measurable_if_pushfowrard_subset. *)
  (*   Check (@measurability _ _ _ _ setT _ ereal_borel_subbase _). *)
  (*   Search subset smallest. *)
  (*   rewrite /subset. *)
  (*   intros Rs HRs. *)
  (*   simpl. *)
  (*   rewrite /pushforward. *)
  (*   rewrite /preimage. *)
  (*    *) *)
  (* Admitted. *)

  (* HB.instance Definition _ (f : measurable_map T1 T2)  := *)
  (*   isMeasurableMap.Build _ _ (giryM T1) (giryM T2) *)
  (*     (giryM_map_def' f) *)
  (*     (giryM_map_def'_is_measurable f). *)

End giryM_map_definition.

(** Public definition for giryM_map *)
(* Definition giryM_map {R : realType} {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : measurable_map T1 T2) : *)
(*     measurable_map (@giryM R _ T1) (@giryM R _ T2) *)
(*   := giryM_map_def' f. *)

(* (** Public equality for giryM_map *) *)
(* Lemma giryM_map_eval {R : realType} {d1} {d2} {T1 : measurableType d1} {T2 : measurableType d2} (f : measurable_map T1 T2) : *)
(*   forall μ S, (@giryM_map R _ _ _ _ f μ) S = pushforward μ (@measurable_mapP _ _ _ _ f) S. *)
(* Proof. *)
(*   intros μ S. *)
(*   rewrite /giryM_map/giryM_map_def'. *)
(*   rewrite -giryM_map_def_pushforward_equiv. *)
(*   simpl. *)
(*   done. *)
(* Qed. *)
