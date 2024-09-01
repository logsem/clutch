(** join *)

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

Section giryM_join_definition.
  Context `{R : realType}.
  Notation giryM := (giryM (R := R)).
  Context {d} {T : measurableType d}.

  Local Open Scope classical_set_scope.

  (* Specification of giryM_join as an integral *)
  Local Definition giryM_join_def {d} {T : measurableType d} (m : giryM (giryM T)) : (set T -> \bar R)
    := (fun S => \int[m]_μ (μ S))%E.

  Section giryM_join_measure_def.
    Context (m : giryM (giryM T)).

    Definition giryM_join0 : giryM_join_def m set0 = 0%E.
    Proof.
      rewrite /giryM_join_def.
      have X1 : (\int[m]_μ μ set0)%E  = ((integral m setT (cst GRing.zero)))%E.
      { f_equal.
        apply functional_extensionality.
        intro μ.
        by rewrite measure0.
      }
      rewrite X1.
      rewrite integral_cst.
      - by rewrite (mul0e _).
      - rewrite /=.
        by apply (@measurableT _ (salgebraType _)).
    Qed.

    Definition giryM_join_ge0 A : (0 <= giryM_join_def m A)%E.
    Proof.
      rewrite /giryM_join_def.
      apply integral_ge0.
      intros μ _.
      apply (measure_ge0 μ A).
    Qed.

    Definition giryM_join_semi_additive : semi_sigma_additive (giryM_join_def m).
    Proof.
      rewrite /semi_sigma_additive.
      intros F Fmeas Htriv_int HFunion_meas.
      rewrite /giryM_join_def.
      (* Check (integral_bigcup Htriv_int Fmeas).
      Check (@integral_bigcup _ _ R m _ _ _ _). *)
    Admitted.

    HB.instance Definition _
      := isMeasure.Build _ _ _
           (giryM_join_def m)
           giryM_join0
           giryM_join_ge0
           giryM_join_semi_additive.

    Lemma giryM_join_setT : (giryM_join_def m setT <= 1)%E.
    Proof.
      rewrite /giryM_join_def.
      have H : (\int[m]_μ μ [set: T] <= \int[m]_μ (cst 1 μ))%E.
      { apply ge0_le_integral.
        - by [].
        - intros ? ?; by [].
        - apply base_eval_measurable.
          by apply @measurableT.
        - intros ? ?; by [].
        - by apply measurable_cst.
        - intros ? ?.
          simpl.
          by apply sprobability_setT.
      }
      rewrite integral_cst/= in H; last by apply (@measurableT _ (giryM T)).
      apply (Order.le_trans H).
      rewrite mul1e.
      apply sprobability_setT.
    Qed.

    HB.instance Definition _ :=  Measure_isSubProbability.Build _ _ _ (giryM_join_def m) giryM_join_setT.

  End giryM_join_measure_def.

  (* Workaround for HB bindings issue *)
  Definition giryM_join_def' : giryM (giryM T) -> (giryM T) := giryM_join_def.


  (* The measurable evaluation function which computes the giryM_join_def on measurable sets *)
  Definition giryM_join_meas_map_pre {S : set T} (HS : d.-measurable S) : measurable_map (giryM (giryM T)) (\bar R) :=
    @giryM_integrate R _ (giryM T) (giryM_eval R HS) (giryM_eval_nonneg HS).

  (* giryM_join_def equals the measurable evaluation function at each measruable set *)
  Lemma giryM_join_meas_map_pre_spec {S : set T} (HS : d.-measurable S) (m : giryM (giryM T)):
      giryM_join_meas_map_pre HS m = giryM_join_def m S.
  Proof. by rewrite /giryM_join_meas_map_pre giryM_integrate_eval /giryM_join_def. Qed.


  Lemma giryM_join_def'_measurable : @measurable_fun _ _ (giryM (giryM T)) (giryM T) setT giryM_join_def'.
  Proof.
    apply measurable_if_measurable_evals.
    rewrite /giryM_join_def'/measurable_evaluations.
    intros S HS.
    have H1 : (fun x : giryM (giryM T) => giryM_join_def x S) = (fun x : giryM (giryM T) => giryM_join_meas_map_pre HS x).
    { apply functional_extensionality.
      intros ?.
      by rewrite giryM_join_meas_map_pre_spec.
    }
    rewrite H1.
    rewrite /giryM_join_meas_map_pre.
    apply measurable_mapP.
  Qed.

  HB.instance Definition _ :=
    isMeasurableMap.Build _ _ (giryM (giryM T)) (giryM T) (giryM_join_def' : giryM (giryM T) -> (giryM T)) giryM_join_def'_measurable.

End giryM_join_definition.

(** Public definition of join*)
Definition giryM_join {R : realType} {d} {T : measurableType d} :
    measurable_map (@giryM R _ (@giryM R _ T)) (@giryM R _ T) :=
  giryM_join_def'.

(** Public equation for join*)
Lemma giryM_join_eval {R : realType} {d} {T : measurableType d} (m : @giryM R _ (@giryM R _ T)) :
  forall S, (giryM_join m S = \int[m]_μ (μ S))%E.
Proof. done. Qed.
