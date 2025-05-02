Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Program.Wf Reals.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets.
From mathcomp.analysis Require Import reals measure ereal Rstruct sequences.
From clutch.prob.monad Require Export giry.

From mathcomp.analysis Require Import topology.

From Coq.ssr Require Import ssreflect ssrfun.

Set Warnings "hiding-delimiting-key".

Section setwise_measure_limit.
  Context {d} {T : measurableType d}.
  Context (μ : nat -> subprobability T R).

  Local Open Scope classical_set_scope.

  Definition limit_measure (S : set T) : \bar R :=
    limn_esup (fun n => μ n S).

  Lemma limit_measure0 : limit_measure set0 = 0%E.
  Proof.
    rewrite /limit_measure.
    rewrite limn_esup_lim.
    suffices -> : (esups (R := R) (fun n : nat => μ n set0)) = (fun n => (0)%E).
    { (* why is this hard *)
      admit.
    }
    apply funext; intro n.
    rewrite /esups/sdrop//=.
    eapply eq_trans_r; last (symmetry; eapply ereal_sup1).
    f_equal.
    apply funext; intro x.
    apply propext; simpl; split.
    { by intros [??<-]. }
    { move=>->//=; by exists n. }
  Admitted.

  Lemma limit_measure_ge0 X : (0 <= limit_measure X)%E.
  Proof.
    (* Because measuring a set is always nonnegative *)
  Admitted.

  Lemma semi_sigma_additive_limit_measure : semi_sigma_additive limit_measure.
  Proof.
    (* ? *)
  Admitted.

  HB.instance Definition _ :=
    isMeasure.Build _ _ _ limit_measure
    limit_measure0 limit_measure_ge0 semi_sigma_additive_limit_measure.

  Lemma limit_measure_setT : (limit_measure setT <= 1)%E.
  Proof.
    (* Because each is bounded above by 1 *)
  Admitted.

  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ limit_measure limit_measure_setT.

End setwise_measure_limit.
