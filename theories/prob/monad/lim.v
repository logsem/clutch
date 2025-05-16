Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Program.Wf Reals.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets.
From mathcomp.analysis Require Import measure ereal sequences normedtype.
From clutch.prob.monad Require Export giry.
Require Import mathcomp.reals_stdlib.Rstruct.
Require Import mathcomp.reals.reals.

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
    suffices -> : (esups (R := R) (fun n : nat => μ n set0)) = (fun n => (0)%E) by rewrite lim_cst.
    apply funext; intro n.
    rewrite /esups/sdrop//=.
    eapply eq_trans_r; last (symmetry; eapply ereal_sup1).
    f_equal.
    apply funext; intro x.
    apply propext; simpl; split.
    { by intros [??<-]. }
    { move=>->//=; by exists n. }
  Qed. 

  Lemma limit_measure_ge0 X : (0 <= limit_measure X)%E.
  Proof.
    rewrite /limit_measure.
    rewrite /limn_esup/=.
    by apply: limf_esup_ge0.
  Qed. 

  Lemma semi_sigma_additive_limit_measure : semi_sigma_additive limit_measure.
  Proof.
    rewrite /semi_sigma_additive.
    (* ? *)
  Admitted.

  HB.instance Definition _ :=
    isMeasure.Build _ _ _ limit_measure
    limit_measure0 limit_measure_ge0 semi_sigma_additive_limit_measure.

  Lemma limit_measure_setT : (limit_measure setT <= 1)%E.
  Proof.
    rewrite /limit_measure.
    rewrite /limn_esup.
    rewrite /limf_esup.
    apply ereal_inf_le.
    eexists _.
    { simpl. exists setT.
      - rewrite /eventually.
        rewrite /filter_from. simpl.
        by exists 0.       
             - done. }
    apply: ub_ereal_sup.
    rewrite /ubound/=.
    intros ?[??<-].
    apply: sprobability_setT.
  Qed. 
  HB.instance Definition _ := Measure_isSubProbability.Build _ _ _ limit_measure limit_measure_setT.

End setwise_measure_limit.
