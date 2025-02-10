Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Program.Wf Reals.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets.
From mathcomp.analysis Require Import reals measure ereal Rstruct sequences.
From clutch.prob.monad Require Export laws.

From mathcomp.analysis Require Import topology.

Set Warnings "hiding-delimiting-key".

Section setwise_measure_limit.

  Context {d} {T : measurableType d}.
  Context (μ : nat -> subprobability T R).

  Definition limit_measure (S : set T) : \bar R :=
    limn_esup (fun n => μ n S).


  Lemma limit_measure0 : limit_measure set0 = 0%E.
  Proof. Admitted.

  Lemma limit_measure_ge0 X : (0 <= limit_measure X)%E.
  Proof. Admitted.

  Lemma semi_sigma_additive_limit_measure : semi_sigma_additive limit_measure.
  Proof. Admitted.

  HB.instance Definition _ :=
    isMeasure.Build _ _ _ limit_measure
    limit_measure0 limit_measure_ge0 semi_sigma_additive_limit_measure.

End setwise_measure_limit.
