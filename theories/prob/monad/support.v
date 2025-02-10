Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Program.Wf Reals.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets.
From mathcomp.analysis Require Import reals measure ereal Rstruct sequences measure lebesgue_measure lebesgue_integral.
From clutch.prob.monad Require Export laws.

From mathcomp.analysis Require Import topology.

Set Warnings "hiding-delimiting-key".

Section support.
  Context {d} {T : measurableType d}.
  Context (μ : subprobability T R).
  Context (f : T -> \bar R).

  Definition mass (S : set T) : \bar R := (\int[μ]_(x in S) f x)%E.

  Definition has_support (S : set T) : Prop := mass S = mass setT.

End support.
