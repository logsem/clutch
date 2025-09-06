From clutch.prob Require Export countable_sum countable_distribution.
From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable finite.
From Coq.Logic Require Import ClassicalEpsilon.
From clutch.prelude Require Export base stdpp_ext Reals_ext Coquelicot_ext Series_ext classical uniform_list.

Open Scope R.

Section couplings_c.
  Context {A B : Type}.
  Context (μ1 : cdistr A) (μ2 : cdistr B) (S : A -> B -> Prop).

  Definition ARcouplC (ε : R) :=
    forall (f: A → R) (g: B -> R),
      (forall a, 0 <= f a <= 1) ->
      (forall b, 0 <= g b <= 1) ->
      (forall a b, S a b -> f a <= g b) ->
      SeriesCS (λ a, μ1 a * f a) <= SeriesCS (λ b, μ2 b * g b) + ε.

End couplings_c.
