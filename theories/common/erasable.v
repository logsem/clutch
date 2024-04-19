From Coq Require Import Reals Psatz.
From clutch.common Require Import language.
From clutch.prob Require Export couplings distribution markov.

Section erasable.
  Definition erasable {Λ: language} (μ: state Λ -> distr (state Λ)) :=
    (∀ e σ m, μ σ ≫= (λ σ', exec m (e, σ'))= exec m (e, σ)).
End erasable.
