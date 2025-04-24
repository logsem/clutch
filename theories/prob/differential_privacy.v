From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Import couplings_exp.

(* TODO define some of the standard metric spaces used as input for diffpriv *)

Definition diffpriv_pure {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε : R) :=
  ∀ a1 a2,
    d a1 a2 <= 1 →
    ∀ (P : B → Prop),
      prob (f a1) (λ b, bool_decide (P b))
      <=
        exp ε * prob (f a2) (λ b, bool_decide (P b)).

Fact Mcoupl_diffpriv {A B : Type} `{Countable B}
  (d : A → A → R) (f : A → distr B) (ε : R) :
  (∀ a1 a2, d a1 a2 <= 1 → Mcoupl (f a1) (f a2) eq ε)
  →
    diffpriv_pure d f ε.
Proof.
  intros cpl.
  intros a1 a2 d12 P.
  eapply (Mcoupl_eq_elim_dp).
  by apply cpl.
Qed.
