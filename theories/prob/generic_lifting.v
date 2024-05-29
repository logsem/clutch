From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements.
From stdpp Require Export countable.
From self.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From self.prob Require Export countable_sum distribution.

Open Scope R.


Record mlift := MkMLift {
  mlift_funct :> forall {A : Type} `{Countable A}, distr A -> (A → Prop) -> Prop;
  mlift_unit : ∀ A `{Countable A} (P : A → Prop) (a : A), P a -> mlift_funct (dret a) P;
  mlift_bind : ∀ A B `{Countable A, Countable B} (P : A → Prop) (Q : B -> Prop) (m : distr A) (f : A -> distr B),
      mlift_funct m P -> (forall a, P a -> mlift_funct (f a) Q) -> mlift_funct (dbind f m) Q;
  mlift_mono : ∀ A `{Countable A} (P Q : A → Prop) (m : distr A), (forall a, P a -> Q a) -> mlift_funct m P -> mlift_funct m Q;
  mlift_posR : ∀ A `{Countable A} (P : A → Prop) (m : distr A), mlift_funct m P -> mlift_funct m (λ a, P a /\ m a > 0);
  mlift_dzero : ∀ A `{Countable A} (P : A → Prop), mlift_funct dzero P;
}.
