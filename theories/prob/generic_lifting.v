From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements.
From stdpp Require Export countable.
From coneris.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From coneris.prob Require Export countable_sum distribution.

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

Record ord_monoid {A : Type} (e : A) (op : A -> A -> A) (leq : A -> A -> Prop) := MkOrdMonoid {
   ord_refl : forall (a : A), leq a a;
   ord_antisym : forall (a b : A), leq a b -> leq b a -> a = b;
   ord_trans : forall (a b c : A), leq a b -> leq b c -> leq a c;
   op_unit_l : forall (a : A), op e a = a;
   op_unit_r : forall (a : A), op a e = a;
   op_assoc : forall (a b c : A), op a (op b c) = op (op a b) c;
   op_mono : forall (a b c d : A), leq a c -> leq b d -> leq (op a b) (op c d);
}.

Record graded_mlift {M : Type} `{M_ord_mon : @ord_monoid M e op leq} := MkGradedMLift {
    gmlift_funct :> forall {A : Type} `{Countable A}, M -> distr A -> (A → Prop) -> Prop;
    gmlift_unit : ∀ A `{Countable A} (P : A → Prop) (a : A), P a -> gmlift_funct e (dret a) P;
    gmlift_bind : ∀ A B `{Countable A, Countable B} (m1 m2 : M) (P : A → Prop) (Q : B -> Prop) (μ : distr A) (f : A -> distr B),
            gmlift_funct m1 μ P -> (forall a, P a -> gmlift_funct m2 (f a) Q) -> gmlift_funct (op m1 m2) (dbind f μ) Q;
    gmlift_mono : ∀ A `{Countable A} (m1 m2 : M) (P Q : A → Prop) (μ : distr A), (leq m1 m2) -> (forall a, P a -> Q a) ->
            gmlift_funct m1 μ P -> gmlift_funct m2 μ Q;
    gmlift_posR : ∀ A `{Countable A} (m : M) (P : A → Prop) (μ : distr A), gmlift_funct m μ P -> gmlift_funct m μ (λ a, P a /\ μ a > 0);
    gmlift_dzero : ∀ A `{Countable A} (m : M) (P : A → Prop), gmlift_funct m dzero P;
}.
