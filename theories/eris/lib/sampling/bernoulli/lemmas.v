(* This file contains some lemmas used in the specification of bernoulli. They are quite specific, and probably won't be useful in other places. Most of them are local as only the final lemma is useful in bernoulli.v *)

From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.


#[local] Open Scope R.

#[local] Ltac done ::= 
  solve[
    lia |
    lra |
    nra |
    real_solver  |
    tactics.done |
    auto
  ].

#[local] Lemma foldr_plus_app (l1 l2 : list R) (acc : R) :
  foldr Rplus acc (l1 ++ l2) = foldr Rplus 0 l1 + foldr Rplus acc l2.
Proof.
  elim: l1 => //=.
Qed.


#[local] Lemma fmap_prop {A B : Type} (l : list A) (f : A → B) (P₁ : A → Prop) (P₂ : B → Prop) :
  (∀ a, P₁ a → P₂ (f a)) →
  (∀ a, a ∈ l → P₁ a) →
  ∀ b, b ∈ (f <$> l) → P₂ b.
Proof.
  add_hint @elem_of_list_here.
  add_hint @elem_of_list_further.
  move=> HPs.
  elim: l => [_ ? /= HinNil| a l IH Hforall /= b Hin].
  - by apply not_elem_of_nil in HinNil.
  - apply elem_of_cons in Hin as [-> | Hin]; done.
Qed.

#[local] Lemma forall_list_eq {A : Type} (l : list A) (a : A) :
  (∀ e, e ∈ l → e = a) →
  l = repeat a (length l).
Proof.
  add_hint @elem_of_list_here.
  add_hint @elem_of_list_further.
  elim: l => //= e ? IH Hl.
  rewrite (Hl e) // -IH //.
Qed.

#[local] Lemma map_seq_if_lt {A : Type} (e1 e2 : A) (N : nat):
  (λ x, if bool_decide (x < N)%nat then e1 else e2) <$> seq 0 N = repeat e1 N.
Proof.
  set f := (λ x : nat, if bool_decide (x < N)%nat then e1 else e2).
  assert (Heq: ∀ e, e ∈ f <$> seq 0 N → e = e1). {
    apply (fmap_prop _ f (λ n, n < N)%nat) => [a Ha | a Ha].
    - rewrite /f. by bool_decide.
    - by apply elem_of_seq in Ha as [_ Ha].
  }
  replace N with (length (f <$> seq 0 N)) at 2 by rewrite fmap_length seq_length //.
  exact: forall_list_eq Heq.
Qed.

#[local] Lemma map_seq_if_ge {A : Type} (e1 e2 : A) (N L : nat):
  (λ x, if bool_decide (x < N)%nat then e1 else e2) <$> seq N L = repeat e2 L.
Proof.
  set f := (λ x : nat, if bool_decide (x < N)%nat then e1 else e2).
  assert (Heq: ∀ e, e ∈ f <$> seq N L → e = e2). {
    apply (fmap_prop _ f (λ n, n >= N)%nat) => a Ha.
    - rewrite /f. by bool_decide.
    - by apply elem_of_seq in Ha as [].
  }
  rewrite (forall_list_eq _ _ Heq) fmap_length seq_length //.
Qed.

#[local] Lemma foldr_plus_repeat (ε : R) (L : nat) :
  foldr Rplus 0 (repeat ε L) = ε * L.
Proof.
  elim: L =>> //.
  rewrite S_INR //=.
Qed.


(** This is the main lemma of the file. It is used to prove error credit scaling for the bernoulli implementation *)
Lemma SeriesC_case (N M : nat) (ε1 ε2 : R) :
  (N <= S M)%nat →
  SeriesC (
    λ x : fin (S M), 
    if bool_decide (fin_to_nat x < N)%nat
    then ε2
    else ε1
  ) = (ε1 * (S M - N) + ε2 * N)%R.
Proof.
  move=> ?.
  rewrite SeriesC_finite_foldr -foldr_fmap.
  trans (
    foldr Rplus 0
    ((λ x : nat, if bool_decide (x < N)%nat then ε2 else ε1) ∘ fin_to_nat <$> enum (fin (S M)))
  ); first reflexivity.
  rewrite list_fmap_compose fin.enum_fin_seq.
  replace (S M) with (N + (S M - N))%nat at 1 by lia.
  rewrite seq_app.
  rewrite fmap_app foldr_plus_app Rplus_comm.
  rewrite map_seq_if_ge map_seq_if_lt.
  rewrite !foldr_plus_repeat minus_INR //.
Qed.