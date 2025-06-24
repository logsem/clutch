(**
  This file implements contains functions to transform usual probability tapes into ones using the bernoulli distribution, as well as lemmas to reason about them
*)


From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.

Section BernoulliTape.
  #[local] Ltac done ::= 
  solve[
    lia |
    lra |
    nra |
    tactics.done |
    auto
  ].

  (** The translation mimics the behavior of the bernoulli function *)
  Definition is_bernoulli_translation (N M : nat) : list (fin 2) → list (fin (S M)) → Prop :=
    Forall2 (
      λ v l, 
        (v = 0%fin ∧ N ≤ fin_to_nat l) ∨
        (v = 1%fin ∧ fin_to_nat l < N)
      )%nat.
  
  Lemma is_bernoulli_translation_def (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    is_bernoulli_translation N M v l =
    Forall2 (
      λ v l, 
        (v = 0%fin ∧ N ≤ fin_to_nat l) ∨
        (v = 1%fin ∧ fin_to_nat l < N)%nat
    ) v l.
  Proof.
    reflexivity.
  Qed.

  Lemma is_bernoulli_translation_length (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    is_bernoulli_translation N M v l → length v = length l.
  Proof.
    apply Forall2_length.
  Qed.
  
  Lemma is_bernoulli_translation_nil (N M : nat) :
    is_bernoulli_translation N M [] [].
  Proof.
    apply Forall2_nil_2.
  Qed.

  Lemma is_bernoulli_translation_cons 
      (N M : nat) 
      (b_tape_h : fin 2) (tape_h : fin (S M)) 
      (b_tape : list (fin 2)) (tape : list (fin (S M))) :
    is_bernoulli_translation N M (b_tape_h :: b_tape) (tape_h :: tape) <->
    (b_tape_h = 0%fin ∧ (N ≤ tape_h)%nat ∧ is_bernoulli_translation N M b_tape tape) ∨
    (b_tape_h = 1%fin ∧ (tape_h < N)%nat ∧ is_bernoulli_translation N M b_tape tape)
  .
  Proof.
    rewrite is_bernoulli_translation_def Forall2_cons. tauto.
  Qed.
   
  Lemma is_bernoulli_translation_0 (N M : nat) (k : fin (S M)) :
    N ≤ k →
    is_bernoulli_translation N M [0%fin] [k].
  Proof.
    move=>?.
    apply Forall2_cons; auto.
  Qed.

  Lemma is_bernoulli_translation_1 (N M : nat) (k : fin (S M)) :
    k < N →
    is_bernoulli_translation N M [1%fin] [k].
  Proof.
    move=>?.
    apply Forall2_cons; auto.
  Qed.

  Lemma is_bernoulli_translation_app (N M : nat) : ∀ (b_tape1 b_tape2 : list (fin 2)) (tape1 tape2 : list (fin (S M))),
    is_bernoulli_translation N M b_tape1 tape1 → 
    is_bernoulli_translation N M b_tape2 tape2 → 
    is_bernoulli_translation N M (b_tape1 ++ b_tape2) (tape1 ++ tape2).
  Proof.
    unfold is_bernoulli_translation.
    elim=>[|htape_1 ttape1 IH] b_tape2 tape1 tape2 is_tl1 is_tl2.
    - by apply Forall2_nil_inv_l in is_tl1 as ->.
    - apply Forall2_cons_inv_l in is_tl1 as (ht1 & tt1 & P1 & is_tltt1 & ->).
      simpl.
      apply Forall2_cons.
      split; first done.
      by apply IH.
  Qed.

  Lemma is_bernoulli_translation_app_0 
    (N M : nat) (k : fin (S M))
    (b_tape : list (fin 2)) (tape : list (fin (S M))) :
  N ≤ k →
  is_bernoulli_translation N M b_tape tape →
  is_bernoulli_translation N M (b_tape ++ [0%fin]) (tape ++ [k]).
  Proof.
    add_hint is_bernoulli_translation_app.
    add_hint is_bernoulli_translation_0.
    done.
  Qed.

  Lemma is_bernoulli_translation_app_1 
    (N M : nat) (k : fin (S M))
    (b_tape : list (fin 2)) (tape : list (fin (S M))) :
  k < N →
  is_bernoulli_translation N M b_tape tape →
  is_bernoulli_translation N M (b_tape ++ [1%fin]) (tape ++ [k]).
  Proof.
    add_hint is_bernoulli_translation_app.
    add_hint is_bernoulli_translation_1.
    done.
  Qed.

End BernoulliTape.

#[global] Opaque is_bernoulli_translation.
