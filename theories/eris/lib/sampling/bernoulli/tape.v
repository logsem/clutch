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
    real_solver  |
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
  

  Definition tape_to_bernoulli (N M : nat) (t : list (fin (S M))) : list (fin 2) :=
    let f v :=
      if bool_decide (N ≤ fin_to_nat v)%nat 
      then 0%fin 
      else 1%fin
    in
    f <$> t.

  Lemma tape_to_bernoulli_def (N M : nat) (l : list (fin (S M))) :
    tape_to_bernoulli N M l = map (λ v, if bool_decide (N ≤ fin_to_nat v)%nat then 0%fin else 1%fin) l.
  Proof.
    reflexivity.
  Qed.
  
  (** When going from bernoulli tape to usual tape, there is some information we can't recover. Therefore 0 becomes M and 1 becomes N  *)
  Definition bernoulli_to_tape (M : nat) (b : list (fin 2)) : list (fin (S M)) :=
    let f v := 
      if bool_decide (v = 1)%fin 
      then 0%fin 
      else (nat_to_fin (Nat.lt_succ_diag_r M))
    in 
    f <$> b.
  
  Lemma bernoulli_to_tape_def (M : nat) (l : list (fin 2)) :
    bernoulli_to_tape M l = map (λ v, if bool_decide (v = 1)%fin then 0%fin else (nat_to_fin (Nat.lt_succ_diag_r M))) l.
  Proof.
    reflexivity.
  Qed.
  
  Lemma tape_to_bernoulli_translation (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    is_bernoulli_translation N M v l ↔ v = tape_to_bernoulli N M l.
  Proof.
    elim: l v => [[|hv tv]|h t IHt [|hv tv]] /= //; split => H //.
    - exact: Forall2_nil_2.
    - by apply Forall2_length in H.
    - by apply Forall2_length in H.
    - case (IHt tv) => [IHt1 IHt2]. 
      apply Forall2_cons in H as [[[-> HNleh] | [-> HhtapeN] ] Hforall]; 
        bool_decide; rewrite -IHt1 //.
    - case:H => -> ->.
      rewrite is_bernoulli_translation_cons.
      destruct (decide (N ≤ h))%nat as [HNleh | HhtapeN%not_le];
        bool_decide; rewrite IHt //.
  Qed.


  Lemma tape_to_bernoulli_app (N M : nat) (l1 l2 : list (fin (S M))) :
    tape_to_bernoulli N M (l1 ++ l2) = tape_to_bernoulli N M l1 ++ tape_to_bernoulli N M l2.
  Proof.
    apply fmap_app.
  Qed.
    
  Lemma tape_to_bernoulli_length (N M : nat) (l : list (fin (S M))) :
    length (tape_to_bernoulli N M l) = length l.
  Proof.
    apply fmap_length.
  Qed.

  Lemma bernoulli_to_tape_length (M : nat) (l : list (fin 2)) : length (bernoulli_to_tape M l) = length l.
  Proof.
    apply fmap_length.
  Qed.

  Lemma bernoulli_to_tape_to_bernoulli (N M : nat) (l : list (fin 2)) :
    (0 < N ≤ M)%nat →
    tape_to_bernoulli N M (bernoulli_to_tape M l) = l.
  Proof.
    move=> [zero_tape_N N_le_M].
    elim: l =>[// |h t IHt]; full_inv_fin.
    - rewrite /= IHt fin_to_nat_to_fin bool_decide_eq_true_2 //.
    - rewrite /= IHt bool_decide_eq_false_2 //.
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

  Lemma is_bernoulli_translation_app (N M : nat) (b_tape1 b_tape2 : list (fin 2)) (tape1 tape2 : list (fin (S M))) :
    is_bernoulli_translation N M b_tape1 tape1 → 
    is_bernoulli_translation N M b_tape2 tape2 → 
    is_bernoulli_translation N M (b_tape1 ++ b_tape2) (tape1 ++ tape2).
  Proof.
    intros ->%tape_to_bernoulli_translation 
           ->%tape_to_bernoulli_translation.
    apply tape_to_bernoulli_translation.
    by rewrite tape_to_bernoulli_app.
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
#[global] Opaque tape_to_bernoulli.
#[global] Opaque bernoulli_to_tape.