From clutch.eris Require Import eris.


Module Type BernoulliTapeSpec.
  Parameter is_bernoulli_translation : 
    ∀ (N M : nat), list (fin 2) → list (fin (S M)) → Prop.
  
  Parameter tape_to_bernoulli : ∀ (N M : nat), list (fin (S M)) → list (fin 2).
  Parameter bernoulli_to_tape : ∀ (M : nat), list (fin 2) → list (fin (S M)).

  Parameter is_bernoulli_translation_length :
    ∀ (N M : nat) (b_tape : list (fin 2)) 
      (tape : list (fin (S M))),
    is_bernoulli_translation N M b_tape tape → length b_tape = length tape.
  
  Parameter is_bernoulli_translation_nil :
    ∀ (N M : nat),
    is_bernoulli_translation N M [] [].
  
  Parameter is_bernoulli_translation_cons :
    ∀ (N M : nat) 
      (b_tape_h : fin 2) (tape_h : fin (S M)) 
      (b_tape : list (fin 2)) (tape : list (fin (S M))),
    is_bernoulli_translation N M (b_tape_h :: b_tape) (tape_h :: tape)
    ↔
    (b_tape_h = 0%fin ∧ (N ≤ tape_h)%nat ∧ is_bernoulli_translation N M b_tape tape) ∨
    (b_tape_h = 1%fin ∧ (tape_h < N)%nat ∧ is_bernoulli_translation N M b_tape tape)
  .
  
  Parameter tape_to_bernoulli_translation : 
    ∀ (N M : nat) (b_tape : list (fin 2)) (tape : list (fin (S M))),
    is_bernoulli_translation N M b_tape tape ↔ b_tape = tape_to_bernoulli N M tape.

  Parameter tape_to_bernoulli_app :
    ∀ (N M : nat) (t1 t2 : list (fin (S M))),
    tape_to_bernoulli N M (t1 ++ t2) =
    tape_to_bernoulli N M t1 ++ tape_to_bernoulli N M t2.
  
  Parameter tape_to_bernoulli_length :
    ∀ (N M : nat) (tape : list (fin (S M))),
    length (tape_to_bernoulli N M tape) = length tape.

  Parameter bernoulli_to_tape_length :
    ∀ (M : nat) (tape : list (fin 2)),
    length (bernoulli_to_tape M tape) = length tape.
  
  Parameter bernoulli_to_tape_to_bernoulli :
    ∀ (N M : nat) (b_tape : list (fin 2)),
    0 < N ≤ M →
    tape_to_bernoulli N M (bernoulli_to_tape M b_tape) = b_tape.
  
  Parameter is_bernoulli_translation_0 : 
    ∀ (N M : nat) (k : fin (S M)),
    N ≤ k →
    is_bernoulli_translation N M [0%fin] [k].
  
  Parameter is_bernoulli_translation_1 :
    ∀ (N M : nat) (k : fin (S M)),
    k < N →
    is_bernoulli_translation N M [1%fin] [k].

End BernoulliTapeSpec.

Module BernoulliTapeLemmas (M : BernoulliTapeSpec).
  Import M.
  Lemma is_bernoulli_translation_app (N M : nat) (b_tape1 b_tape2 : list (fin 2)) (tape1 tape2 : list (fin (S M))) :
    is_bernoulli_translation N M b_tape1 tape1 → 
    is_bernoulli_translation N M b_tape2 tape2 → 
    is_bernoulli_translation N M (b_tape1 ++ b_tape2) (tape1 ++ tape2).
  Proof.
    move=>> Htrans1 Htrans2.
    apply tape_to_bernoulli_translation in Htrans1.
    apply tape_to_bernoulli_translation in Htrans2.
    apply tape_to_bernoulli_translation.
    by rewrite tape_to_bernoulli_app Htrans1 Htrans2.
  Qed.

  Lemma is_bernoulli_translation_app_0 
    (N M : nat) (k : fin (S M))
    (b_tape : list (fin 2)) (tape : list (fin (S M))) :
  N ≤ k →
  is_bernoulli_translation N M b_tape tape →
  is_bernoulli_translation N M (b_tape ++ [0%fin]) (tape ++ [k]).
  Proof.
    move=> H_N_le_k H_ber_trans.
    by apply 
          is_bernoulli_translation_app, 
          is_bernoulli_translation_0.
  Qed.

  Lemma is_bernoulli_translation_app_1 
    (N M : nat) (k : fin (S M))
    (b_tape : list (fin 2)) (tape : list (fin (S M))) :
  k < N →
  is_bernoulli_translation N M b_tape tape →
  is_bernoulli_translation N M (b_tape ++ [1%fin]) (tape ++ [k]).
  Proof.
    move=> H_N_le_k H_ber_trans.
    by apply 
          is_bernoulli_translation_app, 
          is_bernoulli_translation_1.
  Qed.



End BernoulliTapeLemmas.

