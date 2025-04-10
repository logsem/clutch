From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling.bernoulli.tape Require Import interface.


Module BernoulliTape : BernoulliTapeSpec.
  #[local] Ltac done ::= 
  solve[
    lia |
    lra |
    nra |
    real_solver  |
    tactics.done |
    auto
  ].
  Definition is_bernoulli_translation (N M : nat) : list (fin 2) → list (fin (S M)) → Prop :=
    Forall2 (
      λ v l, 
        (v = 0%fin ∧ N ≤ fin_to_nat l) ∨
        (v = 1%fin ∧ fin_to_nat l < N)%nat
    ).
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

  
  Lemma is_bernoulli_translation_dec (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    {is_bernoulli_translation N M v l} + {¬ is_bernoulli_translation N M v l}.
  Proof.
    rewrite is_bernoulli_translation_def.
    apply Forall2_dec => b_tape_h tape_h.
    repeat inv_fin b_tape_h =>[|b_tape_h]; destruct (decide (N ≤ tape_h)) as [? | ?%not_le];
    solve
      [ left; done 
      | right; move=> [[_ Hcontra] | [Hcontra _]] // ].
  Qed.

  Lemma is_bernoulli_translation_length (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    is_bernoulli_translation N M v l → length v = length l.
  Proof.
    rewrite is_bernoulli_translation_def.
    apply Forall2_length.
  Qed.
  
  Lemma is_bernoulli_translation_nil (N M : nat) :
    is_bernoulli_translation N M [] [].
  Proof.
    rewrite is_bernoulli_translation_def.
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
    rewrite is_bernoulli_translation_def.
    rewrite Forall2_cons; tauto.
  Qed.
  

  Definition tape_to_bernoulli (N M : nat) : list (fin (S M)) → list (fin 2) :=
    map (λ v, if bool_decide (N ≤ fin_to_nat v)%nat then 0%fin else 1%fin).

  Lemma tape_to_bernoulli_def (N M : nat) (l : list (fin (S M))) :
    tape_to_bernoulli N M l = map (λ v, if bool_decide (N ≤ fin_to_nat v)%nat then 0%fin else 1%fin) l.
  Proof.
    reflexivity.
  Qed.
  
  Definition bernoulli_to_tape (M : nat) : list (fin 2) → list (fin (S M)) :=
    map (λ v, if bool_decide (v = 1)%fin then 0%fin else (nat_to_fin (Nat.lt_succ_diag_r M))).
  
  Lemma bernoulli_to_tape_def (M : nat) (l : list (fin 2)) :
    bernoulli_to_tape M l = map (λ v, if bool_decide (v = 1)%fin then 0%fin else (nat_to_fin (Nat.lt_succ_diag_r M))) l.
  Proof.
    reflexivity.
  Qed.

  
  Lemma tape_to_bernoulli_translation (N M : nat) (v : list (fin 2)) (l : list (fin (S M))) :
    is_bernoulli_translation N M v l ↔ v = tape_to_bernoulli N M l.
  Proof.
    elim: l v => [[|hv tv]|h t IHt [|hv tv]] /= //; split => H //;
    [apply is_bernoulli_translation_nil | by apply Forall2_length in H..| |].
    - destruct (IHt tv) as [IHt1 IHt2]. 
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
    apply map_app.
  Qed.
    
  Lemma tape_to_bernoulli_length (N M : nat) (l : list (fin (S M))) :
    length (tape_to_bernoulli N M l) = length l.
  Proof.
    apply map_length.
  Qed.

  Lemma bernoulli_to_tape_length (M : nat) (l : list (fin 2)) : length (bernoulli_to_tape M l) = length l.
  Proof.
    apply map_length.
  Qed.

  Lemma bernoulli_to_tape_to_bernoulli (N M : nat) (l : list (fin 2)) :
    (0 < N ≤ M)%nat →
    tape_to_bernoulli N M (bernoulli_to_tape M l) = l.
  Proof.
    move=> [zero_tape_N N_le_M].
    elim: l =>[// |h t IHt].
    inv_fin h;
      last (move=>h; inv_fin h; last (move=>h; inv_fin h));
      simpl;
      rewrite IHt;
      first rewrite fin_to_nat_to_fin;
      case_bool_decide;
      done.
  Qed.
    
  Lemma is_bernoulli_translation_0 (N M : nat) (k : fin (S M)) :
    N ≤ k →
    is_bernoulli_translation N M [0%fin] [k].
  Proof.
    move=>?.
    apply Forall2_cons =>//.
  Qed.

  Lemma is_bernoulli_translation_1 (N M : nat) (k : fin (S M)) :
    k < N →
    is_bernoulli_translation N M [1%fin] [k].
  Proof.
    move=>?.
    apply Forall2_cons =>//.
  Qed.

End BernoulliTape.
