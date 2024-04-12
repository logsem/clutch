From stdpp Require Import fin countable finite.
From clutch.prelude Require Import base classical.
Set Default Proof Using "Type*".

Section fin.
  Lemma enum_fin_seq n: fin_to_nat <$> enum (fin n) = seq 0 n.
  Proof.
    induction n.
    - done.
    - simpl. f_equal.
      rewrite <-fmap_S_seq. rewrite <-IHn.
      simpl. clear.
      induction (fin_enum n).
      + done.
      + simpl. by f_equal.
  Qed.

  Lemma seq_enum_fin (n:nat) :
    (fun x => match le_lt_dec (S n) x with
           | left _ => 0%fin
           | right h => nat_to_fin h
           end) <$> seq 0 (S n) = enum (fin (S n)).
  Proof.
    induction n as [|n IHn]; first done.
    rewrite -cons_seq. rewrite fmap_cons.
    replace (enum _) with (fin_enum (S (S n))) by done.
    rewrite /fin_enum. f_equal.
    replace (_::_) with (enum (fin (S n))) by done.
    rewrite <-IHn. rewrite <-seq_shift.
    replace (map _ _) with (S <$> (seq 0 (S n))) by done.
    rewrite <- !list_fmap_compose. apply Forall_fmap_ext_1.
    clear.
    rewrite list.Forall_forall.
    intros x Hx.
    rewrite elem_of_seq in Hx.
    replace (_ x) with (match le_lt_dec (S (S n)) (S x) with
                | left _ => 0%fin
                | right h => nat_to_fin h
                        end) by done.
    replace ((_∘_) x) with (FS  (match le_lt_dec (S n) x with
                     | left _ => 0%fin
                     | right h => nat_to_fin h
                                 end)) by done.
    destruct (le_lt_dec (S (S n)) (S x)) eqn:H1;
      destruct (le_lt_dec (S n) x) eqn:H2; try lia.
    apply fin_to_nat_inj. simpl. 
    by rewrite !fin_to_nat_to_fin.
  Qed.
  
  Lemma fin_to_nat_encode_nat {n:nat} (x:fin n): fin_to_nat x = encode_nat x.
  Proof.
    rewrite /encode_nat/encode/=. rewrite Nat2Pos.id.
    { lia. }
    rewrite Nat.pred_succ.
    induction x.
    - simpl; lia.
    - simpl. rewrite IHx.
      rewrite list_find_fmap.
      erewrite (list_find_ext (eq (FS x) ∘ FS) (eq x)); last first.
      { intros. split; simpl; naive_solver. }
      edestruct (list_find (eq x) (fin_enum n)) eqn:H1.
      + done.
      + exfalso. 
        pose proof elem_of_enum x as H.
        epose proof list_find_elem_of _ _  x _ _ as H0.
        erewrite H1 in H0. by eapply is_Some_None.
        Unshelve.
        * done.
        * done.
  Qed.

End fin.
