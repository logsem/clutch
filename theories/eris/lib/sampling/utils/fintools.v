From stdpp Require Import fin finite ssreflect.
#[local] Set Asymmetric Patterns.

Section fintools.

  Fixpoint fin_S_inj {n : nat} (m : fin n) : fin (S n) :=
    match m with
    | Fin.F1 _ => Fin.F1
    | Fin.FS _ k=> Fin.FS (fin_S_inj k)
    end.

  Lemma fin_S_inj_to_nat : ∀ (m : nat) (n : fin m), fin_to_nat n = fin_to_nat (fin_S_inj n).
  Proof.
    intros m n.
    induction n; first done.
    simpl.
    by f_equal.
  Qed.

  Lemma fin_to_nat_FS : ∀ (m : nat) (n : fin m), fin_to_nat (FS n) = S (fin_to_nat n).
  Proof.
    intros m n.
    reflexivity.
  Qed.

  Lemma nat_to_fin_proof_ext : ∀ (k n : nat) (H1 H2 : k < n), nat_to_fin H1 = nat_to_fin H2.
  Proof.
    intros k.
    induction k.
    - intros n H1 H2. destruct n; last done. inversion H1.
    - intros n H1 H2.
      destruct n; first inversion H1.
      simpl.
      f_equal.
      apply IHk.
  Qed.
  
  Lemma enum_fin_last : ∀ (n : nat) (H : n < S n), last (enum (fin (S n))) = Some (nat_to_fin H).
  Proof.
    intros n.
    induction n; first done.
    intros H.
    replace (last (enum (fin (S (S n))))) with (last (FS <$> enum (fin (S n)))); last done.
    rewrite fmap_last (IHn (Nat.lt_succ_diag_r n)).
    simpl.
    do 2 f_equal.
    apply nat_to_fin_proof_ext.
  Qed.

  Lemma enum_fin_split : ∀ (n : nat) (H : n < S n), enum (fin (S n)) = (fin_S_inj <$> enum (fin n)) ++ [nat_to_fin H].
  Proof.
    intros n.
    induction n; first done.
    intros H.
    replace (enum (fin (S (S n)))) with (0%fin::(FS <$> enum (fin (S n)))); last done.
    rewrite {1}IHn /=.
    f_equal.
    rewrite fmap_app /=.
    f_equal; last first.
    { do 2 f_equal.
      apply nat_to_fin_proof_ext.
    }
    fold (@fmap _ list_fmap).
    rewrite -!list_fmap_compose.
    apply list_fmap_ext.
    done.
  Qed.

    
  Fixpoint fin_succ {n : nat} (i : fin n) : fin n :=
    match i as i0 in fin n0 return fin n0 with
    | Fin.F1 n0 => match n0 as n1 in nat return fin (S n1) with
                   | 0 => Fin.F1
                   | (S n1) => Fin.FS Fin.F1
                   end
    | Fin.FS n0 j => Fin.FS (fin_succ j)
    end.

  Lemma fin_succ_to_nat : ∀ (n : nat) (k : fin n), fin_to_nat (fin_succ k) = min (S k) (n - 1).
  Proof.
    elim=>[|n IH] k; first inv_fin k.
    - inv_fin k.
      + simpl.
        case: n IH => [//|?? //].
      + move=>i /=.
        destruct n; first inv_fin i.
        simpl.
        f_equal.
        rewrite IH.
        simpl.
        rewrite Nat.sub_0_r //.
  Qed.
  
  Fixpoint fin_hsum {m n : nat} (i : fin m) : fin n → fin n :=
  match i with
  | Fin.F1 _ => λ x, x
  | Fin.FS n0 i0 => fin_hsum i0 ∘ fin_succ
  end.


  Lemma fin_hsum_min : ∀ (m n : nat) (i : fin m) (j : fin n), fin_to_nat (fin_hsum i j) = min (fin_to_nat i + fin_to_nat j) (n - 1).
  Proof.
    elim=>[|m IH] n i j; inv_fin i.
    - simpl.
      rewrite Nat.min_l //.
      assert (j < n)%nat by apply fin_to_nat_lt.
      lia.
    - move=> i.
      rewrite IH fin_succ_to_nat. 
      destruct (decide (S j < n)%nat) as [Sj_lt_n | St_ge_n].
      + rewrite (Nat.min_l (S j)); last lia.
        rewrite Nat.add_succ_r //.
      + rewrite (Nat.min_r (S j)); last lia.
        rewrite !Nat.min_r; lia.
  Qed.

  Lemma fin_hsum_succ :
    ∀ (m n : nat),
    ∀ (i : fin m) (j : fin n), fin_hsum i (fin_succ j) = fin_succ (fin_hsum i j).
  Proof.
    elim=>[| m IH] n i j; inv_fin i.
    - reflexivity.
    - move=>i /=.
      rewrite IH //.
  Qed.

  Lemma fin_hsum_FS :
    ∀ (m n : nat),
    ∀ (i : fin m) (j : fin n), FS (fin_hsum i j) = fin_hsum i (FS j).
  Proof.
    elim=>[| m IH] n i j; inv_fin i.
    - reflexivity.
    - move=>i /=.
      rewrite IH //.
  Qed.
  
  Definition fin_sum {n : nat} := @fin_hsum n n.

  Fixpoint fin_max (n : nat) : fin (S n) :=
    match n with
    | 0 => Fin.F1
    | S m => Fin.FS (fin_max m)
    end.

  Lemma fin_succ_max : ∀ (n : nat), fin_succ (fin_max n) = fin_max n.
  Proof.
    elim=>[|n IH] /= //.
    f_equal.
    apply IH.
  Qed.

  Lemma fin_hsum_max : ∀ (m n : nat) (i : fin m), fin_hsum i (fin_max n) = fin_max n.
  Proof.
    move=>m n.
    elim=>[k |k i IH] /= //.
    rewrite fin_succ_max.
    apply IH.
  Qed.

  Lemma fin_succ_fix_max : ∀ (n : nat) (i : fin (S n)), fin_succ i = i → i = fin_max n.
  Proof.
    elim=>[|n IH] i Heq.
    - inv_fin i; first done.
      move=>i. inv_fin i.
    - inv_fin i.
      + move=>/= contra.
        discriminate contra.
      + move=>i /= Heq.
        f_equal.
        apply IH, Fin.FS_inj, Heq.
  Qed.

  Lemma fin_max_sum :
    ∀ (n : nat) (i : fin (S n)), fin_sum (fin_max n) i = fin_max n.
  Proof.
    elim=>[i |n IH i] /=.
    - inv_fin i; first reflexivity.
      move=> i.
      inv_fin i.
    - inv_fin i.
      + unfold fin_sum.
        simpl.
        rewrite -fin_hsum_FS.
        fold (@fin_sum (S n)).
        rewrite IH //.
      + move=> i.
        unfold fin_sum.
        rewrite -fin_hsum_FS.
        simpl.
        fold (@fin_sum (S n)).
        rewrite IH //.
  Qed.
  
  Lemma fin_max_hsum :
    ∀ (m n : nat),
    (n ≤ m)%nat →
    ∀ (i : fin (S n)), fin_hsum (fin_max m) i = fin_max n.
  Proof.
    move=>m n.
    elim=>[i|k n_le_k IH].
    - simpl.
      fold (@fin_sum (S n)).
      apply fin_max_sum.
    - move=>i.
      simpl.
      rewrite IH //.
  Qed.

  Lemma not_max_FS_not_max :
    ∀ (n : nat) (k : fin (S n)),
    k ≠ fin_max n →
    FS k ≠ fin_max (S n).
  Proof.
    move=> /= n k k_not_max contra.
    by apply FS_inj in contra.
  Qed.

  Lemma FS_not_max_inv :
    ∀ (n : nat) (k : fin (S n)),
    FS k ≠ fin_max (S n) →
    k ≠ fin_max n.
  Proof.
    move=> /= n k Sk_not_max contra.
    apply Sk_not_max.
    by f_equal.
  Qed.
  
  Lemma fin_succ_hsum :
    ∀ (m n : nat),
    (n ≤ m)%nat →
    ∀ (i : fin m) (j : fin n), fin_hsum (fin_succ i) j = fin_succ (fin_hsum i j).
  Proof.
    move=> m n n_le_m i j.
    destruct m; first inv_fin i.
    destruct n; first inv_fin j.
    destruct (decide (i = fin_max m)) as [-> | i_not_max].
    - rewrite fin_succ_max fin_max_hsum; last lia.
      rewrite fin_succ_max //.
    - generalize dependent n.
      induction m.
      + inv_fin i; first done.
        move=>i. inv_fin i.
      + inv_fin i.
        * move=> _ //.
        * move=>i i_not_max n Hle j.
          apply FS_not_max_inv in i_not_max.
          inv_fin j.
          -- destruct n; simpl.
             ++ rewrite IHm; try done.
                lia.
             ++ rewrite -!fin_hsum_FS /=.
                f_equal.
                rewrite IHm; try done.
                lia.
          -- move=>j.
            rewrite -!fin_hsum_FS /=.
            f_equal.
            destruct n; first inv_fin j.
            rewrite IHm; try done.
            lia.
  Qed.

  Lemma fin_hsum_assoc : ∀ (k m n : nat),
                           (n ≤ m)%nat →
                           ∀ (h : fin k) (i : fin m) (j : fin n), fin_hsum h (fin_hsum i j) = fin_hsum (fin_hsum h i) j.
  Proof.
    elim=>[|k IH] m n m_le_n h i j.
    - inv_fin h.
    - inv_fin h.
      + reflexivity.
      + move=> h.
        simpl.
        rewrite -IH /=; last done.
        f_equal.
        rewrite fin_succ_hsum //.
  Qed.
  
  Lemma fin_hsum_comm : ∀ (k m n : nat) (h : fin k) (i : fin m) (j : fin n),
    fin_hsum h (fin_hsum i j) = fin_hsum i (fin_hsum h j).
  Proof.
    elim=>[|k IH] m n h i j; inv_fin h; first reflexivity.
    move=>h.
    rewrite /= -IH.
    f_equal.
    rewrite fin_hsum_succ //.
  Qed.

  Lemma fin_sum_0 : ∀ (k : nat) (i : fin (S k)), fin_sum i 0%fin = i.
  Proof.
    elim=>[|k IH] i; inv_fin i; try done.
    - move=>i. inv_fin i.
    - move=>i.
      rewrite /fin_sum /= -fin_hsum_FS.
      f_equal.
      apply IH.
  Qed.

  Definition fin_sum_list (m k : nat) (l : list (fin m)) : fin (S k) :=
    foldr fin_hsum 0%fin l.

  Lemma fin_ind_fixed : ∀ (n : nat) (P : fin (S n) → Prop), P 0%fin → (∀ (i : fin (S n)), i ≠ fin_max n → P i → P (fin_succ i)) → ∀ (i : fin (S n)), P i.
  Proof.
    elim=>[|n IH] P P_0 P_S i; (inv_fin i; first done).
    - move=>i. inv_fin i.
    - move=>i.
      apply (IH (P ∘ FS)).
      { simpl. apply (P_S 0%fin), P_0. discriminate. }
      move=>j j_not_max P_Sj.
      apply (P_S (FS j)), P_Sj.
      by apply not_max_FS_not_max.
  Qed.

  Lemma repeat_not_max : ∀ (A : Set) (a : A) (k : nat) (i : fin (S k)), i ≠ fin_max k → repeat a (fin_succ i) = a::repeat a i.
  Proof.
    move=>A a.
    elim=>[|k IH] i.
    - inv_fin i.
      + move=>contra.
        contradict contra.
        reflexivity.
      + move=>i. inv_fin i.
    - inv_fin i.
      + move=>i_not_max //.
      + move=> i i_not_max /=.
        rewrite IH //.
        by apply FS_not_max_inv.
  Qed.

  Lemma fin_sum_repeat_0 : ∀ (k m : nat), fin_sum_list 2 k (repeat (0%fin : fin 2) m) = 0%fin.
  Proof.
    intros k.
    induction m.
    - reflexivity.
    - simpl. rewrite IHm //.
  Qed.
  
  Lemma fin_sum_repeat_1 : ∀ (k : nat) (i : fin (S k)), fin_sum_list 2 k (repeat (1%fin : fin 2) i) = i.
  Proof.
    intros k.
    apply fin_ind_fixed.
    - reflexivity.
    - move=>i i_not_max IH.
      rewrite repeat_not_max /=; last done.
      f_equal.
      apply IH.
  Qed.

  Lemma fin_hsum_to_nat :
    ∀ (n k : nat) (i : fin n) (j : fin (S k)), fin_to_nat (fin_hsum i j) = (fin_to_nat i + fin_to_nat j) `min` k.
  Proof.
    elim=>[|n IH] k i j; inv_fin i.
    - simpl.
      rewrite Nat.min_l //.
      pose proof (fin_to_nat_lt j).
      lia.
    - move=>i.
      destruct k as [|k].
      + simpl.
        inv_fin j; last (move=>j; inv_fin j).
        rewrite fin_hsum_max //.
      + simpl.
        rewrite IH fin_succ_to_nat.
        lia.
  Qed.
  
  Lemma fin_sum_list_le : ∀ (n m k : nat) (l : list (fin (S m))),
    length l = k →
    fin_to_nat (fin_sum_list (S m) n l) ≤ k * m.
  Proof.
    move=>n m k l.
    elim: l k =>[|h t IH] k <-.
    - reflexivity.
    - simpl.
      specialize (IH (length t) eq_refl).
      rewrite fin_hsum_to_nat.
      pose proof (fin_to_nat_lt h).
      lia.
  Qed.
 
  Lemma fin_succ_inj : ∀ (n : nat) (k : fin n), fin_succ (fin_S_inj k) = FS k.
  Proof.
    elim=>[|n IH] k; first inv_fin k.
    inv_fin k; first reflexivity.
    move=>k /=.
    by f_equal.
  Qed.

  Lemma fin_S_inj_not_max :
    ∀ (n : nat) (k : fin (S n)),
    k ≠ fin_max n →
    fin_S_inj (fin_succ k) = FS k.
  Proof.
    elim=>[|n IH] k k_not_max; inv_fin k; try done.
    { move=>k; inv_fin k. }
    move=>k k_not_max /=.
    f_equal.
    apply IH.
    by apply FS_not_max_inv.
  Qed.
    
  Lemma fin_succ_not_max_to_nat :
    ∀ (n : nat) (k : fin (S n)),
    k ≠ fin_max n →
    fin_to_nat (fin_succ k) = S (fin_to_nat k).
  Proof.
    elim=>[|n IH] k k_not_max.
    { inv_fin k; first done.
      move=>k. inv_fin k.
    } 
    inv_fin k; first done.
    move=>k /= k_not_max.
    f_equal.
    by apply IH, FS_not_max_inv.
  Qed.

  Lemma fin_max_to_nat : ∀ (n : nat), fin_to_nat (fin_max n) = n.
  Proof.
    elim=>[//|n IH] /=.
    by f_equal.
  Qed.

  Lemma fin_not_max_to_nat :
    ∀ (n : nat) (k : fin (S n)),
    k ≠ fin_max n →
    fin_to_nat k < n.
  Proof.
    elim=>[|n IH] k; inv_fin k; first done.
    { move=>k; inv_fin k. }
    { move=>_ /=. lia. }
    move=>k k_not_max /=.
    rewrite -Nat.succ_lt_mono.
    apply IH.
    by apply FS_not_max_inv.
  Qed.
  
  Lemma fin_sum_list_lt_max :
    ∀ (n : nat) (l : list (fin 2)),
    length l < n →
    fin_sum_list 2 n l ≠ fin_max n.
  Proof.
    move=>n l len_l_lt_n contra.
    assert (fin_to_nat (fin_sum_list 2 n l) = n)as sum_n by rewrite contra fin_max_to_nat //.
    pose proof (fin_sum_list_le n 1 _ l eq_refl) as sum_to_nat.
    rewrite sum_n in sum_to_nat.
    lia.
  Qed.
  
  Lemma fin_inj_sum :
    ∀ (n : nat) (l : list (fin 2)),
    length l ≤ n →
    fin_sum_list 2 (S n) l = fin_S_inj (fin_sum_list 2 n l).
  Proof.
    move=>n.
    elim=>[//|h t IH] /= le_h_t.
    rewrite IH; last lia.
    inv_fin h; first done.
    move=>i.
    inv_fin i; last (move=>i; inv_fin i).
    simpl.
    rewrite fin_succ_inj fin_S_inj_not_max //.
    by apply fin_sum_list_lt_max.
  Qed.
  
  
  End fintools.
