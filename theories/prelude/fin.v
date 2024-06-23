Require Import FinFun.
From stdpp Require Import fin countable finite.
From clutch.prelude Require Import base classical stdpp_ext.
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


  Lemma length_enum_fin n: length (fin_enum n) = n.
  Proof.
    induction n; [done|simpl].
    rewrite fmap_length. naive_solver.
  Qed.

  Lemma seq_enum_fin (n:nat) :
    (fun x => match le_lt_dec (S n) x with
           | left _ => 0%fin
           | right h => nat_to_fin h
           end) <$> seq 0 (S n) = enum (fin (S n)).
  Proof.
    apply list_eq.
    intros i.
    destruct (decide(i<S n)) as [H|H].
    - apply (option_fmap_eq_inj _ fin_to_nat_inj).
      rewrite <-!list_lookup_fmap. rewrite enum_fin_seq.
      f_equal. rewrite -list_fmap_compose.
      rewrite <-list_fmap_id.
      apply list_fmap_ext.
      intros ??.
      rewrite lookup_seq. intros [].
      simpl.
      repeat case_match; try rewrite fin_to_nat_to_fin; lia.
    - rewrite !lookup_ge_None_2; last done.
      + rewrite fmap_length. rewrite seq_length. lia.
      + rewrite length_enum_fin. lia.
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

  Ltac fin_solver := 
    by repeat first [apply fin_to_nat_inj|simpl|lia].

  Program Definition fin_cast {N:nat} (M:nat) {_:0<M} (x:fin N): (fin M).
  Proof.
    destruct (decide (N<=M)%nat) as [K|K].
    - replace (M) with (N+ (M-N)) by lia.
      exact (Fin.L _ x).
    - destruct (decide (fin_to_nat x < M)) as [G|G].
      + exact (nat_to_fin G).
      + assert (M-1<M) as Hineq by lia.
        exact (nat_to_fin Hineq).
  Qed.

  Definition fin_force (M : nat) (n : nat) : fin (S M) :=
    match le_lt_dec (S M) n with
    | left _ => nat_to_fin (Nat.lt_succ_diag_r M) 
    | right h => nat_to_fin h
    end.

  Lemma restr_bij_fin N f `{Bij nat nat f} :
    (forall n, n < N -> f n < N) ->
    exists (g : fin N -> fin N), (Bij g) /\
                             (forall x : (fin N), fin_to_nat (g x) = f (fin_to_nat x)).
  Proof.
    intros Hdom.
    exists (Fin2Restrict.restrict Hdom).
    split.
    - split.
      + pose proof (Fin2Restrict.restrict_injective Hdom) as H1.
        intros x y Hxy.
        apply H1; auto.
        intros x' y' Hx' Hy' Hxy'.
        apply H; done.
      + pose proof (Fin2Restrict.restrict_surjective Hdom) as H1.
        destruct H as [Hinj Hsurj].
        intros ?.
        destruct H1 as [H2 H3].
        edestruct H3 as [x Hx].
        * apply bInjective_bSurjective; auto.
          intros x' y' Hx' Hy' Hxy'.
          apply Hinj; done.
        * exists x. eauto.
    - intro x.
      rewrite -{1}(nat_to_fin_to_nat x); [ | apply fin_to_nat_lt ].
      intros Hleq.
      rewrite (Fin2Restrict.restrict_n2f Hdom).
      rewrite fin_to_nat_to_fin //.
  Qed.

End fin.
