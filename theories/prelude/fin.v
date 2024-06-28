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

  Lemma fin_force_to_nat_le (M : nat) (n : nat) :
    (n ≤ M) -> (fin_to_nat (fin_force M n)) = n.
  Proof.
    intros Hle.
    rewrite /fin_force.
    destruct le_lt_dec; try lia.
    rewrite fin_to_nat_to_fin //.
  Qed.

  Lemma fin_force_to_nat_gt (M : nat) (n : nat) :
    (n > M) -> (fin_to_nat (fin_force M n)) = M.
  Proof.
    intros Hgt.
    rewrite /fin_force.
    destruct le_lt_dec; try lia.
    rewrite fin_to_nat_to_fin //.
  Qed.

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

 (* Adapted from Coq standard library FinFun *)

Definition bFunNM n m (f:nat->nat) := forall x, x < n -> f x < m.

Definition restrictNM n m (f:nat->nat) (hf : bFunNM n m f) : (Fin.t n -> Fin.t m) :=
 fun x => nat_to_fin (hf _ (fin_to_nat_lt x)).

Lemma restrictNM_f2n n m f hf (x:Fin.t n) :
 fin_to_nat (restrictNM n m f hf x) = f (fin_to_nat x).
Proof.
  rewrite /restrictNM.
  rewrite fin_to_nat_to_fin //.
Qed.


Lemma restrictNM_n2f n m f hf x (h:x<n) :
 restrictNM n m f hf (nat_to_fin h) = nat_to_fin (hf _ h).
Proof.
  rewrite /restrictNM.
  rewrite Fin.of_nat_ext.
  {
    rewrite fin_to_nat_to_fin.
    intros.
    apply Fin.of_nat_ext.
  }
  rewrite fin_to_nat_to_fin.
  by apply hf.
Qed.

Lemma restrict_injective n m f h :
  Inj (=) (=) (restrictNM n m f h) <-> bInjective n f.
Proof.
  split.
  - intros hf x y hx hy Eq.
    rewrite -(fin_to_nat_to_fin x n).
    rewrite -(fin_to_nat_to_fin y n).
    f_equal.
    apply hf.
    do 2 rewrite restrictNM_n2f.
    rewrite Fin.of_nat_ext.
    {
      rewrite Eq.
      intros.
      apply Fin.of_nat_ext.
    }
    by apply h.
 - intros hf x y Eq.
   apply fin_to_nat_inj.
   apply hf.
   1,2: apply fin_to_nat_lt.
   do 2 rewrite <- (restrictNM_f2n n m f h).
   rewrite Eq //.
Qed.


  Lemma restr_inj_fin N M (f : nat -> nat) `{Inj nat nat (=) (=) f} :
    (N ≤ M) ->
    (forall n : nat, (n < N) -> (f n < M)) ->
    exists (g : fin N -> fin M), (Inj (=) (=) g) /\
                             (forall x : (fin N), fin_to_nat (g x) = f (fin_to_nat x)).
  Proof.
    intros Hleq Hdom.
    exists (restrictNM N M f Hdom).
    destruct (restrict_injective N M f Hdom) as [H1 H2].
    split.
    - intros x y Hxy.
      apply H2; auto.
      intros a b Ha Hb Hab.
      by apply H.
    - intro x.
      rewrite restrictNM_f2n //.
  Qed.

  Lemma fin_to_nat_le {n : nat} (i : fin (S n)) : (fin_to_nat i) ≤ n.
  Proof.
    pose proof (fin_to_nat_lt i); lia.
  Qed.

  Definition bFunListNM n m (f : list nat -> nat) := forall l, (Forall (λ x, x < n) l) -> f l < m.

  Fixpoint forall_leq_to_fin n (l : list nat) (Hfa : (Forall (λ x, x < n) l)) : (list (fin n)) :=
    match l, Hfa with
      | [], H => []
      | y :: ys, H => (nat_to_fin (Forall_inv H)) :: (forall_leq_to_fin n ys (Forall_inv_tail H))
    end.

  Lemma fin_forall_leq n (l : list (fin n)) :
    Forall (λ x : nat, x < n) (fin_to_nat <$> l).
  Proof.
    induction l; auto.
    rewrite fmap_cons.
    apply Forall_cons; auto.
    apply fin_to_nat_lt.
  Qed.

Definition restrictListNM n m (f:list nat -> nat) (hf : bFunListNM n m f) : (list (Fin.t n) -> Fin.t m) :=
  fun l =>  nat_to_fin (hf _ (fin_forall_leq _ l)).

Lemma restrictListNM_f2n n m f hf (l: (list (Fin.t n))) :
 fin_to_nat (restrictListNM n m f hf l) = f (fin_to_nat <$> l).
Proof.
  rewrite /restrictListNM /=.
  rewrite fin_to_nat_to_fin //.
Qed.

Lemma restrictListNM_n2f n m f hf l (hfa : (Forall (λ x, x<n) l)) :
 restrictListNM n m f hf (forall_leq_to_fin _ _ hfa) = nat_to_fin (hf _ hfa).
Proof.
  apply fin_to_nat_inj.
  rewrite !fin_to_nat_to_fin.
  f_equal.
  generalize dependent l.
  intros l.
  induction l; first done.
  intros H.
  simpl. f_equal.
  - by rewrite fin_to_nat_to_fin.
  - by eapply IHl.
Qed.

Lemma restr_list_inj_fixed_length N M p (f : list nat -> nat)
  (Hdom: forall (l : list nat), Forall (λ x, (x < N)%nat) l -> (f l < M)%nat)
  (Hinj: forall (l1 l2:list nat), Forall (λ x, (x < N)%nat) l1 -> Forall (λ x, (x < N)%nat) l2 ->
                           length l1 = p -> length l2 = p -> f l1 = f l2 -> l1 = l2) :
  exists (g : list (fin N) -> fin M),
    (forall (l1 l2: list (fin N)), length l1 = p -> length l2 = p -> g l1 = g l2 -> l1 = l2) /\
      (forall (l : list (fin N)), fin_to_nat (g l) = f (fin_to_nat <$> l)).
Proof.
  eexists (restrictListNM _ _ _ Hdom).
  split; last apply restrictListNM_f2n.
  intros ? ? ? ? H.
  apply (list_fmap_eq_inj fin_to_nat); first apply fin_to_nat_inj.
  apply Hinj; [apply fin_forall_leq|apply fin_forall_leq|by rewrite fmap_length|by rewrite fmap_length|..].
  erewrite <-!restrictListNM_f2n.
  by erewrite H.
Qed.

End fin.

Section decodings.

(* TODO: Move somewhere more appropriate *)

Context {N:nat}.

  Fixpoint decoder_nat (l:list nat) :=
    match l with
    | [] => 0%nat
    | x::l' => x + (S N) * (decoder_nat l')%nat
    end.

  Fixpoint decoder_nat_lr (l:list nat) :=
    match l with
    | [] => 0%nat
    | x::l' => x * (S N)^(length l') + (decoder_nat_lr l')%nat
    end.

  Lemma decoder_nat_app (l1 l2 : list nat) :
    decoder_nat (l1 ++ l2) = decoder_nat l1 + (S N)^(length l1) * (decoder_nat l2).
  Proof.
    induction l1; [simpl; lia |].
    rewrite -app_comm_cons /= IHl1.
    lia.
  Qed.


  Lemma decoder_nat_reverse (l : list nat) :
    decoder_nat (reverse l) = decoder_nat_lr l.
  Proof.
    induction l; auto.
    rewrite reverse_cons decoder_nat_app reverse_length IHl /=.
    lia.
  Qed.


  Local Lemma pow_ge_1 b e :
    (1 ≤ b) -> 1 ≤ (b ^ e).
  Proof.
    intros H.
    rewrite -(Nat.pow_1_l e).
    by apply Nat.pow_le_mono_l.
  Qed.

  Local Lemma decoder_aux_ineq l:
    (Forall (λ x, x < S N)%nat l) ->
    (decoder_nat l < (S N)^ (length l))%nat.
  Proof.
    intros Hfa.
    induction l; first (simpl; lia).
    apply Forall_cons_1 in Hfa as [Hhead Htail].
    specialize (IHl Htail).
    rewrite /decoder_nat.
    rewrite cons_length.
    rewrite -/decoder_nat.
    apply Nat.lt_le_trans with (S N + S N * decoder_nat l)%nat; first lia.
    assert (1<=S N ^ length l)%nat.
    { apply pow_ge_1; lia. }
    assert ((decoder_nat l) ≤ S N ^ length l - 1)%nat as H'; [lia |].
    trans (S N + S N * (S N ^ length l - 1))%nat.
    - apply Nat.add_le_mono_l.
      apply Nat.mul_le_mono_pos_l; lia.
    - rewrite Nat.pow_succ_r'.
      cut (S N * (1+ S N ^ length l - 1) ≤ S N * S N ^ length l)%nat; last lia.
      intros; etrans; last exact.
      rewrite Nat.add_sub'.
      rewrite Nat.mul_sub_distr_l.
      rewrite Nat.mul_1_r.
      rewrite -Nat.le_add_sub; auto.
      rewrite <-Nat.mul_1_r at 1.
      apply Nat.mul_le_mono_l. lia.
  Qed.


  Local Lemma decoder_lr_aux_ineq l:
    (Forall (λ x, x < S N)%nat l) ->
    (decoder_nat_lr l < (S N)^ (length l))%nat.
  Proof.
    intros.
    rewrite -decoder_nat_reverse -reverse_length.
    apply decoder_aux_ineq.
    by apply Forall_reverse.
  Qed.


  Local Lemma decoder_aux_inj l1 l2:
    (Forall (λ x, x < S N)%nat l1) ->
    (Forall (λ x, x < S N)%nat l2) ->
    length l1 = length l2 -> decoder_nat l1 = decoder_nat l2 -> l1 = l2.
  Proof.
    clear.
    revert l2; induction l1.
    - simpl. intros. symmetry. apply nil_length_inv. done.
    - intros l2 Hfa1 Hfa2 Hlen2 H.
      apply Forall_cons_1 in Hfa1 as [Hhead1 Htail1].
      destruct l2; first (simpl in *; lia).
      apply Forall_cons_1 in Hfa2 as [Hhead2 Htail2].
      cut (a=n /\ decoder_nat l1=decoder_nat l2).
      { intros [? ?].
        f_equal; subst; last apply IHl1; try done.
        simplify_eq. done.
      } eapply Nat.mul_split_r; eauto.
      simpl in H. lia.
  Qed.


  Local Lemma decoder_lr_aux_inj l1 l2:
    (Forall (λ x, x < S N)%nat l1) ->
    (Forall (λ x, x < S N)%nat l2) ->
    length l1 = length l2 -> decoder_nat_lr l1 = decoder_nat_lr l2 -> l1 = l2.
  Proof.
    rewrite -(Forall_reverse _ l1).
    rewrite -(Forall_reverse _ l2).
    rewrite -(decoder_nat_reverse l1) -(reverse_length l1).
    rewrite -(decoder_nat_reverse l2) -(reverse_length l2).
    intros.
    apply Inj_instance_2.
    apply decoder_aux_inj; auto.
  Qed.

End decodings.
