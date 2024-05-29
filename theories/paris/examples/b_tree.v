From clutch.paris Require Import adequacy.
From stdpp Require Import list.
From clutch Require Import paris.
Set Default Proof Using "Type*".
Open Scope R.

Section inj.
  Fixpoint index_list {A} (l:list A):=
    match l with
    | [] => []
    | x::l' => (0%nat, x) :: ((prod_map S id) <$> index_list l')
    end.

  Local Lemma filter_list_length l:
    length (filter (λ x : nat * bool, x.2 = true) l) =
    length (filter (λ x : nat * bool, x.2 = true) ((prod_map S id) <$> l)).
  Proof.
    induction l; simpl; first done.
    rewrite !filter_cons; simpl.
    do 2 case_match; try done; simpl; rewrite IHl; done.
  Qed.

  Local Lemma index_list_range {A} (x:nat * A) l:
    x ∈ index_list l -> (x.1 < length l)%nat.
  Proof.
    revert x.
    induction l.
    - simpl. simpl. set_solver.
    - simpl. intros x H.
      rewrite elem_of_cons in H.
      destruct H as [->|H]; simpl; first lia.
      rewrite elem_of_list_fmap in H.
      destruct H as [y [-> Hy]]. simpl.
      pose proof IHl _ Hy. lia.
  Qed.

  Local Lemma index_list_lookup_lemma x l:
    x.2 = true -> x∈index_list l -> l!!x.1 = Some true.
  Proof.
    revert x.
    induction l; simpl; first set_solver.
    intros x. rewrite elem_of_cons.
    intros H [->|H0]; simpl in *; first by subst.
    rewrite elem_of_list_fmap in H0.
    destruct H0 as [y [-> H0]].
    simpl in H.
    by apply IHl.
  Qed.

  Local Lemma filter_prod_map_lemma x (l:list (nat * bool)):
    (x < length (filter (λ x : nat * bool, x.2 = true) l))%nat -> 
    (filter (λ x : nat * bool, x.2 = true) (prod_map S id <$> l) !!! x).1 =
    S ((filter (λ x : nat * bool, x.2 = true)  l) !!! x).1.
  Proof.
    revert x.
    induction l; first (simpl; lia).
    intros x. rewrite !filter_cons.
    case_match; case_match; try done; simpl; last first.
    - intros. apply IHl. done.
    - intros. destruct x; simpl; first done.
      apply IHl; lia.
  Qed.

  Local Lemma index_list_inj x y l:
    (x < length (filter (λ x : nat * bool, x.2 = true) (index_list l)))%nat ->
    (y < length (filter (λ x : nat * bool, x.2 = true) (index_list l)))%nat -> 
    (filter (λ x : nat * bool, x.2 = true) (index_list l) !!! x).1 =
    (filter (λ x : nat * bool, x.2 = true) (index_list l) !!! y).1 ->
    x = y.
  Proof.
    revert x y; induction l; simpl; first lia.
    rewrite !filter_cons; simpl.
    case_match; simpl; intros x y Hx Hy H'; last first.
    - rewrite -filter_list_length in Hx, Hy.
      apply IHl; try done.
      rewrite !filter_prod_map_lemma in H'; lia.
    - destruct x, y; simpl in H'; try done.
      + exfalso.
        cut (0%nat<(filter (λ x : nat * bool, x.2 = true) (prod_map S id <$> index_list l) !!! y).1)%nat.
        * rewrite -H'. lia.
        * clear H'. apply Forall_lookup_total_1; last lia.
          rewrite Forall_forall.
          intros x H0. rewrite elem_of_list_filter in H0.
          destruct H0 as [? H0].
          rewrite elem_of_list_fmap in H0.
          destruct H0 as [?[->?]]. simpl. lia.
      + exfalso.
        cut (0%nat<(filter (λ x : nat * bool, x.2 = true) (prod_map S id <$> index_list l) !!! x).1)%nat.
        * rewrite H'. lia.
        * clear H'. apply Forall_lookup_total_1; last lia.
          rewrite Forall_forall.
          intros y H0. rewrite elem_of_list_filter in H0.
          destruct H0 as [? H0].
          rewrite elem_of_list_fmap in H0.
          destruct H0 as [?[->?]]. simpl. lia.
      + f_equal. apply IHl.
        * rewrite filter_list_length. lia.
        * rewrite filter_list_length. lia.
        * rewrite !filter_prod_map_lemma in H'; first lia.
          -- rewrite filter_list_length. lia.
          -- rewrite filter_list_length. lia.
  Qed.
  
  Lemma inj_function_exists l M N:
    length l = M -> 
    length (filter (λ x, x = true) l) = N ->
    exists f: (fin N -> fin M), Inj eq eq f /\ (forall x, l !! fin_to_nat (f x)= Some true).
  Proof.
    intros Hlen1 Hlen2.
    pose (l' := filter (λ x, x.2 = true) (index_list l)).
    assert (forall x:fin N, x<length l')%nat.
    { intros x.
      pose proof fin_to_nat_lt x.
      replace (length l') with N; first done.
      rewrite -Hlen2.
      rewrite /l'.
      clear.
      induction l; simpl; first done.
      rewrite !filter_cons; simpl; case_match; simpl; by rewrite IHl -filter_list_length.
    }
    assert (forall (x:fin N), (l'!!!(fin_to_nat x)).1 < M)%nat as K; last first.
    - exists (λ x, nat_to_fin (K x)).
      split.
      + (* prove injection *)
        intros x y Hf. apply (f_equal fin_to_nat) in Hf.
        rewrite !fin_to_nat_to_fin in Hf.
        rewrite /l' in Hf, H.
        apply fin_to_nat_inj.
        by eapply index_list_inj. 
      + (* prove domain is true *)
        intros x. rewrite fin_to_nat_to_fin.
        apply Forall_lookup_total_1; last auto.
        rewrite Forall_forall.
        rewrite /l'.
        intros x'. rewrite elem_of_list_filter.
        intros [??]. by apply index_list_lookup_lemma. 
    - (* prove first projection is indeed smaller than length l, i.e. M *)
      intros x.
      apply Forall_lookup_total_1; last auto.
      rewrite Forall_forall.
      rewrite /l'.
      intros x' Hx'.
      rewrite elem_of_list_filter in Hx'.
      destruct Hx' as [? Hx'].
      rewrite -Hlen1; by apply index_list_range.
  Qed.
  
End inj.

Section b_tree.
  Context `{!parisGS Σ}.
  Context {min_child_num' : nat}.
  Context {depth : nat}.
  Local Definition min_child_num := S min_child_num'.
  (** For this example, intermediate nodes do not store keys themselves
      If the depth is 0, the node is a leaf, storing a single key value
      otherwise, if the depth is S n, it has stores a list of k children, each pointing to a tree of depth n
      where k varies from min_child_num to 2* min_child_num inclusive
      (We force min_child_num to be at least 1 for simplicity)
   *)

  (** Intermediate nodes of ranked b-trees store extra info, specifically for each branch it has as a child, 
      the number of leafs it has *)

  (** The naive algorithm for ranked b -tree is to sample from the sum of the total number of children, 
      and then traverse down to find that particular value *)

  (** The optimized algorithm for non-ranked b-tree is at each node, sample from 2*min_child_num 
      then walk down that branch. If the number exceeds the total number of children, repeat from the root
   *)

  (** The intuition is that we assume we are sampling from a "full" tree that has max children,
      but repeat if the child does not exist
   *)
  
End b_tree.

Section proofs.
  (** To prove that the optimzed algorithm refines the naive one
      we show that for each "run", the depth number of (2*min_child_num) state step samples can be coupled
      with a single (2*min_child_num)^depth state step sample
      and that can be sampled with a single (total number of children) state step via a fragmental coupling 
      and appeal to Löb induction.
      To be more precise, one needs to find an injective function, from the total number of children to the single (2*min_child_num)^depth set
      The function is the one that maps i, to the index of the i-th children if the tree is full

      The other direction is the same, except one would need to amplify errors and use a continuity argument to close the proof 
   *)

End proofs.

