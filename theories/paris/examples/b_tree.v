From Coq.Program Require Import Wf.
From clutch.paris Require Import adequacy.
From stdpp Require Import list.
From clutch Require Import paris.
From clutch.paris.examples Require Import list.
Set Default Proof Using "Type*".
Open Scope R.

Section aux_lemmas.
  Local Lemma pow_pos x y:
    (0<x)%nat -> (0<x^y)%nat.
  Proof.
    intros. 
    apply Nat.lt_le_trans with (x^0)%nat.
    - simpl; lia.
    - apply Nat.pow_le_mono_r; lia.
  Qed.
    
End aux_lemmas.

Section stage1.
  (** stage 1 is relating a naive exact rand, with a big rand, via a rejection sampler *)
  Fixpoint index_list {A} (l:list A):=
    match l with
    | [] => []
    | x::l' => (0%nat, x) :: ((prod_map S id) <$> index_list l')
    end.

  (** REVISIT THIS IN THE FUTURE *)
  
  (* Local Lemma elem_of_index_list {A} (l:list A) x b: *)
  (*   l!!x = Some b -> *)
  (*   (x, b) ∈ index_list l. *)
  (* Proof. *)
  (*   revert x b; induction l. *)
  (*   - simpl. set_solver. *)
  (*   - intros x b Hl. *)
  (*     rewrite lookup_cons_Some in Hl. destruct Hl as [[-> ->]|[H Hl]]. *)
  (*     + simpl. set_solver. *)
  (*     + simpl. apply elem_of_list_further. *)
  (*       rewrite elem_of_list_fmap. *)
  (*       exists ((x-1)%nat, b). simpl; split. *)
  (*       * f_equal. lia. *)
  (*       * apply IHl. done. *)
  (* Qed. *)

  (* Local Lemma index_list_index_relate x y l: *)
  (*   filter (λ x1 : nat * bool, x1.2 = true) (index_list l) !! x = Some y -> *)
  (*   length (filter (λ x1 : bool, x1 = true) (take (y.1) l)) = x. *)
  (* Proof. *)
  (*   revert x y. *)
  (*   induction l; simpl; first done. *)
  (*   intros x y. rewrite !filter_cons; simpl. *)
  (*   case_match. *)
  (*   - subst. rewrite lookup_cons_Some. *)
  (*     intros [[-> ?]|[]]. *)
  (*     + by subst. *)
  (*     + simpl. *)
  (*       admit. *)
  (*   - intros. *)
  (*     admit. *)
  (* Admitted. *)
  
  (* Local Lemma filter_list_length l: *)
  (*   length (filter (λ x : nat * bool, x.2 = true) l) = *)
  (*   length (filter (λ x : nat * bool, x.2 = true) ((prod_map S id) <$> l)). *)
  (* Proof. *)
  (*   induction l; simpl; first done. *)
  (*   rewrite !filter_cons; simpl. *)
  (*   do 2 case_match; try done; simpl; rewrite IHl; done. *)
  (* Qed. *)

  (* Local Lemma filter_list_length' l: *)
  (*   length (filter (λ x, x = true) l) = *)
  (*   length (filter (λ x : nat * bool, x.2 = true) (index_list l)). *)
  (* Proof. *)
  (*   induction l; first (by simpl). *)
  (*   rewrite !filter_cons; do 2 case_match; try done; simpl; *)
  (*     rewrite IHl filter_list_length; done. *)
  (* Qed. *)

  (* Local Lemma index_list_range {A} (x:nat * A) l: *)
  (*   x ∈ index_list l -> (x.1 < length l)%nat. *)
  (* Proof. *)
  (*   revert x. *)
  (*   induction l. *)
  (*   - simpl. simpl. set_solver. *)
  (*   - simpl. intros x H. *)
  (*     rewrite elem_of_cons in H. *)
  (*     destruct H as [->|H]; simpl; first lia. *)
  (*     rewrite elem_of_list_fmap in H. *)
  (*     destruct H as [y [-> Hy]]. simpl. *)
  (*     pose proof IHl _ Hy. lia. *)
  (* Qed. *)

  (* Local Lemma index_list_lookup_lemma x l: *)
  (*   x.2 = true -> x∈index_list l -> l!!x.1 = Some true. *)
  (* Proof. *)
  (*   revert x. *)
  (*   induction l; simpl; first set_solver. *)
  (*   intros x. rewrite elem_of_cons. *)
  (*   intros H [->|H0]; simpl in *; first by subst. *)
  (*   rewrite elem_of_list_fmap in H0. *)
  (*   destruct H0 as [y [-> H0]]. *)
  (*   simpl in H. *)
  (*   by apply IHl. *)
  (* Qed. *)

  (* Local Lemma filter_prod_map_lemma x (l:list (nat * bool)): *)
  (*   (x < length (filter (λ x : nat * bool, x.2 = true) l))%nat ->  *)
  (*   (filter (λ x : nat * bool, x.2 = true) (prod_map S id <$> l) !!! x).1 = *)
  (*   S ((filter (λ x : nat * bool, x.2 = true)  l) !!! x).1. *)
  (* Proof. *)
  (*   revert x. *)
  (*   induction l; first (simpl; lia). *)
  (*   intros x. rewrite !filter_cons. *)
  (*   case_match; case_match; try done; simpl; last first. *)
  (*   - intros. apply IHl. done. *)
  (*   - intros. destruct x; simpl; first done. *)
  (*     apply IHl; lia. *)
  (* Qed. *)

  (* Local Lemma index_list_inj x y l: *)
  (*   (x < length (filter (λ x : nat * bool, x.2 = true) (index_list l)))%nat -> *)
  (*   (y < length (filter (λ x : nat * bool, x.2 = true) (index_list l)))%nat ->  *)
  (*   (filter (λ x : nat * bool, x.2 = true) (index_list l) !!! x).1 = *)
  (*   (filter (λ x : nat * bool, x.2 = true) (index_list l) !!! y).1 -> *)
  (*   x = y. *)
  (* Proof. *)
  (*   revert x y; induction l; simpl; first lia. *)
  (*   rewrite !filter_cons; simpl. *)
  (*   case_match; simpl; intros x y Hx Hy H'; last first. *)
  (*   - rewrite -filter_list_length in Hx, Hy. *)
  (*     apply IHl; try done. *)
  (*     rewrite !filter_prod_map_lemma in H'; lia. *)
  (*   - destruct x, y; simpl in H'; try done. *)
  (*     + exfalso. *)
  (*       cut (0%nat<(filter (λ x : nat * bool, x.2 = true) (prod_map S id <$> index_list l) !!! y).1)%nat. *)
  (*       * rewrite -H'. lia. *)
  (*       * clear H'. apply Forall_lookup_total_1; last lia. *)
  (*         rewrite Forall_forall. *)
  (*         intros x H0. rewrite elem_of_list_filter in H0. *)
  (*         destruct H0 as [? H0]. *)
  (*         rewrite elem_of_list_fmap in H0. *)
  (*         destruct H0 as [?[->?]]. simpl. lia. *)
  (*     + exfalso. *)
  (*       cut (0%nat<(filter (λ x : nat * bool, x.2 = true) (prod_map S id <$> index_list l) !!! x).1)%nat. *)
  (*       * rewrite H'. lia. *)
  (*       * clear H'. apply Forall_lookup_total_1; last lia. *)
  (*         rewrite Forall_forall. *)
  (*         intros y H0. rewrite elem_of_list_filter in H0. *)
  (*         destruct H0 as [? H0]. *)
  (*         rewrite elem_of_list_fmap in H0. *)
  (*         destruct H0 as [?[->?]]. simpl. lia. *)
  (*     + f_equal. apply IHl. *)
  (*       * rewrite filter_list_length. lia. *)
  (*       * rewrite filter_list_length. lia. *)
  (*       * rewrite !filter_prod_map_lemma in H'; first lia. *)
  (*         -- rewrite filter_list_length. lia. *)
  (*         -- rewrite filter_list_length. lia. *)
  (* Qed. *)
  
  (* Lemma inj_function_exists l M N: *)
  (*   length l = M ->  *)
  (*   length (filter (λ x, x = true) l) = N -> *)
  (*   exists f: (fin N -> fin M), Inj eq eq f /\ *)
  (*                         (forall x, l !! fin_to_nat (f x)= Some true /\ *)
  (*                               length (filter (λ x, x = true) (take ((fin_to_nat (f x))) l)) *)
  (*                               = (fin_to_nat x) *)
  (*                         ) /\ *)
  (*                         (forall x, (forall y, x≠f y) -> l!!fin_to_nat (x) = Some false). *)
  (* Proof. *)
  (*   intros Hlen1 Hlen2. *)
  (*   pose (l' := filter (λ x, x.2 = true) (index_list l)). *)
  (*   assert (forall x:fin N, x<length l')%nat. *)
  (*   { intros x. *)
  (*     pose proof fin_to_nat_lt x. *)
  (*     replace (length l') with N; first done. *)
  (*     rewrite -Hlen2. *)
  (*     rewrite /l'. *)
  (*     clear. *)
  (*     induction l; simpl; first done. *)
  (*     rewrite !filter_cons; simpl; case_match; simpl; by rewrite IHl -filter_list_length. *)
  (*   } *)
  (*   assert (forall (x:fin N), (l'!!!(fin_to_nat x)).1 < M)%nat as K; last first. *)
  (*   - exists (λ x, nat_to_fin (K x)). *)
  (*     split; last split. *)
  (*     + (* prove injection *) *)
  (*       intros x y Hf. apply (f_equal fin_to_nat) in Hf. *)
  (*       rewrite !fin_to_nat_to_fin in Hf. *)
  (*       rewrite /l' in Hf, H. *)
  (*       apply fin_to_nat_inj. *)
  (*       by eapply index_list_inj.  *)
  (*     + (* prove domain is true *) *)
  (*       intros x. rewrite fin_to_nat_to_fin. *)
  (*       split.  *)
  (*       * apply Forall_lookup_total_1; last auto. *)
  (*         rewrite Forall_forall. *)
  (*         rewrite /l'. *)
  (*         intros x'. rewrite elem_of_list_filter. *)
  (*         intros [??]. by apply index_list_lookup_lemma. *)
  (*       * erewrite index_list_index_relate; first done. *)
  (*         rewrite /l'. apply list_lookup_lookup_total_lt. *)
  (*         rewrite -filter_list_length'. *)
  (*         rewrite Hlen2. apply fin_to_nat_lt. *)
  (*     + (* prove if not in domain, it must be false *) *)
  (*       intros x Hx. *)
  (*       destruct (l!!fin_to_nat x) eqn :Heqn1; last first. *)
  (*       { apply lookup_ge_None_1 in Heqn1. *)
  (*         pose proof fin_to_nat_lt x. rewrite Hlen1 in Heqn1. lia.  *)
  (*       } *)
  (*       destruct b; last done. *)
  (*       exfalso. *)
  (*       cut ((fin_to_nat x, true) ∈ l'). *)
  (*       * rewrite /l'. rewrite elem_of_list_lookup. *)
  (*         intros [i Hi]. *)
  (*         cut (i<N)%nat. *)
  (*         -- intros Hproof. *)
  (*            cut (x=nat_to_fin (K (nat_to_fin Hproof))); first naive_solver. *)
  (*            apply fin_to_nat_inj. rewrite fin_to_nat_to_fin. *)
  (*            rewrite /l'. *)
  (*            rewrite fin_to_nat_to_fin. *)
  (*            apply list_lookup_total_correct in Hi. *)
  (*            by rewrite Hi. *)
  (*         -- apply lookup_lt_Some in Hi. *)
  (*            rewrite -Hlen2. rewrite -filter_list_length' in Hi. lia. *)
  (*       * rewrite /l'. rewrite elem_of_list_filter; simpl; split; first done. *)
  (*         apply elem_of_index_list. done. *)
  (*   - (* prove first projection is indeed smaller than length l, i.e. M *) *)
  (*     intros x. *)
  (*     apply Forall_lookup_total_1; last auto. *)
  (*     rewrite Forall_forall. *)
  (*     rewrite /l'. *)
  (*     intros x' Hx'. *)
  (*     rewrite elem_of_list_filter in Hx'. *)
  (*     destruct Hx' as [? Hx']. *)
  (*     rewrite -Hlen1; by apply index_list_range. *)
  (* Qed. *)
  
End stage1.


Section stage2.
  (** Stage 2 is relating the big state step with many small steps, via Rcoupl_state_state_exp *)
  Context {N:nat}.

  Fixpoint decoder_aux (l:list (fin (S N))) :=
    match l with
    | [] => 0%nat
    | x::l' => (fin_to_nat x + (S N) * decoder_aux l')%nat
    end.

  
  Local Lemma decoder_aux_ineq l:
    (decoder_aux l < (S N)^ (length l))%nat.
  Proof.
    induction l; first (simpl; lia).
    pose proof fin_to_nat_lt a. rewrite /decoder_aux.
    rewrite cons_length.
    rewrite -/decoder_aux.
    apply Nat.lt_le_trans with (S N + S N * decoder_aux l)%nat; first lia.
    assert (1<=S N ^ length l)%nat.
    { pose proof pow_pos (S N) (length l). lia. }
    assert ((decoder_aux l) <= S N ^ length l - 1)%nat as H' by lia.
    trans (S N + S N * (S N ^ length l - 1))%nat.
    - apply Nat.add_le_mono_l. 
      apply Nat.mul_le_mono_pos_l; lia.
    - rewrite Nat.pow_succ_r'. 
      cut (S N * (1+ S N ^ length l - 1) <= S N * S N ^ length l)%nat; last lia.
      intros; etrans; last exact.
      rewrite Nat.add_sub'.
      rewrite Nat.mul_sub_distr_l.
      rewrite Nat.mul_1_r.
      rewrite -Nat.le_add_sub; first lia.
      rewrite <-Nat.mul_1_r at 1.
      apply Nat.mul_le_mono_l. lia.
  Qed.

  Local Lemma decoder_aux_inj l1 l2:
    length l1 = length l2 -> decoder_aux l1 = decoder_aux l2 -> l1 = l2.
  Proof.
    clear.
    revert l2; induction l1.
    - simpl. intros. symmetry. apply nil_length_inv. done.
    - intros l2 Hlen2 H. destruct l2; first (simpl in *; lia).
      cut (fin_to_nat a=fin_to_nat t/\decoder_aux l1=decoder_aux l2).
      { intros [?%fin_to_nat_inj ?].
        f_equal; subst; last apply IHl1; try done.
        simplify_eq. done.
      } eapply Nat.mul_split_r.
      + apply fin_to_nat_lt.
      + apply fin_to_nat_lt.
      + simpl in H. lia.
  Qed.
  
  Context {M p: nat}.
  Context {Heq : (S N ^ p = S M)%nat}.
  Definition decoder l :=
    match lt_dec (decoder_aux (rev l)) (S M) with
    | left Hproof => nat_to_fin Hproof
    | _ => 0%fin
    end.
  
  Local Lemma decoder_inj l1 l2:
    length l1 = p -> length l2 = p -> decoder l1 = decoder l2 -> l1 = l2.
  Proof.
    intros Hlen1 Hlen2. rewrite /decoder.
    case_match eqn:Heq1; case_match eqn:Heq2; last first.
    - pose proof decoder_aux_ineq (rev l1) as H. rewrite rev_length Hlen1 Heq in H. lia.
    - pose proof decoder_aux_ineq (rev l1) as H. rewrite rev_length Hlen1 Heq in H. lia.
    - pose proof decoder_aux_ineq (rev l2) as H. rewrite rev_length Hlen2 Heq in H. lia.
    - intros H. apply (f_equal fin_to_nat) in H. rewrite !fin_to_nat_to_fin in H.
      apply rev_inj.
      apply decoder_aux_inj; last done.
      rewrite !rev_length. trans p; done.
  Qed.
  
End stage2.

Section b_tree.
  Context `{!parisGS Σ}.
  Context {min_child_num' : nat}.
  Context {depth : nat}.
  Local Definition min_child_num := S min_child_num'.
  Local Definition max_child_num := (2*min_child_num)%nat.
  (** For this example, intermediate nodes do not store keys themselves
      If the depth is 0, the node is a leaf, storing a single key value
      otherwise, if the depth is S n, it has stores a list of k children, each pointing to a tree of depth n
      where k varies from min_child_num to 2* min_child_num inclusive
      (We force min_child_num to be at least 1 for simplicity)
   *)

  Local Unset Elimination Schemes.
  Inductive ab_tree :=
  | Lf (v: val)
  | Br (l:list ab_tree).

  Lemma ab_tree_ind P:
    (∀ v : val, P (Lf v)) →
    (∀ l : list ab_tree,
       Forall (λ x, P x) l -> P (Br l)) →
    ∀ a : ab_tree, P a.
  Proof.
    clear.
    move => ?? t.
    generalize dependent P => P.
    generalize dependent t.
    fix FIX 1.
    move => [] ?? Hcall; first naive_solver.
    apply Hcall.
    apply Forall_true => ?. by apply FIX.
  Qed.

  Inductive is_ab_b_tree : nat -> list (option val) -> ab_tree -> Prop :=
  | is_ab_b_tree_lf v: is_ab_b_tree 0%nat [Some v] (Lf v)
  | is_ab_b_tree_br n (l:list (list(option val) * ab_tree)) :
    Forall (λ x, is_ab_b_tree n x.1 x.2) l ->
    (min_child_num <= length l <= max_child_num)%nat ->
    is_ab_b_tree (S n)
      (flat_map id (fst <$> l) ++ replicate ((max_child_num-length l)*max_child_num ^ n)%nat None)
      (Br (snd <$> l)).

  Lemma is_ab_b_tree_ind P:
    (∀ v : val, P 0%nat [Some v] (Lf v))
    → (∀ (n : nat) (l : list (list (option val) * ab_tree)),
         Forall (λ x : list (option val) * ab_tree, is_ab_b_tree n x.1 x.2) l ->
         Forall (λ x, P n x.1 x.2) l
         → (min_child_num <= length l <= max_child_num)%nat
           → P (S n)
               (flat_map id l.*1 ++ replicate ((max_child_num - length l) * max_child_num ^ n) None)
               (Br l.*2))
      → ∀ (n : nat) (l : list (option val)) (a : ab_tree), is_ab_b_tree n l a → P n l a.
  Proof.
    move => ?? n l t ?.
    generalize dependent P => P.
    generalize dependent n.
    generalize dependent l.
    generalize dependent t.
    fix FIX 4. move => t l n [ ]; first naive_solver.
    move => ????? Hcall.
    apply Hcall; [done| |done].
    eapply Forall_impl; first done.
    intros. by apply FIX.
  Qed.

  
  Local Set Elimination Schemes.
    
  Lemma ab_b_tree_list_length n l t:
    is_ab_b_tree n l t-> length l = (max_child_num ^ n)%nat.
  Proof.
    clear. intros H. induction H.
    - by simpl.
    - rewrite app_length.
      erewrite flat_map_constant_length; last first.
      { apply List.Forall_forall. rewrite Forall_fmap. eapply Forall_impl; first done.
        simpl. done.
      }
      rewrite replicate_length.
      rewrite Nat.pow_succ_r'.
      rewrite -Nat.mul_add_distr_r.
      rewrite fmap_length.
      rewrite -Nat.le_add_sub; lia.
  Qed.

  Definition succ (x y : ab_tree) : Prop :=
    match y with
    | Lf v => False
    | Br l => x ∈ l
    end.

  Lemma succ_wf : well_founded succ.
  Proof.
    intros t. induction t; apply Acc_intro.
    - rewrite /succ. done. 
    - intros t ? => /=. by eapply Forall_forall.
  Qed.

  Program Fixpoint relate_ab_tree_with_v (t:ab_tree) (v:val) {wf succ t} : iProp Σ :=
    match t with
    | Lf v' => ⌜v = v'⌝
    | Br tlis => ∃ loc_lis v_lis,
      ⌜length tlis = length loc_lis⌝ ∗
      ⌜length tlis = length v_lis⌝ ∗
      ⌜is_list loc_lis v⌝ ∗
      ([∗ list] x ∈ combine loc_lis v_lis, x.1 ↦ x.2) ∗
      ([∗ list] x ∈ combine tlis v_lis,
        match ClassicalEpsilon.excluded_middle_informative (succ x.1 t)
        with
        |left Hproof => relate_ab_tree_with_v x.1 x.2
        | _ => True
        end)
    end.
  Solve Obligations with auto using succ_wf.

  Lemma relate_ab_tree_with_v_Lf v v' :
    relate_ab_tree_with_v (Lf v') v ≡ ⌜v = v'⌝%I.
  Proof.
    rewrite /relate_ab_tree_with_v /relate_ab_tree_with_v_func.
    rewrite WfExtensionality.fix_sub_eq_ext //.  
  Qed.

  Lemma relate_ab_tree_with_v_Br v tlis :
    relate_ab_tree_with_v (Br tlis) v ≡
      (∃ loc_lis v_lis,
      ⌜length tlis = length loc_lis⌝ ∗
      ⌜length tlis = length v_lis⌝ ∗
      ⌜is_list loc_lis v⌝ ∗
      ([∗ list] x ∈ combine loc_lis v_lis, x.1 ↦ x.2) ∗
      ([∗ list] x ∈ combine tlis v_lis,
        match ClassicalEpsilon.excluded_middle_informative (succ x.1 (Br tlis))
        with
        |left Hproof => relate_ab_tree_with_v x.1 x.2
        | _ => True
        end))%I.
  Proof.
    rewrite {1}/relate_ab_tree_with_v /relate_ab_tree_with_v_func.
    rewrite WfExtensionality.fix_sub_eq_ext /=.
    repeat f_equiv.     
    by case_match.
  Qed. 

  
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

