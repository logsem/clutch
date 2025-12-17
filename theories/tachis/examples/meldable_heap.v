(** * Meldable Heaps *)
From clutch.tachis Require Import ert_weakestpre lifting ectx_lifting primitive_laws expected_time_credits cost_models problang_wp proofmode ert_rules.
From clutch.tachis Require Import min_heap_spec.
From clutch.common Require Import inject.
From iris.proofmode Require Export tactics.
From Stdlib Require Export Reals Psatz.
From stdpp Require Import sorting.
From Stdlib.Program Require Import Tactics.
From Stdlib.Program Require Import Wf WfExtensionality.

Set Default Proof Using "Type*".
From Stdlib Require Import Lra.

Section log.


  Lemma fin2_subst_0 (s : fin 2) : (Z.of_nat (fin_to_nat s) = 0%Z) -> (fin_to_bool s = false).
  Proof. intros. rewrite -fin_to_nat_to_bool_inv -nat_to_bool_eq_0. f_equal. lia. Qed.

  Lemma fin2_subst_neq0 (s : fin 2) : ((Z.of_nat (fin_to_nat s)) ≠ 0%Z ) -> (fin_to_bool s = true).
  Proof. intros. rewrite -fin_to_nat_to_bool_inv nat_to_bool_neq_0; auto. lia. Qed.

  (* Coq uses a fake version of log, which will be nice for handling edge cases in our derivation *)
  Lemma ln_0 : (ln 0%R = 0%R).
  Proof. compute. destruct (Rlt_dec R0 R0); auto. exfalso. lra. Qed.

  Lemma ln_pos (n : nat) : (1 < n)%nat -> (0 < ln n)%R.
  Proof.
    intros.
    apply exp_lt_inv.
    rewrite exp_0.
    pose P := (pos_INR n).
    rewrite exp_ln; [apply lt_1_INR; lia | apply lt_0_INR; lia].
  Qed.

  Lemma ln_nonneg (n : nat) : (0 <= ln n)%R.
  Proof.
    destruct n as [|n]; [ rewrite ln_0; lra | ].
    destruct n as [|n]; [ rewrite ln_1; lra | ].
    apply Rlt_le, ln_pos. lia.
  Qed.


  Lemma Rlog_pos (b : R) (v : nat) : (1 < b)%R -> (0 <= Rlog b v)%R.
  Proof.
    intros.
    rewrite /Rlog Rdiv_def.
    apply Rmult_le_pos; [apply ln_nonneg | ].
    apply Rlt_le, Rinv_0_lt_compat.
    rewrite -(ln_exp 0) exp_0.
    apply ln_increasing; lra.
  Qed.

  Lemma Rlog_nonneg_nats (b v : nat) : (0 <= Rlog b v)%R.
  Proof.
    rewrite /Rlog Rdiv_def.
    apply Rmult_le_pos; [apply ln_nonneg | ].
    destruct b; [rewrite /= ln_0 Rinv_0; lra |].
    destruct b; [rewrite /= ln_1 Rinv_0; lra |].
    apply Rlt_le, Rinv_0_lt_compat.
    apply ln_pos.
    lia.
  Qed.


  Lemma Rlog_increasing x y b : (1 < b)%R -> (0 < x < y)%R -> (Rlog b x < Rlog b y)%R.
  Proof.
    intros.
    rewrite /Rlog Rdiv_def.
    apply Rmult_lt_compat_r.
    { apply Rinv_0_lt_compat.
      rewrite -(ln_exp 0) exp_0.
      apply ln_increasing; lra.
    }
    apply ln_increasing; lra.
  Qed.

End log.



Section heaps.

  (** Binary trees *)
  Context (A : Type).

  Inductive BinaryTree : Type :=
    | Nil
    | Node (v : A) (l : BinaryTree) (r : BinaryTree).


  Fixpoint tree_size (t : BinaryTree) : nat
    := match t with
        | Nil => 0%nat
        | (Node _ l r) => 1 + (tree_size l) + (tree_size r)
       end.

  Fixpoint tree_to_list (t : BinaryTree) : list A
    := match t with
        | Nil => []
        | (Node x l r) => [x] ++ (tree_to_list l) ++ (tree_to_list r)
       end.

  (** Heaps: Heap-ordered binary trees *)

  Context (R : relation A).

  Definition HeapOrdered (v : A) (next : BinaryTree) : Prop
    := match next with
        | Nil => True
        | (Node v' _ _) => R v v'
       end.

  Inductive IsHeap : BinaryTree -> Prop :=
      | Heap_nil : IsHeap Nil
      | Heap_node (v : A) (l r : BinaryTree) :
          IsHeap l -> IsHeap r -> HeapOrdered v l -> HeapOrdered v r -> IsHeap (Node v l r).

End heaps.


Section program.
  Context `{A : Type}.
  Context `{!tachisGS Σ CostTick}.


  (** Lifts a representation predicate into binary trees *)
  Fixpoint repr_binarytree (cmp : comparator A CostTick) (b : BinaryTree A) (v : val) : iProp Σ
    := match b with
        | Nil =>
            ⌜ v = NONEV ⌝
        | Node x l r =>
            ∃ vv vl vr, ⌜v = SOMEV (PairV vv (PairV vl vr)) ⌝ ∗
                        cmp_has_key cmp x vv ∗
                        repr_binarytree cmp l vl ∗
                        repr_binarytree cmp r vr
       end.


  (* If x is heap ordered with respect to a node, it is heap ordered with respect to it's left child *)
  Lemma heap_ordered_strong_L (cmp : comparator A CostTick)  :
      ∀ x k h1 h2,
          (IsHeap A (cmp_rel cmp) (Node A k h1 h2)) ->
          (cmp_rel cmp x k) ->
          (HeapOrdered A (cmp_rel cmp) x h1).
  Proof.
    intros x k h1 h2.
    generalize dependent k.
    generalize dependent h2.
    induction h1 as [|k' l' IHl' r' IHr'].
    - intros. by simpl.
    - intros h' k.
      simpl in *.
      intros ? ?.
      inversion H.
      simplify_eq; simpl in *.
      by etrans.
  Qed.

  Lemma heap_ordered_strong_R (cmp : comparator A CostTick)  :
      ∀ x k h1 h2,
          (IsHeap A (cmp_rel cmp) (Node A k h1 h2)) ->
          (cmp_rel cmp x k) ->
          (HeapOrdered A (cmp_rel cmp) x h2).
  Proof.
    intros x k h1 h2.
    generalize dependent k.
    generalize dependent h1.
    induction h2 as [|k' l' IHl' r' IHr'].
    - intros. by simpl.
    - intros h' k.
      simpl in *.
      intros ? ?.
      inversion H.
      simplify_eq; simpl in *.
      by etrans.
  Qed.


  (* Now we can prove that, if x is less than the root of a heap, it is less than all elements of the heap *)
  Lemma heap_ordered_strong_elems (cmp : comparator A CostTick) :
      forall x h, (IsHeap A (cmp_rel cmp) h) ->
             (HeapOrdered A (cmp_rel cmp) x h) ->
             (forall x', In x' (tree_to_list _ h) -> (cmp_rel cmp x x')).
  Proof.
    intros x.
    induction h.
    - simpl. intros. done.
    - intros Hhp Hx x' Hx'.
      simpl in Hx.
      (* x' is either equal to the root, in the left branch, or in the right branch *)
      simpl in Hx'.
      destruct Hx' as [-> | Hx']; last (apply in_app_or in Hx'; destruct Hx' as [Hx' | Hx']).
      + done.
      + inversion Hhp; simplify_eq.
        apply IHh1; try auto.
        eapply heap_ordered_strong_L; eauto.
      + inversion Hhp; simplify_eq.
        apply IHh2; try auto.
        eapply heap_ordered_strong_R; eauto.
  Qed.


  (* If x is less than all elements in a heap, x is heap orderd with repsect to that heap *)
  Lemma heap_ordered_conv_elems (cmp : comparator A CostTick) h :
      forall x, (forall x', In x' (tree_to_list _ h) -> cmp_rel cmp x x') ->
           (HeapOrdered A (cmp_rel cmp) x h).
  Proof.
    intros.
    destruct h; first done.
    simpl.
    apply H.
    simpl.
    left; done.
  Qed.





  Definition is_meld_heap_val (cmp : comparator A CostTick) (L : list A) (v : val) : iProp Σ
    := ∃ (b : BinaryTree A),
            repr_binarytree cmp b v ∗         (* v is a representation of a binary tree b *)
            ⌜IsHeap A (cmp_rel cmp) b ⌝ ∗   (* ... where b is a heap with respect to cmp *)
            ⌜L ≡ₚ tree_to_list A b ⌝        (* ... and b's elements are L *).

  Lemma is_meld_heap_val_perm cmp (L1 L2 : list A) v :
      ⊢ ⌜L1 ≡ₚ L2 ⌝ -∗ (is_meld_heap_val cmp L1 v) -∗ (is_meld_heap_val cmp L2 v).
  Proof.
    rewrite /is_meld_heap_val.
    iIntros "%H [% ?]".
    rewrite H.
    iExists _.
    iFrame.
  Qed.

  Definition is_meld_heap_ref (cmp : comparator A CostTick) (L : list A) (v : val) : iProp Σ
    := ∃ (l : loc) (v' : val),
            ⌜ v = #l ⌝ ∗                  (* v is a location *)
            l ↦ v' ∗                       (* ... which points to a value *)
            is_meld_heap_val cmp L v'       (* ... which is a meld heap *).




  Definition meld_heap_new : val := (λ: "_", ref NONEV)%V.

  (* Takes two values (not references!) and melds them *)
  Definition meld_heap_meld (c : comparator A CostTick) : val
    :=  (rec: "meld" "mh1" "mh2" :=
          match: "mh1" with
           | NONE => "mh2"
           | SOME "h1" =>

          match: "mh2" with
           | NONE => "mh1"
           | SOME "h2" =>

          let: "h'" := if: (c (Fst "h1") (Fst "h2")) then ("h1", "h2") else ("h2", "h1") in
          let: "h_min" := (Fst "h'") in
          let: "h_max" := (Snd "h'") in
          (* Now (Fst h_min) <= (Fst h_max), so h_max should get melded into a child of h_min *)

          if: (rand #1 = #0)
            then (* Meld into the left branch of h_min *)
              let: "melded" := ("meld" (Fst (Snd "h_min")) (SOME "h_max")) in
              SOME (Fst "h_min", ("melded", (Snd (Snd "h_min"))))
            else (* Meld into the right branch of h_min *)
              let: "melded" := ("meld" (Snd (Snd "h_min")) (SOME "h_max")) in
              SOME (Fst "h_min",(Fst (Snd "h_min"), "melded"))

          end
          end
        )%V.


  Definition meld_heap_insert (c : comparator A CostTick) : val
    := (λ: "ref_h" "v",
          "ref_h" <- (meld_heap_meld c (!"ref_h") (SOME ("v", (NONEV, NONEV)))) ;;
          #())%V.


  Definition meld_heap_remove (c : comparator A CostTick) : val
    := (λ: "ref_h",
          match: (!"ref_h") with
            | NONE => NONEV
            | SOME "hv" =>
                "ref_h" <- (meld_heap_meld c (Fst (Snd "hv")) (Snd (Snd "hv"))) ;;
                SOME (Fst "hv")
          end)%V.


  (** Time credit accounting *)

  Definition tc_meld (k : R) (n : nat) := if (n =? 0)%nat then 0%R else (2 * k * (1 + Rlog 2 n))%R.

  Lemma tc_meld_1 (k : R) : (tc_meld k 1 = 2 * k)%R.
  Proof. rewrite /tc_meld /Rlog ln_1 /=. lra. Qed.

  Lemma tc_meld_0 (k : R) : (tc_meld k 0 = 0)%R.
  Proof. rewrite /tc_meld /=. lra. Qed.


  (* Edge case for tc_meld *)
  Lemma tc_meld_ind_L (k : R) (a : nat) :
      (0 < a) -> (0 <= k)%R -> (k + (tc_meld k a + tc_meld k 0) / 2 <= tc_meld k (1 + a + 0))%R.
  Proof.
    intros ? Hk.
    rewrite tc_meld_0.
    rewrite /tc_meld.
    replace (a =? 0)%nat with false; last (destruct a; simpl; lia).
    replace (1 + a + 0 =? 0)%nat with false; last (destruct a; simpl; lia).
    rewrite ?Rdiv_def.
    rewrite Rplus_0_r.
    replace ( 2 * k * (1 + Rlog 2 a) * / 2 )%R with (k * (1 + Rlog 2 a) )%R by lra.
    replace (2 * k * (1 + Rlog 2 (1 + a + 0)%nat))%R with (2 * k + 2 * k * Rlog 2 (1 + a + 0)%nat)%R by lra.
    rewrite Rmult_plus_distr_l Rmult_1_r.
    replace ( k + (k + k * Rlog 2 a))%R with (2*k + k * Rlog 2 a)%R by lra.
    apply Rplus_le_compat_l.
    rewrite (Rmult_comm 2 k) Rmult_assoc.
    apply Rmult_le_compat_l; [lra|].
    replace (2 * Rlog 2 (1 + a + 0)%nat)%R with (Rlog 2 ((1 + a + 0)%nat * (1 + a + 0)%nat))%R; last first.
    { rewrite /Rlog ?Rdiv_def -Rmult_assoc.
      apply Rdiv_eq_compat_r.
      replace 2%R with (1 + 1)%R; last (simpl; lra).
      rewrite Rmult_plus_distr_r ?Rmult_1_l.
      by rewrite ln_mult; try (apply lt_0_INR; lia).
    }
    apply Rlt_le, Rlog_increasing; try lra.
    split.
    - apply lt_0_INR; lia.
    - rewrite -mult_INR.
      apply lt_INR.
      lia.
  Qed.


  (* Edge case for tc_meld *)
  Lemma tc_meld_ind_R (k : R) (b : nat) :
      (0 < b) -> (0 <= k)%R -> (k + (tc_meld k 0 + tc_meld k b) / 2 <= tc_meld k (1 + 0 + b))%R.
  Proof.
    intros.
    rewrite (Rplus_comm (tc_meld _ _)).
    replace (1 + 0 + b)%nat with (1 + b + 0)%nat by lia.
    apply tc_meld_ind_L; auto.
  Qed.

  (* Edge case for tc_meld *)
  Lemma tc_meld_ind_LR (k : R) :
      (0 <= k)%R -> (k + (tc_meld k 0 + tc_meld k 0) / 2 <= tc_meld k (1 + 0 + 0))%R.
  Proof.
    intros.
    rewrite ?tc_meld_0.
    rewrite ?Nat.add_0_r tc_meld_1.
    lra.
  Qed.

  (* Inductive bound for tc_meld *)
  (* We will only apply advanced composition in the case that both a and b have size at at least 1 *)
  Lemma tc_meld_ind' (k : R) (a b : nat) :
      (0 < k)%R -> (k + (tc_meld k a + tc_meld k b) / 2 <= tc_meld k (1 + a + b))%R.
  Proof.
    intros Hk.
    destruct a as [|a']; destruct b as [|b'].
    { (* a = b = 0 *) apply tc_meld_ind_LR; lra.  }
    { (* a = 0 *) apply tc_meld_ind_R; [lia|lra]. }
    { (* b = 0 *) apply tc_meld_ind_L; [lia|lra]. }

    rewrite /tc_meld.

    (* Simplify edge cases from tc_meld *)
    remember (S a') as a.
    remember (S b') as b.
    assert (Ha : (0 < a)%nat) by lia.
    assert (Hb : (0 < b)%nat) by lia.
    replace (a =? 0)%nat with false; last (destruct a; simpl; lia).
    replace (b =? 0)%nat with false; last (destruct b; simpl; lia).
    replace (1 + a + b =? 0) with false; last first.
    { symmetry. apply PeanoNat.Nat.eqb_neq. lia. }
    clear Heqa Heqb a' b'.

    (* Divide by k and cancel the 2 factors *)
    apply (Rmult_le_reg_r (/ k)%R); first by apply Rinv_0_lt_compat.
    rewrite Rmult_plus_distr_r.
    rewrite Rinv_r; last lra.
    rewrite Rdiv_def.
    rewrite Rmult_assoc.
    rewrite -Rinv_mult.
    rewrite Rmult_comm.
    rewrite Rmult_plus_distr_l.
    replace  (/ (2 * k) * (2 * k * (1 + Rlog 2 a)))%R with (1 + Rlog 2 a)%R; last first.
    { rewrite -Rmult_assoc. rewrite Rinv_l; lra. }
    replace  (/ (2 * k) * (2 * k * (1 + Rlog 2 b)))%R with (1 + Rlog 2 b)%R; last first.
    { rewrite -Rmult_assoc. rewrite Rinv_l; lra. }
    replace (2 * k * (1 + Rlog 2 (1 + a + b)%nat) * / k)%R with (2 * (1 + Rlog 2 (1 + a + b)%nat))%R; last first.
    { rewrite (Rmult_comm _ (/ _)%R) -Rmult_assoc (Rmult_comm _ k) -Rmult_assoc.
      rewrite Rinv_l; lra. }

    (* Cancel out some 1's *)
    rewrite Rmult_plus_distr_l Rmult_1_r.
    do 3 rewrite -Rplus_assoc.
    replace (1 + 1)%R with 2%R by lra.
    repeat rewrite Rplus_assoc.
    repeat apply Rplus_le_compat_l.
    rewrite Rplus_comm.

    (* Replace 1 with a logarithm *)
    replace 1%R with (INR 1) by done.
    rewrite -(Rlog_pow 2); try lra.

    (* Turn Rlog into ln so that we can add them *)
    rewrite /Rlog.
    assert (Hln2 : (0 < ln 2)%R).
    { eapply Rlt_trans; [| eapply ln_lt_2]. lra. }
    apply (Rmult_le_reg_r (ln 2)); [done|].
    repeat rewrite (Rmult_plus_distr_r _ _ (ln 2)).
    repeat rewrite (Rmult_assoc _ _ (ln 2)).
    repeat (rewrite Rinv_l; last lra).
    repeat rewrite Rmult_1_r.


    (* Simplify the logarithms; apply monotonicity *)
    rewrite -ln_mult; [| lra | by apply lt_0_INR].
    rewrite -ln_mult; [ | | by apply lt_0_INR]; last first.
    { apply Rmult_lt_0_compat; [lra | by apply lt_0_INR]. }
    rewrite -ln_Rpower.
    apply Rcomplements.ln_le.
    { apply Rmult_lt_0_compat; last by apply lt_0_INR.
      apply Rmult_lt_0_compat; last by apply lt_0_INR.
      lra.
    }

    (* Turn the exponent into a product *)
    replace 2%R with (1%R + 1%R)%R by lra.
    rewrite Rpower_plus.
    rewrite Rpower_1; last (apply lt_0_INR; lia).
    replace (1%R + 1%R)%R with 2%R by lra.
    rewrite pow_1.


    (* Expand the binomial, bound using some of the terms *)
    repeat rewrite plus_INR.
    eapply (Rle_trans _ (a * b + b * a)%R); try lra.
    repeat rewrite Rmult_plus_distr_r.
    repeat rewrite Rmult_plus_distr_l.
    repeat rewrite INR_1.
    assert (0 < a)%R; [by apply lt_0_INR|].
    assert (0 < b)%R; [by apply lt_0_INR|].
    repeat rewrite Rmult_1_r.
    repeat rewrite Rmult_1_l.

    rewrite Rplus_assoc.
    rewrite -{1}(Rplus_0_l ((_ * _) + (_ * _))%R).
    apply Rle_plus_plus; first lra.

    rewrite Rplus_assoc.
    rewrite -{1}(Rplus_0_l ((_ * _) + (_ * _))%R).
    apply Rle_plus_plus.
    { apply Rplus_le_le_0_compat; try lra. apply Rmult_le_pos; try lra. }

    apply Rplus_le_compat_l.

    rewrite Rplus_assoc.
    rewrite -{1}(Rplus_0_l ((_ * _))%R).
    apply Rle_plus_plus; first lra.

    rewrite -{1}(Rplus_0_r ((_ * _))%R).
    apply Rplus_le_compat_l.

    apply Rmult_le_pos; try lra.

  Qed.

  (* Final version of the inductive bound *)
  Lemma tc_meld_ind (k : R) (a b : nat) :
      (0 <= k)%R -> (k + (tc_meld k a + tc_meld k b) / 2 <= tc_meld k (1 + a + b))%R.
  Proof.
    intros Hk.
    destruct Hk; last first.
    - simplify_eq.
      rewrite /tc_meld.
      destruct (a =? 0), (b =? 0), (1 + a + b =? 0); lra.
    - by apply tc_meld_ind'.
  Qed.


  Lemma tc_meld_nonneg (cmp : comparator A CostTick) n : (0 <= (tc_meld (cmp_cost cmp) n))%R.
  Proof.
    rewrite /tc_meld.
    pose P := (cmp_nonneg _ _ cmp).
    destruct (n =? 0); try lra.
    apply Rmult_le_pos; try lra.
    apply Rplus_le_le_0_compat; try lra.
    rewrite /Rlog Rdiv_def.
    apply Rmult_le_pos; [apply ln_nonneg|].
    pose Q := ln_lt_2.
    apply Rlt_le.
    apply Rinv_0_lt_compat.
    lra.
  Qed.

  Lemma tc_meld_mono (cmp : comparator A CostTick) m n : (m <= n)%nat -> (tc_meld (cmp_cost cmp) m <= tc_meld (cmp_cost cmp) n)%R.
  Proof.
    intros.
    rewrite /tc_meld.
    Opaque INR.
    destruct m as [|m']; destruct n as [|n'].
    { simpl; lra. }
    { simpl.
      pose (P := Rlog_pos 2 (S n')).
      pose (Q := cmp_nonneg _ _ cmp).
      apply Rmult_le_pos; try lra. }
    { exfalso. lia. }

    apply Rmult_le_compat_l.
    {  pose P := (cmp_nonneg _ _ cmp). lra. }
    apply Rplus_le_compat_l.
    rewrite /Rlog Rdiv_def.
    apply Rmult_le_compat_r.
    { apply Rlt_le, Rinv_0_lt_compat. pose P := ln_lt_2. lra. }
    apply Rcomplements.ln_le.
      - apply pos_INR_S.
      - by apply le_INR.
    Transparent INR.
  Qed.



  Lemma spec_meld_heap_new cmp : {{{ True }}} meld_heap_new #() {{{ v, RET v; (is_meld_heap_ref cmp) [] v }}}.
  Proof.
    iIntros (Φ _) "HΦ".
    rewrite /meld_heap_new.
    wp_pures.
    wp_alloc.
    iApply "HΦ".
    rewrite /is_meld_heap_ref.
    iExists _, _; iFrame.
    iSplit; eauto.
    rewrite /is_meld_heap_val.
    iExists (Nil A).
    iPureIntro.
    split; auto.
    simpl; split; auto.
    constructor.
  Qed.





  Definition tc_meld_distr (cmp : comparator A _) (LL LR : list A) (b : bool) : R :=
    if b
      then (cmp_cost cmp + tc_meld (cmp_cost cmp) (length LR))%R
      else (cmp_cost cmp + tc_meld (cmp_cost cmp) (length LL))%R.

  Lemma spec_meld_heap_meld cmp h1 h2 (L1 L2 : list A) :
      {{{ (is_meld_heap_val cmp L1 h1) ∗
          (is_meld_heap_val cmp L2 h2) ∗
          ⧖ ((cmp_cost cmp) + tc_meld (cmp_cost cmp) (length L1) + tc_meld (cmp_cost cmp) (length L2))
      }}}
        (meld_heap_meld cmp h1 h2)%E
      {{{ v, RET v;
          ∃ L, is_meld_heap_val cmp L v ∗ ⌜L ≡ₚ L1 ++ L2 ⌝
      }}}.
  Proof.
    iLöb as "IH" forall (h1 h2 L1 L2).
    iIntros (Φ) "((%b1 & HBb1 & %HHb1 & %HLb1) & (%b2 & HBb2 & %HHb2 & %HLb2 ) & H⧖) HΦ".
    rewrite {2}/meld_heap_meld.
    wp_pure.
    remember (rec: "meld" _ _ := _)%V as Vrec.
    wp_pures.

    destruct b1 as [| b1K b1BL b1BR ].
    { rewrite {1}/repr_binarytree.
      iDestruct "HBb1" as "->".
      wp_pures.
      iModIntro; iApply "HΦ".
      iExists (tree_to_list A b2).
      iSplitL.
      - rewrite /is_meld_heap_val.
        iExists _; iFrame.
        iPureIntro.
        split; auto.
      - rewrite HLb1 HLb2 /=. auto.
    }
    rewrite {1}/repr_binarytree -/repr_binarytree.
    iDestruct "HBb1" as "(%b1v & %b1vl & %b1vr & -> & HB1v & HRb1L & HRb1R)".
    wp_pures.

    destruct b2 as [| b2K b2BL b2BR ].
    { rewrite {2}/repr_binarytree.
      iDestruct "HBb2" as "->".
      wp_pures.
      iModIntro; iApply "HΦ".
      iExists _.
      iSplitL; last first.
      - rewrite HLb2 HLb1 /=. auto.
      - rewrite /is_meld_heap_val.
        iExists (Node A b1K b1BL b1BR).
        iSplitL "HB1v HRb1L HRb1R".
        { simpl. iExists _, _, _; iFrame; auto. }
        iPureIntro.
        simpl; split; auto.
        rewrite app_nil_r.
        simplify_eq.
        done.
    }
    rewrite {3}/repr_binarytree -/repr_binarytree.
    iDestruct "HBb2" as "(%b2v & %b2vl & %b2vr & -> & HB2v & HRb2L & HRb2R)".
    wp_pures.

    iAssert ( ⧖ (cmp_cost cmp) ∗
              ⧖ (tc_meld (cmp_cost cmp) (length (tree_to_list A (Node A b1K b1BL b1BR)))) ∗
              ⧖ (tc_meld (cmp_cost cmp) (length (tree_to_list A (Node A b2K b2BL b2BR)))))%I
      with "[H⧖]"
      as "(H⧖cmp & H⧖b1 & H⧖b2)".
    { iClear "IH".
       rewrite Rplus_assoc.
       iDestruct (etc_split with "H⧖") as "[? H⧖']".
       { apply cmp_nonneg. }
       { apply Rplus_le_le_0_compat; apply tc_meld_nonneg. }
       iFrame.
       iDestruct (etc_split with "H⧖'") as "[H⧖1 H⧖2]".
       { apply tc_meld_nonneg. }
       { apply tc_meld_nonneg. }
       iSplitL "H⧖1".
       { iApply (etc_weaken with "[$]"). split; [apply tc_meld_nonneg| rewrite HLb1; lra]. }
       { iApply (etc_weaken with "[$]"). split; [apply tc_meld_nonneg| rewrite HLb2; lra]. }
    }

    wp_apply ((@wp_cmp _ _ cmp _ _ b1K b2K) with "[H⧖cmp HB1v HB2v]"); iFrame.
    iIntros "(HB1v & HB2v)".

    case_bool_decide.
    - (* Minimum is heap 1, maximum is heap 2 *)
      wp_pures.

      (* Apply advanced composition on the branch of the minimum heap *)
      wp_apply (wp_couple_rand_adv_comp_strong' _ _ _ _
                  (tc_meld (cmp_cost cmp) (length (tree_to_list A (Node A b1K b1BL b1BR))))
                  ((tc_meld_distr cmp (tree_to_list A b1BL) (tree_to_list A b1BR)) ∘ fin_to_bool) with "H⧖b1").
      { intros. simpl.
        destruct (fin_to_bool _); simpl;
          apply Rplus_le_le_0_compat; try apply cmp_nonneg; try apply tc_meld_nonneg.
      }
      { rewrite /= Rplus_0_l.
        rewrite SeriesC_fin2.
        simpl.
        rewrite length_app -(Nat.add_1_l (length _ + length _)) Nat.add_assoc.
        pose P := (cmp_nonneg _ _ cmp).
        etrans; last eapply tc_meld_ind; [|done].
        lra.
      }

      iIntros (s) "H⧖".
      wp_pures.
      case_bool_decide.


      + inversion H0.
        wp_pures.

        rewrite HeqVrec.
        wp_apply ("IH" with "[HRb1L H⧖ H⧖b2 HB2v HRb2L HRb2R]").
        { iSplitL "HRb1L".
          { iExists _; iFrame. inversion HHb1; auto. }
          iSplitL "HB2v HRb2L HRb2R".
          { rewrite {4}/is_meld_heap_val.
            iExists _; iFrame.
            iSplitL; auto; simpl.
            iExists _, _, _; iFrame. eauto.
          }
          rewrite /= fin2_subst_0 /=; last auto.
          iApply etc_combine; iFrame.
          iApply (etc_irrel with "H⧖b2").
          by rewrite HLb2.
        }
        iClear "IH".

        iIntros (v) "(%L & (%hR & HhRR & %HhR & %HL') & %HL)".
        wp_pures.
        iModIntro; iApply "HΦ".
        iExists _.
        iSplitL.
        * rewrite /is_meld_heap_val.
          iExists (Node A b1K hR b1BR).
          iSplitL. { iExists _, _, _; iFrame; eauto. }
          iPureIntro.
          simpl; split; eauto.


          (* Prove that the resulting value is a heap *)
          clear HeqVrec.
          constructor; try done.
          -- inversion HHb1. done.
          -- apply heap_ordered_conv_elems.
             intros x' Hx'.
             rewrite -HL' HL HLb2 in Hx'.
             apply in_app_or in Hx'; destruct Hx'.
             --- inversion HHb1; simplify_eq.
                 eapply (heap_ordered_strong_elems _ _ b1BL); auto.
             --- etrans; [done|].
                 apply (heap_ordered_strong_elems _ _ (Node A b2K b2BL b2BR)); auto.
                 inversion HHb2; simplify_eq.
                 simpl. reflexivity.
          -- inversion HHb1. done.

        * iPureIntro; eauto.
          rewrite -HL' HL HLb1 /=.
          rewrite -?app_assoc.
          apply perm_skip, Permutation_app_head, Permutation_app_comm.


      + wp_pures.

        rewrite HeqVrec.
        wp_apply ("IH" with "[HRb1R H⧖ H⧖b2 HB2v HRb2L HRb2R]").
        { iSplitL "HRb1R".
          { iExists _; iFrame. inversion HHb1; auto. }
          iSplitL "HB2v HRb2L HRb2R".
          { rewrite {4}/is_meld_heap_val.
            iExists _; iFrame.
            iSplitL; auto; simpl.
            iExists _, _, _; iFrame. eauto.
          }
          rewrite /= fin2_subst_neq0; last first.
          { rewrite /not; intros HRW. rewrite HRW in H0. auto. }
          simpl.
          iApply etc_combine; iFrame.
          iApply (etc_irrel with "H⧖b2").
          by rewrite HLb2.
        }
        iClear "IH".

        iIntros (v) "(%L & (%hR & HhRR & %HhR & %HL') & %HL)".
        wp_pures.
        iModIntro; iApply "HΦ".
        iExists _.
        iSplitL.
        * rewrite /is_meld_heap_val.
          iExists (Node A b1K b1BL hR).
          iSplitL. { iExists _, _, _; iFrame; eauto. }
          iPureIntro.
          simpl; split; eauto.


          (* Prove that the resulting value is a heap *)
          clear HeqVrec.
          inversion HHb1.
          constructor; try done.
          apply heap_ordered_conv_elems.
          intros x' Hx'.
          simplify_eq.
          rewrite -HL' HL HLb2 in Hx'.
          apply in_app_or in Hx'; destruct Hx'.
          -- inversion HHb1; simplify_eq.
              eapply (heap_ordered_strong_elems _ _ b1BR); auto.
          -- etrans; [done|].
             apply (heap_ordered_strong_elems _ _ (Node A b2K b2BL b2BR)); auto.
             inversion HHb2; simplify_eq => /=.
             reflexivity.

        * iPureIntro; eauto.
          rewrite -HL' HL HLb1 /=.
          rewrite -?app_assoc.
          reflexivity.

    - (* Minimum is heap 2, maximum is heap 1 *)
      wp_pures.

      (* Apply advanced composition on the branch of the minimum heap *)
      wp_apply (wp_couple_rand_adv_comp_strong' _ _ _ _
                  (tc_meld (cmp_cost cmp) (length (tree_to_list A (Node A b2K b2BL b2BR))))
                  ((tc_meld_distr cmp (tree_to_list A b2BL) (tree_to_list A b2BR)) ∘ fin_to_bool) with "H⧖b2").
      { intros. simpl.
        destruct (fin_to_bool _); simpl;
          apply Rplus_le_le_0_compat; try apply cmp_nonneg; try apply tc_meld_nonneg.
      }
      { rewrite /= Rplus_0_l.
        rewrite SeriesC_fin2.
        simpl.
        rewrite length_app -(Nat.add_1_l (length _ + length _)) Nat.add_assoc.
        pose P := (cmp_nonneg _ _ cmp).
        etrans; last eapply tc_meld_ind; [|done].
        lra.
      }


      iIntros (s) "H⧖".
      wp_pures.
      case_bool_decide.


      + inversion H0.
        wp_pures.

        rewrite HeqVrec.
        wp_apply ("IH" with "[HRb2L H⧖ H⧖b1 HB1v HRb1L HRb1R]").
        { iSplitL "HRb2L".
          { iExists _; iFrame. inversion HHb2; auto. }
          iSplitL "HB1v HRb1L HRb1R".
          { rewrite {4}/is_meld_heap_val.
            iExists (Node A b1K b1BL b1BR); iFrame. eauto. }
          rewrite /= fin2_subst_0 /=; last auto.
          iApply etc_combine; iFrame.
          iApply (etc_irrel with "H⧖b1").
          by rewrite HLb1.
        }
        iClear "IH".

        iIntros (v) "(%L & (%hR & HhRR & %HhR & %HL') & %HL)".
        wp_pures.
        iModIntro; iApply "HΦ".
        iExists _.
        iSplitL.
        * rewrite /is_meld_heap_val.
          iExists (Node A b2K hR b2BR).
          iSplitL. { iExists _, _, _; iFrame; eauto. }
          iPureIntro.
          simpl; split; eauto.


          (* Prove that the resulting value is a heap *)
          clear HeqVrec.

          assert (cmp_rel cmp b2K b1K) by (destruct (total (cmp_rel cmp) b2K b1K); done).

          constructor; try done.
          -- inversion HHb2. done.
          -- apply heap_ordered_conv_elems.
             intros x' Hx'.
             rewrite -HL' HL HLb1 in Hx'.
             apply in_app_or in Hx'; destruct Hx'.
             --- inversion HHb2; simplify_eq.
                 eapply (heap_ordered_strong_elems _ _ b2BL); auto.
             --- etrans; [done|].
                 apply (heap_ordered_strong_elems _ _ (Node A b1K b1BL b1BR)); auto.
                 inversion HHb1; simplify_eq => /=.
                 reflexivity.
          -- inversion HHb2. done.

        * iPureIntro; eauto.
          rewrite -HL' HL HLb2 /=.
          rewrite (Permutation_app_comm L1) -?app_assoc /=.
          apply perm_skip.
          rewrite -?app_assoc.
          apply Permutation_app_head, Permutation_app_comm.

      + wp_pures.

        rewrite HeqVrec.
        wp_apply ("IH" with "[HRb2R H⧖ H⧖b1 HB1v HRb1L HRb1R]").
        { iSplitL "HRb2R".
          { iExists _; iFrame. inversion HHb2; auto. }
          iSplitL "HB1v HRb1L HRb1R".
          { rewrite {4}/is_meld_heap_val.
            iExists (Node  A b1K b1BL b1BR); iFrame. auto. 
          }
          rewrite /= fin2_subst_neq0; last first.
          { rewrite /not; intros HRW. rewrite HRW in H0. auto. }
          iApply etc_combine; iFrame.
          iApply (etc_irrel with "H⧖b1").
          by rewrite HLb1.
        }

        iClear "IH".

        iIntros (v) "(%L & (%hR & HhRR & %HhR & %HL') & %HL)".
        wp_pures.
        iModIntro; iApply "HΦ".
        iExists _.
        iSplitL.
        * rewrite /is_meld_heap_val.
          iExists (Node A b2K b2BL hR).
          iSplitL. { iExists _, _, _; iFrame; eauto. }
          iPureIntro.
          simpl; split; eauto.


          assert (cmp_rel cmp b2K b1K) by (destruct (total (cmp_rel cmp) b2K b1K); done).

          (* Prove that the resulting value is a heap *)
          clear HeqVrec.
          inversion HHb2.
          constructor; try done.
          apply heap_ordered_conv_elems.
          intros x' Hx'.
          simplify_eq.
          rewrite -HL' HL HLb1 in Hx'.
          apply in_app_or in Hx'; destruct Hx'.
          -- inversion HHb2; simplify_eq.
              eapply (heap_ordered_strong_elems _ _ b2BR); auto.
          -- etrans; [done|].
             apply (heap_ordered_strong_elems _ _ (Node A b1K b1BL b1BR)); auto.
             inversion HHb1; simplify_eq => /=.
             reflexivity.

        * iPureIntro; eauto.
          rewrite -HL' HL HLb2 /=.
          rewrite -?app_assoc.
          rewrite (Permutation_app_comm L1) /=.
          apply perm_skip.
          rewrite -?app_assoc.
          apply Permutation_app_head.
          reflexivity.
  Qed.


  Definition meld_heap_insert_cost (cmp : comparator A CostTick) N : R
    := ((cmp_cost cmp) + tc_meld (cmp_cost cmp) N + tc_meld (cmp_cost cmp) 1)%R.

  Lemma spec_meld_heap_insert cmp ref_h w (l : list A) k :
      {{{ is_meld_heap_ref cmp l ref_h ∗
          (cmp_has_key cmp k w) ∗
          ⧖ (meld_heap_insert_cost cmp (length l)) }}}
        meld_heap_insert cmp ref_h w
      {{{ l', RET #(); is_meld_heap_ref cmp l' ref_h ∗ ⌜l' ≡ₚ k :: l⌝ }}}.
  Proof.
    rewrite /is_meld_heap_ref.
    iIntros (Φ) "((%ℓ & %h & -> & Hℓ & Hh) & Hw & H⧖) HΦ".
    rewrite /meld_heap_insert.
    wp_pures.
    wp_load.
    iIntros "Hℓ".
    wp_apply ((spec_meld_heap_meld cmp _ _ l [k]) with "[H⧖ Hh Hw]").
    { iFrame.
      rewrite /is_meld_heap_val /=.
      iExists (Node A k (Nil A) (Nil A)).
      iSplitL.
      - rewrite /repr_binarytree. iExists _, _, _; eauto.
      - iPureIntro.
        simpl; split; eauto.
        repeat constructor.
    }
    iIntros (h') "[%l' (Hh' & %Hl')]".
    wp_store.
    iIntros "Hℓ".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iSplitL; [| iPureIntro; eauto].
    iExists _, _.
    iFrame.
    iSplit; eauto.
    (* Needs is_meld_heap_val to only be up to permutation, but otherweise done. *)
    iApply (is_meld_heap_val_perm with "[] Hh'").
    iPureIntro.
    by rewrite Permutation_cons_append.
  Qed.


  Definition meld_heap_remove_cost (cmp : comparator A CostTick) N : R
    := (cmp_cost cmp + 2 * tc_meld (cmp_cost cmp) N)%R.


  Lemma spec_meld_heap_remove (cmp : comparator A CostTick) ref_h l :
      {{{ is_meld_heap_ref cmp l ref_h ∗ ⧖ (meld_heap_remove_cost cmp (length l)) }}}
          meld_heap_remove cmp ref_h
      {{{ w, RET w;
            ⌜w = InjLV #()⌝ ∗ ⌜l = []⌝ ∗ is_meld_heap_ref cmp [] ref_h
           ∨ (∃ (k : A) (u : val) (l' : list A), ⌜w = InjRV u⌝ ∗ ⌜l ≡ₚ k :: l'⌝ ∗ cmp_has_key cmp k u ∗
                ⌜Forall (cmp_rel cmp k) l⌝ ∗ is_meld_heap_ref cmp l' ref_h)
      }}}.
  Proof.
    iIntros (Φ) "((%ℓ & %h & -> & Hℓ & (%b & Hb & %Hh & %Hl)) & H⧖) HΦ".
    rewrite /meld_heap_remove.
    wp_pures.
    wp_load; iIntros "Hℓ".
    destruct b; simpl.
    - iDestruct "Hb" as "->".
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iLeft.
      simpl in *.
      iSplit; eauto.
      iSplit; first (apply Permutation_nil_r in Hl; eauto).
      rewrite /is_meld_heap_ref.
      iExists _, _.
      iFrame.
      iSplit; eauto.
      rewrite /is_meld_heap_val.
      iExists (Nil A).
      simpl.
      iSplit; eauto.
    - iDestruct "Hb" as "(%vv & %vl & %vr & -> & Hvv & Hvl & Hvr )".
      wp_pures.
      simpl in Hl.
      wp_apply ((spec_meld_heap_meld cmp _ _ (tree_to_list A b1) (tree_to_list A b2)) with "[H⧖ Hvl Hvr]").
      { inversion Hh.
        iSplitL "Hvl". { rewrite /is_meld_heap_val. iExists b1; iFrame. iPureIntro. eauto. }
        iSplitL "Hvr". { rewrite /is_meld_heap_val. iExists b2; iFrame. iPureIntro. eauto. }
        rewrite /meld_heap_remove_cost /=.
        iApply (etc_weaken with "H⧖").
        split.
        - pose P1 := (tc_meld_nonneg cmp (length (tree_to_list A b1))).
          pose P2 := (tc_meld_nonneg cmp (length (tree_to_list A b2))).
          pose Q := (cmp_nonneg _ _ cmp).
          lra.
        - rewrite ?Rplus_assoc.
          apply Rplus_le_compat_l.
          replace 2%R with (1 + 1)%R by lra.
          rewrite Rmult_plus_distr_r ?Rmult_1_l.
          apply Rplus_le_compat; apply tc_meld_mono.
          + rewrite Hl /= length_app. lia.
          + rewrite Hl /= length_app. lia.
      }
      iIntros (h') "(%L & (%b & Hb & %Hb_heap & %HL) & %HL')".
      wp_store.
      iIntros "Hℓ".
      wp_pures.
      iModIntro; iApply "HΦ".
      iRight.
      iExists _, _, L.
      iFrame.
      iSplit; eauto.
      iSplit. { iPureIntro. rewrite Hl HL'. done. }
      rewrite /is_meld_heap_ref.
      iSplit.
      + (* Use one of those lemmas which relate the head of a heap to the body *)
        iPureIntro.
        rewrite Hl.
        replace (v :: tree_to_list A b1 ++ tree_to_list A b2) with (tree_to_list _ (Node A v b1 b2)); last by simpl.
        apply List.Forall_forall, heap_ordered_strong_elems; auto.
        simpl.
        inversion Hh.
        done.
      + auto.
  Qed.

End program.


Section interface.

  Context `{A : Type}.



  Program Definition meld_heap_spec cmp : (@min_heap A CostTick cmp)
    := {| heap_new := meld_heap_new ;
          heap_insert := meld_heap_insert cmp ;
          heap_remove := meld_heap_remove cmp ;
          is_min_heap := (fun Σ q L v => @is_meld_heap_ref A Σ q cmp L v) ;
          heap_insert_cost := meld_heap_insert_cost cmp ;
          heap_remove_cost := meld_heap_remove_cost cmp ;
       |}.
  Next Obligation.
    (* meld_heap_insert_cost is nonnegative *)
    intros.
    rewrite /meld_heap_insert_cost /=.
    rewrite Rplus_assoc.
    pose P := (cmp_nonneg _ _ cmp).
    apply Rplus_le_le_0_compat; [lra|].
    apply Rplus_le_le_0_compat; apply tc_meld_nonneg.
  Qed.
  Next Obligation.
    (* meld_heap_remove_cost is nonnegative *)
    intros.
    rewrite /meld_heap_remove_cost.
    pose P := (tc_meld_nonneg cmp n).
    pose Q := (cmp_nonneg _ _ cmp).
    lra.
  Qed.
  Next Obligation.
    (* meld_heap_insert_cost is monotone*)
    intros.
    rewrite /meld_heap_insert_cost /=.
    rewrite ?Rplus_assoc; apply Rplus_le_compat_l, Rplus_le_compat_r.
    by apply tc_meld_mono.
  Qed.
  Next Obligation.
    (* meld_heap_remove_cost is monotone *)
    intros.
    rewrite /meld_heap_remove_cost.
    apply Rplus_le_compat_l.
    apply Rmult_le_compat_l; try lra.
    by apply tc_meld_mono.
  Qed.
  Next Obligation.
    (* is_meld_heap respects permutations *)
    intros ? ? ? ? ? ->.
    rewrite /is_meld_heap_ref.
    iStartProof; iSplit.
    - iIntros "(% & % & ? & ? & ? )".
      iExists _, _.
      iFrame.
      iApply is_meld_heap_val_perm; eauto.
    - iIntros "(% & % & ? & ? & ? )".
      iExists _, _.
      iFrame.
      iApply is_meld_heap_val_perm; eauto.
  Qed.
  Next Obligation.
    (* New heap *)
    iIntros "_ H".
    wp_apply (spec_meld_heap_new cmp); auto.
  Qed.
  Next Obligation.
    (* Insert *)
    iIntros "H ?".
    wp_apply (spec_meld_heap_insert with "H"); iFrame.
  Qed.
  Next Obligation.
    (* Remove *)
    iIntros "H ?".
    wp_apply (spec_meld_heap_remove with "H"); iFrame.
  Qed.

End interface.
