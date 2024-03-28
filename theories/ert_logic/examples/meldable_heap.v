(** * Meldable Heaps *)
From clutch.ert_logic Require Import ert_weakestpre lifting ectx_lifting primitive_laws expected_time_credits cost_models problang_wp proofmode ert_rules.
From clutch.ert_logic Require Import min_heap_spec.
From clutch.lib Require Import utils.
From iris.proofmode Require Export tactics.
From Coq Require Export Reals Psatz.
From stdpp Require Import sorting.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Set Default Proof Using "Type*".
Require Import Lra.


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
  Context (HTo : TotalOrder R).

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
  Context `{!ert_clutchGS Σ CostTick}.


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
              let: "melded" := ("meld" (Fst (Snd "h_min")) "h_max") in
              (Fst "h_min",
                 ("melded", (Snd (Snd "h_max"))))
            else (* Meld into the right branch of h_min *)
              let: "melded" := ("meld" (Snd (Snd "h_min")) "h_max") in
              (Fst "h_min",
                 (Fst (Snd "h_max"), "melded"))

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

  Lemma Rlog_nonneg (b v : nat) : (0 <= Rlog b v)%R.
  Proof.
    rewrite /Rlog Rdiv_def.
    apply Rmult_le_pos; [apply ln_nonneg | ].
    destruct b; [rewrite /= ln_0 Rinv_0; lra |].
    destruct b; [rewrite /= ln_1 Rinv_0; lra |].
    apply Rlt_le, Rinv_0_lt_compat.
    apply ln_pos.
    lia.
  Qed.

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
    (* destruct Hk as [ Hk | <- ]; last (rewrite /tc_meld; lra ). *)
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
    (* True *)
  Admitted.


  (* Edge case for tc_meld *)
  Lemma tc_meld_ind_R (k : R) (b : nat) :
      (0 < b) -> (0 <= k)%R -> (k + (tc_meld k 0 + tc_meld k b) / 2 <= tc_meld k (1 + 0 + b))%R.
  Proof. Admitted.

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
    { simpl. admit. }
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
  Admitted.



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
    if b then tc_meld (cmp_cost cmp) (length LR) else tc_meld (cmp_cost cmp) (length LL).

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
    { admit. }

    wp_apply ((@wp_cmp _ _ cmp _ _ b1K b2K) with "[H⧖cmp HB1v HB2v]"); iFrame.
    iIntros "(HB1v & HB2v)".

    case_bool_decide.
    - (* Minimum is heap 1, maximum is heap 2 *)
      wp_pures.

      (* Apply advanced composition on the branch of the minimum heap *)
      wp_apply (wp_couple_rand_adv_comp_strong' _ _ _ _
                  (tc_meld (cmp_cost cmp) (length (tree_to_list A (Node A b1K b1BL b1BR))))
                  ((tc_meld_distr cmp (tree_to_list A b1BL) (tree_to_list A b1BR)) ∘ fin_to_bool) with "H⧖b1").
      { intros. simpl. destruct (fin_to_bool _); simpl; apply tc_meld_nonneg. }
      { rewrite /= Rplus_0_l.
        rewrite SeriesC_fin2.
        simpl.
        rewrite app_length -(Nat.add_1_l (length _ + length _)) Nat.add_assoc.
        pose P := (cmp_nonneg _ _ cmp).
        etrans; last eapply tc_meld_ind; [lra|done].
      }

      iIntros (s) "H⧖".
      wp_pures.
      case_bool_decide.
      + inversion H0.
        wp_pures.
        rewrite HeqVrec.
        wp_apply ("IH" with "[]"); admit.
      + assert (Z.of_nat(fin_to_nat s) = 1)%Z by admit.
        wp_pures.
        rewrite HeqVrec.
        wp_apply ("IH" with "[]"); admit.



    (* !! COPY PROOF TO BELOW !! *)


    - (* Minimum is heap 2, maximum is heap 1 *)
      wp_pures.

      (* Apply advanced composition on the branch of the minimum heap *)
      wp_apply (wp_couple_rand_adv_comp_strong' _ _ _ _
                  (tc_meld (cmp_cost cmp) (length (tree_to_list A (Node A b2K b2BL b2BR))))
                  ((tc_meld_distr cmp (tree_to_list A b2BL) (tree_to_list A b2BR)) ∘ fin_to_bool) with "H⧖b2").
      { intros. simpl. destruct (fin_to_bool _); simpl; apply tc_meld_nonneg. }
      { rewrite /= Rplus_0_l.
        rewrite SeriesC_fin2.
        simpl.
        rewrite app_length -(Nat.add_1_l (length _ + length _)) Nat.add_assoc.
        pose P := (cmp_nonneg _ _ cmp).
        etrans; last eapply tc_meld_ind; [lra|done].
      }

      iIntros (s) "H⧖".
      wp_pures.
      case_bool_decide.
      + inversion H0.
        wp_pures.
        rewrite HeqVrec.
        wp_apply ("IH" with "[]"); admit.
      + assert (Z.of_nat(fin_to_nat s) = 1)%Z by admit.
        wp_pures.
        rewrite HeqVrec.
        wp_apply ("IH" with "[]"); admit.
  Admitted.


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
    := (2 * tc_meld (cmp_cost cmp) N)%R.


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
    apply Rmult_le_compat_l; try lra.
    by apply tc_meld_mono.
  Qed.
  Next Obligation.
    (* is_meld_heap respects permutations *)
    intros.
  Admitted.
  Next Obligation.
    (* New heap *)
    iIntros (? ? ? ?) "_ H".
    wp_apply (spec_meld_heap_new cmp); auto.
  Qed.
  Next Obligation.
    (* Insert *)
    iIntros (? ? ? ? ? ? ? ?) "H ?".
    wp_apply (spec_meld_heap_insert with "H"); iFrame.
  Qed.
  Next Obligation.
    (* Remove *)

  Admitted.

End interface.
