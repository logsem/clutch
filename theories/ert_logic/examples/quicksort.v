(** * Exact time credit accounting for Quicksort *)
From clutch.ert_logic Require Import ert_weakestpre lifting ectx_lifting primitive_laws expected_time_credits cost_models problang_wp proofmode.
From Coq Require Export Reals Psatz.
Require Import Lra.

(* From stdpp Require Import sorting.
From clutch.lib Require Import utils.
Set Default Proof Using "Type*".
Import list. *)

(* From clutch.examples Require Import quicksort. *)

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* From iris.proofmode Require Import coq_tactics reduction spec_patterns intro_patterns. *)
From iris.proofmode Require Export tactics.

(* From iris.prelude Require Import options. *)




Section accounting.
  (** Defines the Quicksort recurrence relation and bounds it above by (??) *)
  (* atm: bounded above by a series *)
  (* Could go "all the way" and bound it above by n log n *)



  (* Tighter bounding argument necessitates the pivot take time An+B *)
  Definition tc_pivot_lin (A B n : nat) : nonnegreal := nnreal_nat (A*n+B)%nat.

  Definition tc_base : nonnegreal. Admitted.

  (* tc_quicksort(len) = (1/len) + 2 * sum(i=0 to len-1)(tc_quicksort i) *)
  Program Fixpoint tc_quicksort (A B len : nat) {measure len} : nonnegreal
      := match len with
        | 0%nat => tc_base
        | (S len1)%nat =>
            nnreal_plus (tc_pivot_lin A B len) $
            nnreal_mult (nnreal_nat 2) $
            nnreal_div
              (foldr nnreal_plus nnreal_zero $ map (fun n => (tc_quicksort A B (fin_to_nat n))) $ fin_enum len)%NNR
              (nnreal_nat len)
       end.
  Next Obligation. intros. apply fin_to_nat_lt. (* This is the reason I need the haunted fin_enum *) Qed.
  Next Obligation. apply Wf.measure_wf, lt_wf. Qed.

  (* Exhausting unfolding lemmas, provable. *)
  Lemma tc_quicksort_0 A B : tc_quicksort A B 0%nat = tc_base.
  Proof.
      rewrite /tc_quicksort.
      rewrite /tc_quicksort_func /=.
      rewrite Wf.WfExtensionality.fix_sub_eq_ext.
      apply nnreal_ext; simpl.
      lra.
  Qed.

  (* Eliminate the hauntedness *)
  Lemma tc_quicksort_unfold A B n :
    (1 <= n)%nat ->
    tc_quicksort A B n =
            nnreal_plus (tc_pivot_lin A B n) $
            nnreal_mult (nnreal_nat 2) $
            nnreal_div
              (foldr nnreal_plus nnreal_zero $ map (fun i => ((tc_quicksort A B i))%NNR) $ seq 0%nat n)%NNR
              (nnreal_nat n).
  Proof.
    intros.
    Opaque INR.
    induction n as [|n' IH]; [lia|].
    destruct n'.
    - (* n' = 0 (n = 1) *)
      simpl.
      rewrite /tc_quicksort.
      rewrite /tc_quicksort_func /=.
      rewrite Wf.WfExtensionality.fix_sub_eq_ext.
      apply nnreal_ext; simpl.
      lra.
    - (* n' > 0 (n > 1) *)
      Opaque seq.
      rewrite {1}/tc_quicksort.
      rewrite /tc_quicksort_func /=.
      rewrite Wf.WfExtensionality.fix_sub_eq_ext.
      apply nnreal_ext; simpl.
      apply Rplus_eq_compat_l, Rmult_eq_compat_l.
      simpl.
      (* Still Haunted *)

      Transparent seq.
      Transparent INR.
  Admitted.


  Lemma tc_quicksort_bound_ind n' A B (HAB : (B <= A)%nat) :
    (nnreal_div (tc_quicksort A B (S n')) (nnreal_nat (S n' +  1)%nat) <=
       (nnreal_div (nnreal_nat (2* A)%nat) (nnreal_nat (S n' + 1)%nat) +
        nnreal_div (tc_quicksort A B n') (nnreal_nat (n' + 1)%nat))%NNR)%R.
  Proof.
    Opaque INR.
    remember (S n') as n.
    remember (tc_quicksort A B) as C.
    simpl.

    etrans; last first.
    { (* Include the (B-A)/(n(n+1)) term *)
      eapply Rplus_le_compat_l.
      rewrite -(Rplus_0_l (_ * _)%R).
      eapply Rplus_le_compat_r.
      assert (Hinst: (((B - A) / (n * (n+1)) <= 0)%R)).
      { apply Rcomplements.Rle_div_l.
        - apply Rlt_gt.
          rewrite Heqn.
          pose P := (pos_INR n').
          rewrite S_INR.
          apply Rmult_lt_0_compat;lra.
        - rewrite Rmult_0_l.
          apply Rle_minus, le_INR.
          lia.
      }
      eapply Hinst.
    }

    (* In this form, they should be equal *)
    apply Req_le.

    (* n'=0, separate proof *)
    destruct n' as [|n''].
    { simplify_eq; simpl.
      rewrite tc_quicksort_unfold /=; [|lia].
      rewrite tc_quicksort_0 /=.
      rewrite Rinv_1 Rmult_1_r Rmult_1_l Rmult_1_r Rplus_0_r.
      replace ((A + (A + 0))%nat * / (1 + 1))%R with (INR A); last first.
      { rewrite Nat.add_0_r.
        rewrite -{2}(Nat.mul_1_r A) -{3}(Nat.mul_1_r A).
        rewrite -Nat.mul_add_distr_l.
        rewrite mult_INR plus_INR INR_1.
        lra.
      }
      rewrite Nat.mul_1_r.
      rewrite Rmult_plus_distr_r.
      replace ((1 + 1) * nonneg tc_base * / (1 + 1))%R with (nonneg tc_base).
      { repeat rewrite plus_INR.
        rewrite INR_0 Rplus_0_r.
        do 2 rewrite Rmult_plus_distr_r.
        do 2 rewrite Rplus_assoc.
        apply Rplus_eq_compat_l.
        rewrite -S_INR.
        rewrite (Rmult_comm (INR 2)) Rmult_assoc.
        rewrite Rinv_r; [|rewrite S_INR S_INR INR_0; lra].
        lra.
      }
      lra.
    }

    (* Get rid of some n+1 denominators *)
    eapply (Rmult_eq_reg_r (INR (n + 1))); last first.
    { rewrite Nat.add_1_r S_INR. pose P:= (pos_INR n); lra. }
    rewrite Rmult_assoc Rinv_l; last first.
    { rewrite Nat.add_1_r S_INR. pose P:= (pos_INR n); lra. }
    rewrite Rmult_1_r.
    do 2 rewrite Rmult_plus_distr_r.
    rewrite Rmult_assoc Rinv_l; last first.
    { rewrite Nat.add_1_r S_INR. pose P:= (pos_INR n); lra. }
    rewrite Rmult_1_r.
    rewrite Rdiv_mult_distr.
    replace (((((INR B) - (INR A)) / (INR n)) / ((INR n) + 1)) * (INR (n + 1)))%R
       with ((((INR B - INR A)) / (INR n)))%R; last first.
    { rewrite (Rdiv_def _ (_ + _)%R).
      rewrite Rmult_assoc.
      rewrite Nat.add_1_r S_INR.
      rewrite Rinv_l; last (pose P := (pos_INR n); lra).
      lra.
    }

    (* Unfold C *)
    Opaque INR.
    rewrite HeqC Heqn.
    rewrite tc_quicksort_unfold; last lia.
    rewrite -Heqn -HeqC.
    Opaque seq.
    simpl.
    Transparent seq.

    (* Pull out one term from the series *)
    replace (foldr nnreal_plus nnreal_zero (map (λ i : nat, (C i)) (seq 0 n)))
       with (C (S n'') + (foldr nnreal_plus nnreal_zero (map (λ i : nat, (C i)) (seq 0 (S n'')))))%NNR;
      last first.
    { rewrite Heqn.
      Opaque seq.
      rewrite (seq_S (S n'')) /=.
      rewrite map_app.
      rewrite foldr_snoc.
      rewrite foldr_comm_acc; [done|].
      intros; simpl.
      rewrite nnreal_plus_comm nnreal_plus_assoc.
      do 2 rewrite -nnreal_plus_assoc.
      rewrite (nnreal_plus_comm x _).
      done.
      Transparent seq.
    }
    remember (foldr nnreal_plus nnreal_zero (map (λ i : nat, (C i)) (seq 0 (S n'')))) as SR.

    (* Remove n denominators *)
    replace (S (n'' + 1)) with n by lia.
    apply (Rmult_eq_reg_r (INR n)); last (apply not_0_INR; lia).
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_assoc.
    rewrite Rmult_assoc.
    rewrite Rinv_l; last (apply not_0_INR; lia).
    rewrite Rmult_1_r.
    rewrite Rmult_assoc.
    rewrite (Rmult_comm (/ (INR n))).
    rewrite -Rmult_assoc.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_assoc.
    rewrite Rinv_l; last (apply not_0_INR; lia).
    rewrite Rmult_1_r.
    replace (((INR B - INR A) / (INR n)) * (INR n))%R with (INR B - INR A)%R; last first.
    { rewrite Rdiv_def.
      rewrite Rmult_assoc.
      rewrite Rinv_l; last (apply not_0_INR; lia).
      lra.
    }

    (* Collect C (S n'') on the left *)
    apply (Rplus_eq_reg_l (- ((INR ((A * n) + B)) * (INR n)))%R).
    rewrite -Rplus_assoc.
    rewrite Rplus_opp_l Rplus_0_l.
    rewrite -Rplus_assoc.
    apply (Rplus_eq_reg_r (- (nonneg (C (S n''))) * (INR (n + 1)))%R).
    rewrite Rplus_assoc.
    rewrite Rplus_assoc.
    rewrite Rplus_assoc.
    replace (((nonneg (C (S n''))) * (INR (n + 1))) + ((- (nonneg (C (S n'')))) * (INR (n + 1))))%R
        with (0)%R by lra.
    rewrite Rplus_0_r.
    simpl.
    rewrite Rmult_plus_distr_l.
    rewrite Rplus_comm.
    rewrite -Rplus_assoc.
    rewrite Ropp_mult_distr_l_reverse Ropp_mult_distr_r.
    rewrite Rmult_comm.
    rewrite -Rmult_plus_distr_r.
    replace ((- (INR (n + 1))) + (INR 2))%R with (-(S n''))%R; last first.
    { rewrite S_INR.
      rewrite Nat.add_1_r S_INR.
      rewrite Heqn S_INR S_INR S_INR S_INR INR_0.
      lra.
    }

    (* Unfold C *)
    rewrite HeqC.
    rewrite tc_quicksort_unfold; last lia.
    rewrite -HeqC -HeqSR /=.

    (* Cancel the sums *)
    rewrite Rmult_plus_distr_l.
    replace ((- (INR (S n''))) * ((INR 2) * ((nonneg SR) * (/ (INR (S n''))))))%R
       with ((- (INR 2) * ((nonneg SR))))%R; last first.
    { rewrite -Ropp_mult_distr_l.
      rewrite -Ropp_mult_distr_l.
      f_equal.
      rewrite (Rmult_comm (INR (S n''))).
      rewrite Rmult_assoc.
      rewrite Rmult_assoc.
      rewrite Rinv_l; [|apply not_0_INR; lia].
      lra.
    }
    rewrite Rplus_assoc.
    replace (((- (INR 2)) * (nonneg SR)) + ((INR 2) * (nonneg SR)))%R with (0)%R by lra.
    rewrite Rplus_0_r.

    (* Simplify out negatives*)
    apply Ropp_eq_reg.
    rewrite Ropp_plus_distr Ropp_involutive.


    (* Expand binomial to eliminate n^2 term *)
    rewrite Heqn /=.
    replace ((INR ((A * (S (S n''))) + B)) * (INR (S (S n''))))%R
      with  (((INR ((A * (S (S n''))) + B)) * INR (S n'')) + (INR ((A * (S (S n''))) + B)))%R; last first.
    { rewrite (S_INR (S n'')).
      rewrite Rmult_plus_distr_l.
      by rewrite Rmult_1_r.
    }
    replace ((INR ((A * (S (S n''))) + B)) * (INR (S n'')))%R
       with ((INR ((A * (S n'')) + B)) * (INR (S n'')) + (INR A) * (INR (S n'')))%R; last first.
    { symmetry.
      rewrite -{1}Nat.add_1_r.
      rewrite Nat.mul_add_distr_l.
      rewrite Nat.mul_1_r.
      rewrite -Nat.add_assoc (Nat.add_comm A _) Nat.add_assoc.
      rewrite plus_INR.
      rewrite Rmult_plus_distr_r.
      done.
    }
    rewrite Ropp_mult_distr_l.
    rewrite Ropp_involutive.
    rewrite Rmult_comm.
    rewrite -{1}(Rplus_0_r (_ * _)%R).
    rewrite Rplus_assoc.
    rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.

    (* Expand the remaining (S (S n'')) terms *)
    repeat (rewrite S_INR || rewrite plus_INR || rewrite INR_0 || rewrite mult_INR).
    lra.
  Qed.

  Lemma tc_quicksort_bound_closed A B n (HAB : (B <= A)%nat):
    ((nnreal_div (tc_quicksort A B n) (nnreal_nat (n + 1)%nat))
      <= (foldr nnreal_plus (tc_quicksort A B 0%nat) $
          map (fun i => nnreal_div (nnreal_nat (2*A)%nat) (nnreal_nat (i + 1)%nat)) $
          seq 1%nat n))%R.
  Proof.
    Opaque seq.
    simpl.
    induction n as [|n' IH].
    { Transparent seq. simpl. rewrite INR_1. lra. Opaque seq. }
    etrans; first eapply tc_quicksort_bound_ind; first eauto.
    rewrite seq_S map_app foldr_snoc /=.
    rewrite foldr_comm_acc; last first.
    { intros; simpl.
      rewrite nnreal_plus_comm nnreal_plus_assoc.
      do 2 rewrite -nnreal_plus_assoc.
      rewrite (nnreal_plus_comm x _).
      done.
    }
    simpl.
    apply Rplus_le_compat_l, IH.
  Qed.

  (* TODO: Bound above by Riemann sum for 1/n integral *)

End accounting.


Section cost.
  (** Cost fucntion for Quicksort: number of comparisons *)

  Definition cmp_cost_fn (e : expr) :=
    match e with
    | BinOp LeOp _ _ => nnreal_one
    | BinOp LtOp _ _ => nnreal_one
    | _ => nnreal_zero
    end.


  Program Definition CostCmp : Costfun prob_lang := (Build_Costfun cmp_cost_fn _ _ _).
  Next Obligation.
    eexists 1.
    intros; simpl.
    rewrite /cmp_cost_fn.
    destruct e; simpl; try lra.
    destruct op; simpl; try lra.
  Qed.
  Next Obligation.
    intros; simpl.
    rewrite /cmp_cost_fn.
    destruct e; simpl; try lra.
    destruct op; simpl; try lra.
  Qed.
  Next Obligation. Admitted.

  Context `{!ert_clutchGS Σ CostCmp}.

  #[local] Lemma test_wp_pure :
       {{{ ⧖ (nnreal_nat 1) }}} (if: (#0 < #1) then #() else #() ) {{{ RET #(); ⧖ (nnreal_nat 0) }}}.
  Proof.
    Set Printing Coercions.
    iIntros (x) "Hx Hp".
    wp_pure.
    wp_pure.
    iModIntro.
    iApply "Hp".
    simpl in *.
    Unset Printing Coercions.
  Abort.
End cost.

Section program.


  Context `{!ert_clutchGS Σ CostCmp }.
  (** Verifing the number of comparisons done by a (not in place) version of quicksort *)
  (* One thing that's super annoying: we have to copy the functional correctness proofs
     in order to augment them with step counting. This does not match the classical
     style where we prove correctness and runtime separately.

     Somehow it would be nice to say that
        {{{ ⧖ X ∗ W }}} f {{{ ⌜T ⌝ }}}
      in the ect logic and
        {{{ Φ }}} f {{{ Ψ }}}
      in regular or UB clutch is enough to show that
        {{{ ⧖ X ∗ W ∗ Φ }}} f {{{ ⌜T ⌝ ∗ Ψ }}}
      in the credit logic.
   *)


    (* Copied from examples/quicksort.v *)

(*
  Lemma wp_remove_nth_unsafe {A} [_ : Inject A val] E (l : list A) (lv : val) (i : nat) :
    {{{ ⌜ is_list l lv /\ i < length l ⌝ }}}
      list_remove_nth_unsafe lv #i @ E
    {{{ v, RET v;
        ∃ e lv' l1 l2,
          ⌜ l = l1 ++ e :: l2 ∧
          length l1 = i /\
          v = ((inject e), lv')%V ∧
          is_list (l1 ++ l2) lv' ⌝ }}}.
  Proof.
    iIntros (φ (llv & il)) "hφ".
    rewrite /list_remove_nth_unsafe. wp_pures.
    wp_apply wp_remove_nth => //.
    iIntros (?(?&?&?&?&?&?&?&?)) ; subst. wp_pures.
    iApply "hφ". iModIntro. iExists _,_,_,_. intuition eauto.
  Qed.

  Lemma filter_split_perm {A} (l : list A) f :
    l ≡ₚ List.filter f l ++ List.filter (fun x=>negb (f x)) l.
  Proof.
    induction l as [|a l IHl] => // /=.
    destruct (f a) => /= ; rewrite -?Permutation_middle -IHl //.
  Qed.

  Lemma Partition (xs : list Z) l (e : Z) e' :
    e' = Val #e ->
    {{{ ⌜is_list xs l⌝ }}}
      partition l e'
    {{{ le gt, RET (le, gt);
        ∃ xsle xsgt : list Z,
          ⌜is_list xsle le ∧ is_list xsgt gt
          ∧ app xsle xsgt ≡ₚ xs ⌝
          ∧ ⌜ ∀ x, In x xsle → (x ≤ e)%Z ⌝
                   ∧ ⌜ ∀ x, In x xsgt → (e < x)%Z ⌝
    }}}.
  Proof.
    iIntros (-> φ Lxs) "hφ".
    rewrite /partition. subst.
    wp_pures.
    wp_bind (list_filter _ _).
    iApply (wp_list_filter _ (λ x, bool_decide (e < x)%Z)).
    { iSplit => //. iIntros (x ψ) "_ !> hψ".
      simpl. wp_pures. iApply "hψ". eauto. }
    iIntros "!>" (gt egt). wp_pures.
    wp_bind (list_filter _ _).
    iApply (wp_list_filter _ (λ x, negb $ bool_decide (e < x)%Z)).
    { iSplit => //. iIntros (x ψ) "_ !> hψ".
      simpl. wp_pures.
      case_bool_decide ; wp_pures ; by iApply "hψ". }
    iIntros "!>" (le ele).
    wp_pures. iApply "hφ". iPureIntro.
    set (xs_gt := (List.filter (λ x : Z, bool_decide (e < x)%Z) xs)) in *.
    set (xs_le := (List.filter (λ x : Z, negb $ bool_decide (e < x)%Z) xs)) in *.
    exists xs_le, xs_gt. intuition auto.
    2:{ epose proof (filter_In _ x xs) as [h _]. destruct (h H) as [_ hle].
        destruct (bool_decide (e < x)%Z) eqn:hlt => //.
        apply bool_decide_eq_false in hlt.
        apply Z.nlt_ge. done.
    }
    2:{ epose proof (filter_In _ x xs) as [h _]. destruct (h H) as [_ hgt].
        by apply bool_decide_eq_true in hgt.
    }
    epose proof (filter_split_perm xs _) as xs_split.
    symmetry. subst xs_le xs_gt.
    rewrite Permutation_app_comm. apply xs_split.
  Qed.

  Local Notation sorted := (StronglySorted Z.le).

  Fact sorted_append pre post p :
    sorted pre → sorted post →
    (∀ x, In x pre → (x <= p)%Z) → (∀ x, In x post → (p < x)%Z) →
    sorted (pre ++ p :: post).
  Proof.
    intros Spre Spost ppre ppost.
    induction pre => /=.
    - apply SSorted_cons, List.Forall_forall => // ; intros.
      by apply Z.lt_le_incl, ppost.
    - apply SSorted_cons, List.Forall_forall => // ; [| clear IHpre].
      { apply IHpre.
        * apply StronglySorted_inv in Spre. by destruct Spre.
        * intros. apply ppre. set_solver. }
      intros x xppp.
      destruct (in_app_or _ _ _ xppp) as [x_pre | x_post] ; clear xppp.
      + apply StronglySorted_inv in Spre. destruct Spre.
        by apply (List.Forall_forall _ pre).
      + assert (a ≤ p)%Z as ap by (apply ppre ; constructor => //).
        assert (∀ z, In z (p::post) -> (p ≤ z)%Z) as ppost' ; last first.
        { etrans => //. apply ppost' => //. }
        intros z hz.
        destruct (in_inv hz) as [-> | zpost] => //.
        apply Z.lt_le_incl, ppost => //.
  Qed.

  Lemma qs_sorted : ∀ (xs : list Z) (l : val),
    {{{ ⌜is_list xs l⌝ }}}
      qs l
    {{{ v, RET v; ∃ xs', ⌜ is_list xs' v ∧ xs' ≡ₚ xs ∧ sorted xs' ⌝ }}}.
  Proof with wp_pures.
    iLöb as "Hqs". iIntros (xs l φ hl) "hφ".
    rewrite {2}/qs... rewrite -/qs.
    wp_bind (list_length _). iApply (wp_list_length $! hl).
    iIntros "!>" (n) "->"...
    case_bool_decide as hn...
    (* an empty or singleton list is already sorted. *)
    { iApply "hφ". iExists xs. iPureIntro. intuition auto.
      destruct xs => //. 1: constructor. destruct xs => //. simpl in hn. lia. }
    (* pick a pivot index at random *)
    wp_apply wp_rand => //. iIntros (ip) "_"...
    (* pop the pivot from xs *)
    wp_apply (wp_remove_nth_unsafe _ xs l ip).
    { iPureIntro. split => //. apply (Nat.lt_le_trans _ _ _ (fin_to_nat_lt ip)).
      destruct xs => /= ; simpl in hn ; lia. }
    iIntros (pr_opt (p & r & pre & post & hpart & hpos & hpr & hr)).
    rewrite hpr. repeat (wp_pure ; unfold partition ; progress fold partition).
    (* partition xs \ p into smaller and larger elements *)
    wp_apply Partition => //.
    iIntros (le gt (xsle & xsgt & (hle & hgt & hperm) & ple & pgt))...
    (* sort xs_gt *)
    wp_apply "Hqs" => //. iIntros (gts (xs_gt_s & Lgts & Pgts & Sgts)).
    (* sort xs_le *)
    wp_apply "Hqs" => //. iIntros (les (xs_le_s & Lles & Ples & Sles))...
    (* re-assemble the sorted results *)
    replace (#p) with (inject p) by auto.
    wp_apply wp_list_cons => //. iIntros (p_xs_gt_s h_p_xs_gt).
    iApply wp_list_append => //. iIntros "!>" (xs_le_p_gt_s L).
    iApply "hφ".
    iExists (xs_le_s ++ p :: xs_gt_s). iPureIntro. repeat split => //.
    - clear -Ples Pgts hperm hpart.
      rewrite Pgts Ples. rewrite -Permutation_middle.
      rewrite hperm. rewrite Permutation_middle. rewrite -hpart. done.
    - clear -Sles Sgts ple pgt Ples Pgts. apply sorted_append => // ; intros.
      + apply ple. eapply Permutation_in => //.
      + apply pgt. eapply Permutation_in => //.
  Qed.

End quicksort.


*)






End program.



(*



(** Total mess, possibly not needed, but maybe needed for tc_quicksort_unfold *)


(* Source of many deeply annoying lemmas involving fin_enum *)
Fixpoint fin_inj_incr (n : nat) (i : fin n) : (fin (S n)) :=
  match i with
    0%fin => 0%fin
  | (FS _ i) => FS (fin_inj_incr _ i)
  end.

Lemma fin_inj_incr_to_nat (n : nat) (i : fin n) : fin_to_nat i = fin_to_nat (fin_inj_incr n i).
Proof.
  induction i as [|i' IH]; [done|].
  simpl. f_equal. done.
Qed.

(* Proof irrelevance for fin *)
Lemma fin_irrel (n : nat) (x y: fin n) : (fin_to_nat x = fin_to_nat y) -> (x = y).
Proof. Admitted.

Lemma fmap_compat `{A: Type} `{B: Type} f : list_fmap A B f = (fmap f).
Proof.
 apply functional_extensionality.
 intros.
 induction x; simpl; done.
Qed.

Lemma fin_inj_FS_comm (n : nat) (l : list (fin n)) :
  FS <$> (fin_inj_incr _ <$> l) = fin_inj_incr _ <$> (FS <$> l).
Proof.
  induction l; [done|].
  simpl in *.
  f_equal.
  f_equal.
  - apply functional_extensionality.
    intros.
    apply fin_irrel.
Admitted.


Lemma fin_enum_snoc_rec (n : nat) :
  (fin_enum (S n)) = (fin_inj_incr n <$> fin_enum n) ++ [(nat_to_fin (Nat.lt_succ_diag_r n) : fin (S n))%fin].
Proof.
  induction n as [|n' IH]; [done|].
  rewrite {1}/fin_enum.
  rewrite {1}/fin_enum in IH.
  rewrite IH.
  rewrite fmap_app app_comm_cons.
  f_equal; last first.
  - simpl.
    do 3 f_equal.
    apply proof_irrelevance.
  - rewrite /fin_enum /=.
    f_equal.
    rewrite fmap_compat.
    rewrite fin_inj_FS_comm.
    done.
Qed.


*)
