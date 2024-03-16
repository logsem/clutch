(** * Exact time credit accounting for Quicksort *)
From clutch.prob_lang Require Import lang notation tactics metatheory.
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre.
From clutch.lib Require Export array.
From Coq Require Export Reals Psatz.
Require Import Lra.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Definition swap :=
  (λ: "arr" "a" "b",
      let: "tmp" := !("arr" +ₗ "a") in
      "a" <- !("arr" +ₗ "b") ;;
      "b" <- "tmp")%V.


Definition in_place_pivot
  := (λ: "arr" "len" "pivot",
        (* Swap pivot with the last element *)
        swap "arr" "pivot" ("len" - #1) ;;
        let: "pivot_v" := !("arr" +ₗ ("len" - #1)) in

        let: "len_left" := ref #0 in
        (* rec inv.
              len_left < next <= len - 1
              for all 0 <= i < len_left, (arr[i] <= pivot)
              for all len_left <= i < next, (arr[i] > pivot)
              ⇒ if (next = len - 1), array is of the form [less than pivot, greater than pivot, pivot]
        *)
        (rec: "swap_next" "next" :=
           if: ("next" = ("len" - #1))
              then #()
              else (
                  if: (!("arr" +ₗ "next") ≤ "pivot_v")
                    then
                      (* next belongs in the left list *)
                      swap "arr" "next" "len_left" ;;
                      "len_left" <- !("len_left" + #1) ;;
                      "swap_next" ("next" + #1)
                    else
                      "swap_next" ("next" + #1)))
        #0 ;;

        (* Swap pivot back into the right spot*)
        swap "arr" !("len_left") ("len" - #1) ;;
        "len_left")%V.


(* let: "pivot_v" := !("arr" +ₗ "pivot") in *)

Definition tc_pivot : nat -> nonnegreal.
Admitted.


Check ⧖ (tc_pivot _) -∗ (WP in_place_pivot #() @ _ {{ fun _ => ⌜True ⌝ }})%I.


Definition quicksort :=
  (rec: "quicksort" "arr" "len" :=
     if: ("len" = #0)%E
      then "arr"
      else
        let: "pivot" := rand "len" in
        let: "len_left" := in_place_pivot "arr" "pivot" in
        let: "left" := "arr" in
        let: "right" := (#1 + "len_left") in
        let: "len_right" := ("len" - "right" + #1) in

        "quicksort" "left" "len_left" ;;
        "quicksort" "right" "len_right" ;;
        "arr")%V.


Definition tc_base : nonnegreal. Admitted.

(* tc_quicksort(len) = (1/len) + 2 * sum(i=0 to len-1)(tc_quicksort i) *)
Program Fixpoint tc_quicksort (len : nat) {measure len} : nonnegreal
    := match len with
      | 0%nat => tc_base
      | (S len1)%nat =>
          nnreal_plus (tc_pivot len) $
          nnreal_mult (nnreal_nat 2) $
          nnreal_div
            (foldr nnreal_plus nnreal_zero $ map (fun n => (tc_quicksort (fin_to_nat n))) $ fin_enum len)%NNR
            (nnreal_nat len)
     end.
Next Obligation. intros. apply fin_to_nat_lt. (* This is the reason I need the haunted fin_enum *) Qed.
Next Obligation. apply Wf.measure_wf, lt_wf. Qed.

(* Exhausting unfolding lemmas, provable. *)
Lemma tc_quicksort_0 : tc_quicksort 0%nat = tc_base.
Proof. Admitted.

(* Eliminate the hauntedness *)
Lemma tc_quicksort_unfold n :
  (1 <= n)%nat ->
  tc_quicksort n =
          nnreal_plus (tc_pivot n) $
          nnreal_mult (nnreal_nat 2) $
          nnreal_div
            (foldr nnreal_plus nnreal_zero $ map (fun i => ((tc_quicksort i))%NNR) $ seq 0%nat n)%NNR
            (nnreal_nat n).
Proof. Admitted.

Lemma tc_quicksort_bound_ind n' :
  (nnreal_div (tc_quicksort (S n')) (nnreal_nat (S n' +  1)%nat) <=
     (nnreal_div (tc_pivot (S n')) (nnreal_nat (S n' + 1)) +
      nnreal_div (tc_quicksort n') (nnreal_nat (n' + 1)%nat))%NNR)%R.
Proof.
  Opaque INR.
  (* Match notations with my paper derivation (for now) *)
  remember (S n') as n.
  remember tc_quicksort as C.
  remember tc_pivot as m.
  simpl.
  (* Goal: C(n)/(n+1) <= m(n)/(n+1) + C(n-1)/n *)

  (* Suffices: C(n)/(n+1) <= m(n)/(n+1) - m(n-1)(n-1)/n(n+1) + C(n-1)/n *)
  etrans; last first.
  { eapply Rplus_le_compat_l.
    rewrite -(Rplus_0_l (_ * _)%R).
    eapply Rplus_le_compat_r.
    assert (Hinst: (-((m n')*(n-1) / n / (n + 1)) <= 0)%R) by admit.
    eapply Hinst.
  }

  (* Should be equal *)
  apply Req_le.

  (* Multiply by n+1 and simplify *)
  (* Suffices: C(n) <= m(n) - m(n-1)(n-1)/n + C(n-1)(n+1)/n *)
  eapply (Rmult_eq_reg_r (INR (n + 1))); last admit.
  rewrite Rmult_assoc Rinv_l; last admit.
  rewrite Rmult_1_r.
  do 2 rewrite Rmult_plus_distr_r.
  rewrite Rmult_assoc Rinv_l; last admit.
  rewrite Rmult_1_r.
  rewrite Ropp_mult_distr_l_reverse.
  replace (((((m n') * (n - 1)) / n) / (n + 1)) * ((n + 1)%nat))%R
    with (((((m n') * (n - 1)) / n)))%R; last first.
  { do 3 rewrite -Rmult_div_assoc.
    rewrite Rmult_assoc.
    apply Rmult_eq_compat_l.
    simpl.
    admit.  (* doable *)
  }

  (* Proof is different when n' = 0*)
  destruct n' as [| n'1].
  { simplify_eq.
    rewrite tc_quicksort_unfold; last lia.
    Transparent INR.
    simpl.
    rewrite tc_quicksort_0.
    lra.
    Opaque INR.
  }

  (* Proof should follow but unfolding C *)
  rewrite Heqn HeqC.
  rewrite tc_quicksort_unfold; last lia.
  (* rewrite tc_quicksort_unfold; last lia. *)
  Opaque seq.
  rewrite -Heqm -HeqC -Heqn /=.
  apply Rplus_eq_compat_l.
  replace (nonneg (foldr nnreal_plus nnreal_zero (map (λ i : nat, C i) (seq 0 n))))
    with (C (S n'1) + (nonneg (foldr nnreal_plus nnreal_zero (map (λ i : nat, C i) (seq 0 (S n'1))))))%R; last first.
  { simpl. admit. }
  simpl.

  (* Simplify *)
  rewrite Rmult_plus_distr_r Rmult_plus_distr_l.
  rewrite Rmult_plus_distr_r Rmult_plus_distr_l.
  rewrite /= Rmult_1_l.
  replace (nonneg (m (S n'1)) * INR n + nonneg (m (S n'1)) * - (1))%R
      with (nonneg (m (S n'1)) * (INR n - 1))%R by lra.
  rewrite Heqn.
  (* All terms have an INR (S (S n'1)) denominator *)
  apply (Rmult_eq_reg_r (INR (S (S n'1)))); last admit.
  rewrite -Rmult_plus_distr_r.
  rewrite (Rmult_plus_distr_r _ _ (INR _)%R).
  rewrite Rmult_assoc Rinv_l; last admit.
  rewrite Rmult_1_r.
  do 2 rewrite Rmult_assoc.
  rewrite Rmult_assoc Rinv_l; last admit.
  rewrite Rmult_1_r.
  rewrite Rmult_plus_distr_r.
  rewrite -Ropp_mult_distr_l.
  replace (nonneg (m (S n'1)) * (INR (S (S n'1)) - 1) / INR (S (S n'1)) * INR (S (S n'1)))%R
      with (nonneg (m (S n'1)) * (INR (S (S n'1)) - 1))%R; last first.
  { rewrite Rmult_assoc.
    rewrite Rinv_l; last admit.
    lra.
  }

  rewrite Rmult_assoc.
  rewrite (Rmult_comm (/ _) _).
  rewrite Rmult_assoc.
  rewrite (Nat.add_1_r n'1).
  rewrite Rinv_l; last admit.
  rewrite Rmult_1_r.
  rewrite (Nat.add_1_r).
  rewrite (S_INR (S (S _))).
  rewrite Rmult_plus_distr_l Rmult_1_r.
  rewrite -Rplus_assoc (Rplus_comm _ (nonneg _)).
  rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.

  apply (Rplus_eq_reg_r (-C (S n'1))).
  rewrite Rplus_comm Rplus_assoc.
  rewrite -Rplus_assoc Rplus_opp_l Rplus_0_l.
  simpl.
  replace (nonneg (C (S n'1)) * INR (S (S n'1)) + - nonneg (C (S n'1)))%R
    with (nonneg (C (S n'1)) * (INR (S (S n'1)) - 1))%R; last first.
  { rewrite /= (S_INR (S n'1)). lra. }
  rewrite Ropp_mult_distr_l.
  rewrite -Rmult_plus_distr_r.

  (* Unfold C (S n'1)*)
  rewrite HeqC tc_quicksort_unfold; last lia.
  rewrite -HeqC -Heqm /=.
  remember (foldr nnreal_plus nnreal_zero (map (λ i : nat, C i) (seq 0 (S n'1)))) as Tsum.
  rewrite -Rplus_assoc.
  rewrite Rplus_opp_l Rplus_0_l.
  rewrite (S_INR (S n'1)).
  rewrite Rplus_minus_r.
  rewrite Rmult_assoc.
  Set Printing Parentheses.
  rewrite Rmult_assoc.
  rewrite Rinv_l; last admit.
  lra.
  Transparent seq.
  Transparent INR.
Admitted.



Lemma tc_quicksort_bound_closed n :
  ((nnreal_div (tc_quicksort n) (nnreal_nat (n + 1)%nat))
    <= (foldr nnreal_plus (tc_quicksort 0%nat) $
        map (fun i => nnreal_div (tc_pivot (i + 1)%nat) (nnreal_nat (i + 2)%nat)) $
        seq 0%nat n))%R.
Proof.
  induction n as [|n' IH]; [simpl; lra|].
  etrans; first eapply tc_quicksort_bound_ind.
  etrans; first eapply Rplus_le_compat_l, IH.
  apply Req_le.
  Opaque INR.
  replace
    (foldr nnreal_plus (tc_quicksort 0)
     (map (λ i : nat, (nnreal_div (tc_pivot (i + 1)) (nnreal_nat (i + 2)))) (seq 0 (S n'))))
    with
    ((nnreal_div (tc_pivot (n' + 1)) (nnreal_nat (n' + 2))) +
      (foldr nnreal_plus (tc_quicksort 0)
     (map (λ i : nat, (nnreal_div (tc_pivot (i + 1)) (nnreal_nat (i + 2)))) (seq 0 n'))))%NNR;
    last first.
  { rewrite seq_S map_app /=.
    rewrite foldr_snoc /=.
     rewrite foldr_comm_acc; [done|].
     intros.
     rewrite nnreal_plus_comm nnreal_plus_assoc.
     do 2 rewrite -nnreal_plus_assoc.
     f_equal.
     apply nnreal_plus_comm.
  }
  apply Rplus_eq_compat_r.
  do 3 f_equal; try lia.
Qed.

(* Established bound: C(n)/(n+1) <= C(0) + sum_{i=1}^n (m(n)/(n+1))
  Good enough to get n log n when m(n) is linear *)










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



