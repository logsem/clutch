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

(* Tighter bounding argument necessitates the pivot take time An+B *)
Definition tc_pivot_lin (A B n : nat) : nonnegreal := nnreal_nat (A*n+B)%nat.


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
Proof. Admitted.

(* Eliminate the hauntedness *)
Lemma tc_quicksort_unfold A B n :
  (1 <= n)%nat ->
  tc_quicksort A B n =
          nnreal_plus (tc_pivot_lin A B n) $
          nnreal_mult (nnreal_nat 2) $
          nnreal_div
            (foldr nnreal_plus nnreal_zero $ map (fun i => ((tc_quicksort A B i))%NNR) $ seq 0%nat n)%NNR
            (nnreal_nat n).
Proof. Admitted.


Lemma tc_quicksort_bound_ind n' A B (HAB : (B <= A)%nat) :
  (nnreal_div (tc_quicksort A B (S n')) (nnreal_nat (S n' +  1)%nat) <=
     (nnreal_div (nnreal_nat (2* A)%nat) (nnreal_nat (S n' + 1)%nat) +
      nnreal_div (tc_quicksort A B n') (nnreal_nat (n' + 1)%nat))%NNR)%R.
Proof.
  remember (S n') as n.
  remember (tc_quicksort A B) as C.
  simpl.

  etrans; last first.
  { (* Include the (B-A)/(n(n+1)) term *)
    eapply Rplus_le_compat_l.
    rewrite -(Rplus_0_l (_ * _)%R).
    eapply Rplus_le_compat_r.
    assert (Hinst: (((B - A) / (n * (n+1)) <= 0)%R)).
    { apply Rcomplements.Rle_div_l; admit. (* Both true *)
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
    replace ((A + (A + 0))%nat * / (1 + 1))%R with (INR A) by admit.
    rewrite Nat.mul_1_r.
    rewrite Rmult_plus_distr_r.
    replace ((1 + 1) * nonneg tc_base * / (1 + 1))%R with (nonneg tc_base) by admit.
    rewrite -Rplus_assoc.
    apply Rplus_eq_compat_r.
    rewrite plus_INR.
    lra.
  }

  (* Get rid of some n+1 denominators *)
  eapply (Rmult_eq_reg_r (INR (n + 1))); last admit.
  rewrite Rmult_assoc Rinv_l; last admit.
  rewrite Rmult_1_r.
  do 2 rewrite Rmult_plus_distr_r.
  rewrite Rmult_assoc Rinv_l; last admit.
  rewrite Rmult_1_r.
  rewrite Rdiv_mult_distr.
  Set Printing Parentheses.
  replace (((((INR B) - (INR A)) / (INR n)) / ((INR n) + 1)) * (INR (n + 1)))%R
     with ((((INR B - INR A)) / (INR n)))%R; last first.
  { (* True *) admit. }

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
  apply (Rmult_eq_reg_r (INR n));  last admit.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_assoc.
  rewrite Rmult_assoc.
  rewrite Rinv_l; last admit.
  rewrite Rmult_1_r.
  rewrite Rmult_assoc.
  rewrite (Rmult_comm (/ (INR n))).
  rewrite -Rmult_assoc.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_assoc.
  rewrite Rinv_l; last admit.
  rewrite Rmult_1_r.
  replace (((INR B - INR A) / (INR n)) * (INR n))%R with (INR B - INR A)%R; last first.
  { rewrite Rdiv_def.
    rewrite Rmult_assoc.
    rewrite Rinv_l; last admit.
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
  replace ((- (INR (n + 1))) + (INR 2))%R with (-(S n''))%R; last admit.

  (* Unfold C *)
  rewrite HeqC.
  rewrite tc_quicksort_unfold; last lia.
  rewrite -HeqC -HeqSR /=.

  (* Cancel the sums *)
  rewrite Rmult_plus_distr_l.
  replace ((- (INR (S n''))) * ((INR 2) * ((nonneg SR) * (/ (INR (S n''))))))%R
     with ((- (INR 2) * ((nonneg SR))))%R; last first.
  { admit. }
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
  replace (INR (S (S n'')))%R with (1 + INR (S n''))%R by admit.
  replace ((INR (A + (A + 0))))%R with (INR A + INR A)%R by admit.
  replace ((INR ((A * (S (S n''))) + B)))%R with ((INR A) * (INR (S n'')) + (INR A) + (INR B))%R by admit.
  lra.
Admitted.

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
