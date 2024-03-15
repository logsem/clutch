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

(* tc_quicksort(len) = (1/len) + 2 * sum(i=0 to len-1)(tc_quicksort i) *)
Program Fixpoint tc_quicksort (len : nat) {measure len} : nonnegreal
    := match len with
      | 0%nat => nnreal_zero
      | (S len1)%nat =>
          nnreal_plus (tc_pivot len) $
          nnreal_mult (nnreal_nat 2) $
          nnreal_div
            (foldr nnreal_plus nnreal_zero $ map (fun n => (tc_quicksort (fin_to_nat n))) $ fin_enum len1)%NNR
            (nnreal_nat len)
     end.
Next Obligation. intros. eapply Nat.lt_trans; [eapply fin_to_nat_lt|lia]. Qed.
Next Obligation. apply Wf.measure_wf, lt_wf. Qed.
