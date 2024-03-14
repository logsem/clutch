(** * Exact time credit accounting for Quicksort *)
From clutch.prob_lang Require Import lang notation tactics metatheory.
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre.
From clutch.lib Require Export array.
From Coq Require Export Reals Psatz.
Require Import Lra.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Definition in_place_pivot := #().
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
        let: "r" := in_place_pivot "arr" "pivot" in
        let: "left" := "arr" in
        let: "len_left" := Fst "r" in
        let: "right" := Snd "r" in
        let: "len_right" := ("len" - "right" + #1) in

        "quicksort" "left" "len_left" ;;
        "quicksort" "right" "len_right" ;;
        "arr")%V.




(* tc_quicksort(len) = (1/len) + 2 * sum(i=0 to len-1)(tc_quicksort i) *)

Definition range (j : nat) : list nat
 := [].

(* a mess *)

Program Fixpoint tc_quicksort (len : nat) {measure len} : nonnegreal
    := match len with
      | 0%nat => nnreal_zero
      | (S len1)%nat => nnreal_div ((tc_pivot len) + (foldr nnreal_plus nnreal_zero $ map _ $ range len) )%NNR (nnreal_nat len)
     end.
Next Obligation.
  intros.
  eapply tc_quicksort.
  (* want to use H < len from range? *)
Admitted.
Next Obligation. Admitted.

