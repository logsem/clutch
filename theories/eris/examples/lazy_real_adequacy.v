From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real real_decr_trial.
From clutch.eris.examples Require Import math.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(* We prove the simple adequacy statement of samplers e that returns a distribution of lazy reals *)
(* we compare to see whether the lazy real <= (x)/(2^y) *)
(* We have the inequality (x)<2^y *)
Definition pow2 : val :=
  rec: "pow2" "y":=
    if: "y"≤#0%nat then #(1%nat) else #2 * ("pow2" ("y"-#1)).

Definition is_zero : val :=
  (rec: "f" "α" "l" :=
     let, ("z", "l'") := get_chunk "α" "l" in
     if: "z" = #0 then "f" "α" "l'" else #false)%V.

Definition is_smaller_prog_aux : val :=
  (rec: "f" "α" "l" "x" "y" :=
     if: "y"=#0 then is_zero "α" "l"
     else
       let, ("z", "l'") := get_chunk "α" "l" in
       let: "y'" := "y" - #1 in 
       let: "p" := pow2 "y'" in
       if: "x"<"p"
       then (* first digit of (x)/(2^y) is 0*)
         if: "z"=#1 then #false
         else "f" "α" "l'" "x" "y'"
       else (* first digit of (x)/(2^y) is 1*)
         if: "z"=#0 then #true
         else "f" "α" "l'" ("x"-"p") "y'"
  )%V.

Definition is_smaller_prog : val :=
  λ: "l" "x" "y",
    let, ("α", "l'") := "l" in is_smaller_prog_aux "f" "x" "y" "α" "l'"
.
(*
Section adeqaucy.

  (* Lemma wp_pow (n m:nat): *)
  (*   {{{ True }}} *)
  (*     pow #n #m *)
  (*     {{{(x:nat), RET (#x); ⌜x = (n^m)%nat⌝ }}}. *)
  (* Proof. *)
  (*   iIntros (Φ) "_ HΦ". *)
  (*   iLöb as "IH" forall (Φ n m). *)
  (*   rewrite /pow. *)
  (*   wp_pures. rewrite -/pow. *)
  (*   case_bool_decide; wp_pures. *)
  (*   - iModIntro. iApply "HΦ". *)
  (*     assert (m = 0)%nat by lia. *)
  (*     simplify_eq. done. *)
  (*   - replace (Z.of_nat m - 1)%Z with (Z.of_nat (m-1)); last first. *)
  (*     + rewrite Nat2Z.inj_sub; first lia. *)
  (*       destruct m; last lia. done. *)
  (*     + wp_apply ("IH"). *)
  (*       iIntros (x) "%". *)
  (*       wp_pures. *)
  (*       iModIntro. *)
  (*       replace (_*_)%Z with (Z.of_nat (n*x)); last first. *)
  (*       * rewrite Nat2Z.inj_mul. f_equal. *)
  (*       * iApply "HΦ". iPureIntro. subst. *)
  (*         rewrite -PeanoNat.Nat.pow_succ_r'. f_equal. *)
  (*         destruct m; try done. lia. *)
  (* Qed. *)
  
End adequacy.
*)
