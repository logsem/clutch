(** * Exact time credit accounting for Coupon collecting *)
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre problang_wp proofmode.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From iris.proofmode Require Export proofmode.
From Coq Require Export Reals Psatz.
From Coquelicot Require Export Hierarchy.
Require Import Lra.


Set Default Proof Using "Type*".

Section Coupon.
  Variables coupon':nat.
  Definition coupon:= S coupon'.

  Definition coupon_helper : expr :=
    rec: "coupon_helper" "a" "cnt" :=
      if: "cnt" = #coupon then #() else
        let: "k" := rand (#coupon') in
        (if: ! ("a" +ₗ "k") 
        then "coupon_helper" "a" "cnt"
         else ("a" +ₗ "k") <- #true ;;
             "coupon_helper" "a" ("cnt"+#1)).

  Definition coupon_collection : expr :=
    λ: "n",
      let: "a" := AllocN #coupon #false in
      let: "cnt" := ref #0 in
      coupon_helper "a" "cnt".
End Coupon.

Definition harmonic_sum:= sum_n_m (λ x, /INR x).

Local Lemma coupon_etc_credit_split p coupon:
  (p≠0)%nat -> (coupon ≠ 0)%nat -> (p<coupon)%nat -> p/coupon + (coupon-p)/coupon * (1 + (coupon/p)) = (coupon/p).
Proof.
  intros H1 H2. 
  rewrite Rmult_plus_distr_l -Rplus_assoc Rmult_1_r.
  replace (_/_+_) with 1.
  - replace (_*_) with ((coupon-p)/p).
    + replace 1 with (p/p).
      * rewrite -Rdiv_plus_distr.
        by replace (_+_) with (INR coupon) by lra.
      * apply Rdiv_diag. replace 0 with (INR 0) by done. by move => /INR_eq.
    + rewrite Rmult_div_assoc -Rmult_div_swap -Rmult_div_assoc.
      rewrite Rdiv_diag; first lra.
      replace 0 with (INR 0) by done.
      by apply not_INR.
  - rewrite -Rdiv_plus_distr.
    replace (p+_) with (INR coupon) by lra.
    rewrite Rdiv_diag; first lra.
    replace 0 with (INR 0) by done.
    by apply not_INR.
Qed.


Section proofs.
  Context `{!ert_clutchGS Σ}.

  Notation tc_end:= (nnreal_nat 6).
  Notation tc_mid:=(nnreal_nat 9999999999999).

  Local Lemma wp_coupon_helper_end (coupon':nat) (l:loc) E: 
    {{{ ⧖ (tc_end) }}} coupon_helper coupon' #l #(S coupon') @ E {{{ RET #(); True}}}.
  Proof.
    iIntros (Φ) "Hx HΦ".
    wp_pures.
    case_bool_decide; last first.
    { exfalso. apply H. f_equal. }
    wp_pures.
    iApply "HΦ".
    done.
  Qed.

  Local Lemma wp_coupon_helper_ind (coupon':nat) (l:loc) (n:nat) E:
    (n<S coupon')%nat -> 
    {{{ ⧖ (tc_end + )%NNR}}}
    
  
End proofs.
