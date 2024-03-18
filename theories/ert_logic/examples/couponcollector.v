(** * Exact time credit accounting for Coupon collecting *)
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From Coq Require Export Reals Psatz.
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
