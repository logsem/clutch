(** * Examples related to rejection samplers with a bounded number of attempts *)
From clutch.eris Require Export eris error_rules.
From clutch Require Export examples.approximate_samplers.approx_sampler_lib.
From Coquelicot Require Import Series.
Require Import Lra.

Set Default Proof Using "Type*".

Section escaping_spline.

  (** * Example 5.4 from "A New Proof Rule for Almost-Sure Termination" by McIver et al. *)

  Local Open Scope R.
  Context `{!erisGS Σ}.

  Definition spline : val :=
    (rec: "f" "n" :=
       if: "n" < #1
         then #()
         else let: "x" := (rand "n") in
                if: ("x" < "n")
                then "f" ("n" + #1)
                else #()).


  (** Using mathematical induction on k *)
  Theorem spline_AST_aux (k : nat) (n : nat) E :
    ↯ (nnreal_div (nnreal_nat n) (nnreal_nat (S n + k)%nat)) -∗
      WP spline #n @ E [{ v, True }].
  Proof.
    iInduction (k) as [|m] "IH" forall (n).
    - iIntros "Herr".
      wp_rec.
      wp_pures.
      destruct n as [|n'] eqn:Hn.
      + wp_pures. done.
      + rewrite bool_decide_eq_false_2; last by lia.
        rewrite -Hn.
        wp_pures.
        wp_apply (twp_rand_err_filter_below n n' _ _ (1%NNR)); last first.
        * iFrame.
          iIntros (x) "[%Hx | Herr]".
          ** wp_pures.
             rewrite bool_decide_eq_false_2; last by lia.
             wp_pures. done.
          ** iPoseProof (ec_contradict with "Herr") as "?"; auto.
             simpl. lra.
        * rewrite -plus_n_O -Nat.add_1_r.
          simpl.
          rewrite plus_INR Rmult_1_l /=.
          rewrite Rmult_assoc (Rmult_comm _ (n+1)) -Rmult_assoc.
          rewrite Rmult_inv_r_id_l.
          ** rewrite Hn S_INR; lra.
          ** assert (0 <= n) by apply pos_INR. lra.
        * lia.
    - iIntros "Herr".
      wp_rec.
      wp_pures.
      destruct n as [|n'] eqn:Hn.
      + wp_pures. done.
      + rewrite bool_decide_eq_false_2; last by lia.
        rewrite -Hn.
        wp_pures.
        wp_apply (twp_rand_err_filter_below (S n') (n') _ _ ((nnreal_nat (S n) / nnreal_nat (S (S n) + m))%NNR)); last first.
        * iFrame.
          iIntros (x) "[%Hx | Herr]".
          ** wp_pures.
             rewrite bool_decide_eq_false_2; last by lia.
             wp_pures. done.
          ** wp_pures.
             case_bool_decide; [wp_pures|by wp_pures].
             replace #(n+1) with #(S n); last first.
             { do 2 f_equal. lia. }
             iApply ("IH" with "Herr").
        * rewrite -Hn.
          rewrite -Nat.add_1_r.
          rewrite -(Nat.add_1_r (n+1)).
          rewrite -(Nat.add_1_r m).
          simpl.
          rewrite (Rmult_comm _ (n' + 1)).
          rewrite (Rmult_comm _ (n + 1)).
          do 2 rewrite -Rmult_assoc.
          right.
          f_equal.
          ** rewrite plus_INR Hn S_INR /=. lra.
          ** f_equal.
             do 6 rewrite plus_INR. lra.
        * lia.
        * rewrite -Hn Nat2Z.id.
          done.
   Qed.


  Theorem spline_AST (n : nat) (ε : nonnegreal) E :
    (0 < ε)%R ->
    ↯ ε -∗
      WP spline #n @ E [{ v, True }].
  Proof.
    iIntros (Hpos) "Herr".
    assert (exists k : nat, nnreal_div (nnreal_nat n) (nnreal_nat (S n + k)) <= ε ) as [k Hk].
    { rewrite -Nat.add_1_r /=.
      destruct (Rle_exists_nat n ε) as [t Ht]; auto.
      - apply pos_INR.
      - exists t.
        pose proof (pos_INR n).
        pose proof (pos_INR t).
        left.
        eapply Rle_lt_trans; eauto.
        do 2 rewrite plus_INR; simpl.
        apply Rmult_le_compat_l; [lra|].
        apply Rinv_le_contravar; lra.
    }
    iApply (spline_AST_aux k with "[Herr]").
    iApply (ec_weaken with "Herr").
    split.
    { apply Rcomplements.Rdiv_le_0_compat.
      - apply pos_INR.
      - apply lt_0_INR. lia. }      
    etrans; done.
  Qed.


End escaping_spline.
