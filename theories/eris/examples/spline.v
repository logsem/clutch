(** * Examples related to rejection samplers with a bounded number of attempts *)
From clutch.eris Require Export eris error_rules.
From clutch Require Export examples.approximate_samplers.approx_sampler_lib.
From Coquelicot Require Import Series.
From Stdlib Require Import Lra.

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
    ↯ (n / (n + k + 1)) -∗
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
        wp_apply (twp_rand_err_filter_below n n' _ _ (1%R)); last first.
        * iFrame.
          iIntros (x) "[%Hx | Herr]".
          ** wp_pures.
             rewrite bool_decide_eq_false_2; last by lia.
             wp_pures. done.
          ** iPoseProof (ec_contradict with "Herr") as "?"; auto.
             simpl. lra.
        * simpl.
          rewrite Hn S_INR.
          rewrite Rplus_0_r Rmult_1_l.
          rewrite Rmult_assoc Rinv_l; [lra|].
          pose proof (pos_INR n').
          lra.
        * lra.
        * lia.
    - iIntros "Herr".
      wp_rec.
      wp_pures.
      destruct n as [|n'] eqn:Hn.
      + wp_pures. done.
      + rewrite bool_decide_eq_false_2; last by lia.
        rewrite -Hn.
        wp_pures.
        wp_apply (twp_rand_err_filter_below (S n') (n') _ _ ((n+1)/(n+m+2))); last first.
        * iFrame.
          iIntros (x) "[%Hx | Herr]".
          ** wp_pures.
             rewrite bool_decide_eq_false_2; last by lia.
             wp_pures. done.
          ** wp_pures.
             case_bool_decide; [wp_pures|by wp_pures].
             replace #(n+1) with #(S n); last first.
             { do 2 f_equal. lia. }
             iApply ("IH" with "[Herr]").
             rewrite S_INR.
             replace (n+1+m+1) with (n+m+2) by lra.
             iFrame.
        * rewrite Hn.
          do 2 rewrite S_INR.
          replace (n' + 1 + (m + 1) + 1) with (n' + 1 + m + 2); lra.
        * pose proof (pos_INR n).
          pose proof (pos_INR m).
          apply Rcomplements.Rdiv_le_0_compat; lra.
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
    assert (exists k : nat, n / (n + k + 1)  <= ε ) as [k Hk].
    { destruct (Rle_exists_nat n ε) as [t Ht]; auto.
      - apply pos_INR.
      - exists t.
        pose proof (pos_INR n).
        pose proof (pos_INR t).
        left.
        eapply Rle_lt_trans; eauto.
        apply Rmult_le_compat_l; [lra|].
        apply Rinv_le_contravar; lra.
    }
    iApply (spline_AST_aux k with "[Herr]").
    iApply (ec_weaken with "Herr").
    split.
    { apply Rcomplements.Rdiv_le_0_compat.
      - apply pos_INR.
      - pose proof (pos_INR n).
        pose proof (pos_INR k).
        lra.
    }
    etrans; done.
  Qed.


End escaping_spline.

(*

Section uniform_rw.

  Local Open Scope R.
  Context `{!erisGS Σ}.

  Definition urw : val :=
    (rec: "f" "n" :=
       if: "n" < #1
         then #()
         else let: "x" := (rand #1) in
                if: ("x" < #1)
                then "f" ("n" + #1)
                else "f" ("n" - #1)).


  (** Using mathematical induction on k *)
  Theorem urw_AST_aux (k : nat) (n : nat) E :
    ↯ (n / (k+1)) -∗
      WP urw #n @ E [{ v, True }].
  Proof.
    induction k.
    - iIntros "Herr".
      destruct n.
      + rewrite /urw.
        wp_pures.
        done.
      + iPoseProof (ec_weaken _ 1 with "Herr") as "Herr".
        ** split; [lra|].
           rewrite Rplus_0_l.
           rewrite Rdiv_1_r.
           pose proof (pos_INR n).
           admit.
        ** iPoseProof (ec_contradict with "Herr") as "?"; auto.
           lra.
    -

*)
