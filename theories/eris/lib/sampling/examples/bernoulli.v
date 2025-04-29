(**
  This file aims to give some examples of usage of the bernoulli distribution in programs and their specification
*)

From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling.bernoulli Require Import interface.

#[local] Open Scope R.
#[local] Ltac done ::= 
    solve[lia | lra | nra | real_solver | tactics.done | auto].

Set Default Proof Using "Type*".

Section Examples.
  Context `{!erisGS Σ}.
  Context `{!bernoulli_spec bernoulli}.

  (**
    In this example, we prove that with error credit `1 - p²`, we can do 2 independant bernoulli experiments that both succeed.

    To do so, we split the credit into 2 credits of value `1 - p`, used to ensure the success of the first call, and `p(1 - p)`, which can be scaled up to `1 - p`, to ensure the success of the second call
   *)
  Example bernoulli_twice (N M : nat) (p := N / S M) :
    N ≤ S M →
    [[{ ↯ (1 - p^2) }]]
      let v1 := bernoulli #() #N #M in 
      let v2 := bernoulli #() #N #M in 
      (v1, v2)
    [[{ RET (#1, #1); True }]].
  Proof.
    iIntros "%Hlt %Φ Herr HΦ".
    assert (0 <= p <= 1) as Hp. {
      split; subst p; simpl_expr.
    }
    replace (1 - p ^ 2) with ((1 - p) + (p - p^2)) by lra.
    iPoseProof (ec_split with "Herr") as "[Herr1 Herr2]" => //.
    wp_apply (bernoulli_success_spec _ _ (p - p^2) (1 - p) with "[$Herr1 $Herr2]") as "%v [Herr ->]" => //.
    { fold p; nra. }
    wp_apply (bernoulli_success_spec_simple with "Herr") as (?) "->".
    wp_pures.
    by iApply "HΦ".
  Qed.


  (** 
    The next 2 examples showcase how to do 2 independant bernoulli draw, with the first expecting different outcomes and the second the same outcome twice. These examples showcase the use of credit scaling, as doing a naive approach where we require credits where we need credit `max(p, (1 - p))` 
  *)
  Example bernoulli_different (N M : nat) (p := N / S M) :
    (0 < N < S M)%nat →
    [[{ ↯ (1 - 2 * p * (1 - p)) }]]
      let v1 := bernoulli #() #N #M in 
      let v2 := bernoulli #() #N #M in 
      v1 ≠ v2
    [[{ RET #true; True }]].
  Proof.
    iIntros "%Hlt %Φ Herr HΦ".
    assert (0 < p < 1) as Hp. {
      split; subst p; simpl_expr.
    } 
    (* Not required but good to note that the error credit assumption is not impossible *)
    assert (0 <= 1 - 2 * p * (1 - p) < 1) by nra.
    assert (1 - 2 * p * (1 - p) = (1 - p)^2 + p^2) by lra.
    wp_apply (twp_bernoulli_scale _ _ _ (1 - p) p with "Herr") 
      as "%k [[-> Herr]|[-> Herr]]"; fold p =>//.
    - wp_apply (bernoulli_success_spec_simple with "Herr") 
        as "%v ->".
      wp_pures.
      by iApply "HΦ".
    - wp_apply (bernoulli_failure_spec_simple with "Herr") 
        as "%v ->".
      wp_pures.
      by iApply "HΦ".
  Qed.

  Example bernoulli_same (N M : nat) (p := N / S M) :
    (0 < N < S M)%nat →
    [[{ ↯ (2 * p * (1 - p)) }]]
      let v1 := bernoulli #() #N #M in 
      let v2 := bernoulli #() #N #M in 
      v1 = v2
    [[{ RET #true; True }]].
  Proof.
    iIntros "%Hlt %Φ Herr HΦ".
    assert (0 < p < 1) as Hp. {
      split; subst p; simpl_expr.
    }
    (* Not required but good to note that the error credit assumption is not inconsistent *)
    assert (0 <= 2 * p * (1 - p) < 1) by nra.
    wp_apply (twp_bernoulli_scale _ _ _ p (1 - p) with "Herr") 
      as "%k [[-> Herr]|[-> Herr]]"; fold p =>//.
    - wp_apply (bernoulli_failure_spec_simple with "Herr") 
        as "%v ->".
      wp_pures.
      by iApply "HΦ".
    - wp_apply (bernoulli_success_spec_simple with "Herr") 
        as "%v ->".
      wp_pures.
      by iApply "HΦ".
  Qed.
End Examples.

Section Roulette.
  (**
    This section defines a betting strategy where a player starts to bet that a bernoulli experiment will succeed with 1 unit, and doubles the bet everytime it fails until one succeds, leading to an almost sure gain of 1 unit (assuming infinite money to place bets)
    
  *)
  Context `{!erisGS Σ}.
  Context `{!bernoulli_spec bernoulli}.
  
  #[local] Opaque INR.

  Variables N M : nat.
  Hypothesis H0_lt_N_lt_SM : (0 < N < S M)%nat.

  Definition roulette_martingale_aux : val :=
    rec: "loop" "win" "bet" :=
      if: bernoulli #() #N #M = #0 
      then "loop" ("win" - "bet") (#2 * "bet")
      else "win" + "bet"
    .
  
  Definition roulette_martingale : expr :=
    roulette_martingale_aux #0 #1.


  (**
    This is the main lemma, from which we derive almost sure termination with expected outcome. It works as follows:

    First we proceed by error induction, as can be seen in the spline examples.
    - For the base case, we have `1 - p` error credits, enough to ensure a success.
    - For the inductive case, we can use error scaling to transform `(1 - p) * (S M - N) / (S M + k)` credits into `(S M - N) / (S M + k)` in the case of a failure of the experiment, which is what is needed to apply the induction hypothesis, or 0 credits in the case of a success, where the required property is ensured.
      We just need to be sure that we have at least `(1 - p) * (S M - N) / (S M + k)` credits, which we verify.

  *)
  Lemma roulette_martingale_aux_spec_aux (k : nat) (c g : Z) :
    (0 < g)%Z →
    (c < g)%Z →
    [[{↯ ((S M - N) / (S M + k))}]]
      roulette_martingale_aux #c #g
    [[{RET #(c + g); True}]].
  Proof.
    iInduction k as [|k] "IHk" forall (c g).
    - iIntros "%H_g_pos %H_c_lt_g %Φ Herr HΦ".
      rewrite /roulette_martingale /roulette_martingale_aux.
      wp_pures.
      wp_apply (bernoulli_success_spec_simple with "[Herr]") as "% ->".
      { iApply (ec_eq with "Herr"). 
        simpl_expr.
        rewrite Rmult_plus_distr_l Rmult_1_r.
        simpl_expr. }
      wp_pures.
      by iApply "HΦ".
    - iIntros "%H_g_pos %H_c_lt_g %Φ Herr HΦ".
      rewrite /roulette_martingale /roulette_martingale_aux.
      wp_pures.
      set p := (N / S M).
      assert (0 < p < 1).
      { subst p. split; first apply Rmult_lt_0_compat; simpl_expr. }
      set ε1 := (S M - N)%nat / (S M + k)%nat.
      iAssert (↯ (ε1 * (1 - p))) with "[Herr]" as "Herr".
      { assert (S M + k > 0) by rewrite -plus_INR //.
        iApply (ec_weaken with "Herr").
        split.
        - subst ε1. apply Rmult_le_pos; simpl_expr.
        - subst ε1. rewrite -minus_INR // -plus_INR. simpl_expr.
          rewrite -!Rmult_assoc (Rmult_comm (S M + S k)%nat) !Rmult_assoc. 
          rewrite -{2}(Rmult_1_r (S M - N)%nat).
          simpl_expr.
          rewrite !plus_INR.
          rewrite !Rmult_plus_distr_l Rmult_plus_distr_r.
          simpl_expr.
          rewrite (Rmult_comm _ p) -!Rmult_assoc.
          rewrite -!Ropp_mult_distr_l_reverse -!Rmult_plus_distr_r .
          rewrite {1}(S_INR k) Rplus_assoc.
          simpl_expr.
          rewrite -{2}(Rplus_0_r k) Rplus_assoc.
          simpl_expr.
          rewrite !Ropp_mult_distr_l_reverse -Rminus_def.
          apply Rle_minus.
          simpl_expr.
          rewrite -plus_INR -mult_INR //. }
      wp_apply (twp_bernoulli_scale _ _ _ ε1 0 with "Herr") as "% [[-> Herr]|[-> Herr]]";  subst ε1 p; simpl_expr.
      + fold roulette_martingale_aux.
        wp_pures.
        rewrite plus_INR minus_INR //.
        wp_apply ("IHk" with "[] [] Herr"); try (iPureIntro; done).
        rewrite -Z.add_diag Z.add_assoc Z.sub_add.
        by iApply "HΦ".
      + wp_pures.
        by iApply "HΦ".
  Qed.

  (** This lemma proves almost sure termination, as in the spline examples *)
  Lemma roulette_martingale_aux_spec (ε : R) (c g : Z) :
    (0 < ε) →
    (0 < g)%Z →
    (c < g)%Z →
    [[{↯ ε}]]
      roulette_martingale_aux #c #g
    [[{RET #(c + g); True}]].
  Proof.
    iIntros "%H_ε_pos %H_g_pos %H_c_lt_g %Φ Herr HΦ".
    assert (exists k : nat, (S M - N) / (S M + k) <= ε ) as [k Hk].
    { assert (0 < S M - N) by rewrite -minus_INR //.
      destruct (Rle_exists_nat (S M - N) ε) as [t Ht]; first rewrite -minus_INR; simpl_expr.
      pose proof (pos_INR N).
      pose proof (pos_INR t).
      exists t. left.
      eapply Rle_lt_trans; eauto.
      apply Rmult_le_compat_l; first lra.
      change 1 with (1%nat : R).
      rewrite -!plus_INR.
      apply Rinv_le_contravar; simpl_expr. }
    wp_apply (roulette_martingale_aux_spec_aux k with "[Herr]"); auto.
    iApply (ec_weaken with "Herr").
    split; last done.
    rewrite -!plus_INR -!minus_INR //.
  Qed.

  Example roulette_martingale_spec (ε : R) :
    ε > 0 →
    [[{↯ ε}]]
      roulette_martingale
    [[{RET #1; True}]].
  Proof.
    iIntros "%H_ε_pos %Φ Herr HΦ".
    by iApply (roulette_martingale_aux_spec with "Herr").
  Qed.  

End Roulette.
