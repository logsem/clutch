From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling Require Import bernoulli.
#[local] Open Scope R.
#[local] Ltac done ::= 
    solve[lia | lra | nra | real_solver | tactics.done | auto].

Set Default Proof Using "Type*".

Section Examples.
  Context `{!erisGS Σ}.

  Example bernoulli_twice (N M : nat) (p := N / S M) :
    N ≤ S M →
    [[{ ↯ (1 - p^2) }]]
      let v1 := bernoulli #N #M in 
      let v2 := bernoulli #N #M in 
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

  Example bernoulli_different (N M : nat) (p := N / S M) :
    (0 < N < S M)%nat →
    [[{ ↯ (1 - 2 * p * (1 - p)) }]]
      let v1 := bernoulli #N #M in 
      let v2 := bernoulli #N #M in 
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
      let v1 := bernoulli #N #M in 
      let v2 := bernoulli #N #M in 
      v1 ≠ v2
    [[{ RET #false; True }]].
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
  #[local] Opaque INR.

  Context `{!erisGS Σ}.
  Variable N M : nat.
  Hypothesis (H0_lt_N_lt_SM : (0 < N < S M)%nat).

  Definition roulette_martingale_aux : val :=
    rec: "loop" "win" "bet" :=
      if: bernoulli #N #M = #0 
      then "loop" ("win" - "bet") (#2 * "bet")
      else "win" + "bet"
    .
  
  Definition roulette_martingale : expr :=
    λ: "_", roulette_martingale_aux #0 #1.

  Lemma roulette_martingale_aux_spec_aux (k : nat) (c g : Z) :
    (0 < g)%Z →
    (c < g)%Z →
    [[{↯ ((S M - N) / (S M + k))}]]
      roulette_martingale_aux #c #g
    [[{RET #(c + g); True}]].
  Proof.
    generalize dependent c.
    generalize dependent g.
    induction k as [|k IHk].
    - iIntros "%c %g %Hpos %Hlt %Φ Herr HΦ".
      rewrite /roulette_martingale /roulette_martingale_aux.
      wp_pures.
      wp_apply (bernoulli_success_spec_simple with "[Herr]") as "% ->".
      { iApply (ec_eq with "Herr"). 
        simpl_expr.
        rewrite Rmult_plus_distr_l Rmult_1_r.
        simpl_expr. }
      wp_pures.
      change (0 + 1)%Z with (Z.of_nat 1).
      by iApply "HΦ".
    - iIntros "%c %g %Hpos %Hlt %Φ Herr HΦ".
      rewrite /roulette_martingale /roulette_martingale_aux.
      wp_pures.
      set A := (S M - N)%nat.
      set B := (S M + k)%nat.
      set p := (N / S M).
      assert (0 < p < 1).
      { subst p. split; first apply Rmult_lt_0_compat; simpl_expr. }
      set ε1 := A / B.
      set ε2 := ((A / S B) - ε1 * (1 - p)) / p.
      wp_apply (twp_bernoulli_scale _ _ _ ε1 ε2 with "Herr") as "% [[-> Herr]|[-> Herr]]".
      { done. }
      { subst ε1. simpl_expr. }
      { subst ε2.
        apply Rmult_le_pos; last simpl_expr.
        subst ε1.
        rewrite !Rmult_assoc -(Rmult_minus_distr_l A).
        apply Rmult_le_pos; first real_solver.
        apply Rle_0_le_minus.
        rewrite Rmult_comm.
        simpl_expr.
        rewrite Rmult_minus_distr_l.
        simpl_expr.
        rewrite S_INR.
        rewrite -{3}(Rplus_0_r B) Rplus_assoc.
        simpl_expr.
        apply Rle_minus.
        unfold p, B.
        rewrite -Rmult_assoc.
        simpl_expr.
        rewrite -S_INR -mult_INR.
        destruct N; simpl_expr. }
      { rewrite -minus_INR // -plus_INR Nat.add_succ_r.
        fold A B p.
        rewrite -(Rplus_0_l (A / S B)).
        rewrite -(Rminus_diag (ε1 * (1 - N / S M))).
        rewrite !Rminus_def.
        rewrite !Rplus_assoc.
        simpl_expr.
        rewrite Rplus_comm.
        subst ε2.
        rewrite -!Rdiv_def.
        rewrite Rmult_assoc Rinv_l //. }
      + subst ε1 ε2 A B p.
        fold roulette_martingale_aux.
        wp_pures.
        wp_apply (IHk with "[Herr]"); try done.
        { iApply (ec_eq with "Herr"). rewrite minus_INR //. }
        rewrite -Z.add_diag Z.add_assoc Z.sub_add.
        by iApply "HΦ".
      + wp_pures.
        by iApply "HΦ".
  Qed.

  Lemma roulette_martingale_aux_spec (ε : R) (c g : Z) :
    (0 < ε) →
    (0 < g)%Z →
    (c < g)%Z →
    [[{↯ ε}]]
      roulette_martingale_aux #c #g
    [[{RET #(c + g); True}]].
  Proof.
    iIntros "%H_ε_pos %H_g_pos %H_c_lt_g %Φ Herr HΦ".
    assert (exists k : nat, (S M - N) / (S M + k)  <= ε ) as [k Hk].
    { assert (0 < S M - N); first rewrite -minus_INR //.
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
    simpl_expr.
  Qed.

  Example roulette_martingale_spec (ε : R) :
    (ε > 0) →
    [[{↯ ε}]]
      roulette_martingale #()
    [[{RET #(1); True}]].
  Proof.
    iIntros "%H_ε_pos %Φ Herr HΦ".
    rewrite /roulette_martingale.
    wp_pures.
    by wp_apply (roulette_martingale_aux_spec with "Herr").
  Qed.






End Roulette.