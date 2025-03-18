From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.

Local Ltac done ::= lia || lra || nra || real_solver || tactics.done || auto.
Ltac add_hint t := let n := fresh "hint" in have n := t.


Section Bernoulli.
  Context `{!erisGS Σ}.
  Local Open Scope R.
  Program Definition bernoulli_distr (p : R) (p_pos : 0 <= p <= 1) : distr (fin 2) := {|
    pmf := λ x, if bool_decide (x = 1)%fin then p else (1 - p)%R
  |}.
  Next Obligation.
    move=> p Hp a /=.
    case_bool_decide=> //.
  Qed.
  Next Obligation.
    move=> N M.
    apply ex_seriesC_finite.
  Qed.
  Next Obligation.
    move=> p Hp /=.
    rewrite SeriesC_finite_foldr //=.
  Qed.
  


  Definition bernoulli : val := 
    λ: "N" "M",
      let: "x" := rand "M" in 
      if: "x" < "N" then #1 else #0.


  Lemma twp_bernoulli_scale (N M : nat) (ε ε1 ε2 : R) :
  (N <= S M)%nat ->
  0 <= ε1 ->
  0 <= ε2 ->
  ((ε1 * (1 - (N / S M))) + (ε2 * (N/S M)) = ε)%R ->
  [[{↯ ε}]]
    bernoulli #N #M
  [[{
      (k : nat), RET #k; 
      (⌜k = 0%nat⌝ ∗ ↯ ε1) ∨
      (⌜k = 1%nat⌝ ∗ ↯ ε2)
  }]].
  Proof.
    set p := (N / S M)%R.
    iIntros "%HNleM %ε1_pos %ε2_pos %Heq %Φ Herr HΦ".
    rewrite /bernoulli.
    wp_pures.
    iPoseProof (ec_valid with "Herr") as "%Hε".
    set ε' := {|nonneg := ε; cond_nonneg := proj1 Hε |}.
    set ε1' := {|nonneg := ε1; cond_nonneg := ε1_pos |}.
    set ε2' := {|nonneg := ε2; cond_nonneg := ε2_pos |}.
    set f :=
      λ (n : fin (S M)), 
        if bool_decide (fin_to_nat n < N)%nat then ε2' else ε1' 
    .
    wp_apply (twp_couple_rand_adv_comp1 _ _ _ ε' f with "Herr") as "%x Herr".
    { unfold f. move=> n.
      by case_bool_decide. }
    { unfold f. rewrite SeriesC_scal_l. rewrite Rmult_comm.
      simpl_expr.
      Opaque INR.
      rewrite /= -Heq Rmult_plus_distr_l -!Rmult_assoc.
      Transparent INR. 
      rewrite (Rmult_comm _ ε1) (Rmult_comm _ ε2) !Rmult_assoc.
      rewrite Rmult_div_assoc (Rmult_comm _ N) -Rmult_div_assoc.
      rewrite Rdiv_diag; last apply INR_S_not_0.
      rewrite Rmult_plus_distr_l Ropp_mult_distr_r_reverse.
      rewrite Rmult_div_assoc (Rmult_comm _ N) -Rmult_div_assoc.
      rewrite Rdiv_diag; last apply INR_S_not_0.
      rewrite -Rminus_def.
      simpl_expr.
      setoid_rewrite ssrbool.fun_if; cbv [nonneg ε1' ε2'].
      by apply SeriesC_case. }
    wp_pures.
    unfold f. repeat case_bool_decide; wp_pures; try lia.
    - iApply ("HΦ" $! 1)%nat; auto.
    - iApply ("HΦ" $! 0)%nat; auto.
  Qed.
    
  Lemma bernoulli_succes_spec (N M : nat) : 
    [[{↯ (1 - (N / S M))}]]
      bernoulli #N #M 
    [[{ v, RET v; ⌜v = #1⌝ }]].
  Proof.
    iIntros "%Φ Herr HΦ".
    destruct (decide (S M < N)%nat) as [Hlt |Hge%not_lt].
    { iDestruct (ec_contradict_lt0 with "Herr") as "[]".
      rewrite Rcomplements.Rlt_minus_l Rplus_0_l.
      simpl_expr. }
    wp_apply (twp_bernoulli_scale _ _ _ 1 0 with "[$Herr]")%R; [lia | lra..|].
    iIntros "%k [(_ & Herr) | (-> & Herr)]".
    - iDestruct (ec_contradict with "Herr") as "[]"; simplra.
    - by iApply "HΦ".
  Qed.

  Lemma bernoulli_failure_spec (N M : nat) : 
    [[{↯ (N / S M)}]] 
      bernoulli #N #M 
    [[{ v, RET v; ⌜v = #0⌝ }]].
  Proof.
    iIntros "%Φ Herr HΦ".
    destruct (decide (S M < N)%nat) as [Hlt |Hge%not_lt].
    { iDestruct (ec_contradict with "Herr") as "[]".
      simpl_expr. }
    wp_apply (twp_bernoulli_scale _ _ (N / S M) 0 1 with "[$Herr]")%R => //.
    iIntros "%k [(-> & Herr) | (-> & Herr)]".
    - by iApply "HΦ". 
    - iDestruct (ec_contradict with "Herr") as "[]"; simplra.
  Qed.

  Lemma bernoulli_spec (N M : nat) :
    [[{True}]] 
      bernoulli #N #M 
    [[{ v, RET v; ⌜v = #0⌝ ∨ ⌜v = #1⌝}]].
  Proof.
    iIntros "%Φ _ HΦ".
    rewrite /bernoulli; wp_pures.
    wp_apply (twp_rand with "[$]") as "%n _".
    wp_pures; case_bool_decide;
    wp_pures; iApply "HΦ"; auto. 
  Qed.

End Bernoulli.

