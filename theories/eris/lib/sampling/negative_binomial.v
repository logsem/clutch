From clutch.eris Require Export eris.
From clutch.eris.lib.sampling Require Import binomial. 

Section NegativeBinomial.

  Context `{!erisGS Σ}.

  Parameter (B : val).

  Parameter (B_spec : ∀ (N M : nat) (ε ε1 ε2 : R), N ≤ (M + 1) → 
  ((ε1 * (1 - (N / (M + 1)))) + (ε2 * (N / (M + 1))) = ε)%R ->
  [[{↯ ε}]]
    B #N #M
  [[{
      (k : nat), RET #k; 
      (⌜k = 0⌝ ∗ ↯ ε1) ∨
      (⌜k = 1⌝ ∗ ↯ ε2)
  }]]).

  Definition negative_binomial : val :=
    λ: "p" "q",
      rec: "negative_binomial" "r" :=
      if: "r" ≤ #0
      then #0
      else
        let: "b" := B "p" "q" in
        if: "b" = #0
        then "negative_binomial" "r" + #1
        else "negative_binomial" ("r" - #1)
  .

  Definition negative_binom_prob (p q r k : nat) : R :=
    (choose (k + r - 1) k * (p / (q + 1))^r * (1 - p  / (q + 1))^k)%R.

  Lemma negative_binom_prob_split : ∀ (p q r k : nat),
    negative_binom_prob p q (r + 1) (k + 1)%nat =
    ((1 - p / (q + 1)) * negative_binom_prob p q (r + 1) k
     + (p / (q + 1)) * negative_binom_prob p q r (k + 1))%R.
  Proof.
    intros p q r k.
    rewrite /negative_binom_prob.
    replace (k + 1 + (r + 1) - 1) with (S (k + r)); last lia.
    replace (k + 1 + r - 1) with (k + r); last lia.
    replace (k + 1) with (S k); last lia.
    replace (k + (r + 1) - 1) with (k + r); last lia.
    rewrite -pascal' pow_add /=.
    lra.
  Qed.

  Lemma ec_negative_binom_split :
    ∀ (p q r : nat) (D : nat → R),
    let ε := SeriesC (λ k, negative_binom_prob p q (r + 1) k * D k)%R in
    let ε0 := SeriesC (λ k, negative_binom_prob p q (r + 1) k * D (k + 1)%nat)%R in
    let ε1 := SeriesC (λ k, negative_binom_prob p q r k * D k)%R in
    (ε = (1 - (p / (q + 1))) * ε0 + (p / (q + 1))* ε1)%R.
  Proof.
    (* True on paper proof, modulo convergence conditions, enough for now *)
  Admitted.

  Lemma negative_binom_prob_is_distr :
    ∀ (p q r : nat),
    p ≤ q + 1 →
    SeriesC (negative_binom_prob p q r) = 1.
  Admitted.
  
  Lemma twp_negative_binomial_split :
    ∀ (p q : nat),
    0 < p →
    p < (q + 1) →
    ∀ (r : nat) (D : nat → R) (ε : R) (ε_term : R),
    (0 < ε_term)%R →
    (∀ (n : nat), 0 <= D n)%R →
    SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε → ↯ ε_term -∗
    ↯ ε -∗ WP negative_binomial #p #q #r [{ v, ∃ (k : nat), ⌜v = #k⌝ ∗ ↯ (D k) }].
  Proof.
    iIntros (p q Hp Hpq r D ε ε_term Hε_term HD HSum) "Hterm Herr".
    rewrite /negative_binomial.
    do 4 wp_pure.
    iRevert (D ε ε_term Hε_term HD HSum) "Herr Hterm".
    iInduction (r) as [|r] "IHr".
    - iIntros (D ε ε_term Hε_term HD HDε) "Herr Hterm".
      rewrite /negative_binom_prob /choose in HDε.
      erewrite (SeriesC_ext _ (λ k, if bool_decide (k = 0) then D 0 else 0)) in HDε; last first.
      { intros k.
        do 2 case_bool_decide; try lia; subst; simpl; last lra.
        rewrite Rcomplements.C_n_n.
        lra.
      }
      rewrite SeriesC_singleton in HDε.
      rewrite -HDε.
      wp_pures.
      iModIntro.
      iExists 0.
      by iFrame.
    - iIntros (D ε ε_term Hε_term HD HDε) "Herr Hterm".
      iRevert (D ε HD HDε) "Herr".
      set (s1 := (p / (q + 1))%R).
      set (s0 := ((1 - s1)%R)).
      set (sc0 := ((/ s0 + 1) / 2)%R).
      set (sc1 := ((1 - sc0 * s0) / s1)%R).
                                      
      assert (0 < p)%R.
      {
        rewrite -INR_0.
        by apply lt_INR.
      }
      assert (0 <= q)%R by apply pos_INR.
      assert (1 <= q + 1)%R by lra.
      assert (0 < q + 1)%R by lra.
      assert (p < q + 1)%R.
      { rewrite -INR_1 -plus_INR.
        by apply lt_INR.
      } 
      assert (0 < s1 < 1)%R; first split.
      { unfold s1.
        by apply Rcomplements.Rdiv_lt_0_compat.
      }
      { unfold s1.
        apply Rcomplements.Rlt_div_l; lra.
      }
      assert (0 < s0 < 1)%R by (unfold s0; lra).
      
      assert (0 < / s0)%R.
      { apply Rinv_0_lt_compat. lra. }

      assert (1 < / s0)%R.
      {
        apply Rcomplements.Rinv_lt_cancel; first done.
        rewrite Rinv_inv Rinv_1.
        lra.
      }

      assert (1 < sc0)%R by (unfold sc0; lra).
      assert (sc0 * s0 = (1 + s0) / 2)%R as Hsc0s0.
      {
        unfold sc0.
        rewrite -Rmult_div_swap Rmult_plus_distr_r Rmult_1_l Rinv_l; last lra.
        reflexivity.
      }

      assert (0 < sc0 * s0 < 1)%R; first (rewrite Hsc0s0; lra).
      
      assert (0 < sc1)%R.
      { unfold sc1.
        apply Rcomplements.Rdiv_lt_0_compat; lra.
      } 

      assert (sc0 * s0 + sc1 * s1 = 1)%R.
      {
        unfold sc1.
        rewrite -Rmult_div_swap Rmult_div_l; lra.
      }
      
      iApply (ec_ind_amp _ sc0 with "[] Hterm"); try done.
      iModIntro.
      iIntros (ε' Hε') "IH Hterm".
      iIntros (D ε HD HDε) "Herr".
      wp_pures.
      erewrite SeriesC_ext in HDε; last first.
      {
        intros.
        replace (S r) with (r + 1)%nat; first done.
        lia.
      }
      rewrite ec_negative_binom_split in HDε.
      fold s1 s0 in HDε.
      match type of HDε with
      | (s0 * ?A + s1 * ?B)%R = _ => set (ε0 := A);
                                     set (ε1 := B)
      end.
      fold ε0 ε1 in HDε.
      wp_pures.
      iPoseProof (ec_combine with "[Hterm Herr]") as "Hec"; first iFrame.
      
      wp_apply (B_spec _ _ _ (ε0 + ε' * sc0) (ε1 + ε' * sc1) with "Hec"); first lia.
      { rewrite -HDε.
        fold s1 s0.
        nra.
      }
      iIntros (k) "[[-> Herr] | [-> Herr]]".
      {
        do 4 wp_pure.
        iPoseProof (ec_split with "Herr") as "[Herr Hterm]".
        { apply SeriesC_ge_0'.
          intros n.
          apply Rmult_le_pos; last done.
          admit.
        }
        { nra. }
        iPoseProof ("IH" with "[Hterm] [] [] Herr") as "IHH".
        { rewrite Rmult_comm //. }
        { instantiate (1 := λ k, D (k + 1)). iPureIntro. intros. apply HD. }
        { iPureIntro.
          apply SeriesC_ext.
          intros k.
          repeat f_equal.
          lia.
        }
        wp_bind ((rec: _ _ := _)%V _)%E.
        iApply tgl_wp_wand_r.
        iSplitL "IHH"; first done.
        iIntros (v) "(%k & -> & Herr)".
        wp_pures.
        iModIntro.
        iExists (k + 1).
        iFrame.
        iPureIntro.
        f_equal.
        rewrite Nat2Z.inj_add //.
      } 
      { do 5 wp_pure.
        replace (S r - 1)%Z with (r : Z); last lia.
        iPoseProof (ec_split with "Herr") as "[Herr Hterm]".
        { apply SeriesC_ge_0'.
          intros n.
          apply Rmult_le_pos; last done.
          admit.
        }
        { nra. }
        iApply ("IHr" with "[] [] [] Herr Hterm").
        { iPureIntro. nra. }
        { by iPureIntro. }
        { by iPureIntro. }
  Admitted.
End NegativeBinomial.