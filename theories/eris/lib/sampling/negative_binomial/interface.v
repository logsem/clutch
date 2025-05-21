From clutch.eris Require Export eris.
From clutch.eris.lib.sampling Require Import utils. 
From clutch.eris.lib.sampling.binomial Require Import interface.

Section NegativeBinomialProbability.
  
  Definition negative_binom_prob (p q r k : nat) : R :=
    (choose (k + r - 1) k * (p / (q + 1))^r * (1 - p  / (q + 1))^k)%R.

  Lemma negative_binom_pos (p q r k : nat) : p ≤ (q + 1) → (0 <= negative_binom_prob p q r k)%R.
  Proof.
    intros Hpq.

    rewrite /negative_binom_prob.
    assert (0 <= q)%R by apply pos_INR.
    repeat apply Rmult_le_pos.
    { apply choose_pos. }
    { apply pow_le, Rcomplements.Rdiv_le_0_compat; first apply pos_INR.
      lra.
    }
    { apply pow_le.
      rewrite -Rcomplements.Rminus_le_0 Rcomplements.Rle_div_l; last lra.
      rewrite Rmult_1_l -INR_1 -plus_INR.
      apply le_INR, Hpq.
    }
  Qed.
      
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

  Lemma prod_sub_n_opp_nat :
    ∀ (k n : nat), (0 < n) → prod_sub_n k (-n) = (fact (n + k - 1) / fact (n - 1) * (-1)^k)%R.
  Proof.
    elim=>[|k IH] n sum_lt.
    { simpl.
      rewrite Nat.add_0_r Rmult_1_r.
      pose proof (INR_fact_lt_0 (n - 1)).
      rewrite Rdiv_diag; lra.
    }
    rewrite prod_sub_n_last IH //=
            Rminus_def -Ropp_plus_distr
            -(Nat.add_sub_assoc n (S k) 1) /=; last lia.
    rewrite Nat.sub_0_r.
    replace (fact (n + k) : R) with (fact (n + k - 1) * (n + k))%R; last first.
    { destruct n; first lia.
      rewrite S_INR fact_R plus_INR.
      fold Nat.add.
      rewrite /= Nat.sub_0_r.
      lra.
    }
    lra.
  Qed.
    
  Lemma prod_sub_n_choose : ∀ (k n : nat), (0 < n)%nat → (prod_sub_n k (-n) / fact k = interface.choose (k + n - 1) k * (-1)^k)%R.
  Proof.
    move=>k n n_pos.
    rewrite prod_sub_n_opp_nat //.
    unfold interface.choose.
    case_bool_decide; last lia.
    unfold C.
    replace (k + n - 1 - k) with (n - 1) by lia.
    rewrite (Nat.add_comm n k) -Rmult_div_assoc !Rmult_assoc.
    f_equal.
    rewrite Rinv_mult.
    lra.
  Qed.

  Lemma is_seriesC_negative_choose_0 :
    ∀ (q : R),
    is_seriesC (λ k, interface.choose (k - 1) k * q ^ k)%R 1%R.
  Proof.
    move=> q.
    eapply is_seriesC_ext.
    { instantiate (1 := (λ (k : nat), if bool_decide (k = 0) then 1%R else 0%R)).
      move=>i /=.
      case_bool_decide as is_i_0.
      { rewrite is_i_0 interface.choose_n_0 Rmult_1_r //. }
      { unfold interface.choose.
        case_bool_decide; first lia.
        rewrite Rmult_0_l //.
      }
    }
    apply is_seriesC_singleton.
  Qed.

  Lemma is_seriesC_negative_choose_pos :
    ∀ (r : nat) (q : R),
    (0 < r)%nat →
    (Rabs q < 1)%R →
    is_seriesC (λ k, interface.choose (k + r - 1) k * q ^ k)%R (/ ((1 - q)^r))%R.
  Proof.
    move=>r q r_pos q_bounds.
    unfold negative_binom_prob.
    
    assert (0 < (1 - q))%R.
    {
      apply Rabs_def2 in q_bounds.
      lra.
    }
    rewrite -gpow_pow; last lra.
    rewrite -gpow_opp.
    rewrite Rminus_def (Rplus_comm 1 (-q)).
    fold (spow (-r) (- q)).
    eapply is_seriesC_ext; last apply is_seriesC_is_series_nat, is_series_spow; last rewrite Rabs_Ropp //.
    move=>k /=.
    rewrite Rmult_assoc (Rmult_comm (/ fact k)) -Rdiv_def prod_sub_n_choose //
            -{2}(Rmult_1_l q) Ropp_mult_distr_l Rpow_mult_distr.
    repeat rewrite (Rmult_comm ((-1)^k)) Rmult_assoc.
    rewrite -Rpow_mult_distr -Ropp_mult_distr_l -Ropp_mult_distr_r
            Ropp_involutive Rmult_1_l pow1 Rmult_1_r Rmult_comm //.
  Qed.
 
 Lemma is_seriesC_negative_choose :
    ∀ (r : nat) (q : R),
    (Rabs q < 1)%R →
    is_seriesC (λ k, interface.choose (k + r - 1) k * q ^ k)%R (/ ((1 - q)^r))%R.
  Proof.
    move=>r q q_bounds.
    destruct (Nat.lt_dec 0 r); first by apply is_seriesC_negative_choose_pos.
    replace r with 0 by lia.
    rewrite Rinv_1.
    eapply is_seriesC_ext; last apply is_seriesC_negative_choose_0.
    move=>i /=.
    rewrite Nat.add_0_r //.
  Qed.
 
  Lemma is_seriesC_negative_binomial :
    ∀ (p q r : nat),
    (0 < p ≤ q + 1)%nat →
    is_seriesC (negative_binom_prob p q r) 1%R.
  Proof.
    move=>p q r r_pos p_bounds.
    unfold negative_binom_prob.
    set (s := (p / (q + 1))%R).
    set (t := (1 - s)%R).
    eapply is_seriesC_ext.
    { move=>k.
      rewrite Rmult_assoc (Rmult_comm (s ^ r)%R) -Rmult_assoc //.
    }

    assert (0 < s <= 1)%R.
    {
      assert (0 < q + 1)%R as q1_pos.
      {
        rewrite -INR_1 -plus_INR.
        apply lt_0_INR.
        lia.
      }
      assert (0 < p)%R.
      {
        apply lt_0_INR.
        lia.
      }
      unfold s.
      split.
      - apply Rcomplements.Rdiv_lt_0_compat;
          lra.
      - rewrite -Rcomplements.Rdiv_le_1 // -INR_1 -plus_INR.
        apply le_INR.
        lia.
    }
    
    replace 1%R with (s ^ r * / s ^ r)%R; last first.
    {
      apply Rdiv_diag, pow_nonzero.
      lra.
    }
    rewrite Rmult_comm.
    apply is_seriesC_scal_r.
    replace s with (1 - t)%R by (unfold t; lra).
    apply is_seriesC_negative_choose.
    unfold t;
    apply Rabs_def1; lra.
  Qed.

End NegativeBinomialProbability.

Class negative_binomial_spec `{!erisGS Σ} (negative_prog negative_alloc : val) :=
  NegativeSpec
  {
    twp_negative_binomial_adv_comp :
    ∀ (p q : nat),
      (0 < p)%nat →
      (p ≤ q + 1)%nat →
      ∀ (r : nat) (D : nat → R) (L : R) (ε : R) (ε_term : R),
      (0 < ε_term)%R →
      (∀ (n : nat), 0 <= D n <= L)%R →
      SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε → ↯ ε_term -∗
      ↯ ε -∗ WP negative_prog #() #p #q #r [{ v, ∃ (k : nat), ⌜v = #k⌝ ∗ ↯ (D k) }];

    own_negative_tape (α : loc) (N M r : nat) (v : list nat) : iProp Σ;

    twp_negative_alloc (p q r : nat) :
      [[{ True }]]
        negative_alloc #p #q #r
      [[{ (α : loc), RET #lbl:α; own_negative_tape α p q r [] }]];

    twp_negative_tape :
    ∀ (p q r : nat) (α : loc) (n : nat) (ns : list nat) (Φ : val → iProp Σ),
    own_negative_tape α p q r (n::ns) -∗
    (own_negative_tape α p q r ns -∗ Φ #n) -∗
    WP negative_prog #lbl:α #p #q #r [{ Φ }];
 
    twp_negative_binomial_presample :
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (p q r : nat) (ns : list nat) (ε : R),
      (0 < p)%nat →
      (p ≤ q + 1)%nat →
      (0 < ε)%R → 
      to_val e = None →
      ↯ ε ∗ own_negative_tape α p q r ns ∗
      (∀ (i : nat), own_negative_tape α p q r (ns ++ [i]) -∗ WP e [{ Φ }])
      ⊢  WP e [{ Φ }];
  
    twp_negative_binomial_planner :
    ∀ (p q r : nat) (α : loc) (e : expr) (ε : nonnegreal)
      (L_size L_sum : nat) (Φ : val → iProp Σ)
      (prefix : list nat) (suffix : list nat → list nat) ,
      (0 < p < q + 1)%nat →
      0 < r →
      to_val e = None →
      (∀ (junk : list nat),
         0 < length (suffix (prefix ++ junk)) <= L_size ∧ list_sum (suffix (prefix ++ junk)) ≤ L_sum) →
      (0 < ε)%R →
      ↯ ε ∗
      own_negative_tape α p q r prefix ∗
      ((∃ (junk : list nat),
           own_negative_tape α p q r (prefix ++ junk ++ suffix (prefix ++ junk)))
       -∗ WP e [{ Φ }])
      ⊢ WP e [{ Φ }];

    twp_negative_binomial_presample_adv_comp :
    ∀ (p q : nat) (α : loc) (l : list nat) (e : expr) (Φ : val → iProp Σ),
      0 < p →
      p ≤ (q + 1) →
      to_val e = None →
      ∀ (r : nat) (D : nat → R) (L : R) (ε : R) (ε_term : R),
      (0 < ε_term)%R →
      (∀ (n : nat), 0 <= D n <= L)%R →
      SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε →
      ↯ ε_term ∗
      ↯ ε ∗
      own_negative_tape α p q r l ∗
      (∀ (n : nat),
         ↯ (D n) -∗
         own_negative_tape α p q r (l ++ [n]) -∗ WP e [{ Φ }]) ⊢
      WP e [{ Φ }]
  }.
