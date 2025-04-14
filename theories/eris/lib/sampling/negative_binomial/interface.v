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

  Lemma negative_binom_prob_is_distr :
    ∀ (p q r : nat),
    p ≤ q + 1 →
    SeriesC (negative_binom_prob p q r) = 1.
  Admitted.
  
  Lemma ex_seriesC_negative_binom_prob :
    ∀ (p q r : nat),
    p ≤ q + 1 →
    ex_seriesC (negative_binom_prob p q r).
  Proof.
    unfold ex_seriesC.
    unfold is_seriesC.
    intros p q r Hpq.
    exists 1%R.
    apply Series.is_series_Reals.
    unfold infinite_sum.
    intros ε Hε.
  Admitted.

End NegativeBinomialProbability.

Class negative_binomial_spec `{!erisGS Σ} (negative_prog : val) :=
  NegativeSpec
  {
    twp_negative_binomial_adv_comp :
    ∀ (p q : nat),
      (0 < p)%nat →
      (p < q + 1)%nat →
      ∀ (r : nat) (D : nat → R) (ε : R) (ε_term : R),
      (0 < ε_term)%R →
      (∀ (n : nat), 0 <= D n)%R →
      SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε → ↯ ε_term -∗
      ↯ ε -∗ WP negative_prog #() #p #q #r [{ v, ∃ (k : nat), ⌜v = #k⌝ ∗ ↯ (D k) }];

    own_negative_tape (α : loc) (N M r : nat) (v : list nat) : iProp Σ;

    twp_negative_tape :
    ∀ (p q r : nat) (α : loc) (n : nat) (ns : list nat) (Φ : val → iProp Σ),
    own_negative_tape α p q r (n::ns) -∗
    (own_negative_tape α p q r ns -∗ Φ #n) -∗
    WP negative_prog #lbl:α #p #q #r [{ Φ }];
 
    twp_negative_binomial_presample :
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (p q r : nat) (ns : list nat) (ε : R),
      (0 < p)%nat →
      (p < q + 1)%nat →
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
      p < (q + 1) →
      to_val e = None →
      ∀ (r : nat) (D : nat → R) (ε : R) (ε_term : R),
      (0 < ε_term)%R →
      (∀ (n : nat), 0 <= D n)%R →
      SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε →
      ↯ ε_term ∗
      ↯ ε ∗
      own_negative_tape α p q r l ∗
      (∀ (n : nat),
         ↯ (D n) -∗
         own_negative_tape α p q r (l ++ [n]) -∗ WP e [{ Φ }]) ⊢
      WP e [{ Φ }]
  }.
