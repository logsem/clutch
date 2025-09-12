From clutch.eris Require Export eris.
From clutch.eris.lib.sampling Require Import abstract_planner distr_impl utils. 

Section NegativeBinomialProbability.
  
  Definition negative_binom_prob (p q r k : nat) : R :=
    (Choose (k + r - 1) k * (p / (q + 1))^r * (1 - p  / (q + 1))^k)%R.

  Lemma negative_binom_pos (p q r k : nat) : p ≤ (q + 1) → (0 <= negative_binom_prob p q r k)%R.
  Proof.
    intros Hpq.

    rewrite /negative_binom_prob.
    assert (0 <= q)%R by apply pos_INR.
    repeat apply Rmult_le_pos.
    { apply Choose_pos. }
    { apply pow_le, Rcomplements.Rdiv_le_0_compat; first apply pos_INR.
      lra.
    }
    { apply pow_le.
      rewrite -Rcomplements.Rminus_le_0 Rcomplements.Rle_div_l; last lra.
      rewrite Rmult_1_l -INR_1 -plus_INR.
      apply le_INR, Hpq.
    }
  Qed.

  Lemma negative_binom_gt_0 (p q r k : nat) : 0 < p < (q + 1) → 0 < r → (0 < negative_binom_prob p q r k)%R.
  Proof.
    intros Hpq Hr.
    rewrite /negative_binom_prob.
    assert (0 <= q)%R by apply pos_INR.
    repeat apply Rmult_lt_0_compat.
    { unfold Choose.
      bool_decide.
      unfold C.
      apply Rmult_lt_0_compat; first apply INR_fact_lt_0.
      apply Rinv_pos.
      apply Rmult_lt_0_compat; apply INR_fact_lt_0.
    }
    { apply pow_lt, Rdiv_lt_0_compat.
      - apply (lt_INR 0), Hpq.
      - rewrite -INR_1 -plus_INR.
         apply (lt_INR 0). lia.
    }
    { apply pow_lt.
      rewrite -Rcomplements.Rminus_lt_0 Rcomplements.Rlt_div_l; last lra.
      rewrite Rmult_1_l -INR_1 -plus_INR.
      apply lt_INR, Hpq.
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
    
  Lemma prod_sub_n_Choose : ∀ (k n : nat), (0 < n)%nat → (prod_sub_n k (-n) / fact k = Choose (k + n - 1) k * (-1)^k)%R.
  Proof.
    move=>k n n_pos.
    rewrite prod_sub_n_opp_nat //.
    unfold Choose.
    case_bool_decide; last lia.
    unfold C.
    replace (k + n - 1 - k) with (n - 1) by lia.
    rewrite (Nat.add_comm n k) -Rmult_div_assoc !Rmult_assoc.
    f_equal.
    rewrite Rinv_mult.
    lra.
  Qed.

  Lemma is_seriesC_negative_Choose_0 :
    ∀ (q : R),
    is_seriesC (λ k, Choose (k - 1) k * q ^ k)%R 1%R.
  Proof.
    move=> q.
    eapply is_seriesC_ext.
    { instantiate (1 := (λ (k : nat), if bool_decide (k = 0) then 1%R else 0%R)).
      move=>i /=.
      case_bool_decide as is_i_0.
      { rewrite is_i_0 Choose_n_0 Rmult_1_r //. }
      { unfold Choose.
        case_bool_decide; first lia.
        rewrite Rmult_0_l //.
      }
    }
    apply is_seriesC_singleton.
  Qed.

  Lemma is_seriesC_negative_Choose_pos :
    ∀ (r : nat) (q : R),
    (0 < r)%nat →
    (Rabs q < 1)%R →
    is_seriesC (λ k, Choose (k + r - 1) k * q ^ k)%R (/ ((1 - q)^r))%R.
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
    rewrite Rmult_assoc (Rmult_comm (/ fact k)) -Rdiv_def prod_sub_n_Choose //
            -{2}(Rmult_1_l q) Ropp_mult_distr_l Rpow_mult_distr.
    repeat rewrite (Rmult_comm ((-1)^k)) Rmult_assoc.
    rewrite -Rpow_mult_distr -Ropp_mult_distr_l -Ropp_mult_distr_r
            Ropp_involutive Rmult_1_l pow1 Rmult_1_r Rmult_comm //.
  Qed.
 
 Lemma is_seriesC_negative_Choose :
    ∀ (r : nat) (q : R),
    (Rabs q < 1)%R →
    is_seriesC (λ k, Choose (k + r - 1) k * q ^ k)%R (/ ((1 - q)^r))%R.
  Proof.
    move=>r q q_bounds.
    destruct (Nat.lt_dec 0 r); first by apply is_seriesC_negative_Choose_pos.
    replace r with 0 by lia.
    rewrite Rinv_1.
    eapply is_seriesC_ext; last apply is_seriesC_negative_Choose_0.
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
    apply is_seriesC_negative_Choose.
    unfold t;
    apply Rabs_def1; lra.
  Qed.

  Program Definition negative_binomial_distr (p q r : nat) (p_bounds : 0 < p ≤ q + 1) : distr nat
 := MkDistr
      (negative_binom_prob p q r)
      (λ k, negative_binom_pos p q r k (proj2 p_bounds))
      (ex_intro _ _ (is_seriesC_negative_binomial p q r p_bounds))
      _
  .
  Next Obligation.
  Proof. 
    move=>p q r p_bounds.
    rewrite (is_seriesC_unique _ _ (is_seriesC_negative_binomial p q r p_bounds)) //.
  Qed.

End NegativeBinomialProbability.

Class negative_binomial_spec (negative_prog negative_alloc : val) :=
  NegativeSpec
  {
    twp_negative_binomial_adv_comp `{!erisGS Σ} :
    ∀ (p q : nat),
      (0 < p)%nat →
      (p ≤ q + 1)%nat →
      ∀ (r : nat) (D : nat → R) (L : R) (ε : R),
      (∀ (n : nat), 0 <= D n <= L)%R →
      SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε →
      ↯ ε -∗ WP negative_prog #() #p #q #r [{ v, ∃ (k : nat), ⌜v = #k⌝ ∗ ↯ (D k) }];

    own_negative_tape `{!erisGS Σ} (α : loc) (N M r : nat) (v : list nat) : iProp Σ;

    twp_negative_alloc `{!erisGS Σ} (p q r : nat) :
      [[{ True }]]
        negative_alloc #p #q #r
      [[{ (α : loc), RET #lbl:α; own_negative_tape α p q r [] }]];

    twp_negative_tape `{!erisGS Σ} :
    ∀ (p q r : nat) (α : loc) (n : nat) (ns : list nat) (Φ : val → iProp Σ),
    own_negative_tape α p q r (n::ns) -∗
    (own_negative_tape α p q r ns -∗ Φ #n) -∗
    WP negative_prog #lbl:α #p #q #r [{ Φ }];
 
    twp_negative_binomial_presample_adv_comp `{!erisGS Σ} :
      ∀ (p q r : nat) (α : loc) (l : list nat) (e : expr)
        (D : nat → R) (L : R) (ε : R) (Φ : val → iProp Σ),
        0 < p →
        p ≤ (q + 1) →
        to_val e = None →
        (∀ (n : nat), 0 <= D n <= L)%R →
        SeriesC (λ k, (negative_binom_prob p q r k * D k)%R) = ε →
        ↯ ε ∗
        own_negative_tape α p q r l ∗
        (∀ (n : nat),
           ↯ (D n) -∗
           own_negative_tape α p q r (l ++ [n]) -∗ WP e [{ Φ }]) ⊢
        WP e [{ Φ }]
    }.

Section NegativeLemmas.
 
 Context `{negative_spec : !negative_binomial_spec negative_prog negative_alloc}.
 
  Instance negative_binomial_impl {p q r : nat} {p_bounds : 0 < p ≤ q + 1} :
    distr_impl (dmap (LitV ∘ LitInt ∘ Z.of_nat) (negative_binomial_distr p q r p_bounds)).
  Proof using negative_spec.

    refine (MkDistrImpl _
              (λ: "α", negative_prog "α" #p #q #r) (λ: <>, negative_alloc #p #q #r)
              loc
              (λ _ _ Δ l, ∃ l', own_negative_tape Δ p q r l' ∗
                            ⌜l = fmap (λ (k : nat), #k) l'⌝)%I
              (λ _ _ Δ α, ⌜α = #lbl:Δ⌝)%I #() _ _ _ _).
    - iIntros (Σ erisGS0 D ε L ε_ge_0 D_bounds D_sum Φ) "Herr HΦ".
      set (D' (k : nat) := D #k).
      wp_pures.
      iPoseProof (twp_negative_binomial_adv_comp _ _ (proj1 p_bounds) (proj2 p_bounds) r D' L _ _ with "Herr") as "HH".
      Unshelve.
      3:{ move=>k. apply D_bounds. }
      { rewrite (dmap_expected_value _ _ _ L) // in D_sum. }
      wp_apply tgl_wp_wand_r.
      iFrame.
      iIntros (?) "(%k & -> & Herr)".
      by iApply "HΦ".
    - iIntros (Σ erisGS0 Φ) "_ HΦ".
      wp_pures.
      wp_apply (twp_negative_alloc with "[$]") as (α) "Hα".
      iApply "HΦ".
      by iFrame.
    - iIntros (Σ erisGS0 e ε Δ l D L Φ e_not_val ε_ge_0 D_bounds D_sum) "(Herr & (%l' & Htape & ->) & Hnext)".
      set (D' (k : nat) := D #k).
      wp_apply (twp_negative_binomial_presample_adv_comp _ _ _ _ _ _ D' _ _ _ (proj1 p_bounds) (proj2 p_bounds) e_not_val with "[$Herr $Htape Hnext]").
      { move=>k. apply D_bounds. }
      { rewrite (dmap_expected_value _ _ _ L) // in D_sum. }
      iIntros (k) "Herr Htape".
      wp_apply "Hnext".
      iFrame.
      rewrite fmap_app //.
    - iIntros (Σ erisGS0 α Δ l v Φ) "[(%l' & Htape & %Heq) ->] HΦ".
      destruct l' as [|v' l']; first discriminate.
      injection Heq as -> ->.
      wp_pures.
      wp_apply (twp_negative_tape with "Htape") as "Htape".
      iApply "HΦ".
      iExists l'.
      by iFrame.
  Defined.

  (*
  Lemma twp_negative_binomial_planner :
    ∀ (p q r : nat) (α : loc) (e : expr) (ε : R)
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
      ⊢ WP e [{ Φ }].
  Proof.
    iIntros (p q r α e ε L_size L_sum Φ prefix suffix
               p_bounds r_pos e_not_val suf_bounds
               ε_pos) "(Herr & Htape & Hnext)".
    set (ψ l := (own_negative_tape α p q r l ∗ ∃ (ε0 : R), ⌜(0 < ε0)%R⌝ ∗ ↯ ε0)%I).
    unshelve wp_apply (abstract_planner (negative_binom_prob p q r) ψ _ prefix suffix L_size (seq 0 (S L_sum)) (ε / 2) _ (is_seriesC_negative_binomial p q r ltac:(lia))).
    {
      split; first by apply negative_binom_gt_0.
      unshelve epose proof (SeriesC_nat_elem_lt (negative_binom_prob p q r) _ _ _ (is_seriesC_negative_binomial p q r ltac:(lia))); first lra.
      { move=>k. apply negative_binom_gt_0; lia. }
      auto.
    }
    { iIntros (ε0 D L0 l ε0_pos D_bounds D_sum) "([Htape (%ε1 & %ε1_pos & Hfuel)] & Herr & Hnext)".
      replace ε1 with (ε1 / 2 + ε1 / 2)%R by lra.
      iPoseProof (ec_split with "Hfuel") as "[Hfuel_now Hfuel_later]"; try lra.
      wp_apply (twp_negative_binomial_presample_adv_comp p q r α with "[$Hfuel_now $Herr $Htape Hnext Hfuel_later]"); try lia; try done.
      { lra. }
      iIntros (n) "Herr Htape".
      wp_apply ("Hnext" with "Herr").
      iFrame.
      iPureIntro.
      lra.
    }
    { apply suf_bounds. }
    { move=>a j a_elem_suf.
      apply elem_of_seq.
      split; first lia.
      pose proof (list_sum_le _ _ a_elem_suf).
      pose proof (suf_bounds j) as [_ sum_bound].
      lia.
    }
    { lra. }
    assert (ε = (ε / 2 + ε / 2)%R) as ε_half by lra.
    rewrite {1}ε_half.
    iPoseProof (ec_split with "Herr") as "[Hfuel1 Hfuel2]"; try lra.
    iFrame.
    iSplitR; first (iPureIntro; lra).
    iIntros (j) "[Htape _]".
    wp_apply "Hnext".
    iFrame.
  Qed.

  Lemma twp_negative_binomial_presample :
    ∀ (e : expr) (α : loc) (Φ : val → iProp Σ)
      (p q r : nat) (ns : list nat) (ε : R),
      (0 < p)%nat →
      (p ≤ q + 1)%nat →
      (0 < ε)%R → 
      to_val e = None →
      ↯ ε ∗ own_negative_tape α p q r ns ∗
      (∀ (i : nat), own_negative_tape α p q r (ns ++ [i]) -∗ WP e [{ Φ }])
      ⊢  WP e [{ Φ }].
  Proof.
    iIntros (e α Φ p q r ns ε p_pos p_le_Sq ε_pos e_not_val) "(Hfuel & Htape & Hnext)".
    iMod ec_zero as "Herr".
    unshelve wp_apply (twp_negative_binomial_presample_adv_comp p q r _ _ _ (const 0%R) _ 0%R ε); last iFrame; try done.
    { move=> /= _.
      lra.
    }
    { apply SeriesC_0.
      move=>i /=.
      lra.
    }
    iIntros (i) "_".
    iApply "Hnext".
  Qed.
  *)
End NegativeLemmas.
