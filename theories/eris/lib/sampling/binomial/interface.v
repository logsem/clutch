From clutch.eris Require Export eris.
From clutch.eris.lib.sampling Require Import abstract_planner distr_impl utils.
From clutch.eris.lib.sampling.bernoulli Require Import interface.

Section BinomialProbability.
   
  Definition choose (n k : nat) : R :=
    if bool_decide (k ≤ n)%nat then
      C n k
    else 0%R.

  Lemma pascal' (n i : nat) : (choose n i + choose n (S i))%R = choose (S n) (S i).
  Proof.
    rewrite /choose.
    repeat case_bool_decide; try lia; [by rewrite pascal | | lra].
    assert (i = n) as -> by lia.
    rewrite !Rcomplements.C_n_n.
    lra.
  Qed.

  Lemma choose_pos (n i : nat) : (0 <= choose n i)%R.
  Proof.
    rewrite /choose /C.
    case_bool_decide; last done.
    apply Rcomplements.Rdiv_le_0_compat; first apply pos_INR.
    apply Rmult_lt_0_compat;
      rewrite -INR_0;
      apply lt_INR, lt_O_fact.
  Qed.

  Lemma choose_n_0 (n : nat) : choose n 0 = 1.
  Proof.
    unfold choose.
    bool_decide.
    rewrite Rcomplements.C_n_0 //.
  Qed.

  Lemma choose_n_n (n : nat) : choose n n = 1.
  Proof.
    unfold choose.
    bool_decide.
    rewrite Rcomplements.C_n_n //.
  Qed.

  Lemma choose_n_1 : ∀ (n : nat), choose n 1 = n.
  Proof.
    elim=>[|n IH]; first done.
    rewrite -pascal' IH choose_n_0 -plus_INR //.
  Qed.
  
  Definition binom_prob (p q n k : nat) : R := (choose n k * (p / (q + 1))^k * (1 - p / (q + 1))^(n - k))%R.

  Lemma binom_prob_pos (p q n k : nat) : (p ≤ q + 1)%nat → (0 <= binom_prob p q n k)%R.
  Proof.
    move=>is_prob.
    unfold binom_prob.
    repeat apply Rmult_le_pos;
      first apply choose_pos;
      apply pow_le.
    { apply Rcomplements.Rdiv_le_0_compat; real_solver. }
    { rewrite -INR_1 -plus_INR -Rcomplements.Rminus_le_0 -Rcomplements.Rdiv_le_1; real_solver. }
  Qed.

  Lemma binom_prob_split (p q n k : nat) : 
    ((1 - (p / (q + 1))) * binom_prob p q n (k+1) + (p / (q + 1)) * binom_prob p q n k 
      = 
    binom_prob p q (n+1) (k+1))%R.
  Proof.
    rewrite /binom_prob.
    set (r := (p / (q + 1))%R).
    set (s := (1 - r)%R).
    destruct (Nat.lt_ge_cases k n).
    - replace (n + 1 - (k + 1))%nat with (n - k)%nat by lia.
      rewrite !Nat.add_1_r -pascal'.
      set (A := choose n k).
      set (B := choose n (S k)).
      rewrite -(Rmult_assoc s) (Rmult_comm s) (Rmult_assoc _ s).
      replace (s * s ^ (n - S k))%R with (s ^ (n - k))%R; last first.
      {
        rewrite !tech_pow_Rmult.
        f_equal.
        lia.
      }
      rewrite (Rmult_comm A) -!(Rmult_assoc r) !tech_pow_Rmult.
      lra.
    - rewrite /choose.
      replace (n - (k + 1))%nat with 0%nat by lia.
      replace (n - k)%nat with 0%nat by lia.
      replace (n + 1 - (k + 1))%nat with 0%nat by lia.
      repeat case_bool_decide; try (lia || lra).
      assert (k = n) as -> by lia.
      rewrite !Rcomplements.C_n_n pow_add.
      lra.
  Qed.

  Lemma binom_prob_eq (p q n : nat) : (binom_prob p q n n = (p / (q + 1))^n)%R.
  Proof.
    rewrite /binom_prob /choose.
    bool_decide.
    rewrite !Nat.sub_diag Rcomplements.C_n_n.
    lra.
  Qed.

  Lemma binom_prob_0 (p q n : nat) : (binom_prob p q n 0 = (1 - p / (q + 1))^n)%R.
  Proof.
    rewrite /binom_prob /choose.
    bool_decide.
    rewrite Nat.sub_0_r Rcomplements.C_n_0.
    lra.
  Qed.

  Lemma binom_prob_gt_0 (p q n k : nat) :
    0 < p < q + 1 → k ≤ n → (0 < binom_prob p q n k)%R.
  Proof.
    move=>[p_pos p_lt_Sq] k_le_n.
    apply lt_INR in p_pos.
    apply lt_INR in p_lt_Sq.
    rewrite plus_INR in p_lt_Sq.
    simpl in p_pos, p_lt_Sq.
    rewrite /binom_prob /choose.
    bool_decide.
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat.
      + unfold C.
        apply Rdiv_lt_0_compat;
          last apply Rmult_lt_0_compat;
          apply INR_fact_lt_0.
      + apply pow_lt.
        apply Rdiv_lt_0_compat; lra.
    - apply pow_lt.
      apply Rlt_0_minus.
      rewrite Rcomplements.Rlt_div_l; lra.
  Qed.
   
  Lemma binom_prob_gt (p q n k : nat) : n < k → binom_prob p q n k = 0%R.
  Proof.
    intros Hnk.
    rewrite /binom_prob /choose.
    case_bool_decide;
    [lia | simpl_expr].
  Qed.

  Lemma sum_binom_prob (p q n : nat) :
    SeriesC (λ (k : fin (S n)), binom_prob p q n k)%R = 1%R.
  Proof.
    elim: n => [|n IHn].
    - rewrite SeriesC_finite_foldr /= binom_prob_eq.
      lra.
    - rewrite Series_fin_first binom_prob_0.
      set (r := (p / (q + 1))%R).
      set (s := (1 - r)%R).
      erewrite SeriesC_ext; last first.
      { intros k.
        replace (S n) with (n + 1)%nat at 1 by lia.
        replace (S k) with (k + 1)%nat at 1 by lia.
        rewrite -binom_prob_split.
        fold r s.
        replace (k + 1)%nat with (S k) by lia.
        reflexivity.
      }
      rewrite SeriesC_plus; [| apply ex_seriesC_finite..].
      rewrite !SeriesC_scal_l IHn Rmult_1_r Series_fin_last fin_to_nat_to_fin binom_prob_gt; last lia.
      rewrite Rplus_0_r.
      pose proof (Series_fin_first n (binom_prob p q n)) as H.
      rewrite binom_prob_0 IHn Rplus_comm in H.
      fold r s in H.
      apply (Rminus_eq_compat_r (s^n)) in H.
      rewrite Rplus_minus_r in H.
      erewrite SeriesC_ext; last first.
      { intros k.
        rewrite -fin_S_inj_to_nat //.
      }
      rewrite -H Rmult_minus_distr_l /=.
      unfold s.
      lra.
  Qed.

  Lemma binom_prob_lt_1 (p q n : nat) (k : fin (S (S n))) : 0 < p < q + 1 → (binom_prob p q (S n) k < 1)%R.
  Proof.
    move=>p_bounds.
    rewrite -(sum_binom_prob p q (S n)).
    apply (SeriesC_finite_elem_lt n (binom_prob p q (S n))).
    { rewrite sum_binom_prob.
      lra.
    }
    { move=>i.
      apply binom_prob_gt_0; first done.
      pose proof (fin_to_nat_lt i).
      lia.
    }
    { apply SeriesC_correct.
      apply ex_seriesC_finite.
    }
  Qed.

  Program Definition binom_distr (p q n : nat) (p_le_Sq : p ≤ q + 1) : distr nat :=
    MkDistr (binom_prob p q n) (λ k, binom_prob_pos p q n k p_le_Sq) _ _. 
  Next Obligation.
  Proof.
    move=>p q n p_le_Sq.
    apply (ex_seriesC_ext (λ k, if bool_decide (k ≤ n) then binom_prob p q n k else 0%R)).
    { unfold binom_prob, choose.
      move=>k.
      case_bool_decide; lra.
    }
    apply ex_seriesC_nat_bounded.
  Qed.
  
  Next Obligation.
    move=>p q n p_le_Sq.
    pose proof (sum_binom_prob p q n) as sum_b.
    rewrite -SeriesC_nat_bounded_fin in sum_b.
    rewrite (SeriesC_ext _
               (λ k, if bool_decide (k ≤ n)
                     then binom_prob p q n k
                     else 0%R)); first rewrite sum_b //.
    unfold binom_prob, choose.
    move=>k.
    case_bool_decide; lra.
  Qed.

End BinomialProbability.

Class binomial_spec (binomial_prog : val) (binomial_alloc : val) :=
  BinomialSpec {
 
  twp_binom_adv_comp `{!erisGS Σ} (p q : nat) (n : nat) (D : fin (S n) → R) (ε : R) :
    (p ≤ (q + 1))%nat →
    (∀ (k : fin (S n)), 0 <= D k)%R → 
    SeriesC (λ k : fin (S n), (binom_prob p q n k * D k)%R) = ε →
    [[{ ↯ ε }]]
      binomial_prog #() #p #q #n 
    [[{ (k : fin (S n)), RET #k ; ↯ (D k) }]];
   
  own_binomial_tape `{!erisGS Σ} (α : loc) (m n k : nat) (v : list (fin (S k))) : iProp Σ;

  twp_binomial_alloc `{!erisGS Σ} (p q k : nat) :
      [[{ True }]]
        binomial_alloc #p #q #k
      [[{ (α : loc), RET #lbl:α; own_binomial_tape α p q k [] }]];

  twp_binomial_tape `{!erisGS Σ} (N M k : nat) (α : loc) (ns : list (fin (S k))) (n : fin (S k)) :   [[{ own_binomial_tape α N M k (n::ns) }]]
      binomial_prog (#lbl:α) #N #M #k
    [[{ RET #n ; own_binomial_tape α N M k ns }]];

  twp_binomial_presample `{!erisGS Σ} (e : expr) (α : loc) (Φ : val → iProp Σ)
      (N M k : nat) (ns : list (fin (S k))) :
    to_val e = None
    → (0 < k)%nat
    → own_binomial_tape α N M k ns ∗
    (∀ (i : fin (S k)), own_binomial_tape α N M k (ns ++ [i%fin]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }];
      
   twp_binomial_presample_adv_comp `{!erisGS Σ}
      (e : expr) (α : loc) (Φ : val → iProp Σ)
      (p q n : nat) (ns : list (fin (S n))) (ε : R)
      (D : fin (S n) → R) :
    (∀ (i : fin (S n)), 0 <= D i)%R →
    SeriesC (λ k : fin (S n), (binom_prob p q n k * D k)%R) = ε →
    (p ≤ q + 1)%nat →
    to_val e = None →
    own_binomial_tape α p q n ns ∗ ↯ ε ∗
    (∀ (i : fin (S n)), ↯ (D i) ∗ own_binomial_tape α p q n (ns ++ [i]) -∗ WP e [{ Φ }])
    ⊢  WP e [{ Φ }]
    }.

Section BinomialLemmas.

  Context `{binspec: binomial_spec binom binalloc}.

  Instance binomial_impl {p q n : nat} {p_le_Sq : p ≤ q + 1} :
    distr_impl (dmap (LitV ∘ LitInt ∘ Z.of_nat) (binom_distr p q n p_le_Sq)).
  Proof using binspec.
     
    refine (MkDistrImpl _
              (λ: "α", binom "α" #p #q #n) (λ: <>, binalloc #p #q #n)
              loc
              (λ _ _ Δ l, ∃ l', own_binomial_tape Δ p q n l' ∗
                            ⌜l = fmap (λ (k : fin (S n)), #k) l'⌝)%I
              (λ _ _ Δ α, ⌜α = #lbl:Δ⌝)%I #() _ _ _ _).
    - iIntros (Σ erisGS0 D ε L ε_ge_0 D_bounds D_sum Φ) "Herr HΦ".
      set (D' (k : nat) := D #k).
      wp_pures.
      wp_apply (twp_binom_adv_comp _ _ _ D' _ p_le_Sq with "Herr [HΦ]").
      { move=>k. apply D_bounds. }
      { rewrite (dmap_expected_value _ _ _ L) in D_sum;
          last (move=>a; apply D_bounds).
        rewrite -(SeriesC_nat_bounded_fin (λ k, (binom_prob p q n k * D' k)%R)) D_sum.
        apply SeriesC_ext.
        move=>k.
        case_bool_decide; first done.
        rewrite /pmf /= binom_prob_gt; [lra | lia].
      }
      iIntros (k) "Herr".
      by iApply "HΦ".
    - iIntros (Σ erisGS0 Φ) "_ HΦ".
      wp_pures.
      wp_apply (twp_binomial_alloc with "[$]") as (α) "Hα".
      iApply "HΦ".
      by iFrame.
    - iIntros (Σ erisGS0 e ε Δ l D L Φ e_not_val ε_ge_0 D_bounds D_sum) "(Herr & (%l' & Htape & ->) & Hnext)".
      set (D' (k : fin (S n)) := D #k).
      unshelve wp_apply (twp_binomial_presample_adv_comp _ _ _ _ _ _ _ _ D' _ _ p_le_Sq e_not_val  with "[$Herr $Htape Hnext]").
      { move=>k. apply D_bounds. }
      { rewrite (dmap_expected_value _ _ _ L) in D_sum;
          last (move=>a; apply D_bounds).
        rewrite -(SeriesC_nat_bounded_fin (λ k, (binom_prob p q n k * D #k)%R)) -D_sum.
        apply SeriesC_ext.
        move=>k.
        case_bool_decide; first done.
        rewrite /pmf /= binom_prob_gt; [lra | lia].
      }
      iIntros (k) "[Herr Htape]".
      wp_apply "Hnext".
      iFrame.
      rewrite fmap_app //.
    - iIntros (Σ erisGS0 α Δ l v Φ) "[(%l' & Htape & %Heq) ->] HΦ".
      destruct l' as [|v' l']; first discriminate.
      injection Heq as -> ->.
      wp_pures.
      wp_apply (twp_binomial_tape with "Htape") as "Htape".
      iApply "HΦ".
      iExists l'.
      by iFrame.
  Defined.
(*
  Lemma twp_binomial_presample_planner `{!erisGS Σ}
      (N M k : nat) (e : expr) (ε : nonnegreal)
      (L : nat) (α : loc) (Φ : val → iProp Σ)
      (prefix : list (fin (S k))) (suffix : list (fin (S k)) → list (fin (S k))) :
    (0 < N < S M)%nat →
    (0 < k)%nat → 
    to_val e = None →
    (∀ junk : list (fin (S k)),
       (length (suffix (prefix ++ junk)) <= L)%nat) →
    (0 < ε)%R →
    ↯ ε ∗ own_binomial_tape α N M k prefix ∗
    ( (∃ (junk : list (fin (S k))), own_binomial_tape α N M k (prefix ++ junk ++ suffix (prefix ++ junk))) -∗ WP e [{ Φ }]
    ) ⊢ WP e [{ Φ }].
   Proof.
     iIntros (N_bounds k_pos e_not_val suf_bounds ε_pos) "(Herr & Htape & Hnext)".
     wp_apply (abstract_planner (binom_prob N M k ∘ fin_to_nat) (own_binomial_tape α N M k) _ prefix suffix L (enum (fin (S k))) ε); try done.
     { move=>i.
       simpl.
       destruct k; first lia.
       pose proof (fin_to_nat_lt i).
       apply binom_prob_pos.
       lia.
     }
     {
       move=>i _.
       pose proof (fin_to_nat_lt i).
       apply binom_prob_gt_0; lia.
     }
     {
       apply SeriesC_correct'; last apply ex_seriesC_finite.
       apply sum_binom_prob.
     }
     {
       clear ε ε_pos L suf_bounds.
       iIntros (ε D L l ε_pos D_bounds D_sum) "(Htape & Herr & Hnext)".
       wp_apply (twp_binomial_presample_adv_comp _ _ _ _ _ _ _ _ D); try done.
       { move=>i. apply D_bounds. }
       { lia. }
       iFrame.
       iIntros (i) "[Herr Htape]".
       by iApply ("Hnext" with "Herr").
     }
     {
       move=>a j _.
       apply elem_of_enum.
     }
     iFrame.
     iIntros (j) "Htape".
     wp_apply "Hnext".
     iFrame.
   Qed.
  
  Definition binom_cred (p q n k : nat) := (1 - binom_prob p q n k)%R.
  
  Lemma twp_binom_k `{erisGS Σ} (p q n k : nat) :
    (p ≤ (q + 1))%nat →
    k ≤ n →
    [[{ ↯ (binom_cred p q n k) }]] 
      binom #() #p #q #n
    [[{ RET #k ; True }]].
  Proof using binspec.
    intros Hpq Hkn.
    set (fk := nat_to_fin (le_n_S _ _ Hkn)).
    set (D1 (m : fin (S n)) := binom_prob p q n m).
    set (D2 (m : fin (S n)) := if bool_decide (m = fk)
                               then binom_prob p q n k%R
                               else 0%R).
    set (D3 (m : fin (S n)) := if bool_decide (m = fk)
                               then 0%R
                               else binom_prob p q n m%R).
    set (D4 (m : fin (S n)) :=  if bool_decide (m = fk)
                               then 0%R
                                else 1%R).
    set (D5 (m : fin (S n)) := (binom_prob p q n m * D4 m)%R).

    assert (SeriesC D1 = 1%R) as HD1 by apply sum_binom_prob.
    assert (SeriesC D2 = binom_prob p q n k) as HD2 by apply SeriesC_singleton.
    assert (SeriesC D3 = SeriesC (λ k, D1 k - D2 k)%R) as HD3.
    { apply SeriesC_ext => m.
      unfold D1, D2, D3.
      case_bool_decide as H1; last lra.
      rewrite H1 fin_to_nat_to_fin.
      lra.
    }
    assert (SeriesC D3 = SeriesC D5) as HD5.
    {
      apply SeriesC_ext.
      intros m.
      unfold D3, D5, D4.
      case_bool_decide; lra.
    } 
    rewrite SeriesC_minus in HD3;[| apply ex_seriesC_finite..].
    rewrite HD1 HD2 in HD3.
    fold (binom_cred p q n k) in HD3.
    rewrite -HD3 HD5.
    iIntros (Φ) "Herr HΦ".
    wp_apply (twp_binom_adv_comp with "Herr"); [done| | done|].
    { move=>i.
      unfold D4.
      case_bool_decide; lra.
    } 
    iIntros (m).
    unfold D4.
    case_bool_decide as Hk.
    - rewrite Hk fin_to_nat_to_fin.
      iIntros "?".
      by iApply "HΦ".
    - iIntros "Herr".
      cred_contra.
  Qed.
 *)
  
End BinomialLemmas.
