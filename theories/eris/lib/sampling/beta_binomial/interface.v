From clutch.eris Require Export eris.
From clutch.eris.lib.sampling Require Import abstract_planner distr_impl utils. 
From clutch.eris.lib.sampling.binomial Require Import interface.

Section BetaProbability.

  #[local] Ltac done ::= solve[
    lia |
    lra |
    nra |
    real_solver  |
    tactics.done |
    auto
   ].
  
  Definition Beta x y := ((fact (x - 1)) * (fact (y - 1)) / (fact (x + y - 1)))%R.
  
  Lemma Beta_0_l (y : nat) :
    Beta 0 y = 1.
  Proof.
    add_hint INR_fact_lt_0.
    rewrite /Beta /=.
    simpl_expr.
  Qed.
  Lemma Beta_0_r (x : nat) :
    Beta x 0 = 1.
  Proof.
    add_hint INR_fact_lt_0.
    rewrite /Beta /=.
    simpl_expr.
    do 2 f_equal.
    lia.
  Qed.

  Lemma Beta_pos (x y : nat) : (0 < Beta x y)%R.
  Proof.
    add_hint INR_fact_lt_0.
    unfold Beta.
    simpl_expr.
  Qed.

  Definition Beta_prob (r b n k : nat) := (choose n k * Beta (k + r) (n - k + b) / Beta r b)%R.

  Lemma Beta_prob_0_0 (r b : nat) : Beta_prob r b 0 0 = 1.
  Proof.
    rewrite /Beta_prob choose_n_0 /= Rmult_1_l Rdiv_diag //.
    pose proof (Beta_pos r b).
    lra.
  Qed.

  Lemma Beta_prob_pos (r b n k : nat) : (0 <= Beta_prob r b n k)%R.
  Proof.
    add_hint Beta_pos.
    add_hint choose_pos.
    unfold Beta_prob.
    real_solver.
  Qed.

  #[local] Open Scope R.
  Lemma Beta_sum_split (r b n : nat) (E : fin (S (S n)) → R) :
    (0 < r)%nat → 
    (0 < b)%nat →
    SeriesC (λ k : fin (S (S n)), Beta_prob r b (S n) k * E k)%R = 
      r / (r + b) * SeriesC (λ k : fin (S n), Beta_prob (S r) b n k * E (FS k))
    + b / (r + b) * SeriesC (λ k : fin (S n), Beta_prob r (S b) n k * E (fin_S_inj k))
  .
  Proof.
    intros H_r_pos H_b_pos.
    apply lt_INR in H_r_pos as H_r_pos'.
    apply lt_INR in H_b_pos as H_b_pos'.
    assert (0 < r + b) as H_rb_pos by rewrite -plus_INR //.
    add_hint INR_fact_lt_0.
    add_hint Beta_pos.
    add_hint fact_neq_0.
    rewrite Series_fin_first Series_fin_last.
    rewrite Series_fin_last Series_fin_first.
    rewrite !fin_to_nat_FS fin_to_nat_to_fin.
    set T0 := Beta_prob r b (S n) 0%fin * E 0%fin.
    set TN := Beta_prob r b (S n) (S n) * E (FS (nat_to_fin (Nat.lt_succ_diag_r n))).
    set T0' := Beta_prob r (S b) n 0%fin * E (fin_S_inj 0).
    set TN' := Beta_prob (S r) b n n * E (FS (nat_to_fin (Nat.lt_succ_diag_r n))).
    set p1 := r / (r + b).
    set p2 := b / (r + b).
    rewrite !Rmult_plus_distr_l.
    rewrite -!SeriesC_scal_l.
    assert (TN = p1 * TN') as <-.
    {
      subst TN TN'.
      rewrite -(Rmult_assoc p1).
      simpl_expr.
      unfold Beta_prob.
      rewrite !choose_n_n !Rmult_1_l.
      subst p1.
      assert (0 < (r + b) * Beta (S r) b) by real_solver.
      trans (r * Beta (n + S r) (n - n + b) / ((r + b) * Beta (S r) b)); last first.
      {
        simpl_expr.
        rewrite (Rmult_comm _ (/(r + b))).
        rewrite Rmult_assoc.
        rewrite -(Rmult_assoc (Beta (S r) b)).
        rewrite -(Rmult_assoc (Beta (S r) b)).
        rewrite (Rmult_comm _ (/(r + b))).
        rewrite -!(Rmult_assoc (r + b)).
        rewrite Rmult_inv_r // Rmult_1_l.
        rewrite (Rmult_comm _ r).
        rewrite Rmult_assoc.
        simpl_expr.
      }
      rewrite !Nat.sub_diag !Nat.add_0_l.
      simpl_expr.
      unfold Beta.
      simpl.
      rewrite !Nat.sub_0_r.
      replace (n + S r - 1)%nat with (n + r)%nat by lia.
      replace (n + S r + b - 1)%nat with (n + r + b)%nat by lia.
      rewrite -plus_INR.
      rewrite -!(Nat.add_assoc n r b).
      remember (r + b)%nat as A.
      set B := (fact (n + A)).
      remember (fact (n + r) * fact (b - 1)) as C.
      destruct r; first lia.
      rewrite fact_simpl mult_INR S_INR /= Nat.sub_0_r -!Rmult_assoc (Rmult_comm A) !Rmult_assoc.
      simpl_expr.
      rewrite -!mult_INR.
      rewrite -(Rmult_assoc (fact r)) -mult_INR.
      set D := (fact r * fact (b - 1))%nat.
      assert (0 < D) by rewrite mult_INR //.
      rewrite Rinv_mult Rinv_inv (Rmult_comm (/D)) -!Rmult_assoc.
      simpl_expr.
      rewrite Rmult_comm -Rmult_assoc.
      simpl_expr.

      rewrite (Rmult_comm B A) !(Rmult_assoc A) -Rmult_assoc.
      replace (fact (A - 1) * A) with (fact A : R) by rewrite HeqA -mult_INR /= Nat.sub_0_r //.
      rewrite (Rmult_comm _ C) -!Rmult_assoc.
      simpl_expr.
    }
    assert (T0 = p2 * T0') as <-. {
      subst T0 p2 T0'.
      rewrite /= -!(Rmult_assoc _ _ (E 0%fin)).
      simpl_expr.
      unfold Beta_prob.
      rewrite /Beta_prob /= Nat.sub_0_r !choose_n_0 !Rmult_1_l.
      rewrite Rmult_comm Nat.add_succ_r !Rdiv_def Rmult_assoc.
      simpl_expr.
      unfold Beta.
      destruct b; first lia.
      rewrite !Nat.add_succ_r !Nat.sub_succ !Nat.sub_0_r.
      rewrite !Rinv_mult !Rinv_inv !Rmult_assoc.
      simpl_expr.
      rewrite (Rmult_comm (/fact b)) (Rmult_comm (/fact (S b))) (fact_simpl b) mult_INR Rinv_mult -Rmult_assoc.
      simpl_expr.
      rewrite (Rmult_comm (fact _)) !Rmult_assoc.
      simpl_expr.
      rewrite Rmult_comm fact_simpl.
      simpl_expr.
      rewrite -plus_INR -mult_INR Nat.add_succ_r //.
    }
    rewrite -!Rplus_assoc.
    rewrite (Rplus_comm (SeriesC _)).
    rewrite !Rplus_assoc.
    rewrite (Rplus_comm TN).
    rewrite -!Rplus_assoc.
    simpl_expr.
    rewrite (Rplus_comm (SeriesC _)).
    rewrite !Rplus_assoc.
    simpl_expr.
    rewrite -SeriesC_plus; [|apply ex_seriesC_finite..].
    apply SeriesC_ext => k.
    rewrite -(Rmult_assoc p1).
    rewrite -(Rmult_assoc p2).
    rewrite -Rmult_plus_distr_r.
    simpl_expr.
    rewrite !fin_to_nat_FS.
    rewrite -fin_S_inj_to_nat.
    unfold p1, p2, Beta_prob. 
    rewrite -pascal'.
    rewrite Rdiv_def !Rmult_plus_distr_r.
    f_equal.
    - rewrite !Rdiv_def Rmult_assoc.
      rewrite (Rmult_comm (r * / (r + b))).
      rewrite !(Rmult_assoc (choose n k)).
      simpl_expr.
      rewrite Nat.add_succ_r (Rmult_comm (Beta r b)) Rmult_assoc Rmult_assoc -{1}(Rmult_1_r (Beta _ _)).
      simpl.
      simpl_expr.
      rewrite Rmult_comm.
      simpl_expr.
      rewrite Rmult_comm -Rmult_assoc.
      simpl_expr.
      unfold Beta.
      simpl.
      rewrite !Nat.sub_0_r.
      rewrite (Rmult_comm _ r) ((Rmult_comm (r + b))).
      rewrite -!(Rmult_assoc r).
      destruct r; first lia.
      rewrite !Nat.add_succ_l !Nat.sub_succ !Nat.sub_0_r.
      rewrite (Rmult_comm _ (S r + b)) !Rdiv_def -!Rmult_assoc.
      simpl_expr.
      rewrite -!Rmult_assoc.
      simpl_expr.
      rewrite (Rmult_comm _ (S r + b)) -plus_INR -!mult_INR Nat.add_succ_l -!fact_simpl //.
    - rewrite (Rmult_comm (b / (r + b))) !Rdiv_def !(Rmult_assoc (choose n (S k))).
      simpl_expr.
      simpl.
      replace (n - S k + S b)%nat with (n - k + b)%nat; last first.
      {
        pose proof (fin_to_nat_lt k).
        lia.
      }
      unfold Beta.
      simpl.
      rewrite !Nat.sub_0_r.
      simpl_expr.
      rewrite -!Rmult_assoc.
      simpl_expr.
      rewrite (Rmult_comm _ b) -!Rmult_assoc.
      assert (0 < fact (r - 1) * fact b * / fact (r + S b - 1)). {
        simpl_expr.
      }
      simpl_expr.
      rewrite (Rmult_comm b) !Rmult_assoc.
      simpl_expr.
      rewrite (Rmult_comm b) !Rmult_assoc.
      simpl_expr.
      rewrite -!Rmult_assoc (Rmult_comm _ b) -!Rmult_assoc.
      destruct b; first lia.

      rewrite -mult_INR !S_INR /= Nat.sub_0_r.
      simpl_expr.
      rewrite (Rmult_comm _ (r + (b + 1))) -!Rmult_assoc.
      simpl_expr.
      rewrite -!Nat.add_sub_assoc //= Nat.sub_0_r -INR_1 -!plus_INR -!mult_INR Nat.add_1_r Nat.add_succ_r Nat.mul_comm //=.
  Qed.

  Lemma Beta_sum_1 :
    ∀ (r b n : nat),
    (0 < r)%nat → 
    (0 < b)%nat →
    SeriesC (λ k : fin (S n), Beta_prob r b n k)%R = 1.
  Proof.
    move=> r b n.
    elim:n r b=>[|n IH] r b r_gt_0 b_gt_0.
    - rewrite SeriesC_finite_foldr /=.
      rewrite Beta_prob_0_0 /=.
      lra.
    - rewrite (SeriesC_ext _ (λ (k : fin (S (S n))), Beta_prob r b (S n) k * const 1 k)); last (move=>t /=; lra).
      rewrite (Beta_sum_split _ _ _ (const 1) r_gt_0 b_gt_0)
        (SeriesC_ext _ (λ (k : fin (S n)), Beta_prob (S r) b n k)); last (move=>t /=; lra).
      rewrite IH; [|lia..].
      rewrite (SeriesC_ext _ (λ (k : fin (S n)), Beta_prob r (S b) n k)); last (move=>t /=; lra).
      rewrite IH; [|lia..].
      rewrite !Rmult_1_r.
      apply lt_INR in r_gt_0.
      apply lt_INR in b_gt_0.
      simpl in r_gt_0.
      simpl in b_gt_0.
      rewrite -Rmult_plus_distr_r -Rdiv_def Rdiv_diag; lra.
  Qed.

  Program Definition Beta_distr
    (r b n : nat)
    (r_gt_0 : (0 < r)%nat)
    (b_gt_0 : (0 < b)%nat) : distr (fin (S n))
    := MkDistr
         (Beta_prob r b n)
         (Beta_prob_pos r b n)
         (@ex_seriesC_finite (fin (S n)) _ _ (Beta_prob r b n))
         _.
  Next Obligation.
    move=> r b n r_gt_0 b_gt_0.
    rewrite Beta_sum_1 //.
  Qed.

  #[local] Close Scope R.
End BetaProbability.

Class beta_binomial_spec (beta_prog beta_alloc : val) :=
  BetaSpec
    {

      AbsLoc : nat → Type;

      own_beta_tape `{!erisGS Σ} 
        (red black n : nat)
        (Δ : AbsLoc n)
        (l : list (fin (S n))) : iProp Σ;

      is_abs_loc `{!erisGS Σ} : ∀ (n : nat), AbsLoc n →  val → iProp Σ;
      
      loc_unit : nat → val; 
      
      twp_beta_binomial_adv_comp `{!erisGS Σ} :
      ∀ (red black n : nat) (D : fin (S n) → R) (ε : R),
        (red + black > 0)%nat →
        (∀ k, 0 <= D k)%R →
        ε = (SeriesC (λ (k : fin (S n)), Beta_prob red black n k * D k )%R) →
        [[{
              ↯ ε
        }]]
          beta_prog (loc_unit n) #red #black #n
        [[{
              (v : fin (S n)), RET #v; 
              ↯ (D v)
        }]];

      twp_beta_alloc `{!erisGS Σ} (red black n : nat) :
      (0 < red + black)%nat →
        [[{ True }]]
          beta_alloc #red #black #n
        [[{ (Δ : AbsLoc n) (α : val), RET α; is_abs_loc n Δ α ∗ own_beta_tape red black n Δ [] }]];

      twp_beta_presample_adv_comp `{!erisGS Σ} : 
         ∀ (e : expr) (red black n : nat) (ε : R)
           (D : fin (S n) → R)
           (Δ : AbsLoc n)
           (l : list (fin (S n)))
           (Φ : val → iProp Σ),
           (0 < red + black)%nat →
           to_val e = None →
           (∀ (i : fin (S n)), 0 <= D i)%R →
           SeriesC (λ (i : fin (S n)),
                      Beta_prob red black n i * D i)%R = ε →
           ↯ ε ∗
           own_beta_tape red black n Δ l ∗
           (∀ (i : fin (S n)),
              ↯ (D i) ∗ own_beta_tape red black n Δ (l ++ [i]) -∗
              WP e [{ v, Φ v }]
           ) ⊢ WP e [{ v, Φ v }];

      twp_beta_tape `{!erisGS Σ} :
        ∀ (red black n : nat)
          (α : val)
          (Δ : AbsLoc n)
          (l : list (fin (S n)))
          (i : fin (S n)),
          (0 < red + black)%nat →
          [[{ own_beta_tape red black n Δ (i::l) ∗ is_abs_loc n Δ α }]]
            beta_prog α #red #black #n
          [[{ RET #i; own_beta_tape red black n Δ l }]]

    }.

Section BetaBinomialLemmas.

  Context `{betaspec: beta_binomial_spec beta_prog betalloc}.

  Instance beta_binomial_impl {r b n : nat}
    {r_gt_0 : (0 < r)%nat} {b_gt_0 : (0 < b)%nat}:
    distr_impl (dmap (LitV ∘ LitInt ∘ Z.of_nat ∘ fin_to_nat) (Beta_distr r b n r_gt_0 b_gt_0)).
  Proof using betaspec.
     
    refine (MkDistrImpl _
              (λ: "α", beta_prog "α" #r #b #n) (λ: <>, betalloc #r #b #n)
              (AbsLoc n)
              (λ _ _ Δ l, ∃ l', own_beta_tape r b n Δ l' ∗
                            ⌜l = fmap (λ (k : fin (S n)), #k) l'⌝)%I
              (λ _ _, is_abs_loc n)%I (loc_unit n) _ _ _ _).
    - iIntros (Σ erisGS0 D ε L ε_ge_0 D_bounds D_sum Φ) "Herr HΦ".
      set (D' (k : nat) := D #k).
      wp_pures.
      wp_apply (twp_beta_binomial_adv_comp r b n D' _ ltac:(lia) with "Herr [HΦ]").
      { move=>k. apply D_bounds. }
      { rewrite (dmap_expected_value _ _ _ L) // in D_sum. }
      iIntros (k) "Herr".
      by iApply "HΦ".
    - iIntros (Σ erisGS0 Φ) "_ HΦ".
      wp_pures.
      wp_apply (twp_beta_alloc r b n ltac:(lia) with "[$]") as (Δ α) "[Hα HΔ]".
      iApply "HΦ".
      by iFrame.
    - iIntros (Σ erisGS0 e ε Δ l D L Φ e_not_val ε_ge_0 D_bounds D_sum) "(Herr & (%l' & Htape & ->) & Hnext)".
      set (D' (k : fin (S n)) := D #k).
      unshelve wp_apply (twp_beta_presample_adv_comp _ r b n _ D' _ _ _ ltac:(lia) e_not_val  with "[$Herr $Htape Hnext]").
      { move=>k. apply D_bounds. }
      { rewrite (dmap_expected_value _ _ _ L) // in D_sum. }
      iIntros (k) "[Herr Htape]".
      wp_apply "Hnext".
      iFrame.
      rewrite fmap_app //.
    - iIntros (Σ erisGS0 α Δ l v Φ) "[(%l' & HΔ & %Heq) Hα] HΦ".
      destruct l' as [|v' l']; first discriminate.
      injection Heq as -> ->.
      wp_pures.
      wp_apply (twp_beta_tape r b n _ _ _ _ ltac:(lia) with "[$HΔ $Hα]") as "HΔ".
      iApply "HΦ".
      iExists l'.
      by iFrame.
  Defined.

End BetaBinomialLemmas.
