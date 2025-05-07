From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling.bernoulli Require Import interface.
From clutch.eris.lib.sampling.binomial Require Import interface.

Section Polya.
  
  Set Default Proof Using "Type*".
  Context `{!erisGS Σ}.
  Context `{!bernoulli_spec bernoulli}.

  #[local] Ltac done ::= solve[
    lia |
    lra |
    nra |
    real_solver  |
    tactics.done |
    auto
  ].

  Definition polya : val :=
    rec: "polya" "α" "red" "black" "n" :=
      if: "n" = #0 then #0
      else
        let: "x" := bernoulli "α" "red" ("red" + "black" - #1)  in
        if: "x" = #1 
        then #1 + "polya" "α" ("red" + #1) "black" ("n" - #1)
        else "polya" "α" "red" ("black" + #1) ("n" - #1).
  
  
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

  Lemma polya_0_b (black n : nat) :
    (black > 0)%nat →
    [[{True}]]
      polya #() #0 #black #n
    [[{RET #0; True}]].
  Proof.
    iInduction n as [|n] "IH" forall (black).
    - iIntros "%Hb %Φ _ HΦ".
      unfold polya.
      wp_pures.
      by iApply "HΦ".
    - iIntros "%Hb %Φ _ HΦ".
      unfold polya.
      wp_pures.
      fold polya.
      rewrite Z.add_0_l.
      replace (black - 1)%Z with ((black - 1)%nat : Z) by lia.
      wp_apply (bernoulli_0 with "[$]") as "_".
      wp_pures.
      replace (S n - 1)%Z with (n : Z) by lia.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      iApply "IH"; done.
  Qed.

  Lemma polya_r_0 (red n : nat) :
    (red > 0)%nat →
    [[{True}]]
      polya #() #red #0 #n
    [[{RET #n; True}]].
  Proof.
    iInduction n as [|n] "IH" forall (red).
    - iIntros "%Hr %Φ _ HΦ".
      unfold polya.
      wp_pures.
      by iApply "HΦ".
    - iIntros "%Hr %Φ _ HΦ".
      unfold polya.
      wp_pures.
      fold polya.
      destruct red; first lia.
      replace (S red + 0 - 1)%Z with (red : Z) by lia.
      wp_apply (bernoulli_1 with "[$]") as "_".
      wp_pures.
      replace (S n - 1)%Z with (n : Z) by lia.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply "IH" as "_" => //.
      wp_pures. 
      rewrite Z.add_1_l -Nat2Z.inj_succ.
      iApply ("HΦ" with "[$]").
  Qed.
  
  Lemma polya_spec (red black n : nat) (E : fin (S n) → R) (ε : R) :
    (red + black > 0)%nat →
    (∀ k, E k >= 0) →
    ε = (SeriesC (fun k : fin (S n) => Beta_prob red black n k * E k )%R) →
    [[{
      ↯ ε
    }]]
    polya #() #red #black #n
    [[{
      (v : fin (S n)), RET #v; 
      ↯ (E v)
    }]].
  Proof.
    iIntros "%H_red_black_gt_0 %HE_nonneg %Heq %Φ Herr HΦ".
    destruct (decide (red = 0)%nat) as [-> | Hr_not_0].
    {
      rewrite Series_fin_first in Heq.
      subst.
      iPoseProof (ec_split with "Herr") as "[Herr _]".
      { add_hint Beta_prob_pos. done. }
      { add_hint Beta_prob_pos.
        apply SeriesC_ge_0' => k //. }
      rewrite /Beta_prob choose_n_0 !Beta_0_l.
      wp_apply polya_0_b as "_" => //.
      iApply ("HΦ" $! 0%fin with "[Herr]").
      iApply (ec_eq with "Herr") => //=.
    }
    destruct (decide (black = 0)%nat) as [-> | Hb_not_0].
    {
       (* !fin_to_nat_to_fin choose_n_n Nat.sub_diag !Beta_0_r Rmult_1_l Rdiv_diag // Rmult_1_l *)
      rewrite Series_fin_last in Heq.
      subst.
      iPoseProof (ec_split with "Herr") as "[_ Herr]".
      { add_hint Beta_prob_pos.
        apply SeriesC_ge_0' => k //. }
      { add_hint Beta_prob_pos.
        done. }
      wp_apply polya_r_0 as "_" => //.
      assert (n = (fin_to_nat (nat_to_fin (Nat.lt_succ_diag_r n)))) as Heqn by rewrite fin_to_nat_to_fin //.
      rewrite ->Heqn at 2.
      iApply ("HΦ" with "[Herr]").
      rewrite /Beta_prob !fin_to_nat_to_fin choose_n_n Nat.sub_diag !Beta_0_r.
      iApply (ec_eq with "Herr") => //=.
    }
    (* It is easier to prove with E : nat → R, as induction on R can mess with the types, but still requiring E : fin (S n) → R can be interesting, to discuss *)
    rename E into E', HE_nonneg into HE'_nonneg, Heq into Heq'.
    pose E k := if Nat.lt_dec k (S n) is left pf
                then E' (((Fin.of_nat_lt pf)))
                else 1%R.
    assert (HE_nonneg : ∀ k : nat, E k >= 0).
    { move=>k. unfold E. real_solver. }
    iAssert (∀ v : fin (S n), ↯ (E v) -∗ Φ #v)%I with "[HΦ]" as "HΦ".
    { iIntros "%v Herr".
      unfold E.
      iApply "HΦ".
      destruct (Nat.lt_dec v (S n)); last cred_contra.
      rewrite nat_to_fin_to_nat //. }
    assert (ε = SeriesC (λ x : fin (S n), choose n x * Beta (x + red) (n - x + black) / Beta red black * E x)) as Heq. {
      rewrite Heq'.
      apply SeriesC_ext => k.
      simpl_expr.
      pose proof (fin_to_nat_lt k).
      unfold E.
      destruct (Nat.lt_dec k (S n)); last lia.
      rewrite nat_to_fin_to_nat //. }
    clearbody E.
    clear Heq' E' HE'_nonneg.

    (* Here starts the proof *)
    iInduction n as [|n] "IH" forall (E HE_nonneg red Hr_not_0 black Hb_not_0 ε H_red_black_gt_0 Heq Φ).
    - unfold polya. wp_pures.
      rewrite SeriesC_finite_foldr /= in Heq.
      rewrite choose_n_0 Rmult_1_l in Heq.
      add_hint Beta_pos.
      rewrite Rdiv_diag // Rplus_0_r Rmult_1_l in Heq.
      rewrite Heq.
      iApply ("HΦ" $! 0%fin with "[$Herr]").
    - wp_rec. wp_pures.
      rewrite -Nat2Z.inj_add.
      rewrite Beta_sum_split in Heq; [|done..].
      match type of Heq with 
      | _ = (_ * ?A) + (_ * ?B) => 
        set ε2 := A;
        set ε1 := B;
        fold ε1 ε2 in Heq
      end.
      replace ((red + black)%nat - 1)%Z with ((red + black - 1)%nat : Z) by lia.
      wp_apply (twp_bernoulli_scale _ _ ε ε1 ε2 with "Herr") as "% [[-> Herr]| [-> Herr]]".
      { lia. }
      { unfold ε1. 
        apply SeriesC_ge_0, ex_seriesC_finite => k.
        add_hint Beta_prob_pos.
        real_solver. }
      { unfold ε2. 
        apply SeriesC_ge_0, ex_seriesC_finite => k.
        add_hint Beta_prob_pos.
        real_solver. }
      { assert (INR red + INR black ≠ 0). 
        { rewrite -plus_INR. change 0 with (INR 0).
          apply not_INR.
          lia. }
        replace (S (red + black - 1))%nat with (red + black)%nat by lia.
        rewrite Heq Rplus_comm (Rmult_comm ε2 _) (Rmult_comm ε1 _) plus_INR.
        simpl_expr.
        rewrite Rmult_plus_distr_l.
        simpl_expr. }
      + wp_pures.
        rewrite Z.add_1_r -Nat2Z.inj_succ.
        rewrite Z.sub_1_r (Nat2Z.inj_succ n) Z.pred_succ.
        wp_apply ("IH" $! E HE_nonneg with "[] [] [] [] Herr") as "%v [%Hv_le_n Herr]".
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. subst ε1.
          apply SeriesC_ext => k.
          rewrite fin_S_inj_to_nat //. }
        rewrite fin_S_inj_to_nat.
        iApply ("HΦ" with "[$Herr]").
      + wp_pures.
        rewrite Z.add_1_r -Nat2Z.inj_succ.
        rewrite Z.sub_1_r (Nat2Z.inj_succ n) Z.pred_succ.
        wp_apply ("IH" $! (E ∘ S) with "[] [] [] [] [] Herr") as "%v Herr".
        { real_solver. }
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. lia. }
        { iPureIntro. subst ε2.
          apply SeriesC_ext => k.
          fold (Beta_prob (S red) black n k).
          simpl_expr. }
        wp_pures.
        rewrite Z.add_1_l -Nat2Z.inj_succ.
        rewrite -fin_to_nat_FS.
        iApply ("HΦ" with "[Herr]").
        rewrite fin_to_nat_FS //.
  Qed.
  
End Polya.
