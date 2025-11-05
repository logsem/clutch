From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import Coquelicot.
From Coquelicot Require Import RInt RInt_analysis AutoDerive.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real indicators.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Ltac OK := auto; (try by intuition); try lia; try lra.

Section pmf.

  (* The PMF for lazyDecrR starting with N=0 *)
  Definition RealDecrTrial_μ0 (x : R) (n : nat) : R := x ^ n / fact n - x ^ (n + 1) / fact (n + 1).

  (* The PMF for lazyDecrR starting with N=i *)
  Definition RealDecrTrial_μ (x : R) (i n : nat) : R := Iverson (uncurry le) (i, n) * RealDecrTrial_μ0 x (n - i).

  Theorem RealDecrTrial_μ_not_supp {x i n} (H : lt n i) : RealDecrTrial_μ x i n = 0.
  Proof. rewrite /RealDecrTrial_μ Iverson_False //=; OK. Qed.

  Theorem RealDecrTrial_μ_supp {x i n} (H : ¬ lt n i) : RealDecrTrial_μ x i n = RealDecrTrial_μ0 x (n - i).
  Proof. rewrite /RealDecrTrial_μ Iverson_True //=; [lra|lia]. Qed.

  Theorem RealDecrTrial_μ_base {x n} : RealDecrTrial_μ x 0 n = RealDecrTrial_μ0 x n.
  Proof. rewrite RealDecrTrial_μ_supp; [f_equal; lia| lia]. Qed.

  Lemma RealDecrTrial_μ0nn {x n} (Hx : 0 <= x <= 1) : 0 <= RealDecrTrial_μ0 x n.
  Proof.
    rewrite /RealDecrTrial_μ0.
    apply error_credits.Rle_0_le_minus.
    replace (x ^ (n + 1) / fact (n + 1)) with ((x ^ (n + 1)) * (1 / fact (n + 1))) by lra.
    replace (x ^ n / fact n) with ((x ^ n) * (1 / fact n)) by lra.
    apply Rmult_le_compat.
    { apply pow_le; lra. }
    { apply Rcomplements.Rdiv_le_0_compat; [lra|]. apply INR_fact_lt_0. }
    { rewrite pow_add pow_1.
      rewrite -{2}(Rmult_1_l (x^n)) Rmult_comm.
      apply Rmult_le_compat; try lra.
      apply pow_le; lra. }
    rewrite Rdiv_1_l Rdiv_1_l.
    apply Rcomplements.Rinv_le_contravar.
    { apply INR_fact_lt_0. }
    { apply le_INR.
      apply fact_le.
      lia.
    }
  Qed.

  Lemma RealDecrTrial_μnn {x i n} (H : 0 <= x <= 1) : 0 <= RealDecrTrial_μ x i n.
  Proof. rewrite /RealDecrTrial_μ. apply Rmult_le_pos; [apply Iverson_nonneg|apply RealDecrTrial_μ0nn; auto]. Qed.

End pmf.

Section credits.
  Import Hierarchy.

  (* Expected number of credits to execute lazyDecrR i x *)
  Definition RealDecrTrial_CreditV (F : nat → R) (i : nat) (x : R) : R :=
    SeriesC (fun n : nat => RealDecrTrial_μ x i n * F n).

  (* Credit distribution function *)
  Definition g (F : nat → R) (i : nat) (x : R) : R → R := fun y =>
    Iverson (uncurry Rle) (y, x) * RealDecrTrial_CreditV F (i + 1) y +
    Iverson (uncurry Rge) (y, x) * F i.

  Lemma CreditV_nonneg {F i x} (Hnn : ∀ n, 0 <= F n) (H : 0 <= x <= 1) : 0 <= RealDecrTrial_CreditV F i x.
  Proof. rewrite /RealDecrTrial_CreditV. apply SeriesC_ge_0'. intro n. apply Rmult_le_pos; [apply RealDecrTrial_μnn; auto |apply Hnn]. Qed.

  Lemma g_nonneg {F N rx r} (Hnn : ∀ n, 0 <= F n) (H : 0 <= r <= 1) : 0 <= g F N rx r.
  Proof.
    rewrite /g. apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg|]).
    { apply CreditV_nonneg; auto. }
    { apply Hnn. }
  Qed.

  Lemma RealDecrTrial_μ_le_1 {t m n} (H : 0 <= t <= 1) : RealDecrTrial_μ t m n <= 1.
  Proof.
    rewrite /RealDecrTrial_μ.
    rewrite -(Rmult_1_l 1).
    apply Rmult_le_compat.
    { apply Iverson_nonneg. }
    { by apply RealDecrTrial_μ0nn. }
    { apply Iverson_le_1. }
    { rewrite /RealDecrTrial_μ0.
      case (decide (m <= n)%nat).
      { intro Hnm.
        replace (t ^ (n - m) / fact (n - m) - t ^ (n - m + 1) / fact (n - m + 1)) with
                ((t ^ (n - m) * / fact (n - m)) * (1 - t / (n - m + 1))); last first.
        { rewrite Rmult_minus_distr_l.
          f_equal.
          { lra. }
          { rewrite Rdiv_def Rdiv_def.
            rewrite (Rmult_comm (t ^ (n - m)) _).
            rewrite Rmult_assoc.
            rewrite -(Rmult_assoc _ t).
            rewrite -{2}(pow_1 t).
            rewrite -pow_add.
            rewrite Rmult_comm.
            rewrite Rmult_assoc.
            f_equal.
            rewrite -Rinv_mult.
            f_equal.
            rewrite -minus_INR; [|done].
            rewrite -INR_1.
            rewrite -plus_INR.
            rewrite -mult_INR.
            replace (n - m + 1)%nat with (S (n - m)%nat) by lia.
            by rewrite -fact_simpl.
            }
          }
        rewrite -{3}(Rmult_1_l 1).
        apply Rmult_le_compat.
        { apply Rmult_le_pos; [apply pow_le; lra |].
          rewrite -(Rmult_1_l (/ _)).
          apply Rcomplements.Rdiv_le_0_compat; [lra|].
          apply INR_fact_lt_0.
        }
        { apply error_credits.Rle_0_le_minus.
          apply Rcomplements.Rle_div_l.
          { apply Rlt_gt.
            rewrite -INR_0.
            rewrite -minus_INR; [|done].
            rewrite -INR_1.
            rewrite -plus_INR.
            apply lt_INR.
            replace (n - m + 1)%nat with (S (n - m)%nat) by lia.
            lia.
          }
          transitivity 1; [lra|].
          rewrite -minus_INR; [|done].
          rewrite -INR_1.
          rewrite -plus_INR.
          rewrite -mult_INR.
          apply le_INR.
          lia.
        }
        { rewrite -Rcomplements.Rdiv_le_1; [|apply INR_fact_lt_0].
          transitivity 1.
          { rewrite -(pow1 (n - m)). apply pow_incr; lra. }
          rewrite -INR_1.
          apply le_INR.
          rewrite Nat.le_succ_l.
          apply lt_O_fact.
        }
        { apply Rminus_le_0_compat.
          rewrite Rdiv_def.
          apply Rle_mult_inv_pos; [lra|].
          rewrite -INR_0.
          rewrite -minus_INR; [|done].
          rewrite -INR_1.
          rewrite -plus_INR.
          apply lt_INR.
          replace (n - m + 1)%nat with (S (n - m)%nat) by lia.
          lia.
        }
      }
      {
        intro Hnm.
        rewrite Rcomplements.MyNat.minus_0_le; [|lia].
        rewrite pow_O.
        rewrite {1}/fact.
        rewrite INR_1.
        rewrite Rdiv_diag; [|lra].
        apply Rminus_le_0_compat.
        rewrite //= Rmult_1_r.
        lra.
      }
    }
  Qed.

  Lemma RealDecrTrial_μ_ex_RInt {n m} {a b} : ex_RInt (λ y : R, RealDecrTrial_μ y n m) a b.
  Proof.
    rewrite /RealDecrTrial_μ.
    apply ex_RInt_mult; [apply ex_RInt_const|].
    rewrite /RealDecrTrial_μ0.
    replace (λ y : R, y ^ (m - n) / fact (m - n) - y ^ (m - n + 1) / fact (m - n + 1))
       with (λ y : R, (y ^ (m - n) * / fact (m - n)) - ((y ^ (m - n + 1) * / fact (m - n + 1)))); last first.
    { apply functional_extensionality; intros ?.  rewrite /minus/plus/opp//=. }
    apply (ex_RInt_minus (V := R_NormedModule)).
    { apply ex_RInt_mult; [apply ex_RInt_pow|apply ex_RInt_const]. }
    { apply ex_RInt_mult; [apply ex_RInt_pow|apply ex_RInt_const]. }
  Qed.

  Lemma RealDecrTrial_CreditV_ex_RInt {F N M} (Hbound : forall n, 0 <= F n <= M) :
    ex_RInt (RealDecrTrial_CreditV F (N + 1)) 0 1.
  Proof.
    rewrite -ex_RInt_dom.
    rewrite /ex_RInt.
    rewrite /RealDecrTrial_CreditV.
    replace (λ x : R, Iverson (Ioo 0 1) x * SeriesC (λ n : nat, RealDecrTrial_μ x (N + 1) n * F n))
       with (λ x : R, Series.Series (λ n : nat, Iverson (Ioo 0 1) x * (RealDecrTrial_μ x (N + 1) n * F n))); last first.
    { apply functional_extensionality; intros ?.
      rewrite -SeriesC_scal_l.
      rewrite SeriesC_Series_nat.
      done.
    }
    pose s : nat → R → R_CompleteNormedModule := fun M x => sum_n (λ n : nat, Iverson (Ioo 0 1) x * (RealDecrTrial_μ x (N + 1) n * F n)) M.
    pose h : nat → R_CompleteNormedModule := fun x => (RInt (λ x0 : R, sum_n (λ n : nat, Iverson (Ioo 0 1) x0 * (RealDecrTrial_μ x0 (N + 1) n * F n)) x) 0 1).
    have HSLim : filterlim s eventually (locally (λ x : R, Series (λ n : nat, Iverson (Ioo 0 1) x * (RealDecrTrial_μ x (N + 1) n * F n)))).
    { rewrite /s.
      apply (UniformConverge_Series (fun n => M * / (fact (n - (N + 1))%nat))).
      { apply (@ex_series_scal_l _ R_CompleteNormedModule).
        apply ex_exp_series'. }
      intros x n.
      rewrite Rabs_right; last first.
      { apply Rle_ge.
        rewrite /Iverson; case_decide.
        { rewrite Rmult_1_l. apply Rmult_le_pos; [apply RealDecrTrial_μnn|].
          { rewrite /Ioo in H.
            rewrite Rmin_left in H; OK.
            rewrite Rmax_right in H; OK.
          }
          { apply Hbound. }
        }
        OK.
      }
      rewrite /Iverson.
      case_decide; last first.
      { rewrite Rmult_0_l.
        apply Rdiv_le_0_compat. { have ? := Hbound 0%nat. OK. }
        apply INR_fact_lt_0. }
      rewrite /Ioo in H.
      rewrite Rmin_left in H; OK.
      rewrite Rmax_right in H; OK.
      rewrite Rmult_1_l.
      rewrite Rmult_comm.
      apply Rmult_le_compat.
      { apply Hbound. }
      { apply RealDecrTrial_μnn; OK. }
      { apply Hbound. }
      rewrite /RealDecrTrial_μ.
      rewrite /Iverson; case_decide; last first.
      { rewrite Rmult_0_l.
        rewrite -(Rmult_1_l (/ fact _)).
        apply Rdiv_le_0_compat; OK.
        apply INR_fact_lt_0. }
      rewrite Rmult_1_l.
      rewrite /RealDecrTrial_μ0.
      repeat rewrite Rdiv_def.
      replace (n - (N + 1) + 1)%nat with (S (n - (N + 1))) by OK.
      rewrite fact_simpl.
      rewrite mult_INR.
      rewrite Rinv_mult.
      rewrite -Rmult_assoc.
      rewrite -Rmult_minus_distr_r.
      rewrite -{2}(Rmult_1_l (/fact (n - (N + 1)))).
      apply Rmult_le_compat.
      { apply Rle_0_le_minus.
        rewrite -(Rmult_1_l (x ^ (n - (N + 1)))).
        rewrite Rmult_comm.
        apply Rmult_le_compat.
        { rewrite -(Rmult_1_l (/ _)).
          apply Rle_mult_inv_pos; OK.
          apply pos_INR_S. }
        { apply pow_le; OK. }
        { rewrite -Rinv_1.
          apply Rinv_le_contravar; OK.
          rewrite -INR_1.
          apply le_INR.
          OK.
        }
        { rewrite -(Rmult_1_l (x ^ (n - (N + 1)))).
          rewrite -tech_pow_Rmult.
          apply Rmult_le_compat_r; OK.
          apply pow_le; OK.
        }
      }
      { rewrite -(Rmult_1_l (/ _)).
        apply Rle_mult_inv_pos; OK.
        apply INR_fact_lt_0. }
      { have ? : 0 <= x ^ S (n - (N + 1)) * / S (n - (N + 1)).
        { apply Rle_mult_inv_pos; OK.
          { apply pow_le; OK. }
          { apply pos_INR_S. }
        }
        suffices ? : x ^ (n - (N + 1)) <= 1 by OK.
        rewrite -(pow1 (n - (N + 1))).
        apply pow_incr; OK.
      }
      { apply Rinv_le_contravar; OK. apply INR_fact_lt_0. }
    }
    have HSInt : ∀ x : nat, is_RInt (s x) 0 1 (h x).
    { rewrite /s/h. intro N'.
      apply (@RInt_correct R_CompleteNormedModule).
      apply ex_RInt_sum_n.
      intros n.
      rewrite ex_RInt_dom.
      apply ex_RInt_Rmult'.
      apply RealDecrTrial_μ_ex_RInt.
    }
    destruct (@filterlim_RInt nat R_CompleteNormedModule s 0 1 eventually eventually_filter
      (λ x : R, Series (λ n : nat, Iverson (Ioo 0 1) x * (RealDecrTrial_μ x (N + 1) n * F n))) h HSInt HSLim) as [IF [HIf1 HIf2]].
    exists IF. done.
  Qed.

  (* Telescoping series *)
  Lemma RealDecrTrial_μ0_ex_seriesC {x} (Hx : 0 <= x <= 1) : ex_seriesC (λ n : nat, RealDecrTrial_μ0 x n).
  Proof.
  Admitted.

  Lemma RealDecrTrial_μ0_ex_seriesC' {x} (Hx : 0 <= x <= 1) : ex_seriesC (λ n : nat, RealDecrTrial_μ0 x (n + 1)).
  Proof.
  Admitted.

  Lemma g_ex_RInt {F N M rx} (Hbound : ∀ n : nat, 0 <= F n <= M) : ex_RInt (g F N rx) 0 1.
  Proof.
    rewrite /g.
    apply ex_RInt_add.
    { apply ex_RInt_mult; [apply ex_RInt_Iverson_le_uncurry|].
      eapply RealDecrTrial_CreditV_ex_RInt.
      done.
    }
    { apply ex_RInt_mult; [apply ex_RInt_Iverson_ge_uncurry|].
      apply ex_RInt_const.
    }
  Qed.


  Lemma RealDecrTrial_μ_RInt {n m} {a b} :
    RInt (λ y : R, RealDecrTrial_μ y n m) a b =
    Iverson (uncurry le) (n, m) * (RealDecrTrial_μ0 b (m - n + 1) - RealDecrTrial_μ0 a (m - n + 1)).
  Proof.
    rewrite /RealDecrTrial_μ.
    rewrite /Iverson //=.
    case_decide.
    { rewrite Rmult_1_l -RInt_Rmult Rmult_1_l.
      rewrite /RealDecrTrial_μ0.
      replace (λ x : R, x ^ (m - n) / fact (m - n) - x ^ (m - n + 1) / fact (m - n + 1))
         with (λ x : R, x ^ (m - n) * / fact (m - n) - x ^ (m - n + 1) * / fact (m - n + 1)); last first.
      { apply functional_extensionality; intros ?; lra. }
      rewrite RInt_minus /minus//=/plus/opp//=; first last.
      { apply ex_RInt_mult; [|apply ex_RInt_const]. apply ex_RInt_pow. }
      { apply ex_RInt_mult; [|apply ex_RInt_const]. apply ex_RInt_pow. }
      rewrite /minus//=/plus/opp//=.
      have Hswizzle : forall x y z w, (x - y - (z - w)) = (x - z) - (y - w).
      { intros. repeat rewrite Rminus_def. rewrite Ropp_plus_distr Ropp_plus_distr. lra. }
      rewrite Hswizzle; clear Hswizzle.
      rewrite -Rminus_def.
      f_equal.
      { rewrite -RInt_Rmult'.
        rewrite RInt_pow.
        rewrite -Rdiv_minus_distr.
        rewrite Rdiv_def Rmult_assoc.
        rewrite -Rdiv_minus_distr Rdiv_def.
        f_equal.
        rewrite -Rinv_mult.
        f_equal.
        replace (m - n + 1)%nat with (S (m - n)) by lia.
        rewrite fact_simpl.
        rewrite mult_INR.
        done.
      }
      { rewrite -RInt_Rmult'.
        rewrite RInt_pow.
        rewrite -Rdiv_minus_distr.
        rewrite Rdiv_def Rmult_assoc.
        rewrite -Rdiv_minus_distr Rdiv_def.
        f_equal.
        rewrite -Rinv_mult.
        f_equal.
        replace (m - n + 1 + 1)%nat with (S (m - n + 1)) by lia.
        rewrite fact_simpl.
        rewrite mult_INR.
        done.
      }
    }
    { by rewrite Rmult_0_l -RInt_Rmult Rmult_0_l. }
  Qed.

  Theorem g_expectation {F N rx M} (Hrx : 0 <= rx <= 1)
    (Hbound : forall n, 0 <= F n <= M) : is_RInt (g F N rx) 0 1 (RealDecrTrial_CreditV F N rx).
  Proof.
    have Hex' : ∀ n, ex_RInt (λ x : R, Iverson (uncurry Rle) (x, rx) * RealDecrTrial_μ x (N + 1) n) 0 1.
    { intro n.
      apply ex_RInt_mult; [apply ex_RInt_Iverson_le_uncurry|].
      apply RealDecrTrial_μ_ex_RInt.
    }
    suffices H : RInt (g F N rx) 0 1 = RealDecrTrial_CreditV F N rx.
    { rewrite -H. eapply (RInt_correct (V := R_CompleteNormedModule)), g_ex_RInt.
      eapply Hbound. }
    rewrite /g.
    rewrite -RInt_add.
    3: { apply ex_RInt_mult; [apply ex_RInt_Iverson_ge_uncurry|]. apply ex_RInt_const. }
    2: { apply ex_RInt_mult; [apply ex_RInt_Iverson_le_uncurry|].
         eapply RealDecrTrial_CreditV_ex_RInt; done.
    }
    rewrite {1}/RealDecrTrial_CreditV.
    replace
      (λ x : R, Iverson (uncurry Rle) (x, rx) * SeriesC (λ n : nat, RealDecrTrial_μ x (N + 1) n * F n)) with
      (λ x : R, SeriesC (λ n : nat, Iverson (uncurry Rle) (x, rx) * RealDecrTrial_μ x (N + 1) n * F n)); last first.
    { apply functional_extensionality; intros ?.
      rewrite -SeriesC_scal_l.
      f_equal; apply functional_extensionality; intros ?.
      lra.
    }
    replace
      (RInt (λ x : R, SeriesC (λ n : nat, Iverson (uncurry Rle) (x, rx) * RealDecrTrial_μ x (N + 1) n * F n)) 0 1) with
      (SeriesC (λ n : nat, RInt (λ x : R, Iverson (uncurry Rle) (x, rx) * RealDecrTrial_μ x (N + 1) n * F n) 0 1)); last first.
    { (* Is it possible that Hex is needed here? *)
      admit. }
    rewrite (@RInt_Iverson_ge rx (fun x => F N) Hrx).
    rewrite RInt_const/scal//=/mult//=.
    replace ((1 - rx) * F N) with (SeriesC (fun n => Iverson (fun y => y = N) n * ((1 - rx) * F n))); last first.
    { rewrite (SeriesC_Iverson_singleton (F := fun z => (1 - rx) * F z) N); [lra|intuition]. }
    rewrite -SeriesC_plus.
    3: {
      apply (ex_seriesC_le _ (λ n : nat, if bool_decide (N = n) then ((1 - rx) * M) else 0));
        last apply ex_seriesC_singleton'.
      intro n.
      case_bool_decide.
      { rewrite Iverson_True; [|auto].
        rewrite Rmult_1_l.
        split.
        { apply Rmult_le_pos; [lra|]. apply Hbound. }
        { apply Rmult_le_compat_l; [lra|]. apply Hbound. }
      }
      { rewrite Iverson_False; [|auto]. lra. }
    }
    2: {
      apply (ex_seriesC_le _ (λ n : nat, RInt (λ x : R, (Iverson (uncurry Rle) (x, rx) * RealDecrTrial_μ x (N + 1) n) * M) 0 1)).
      { intro n.
        split.
        { apply RInt_ge_0; [lra|  |].
          { apply ex_RInt_Rmult'. apply Hex'.  }
          { intros ??.
            apply Rmult_le_pos; [|apply Hbound].
            apply Rmult_le_pos; [apply Iverson_nonneg|].
            apply RealDecrTrial_μnn.
            lra.
          }
        }
        { apply RInt_le; [lra | | | ].
          { apply ex_RInt_Rmult'. apply Hex'.  }
          { apply ex_RInt_Rmult'. apply Hex'.  }
          { intros x Hx.
            apply Rmult_le_compat_l; [|apply Hbound].
            apply Rmult_le_pos; [apply Iverson_nonneg|].
            apply RealDecrTrial_μnn.
            lra.
          }
        }
      }
      eapply ex_seriesC_ext.
      { intros n. symmetry. rewrite -RInt_Rmult'. done. }
        apply ex_seriesC_scal_r.
        (* Simplify, then telescoping *)
        admit.
      }
    rewrite /RealDecrTrial_CreditV.
    f_equal; apply functional_extensionality; intros n.
    replace
      (RInt (λ x : R, Iverson (uncurry Rle) (x, rx) * RealDecrTrial_μ x (N + 1) n * F n) 0 1) with
      (RInt (λ x : R, RealDecrTrial_μ x (N + 1) n * F n) 0 rx); last first.
    { rewrite -(@RInt_Iverson_le rx (fun x => RealDecrTrial_μ x (N + 1) n * F n) Hrx).
      f_equal. apply functional_extensionality; intros ?; lra. }
    rewrite /Iverson//=.
    case_decide; simpl in H; last first.
    { rewrite Rmult_0_l Rplus_0_r.
      rewrite /RealDecrTrial_μ.
      rewrite {2}/Iverson//=.
      replace (RInt (λ x : R, Iverson (uncurry le) ((N + 1)%nat, n) * RealDecrTrial_μ0 x (n - (N + 1)) * F n) 0 rx)
        with (RInt (λ x : R, Iverson (uncurry le) ((N + 1)%nat, n) * (RealDecrTrial_μ0 x (n - (N + 1)) * F n)) 0 rx);
        last first.
      { f_equal. apply functional_extensionality; intros ?; lra. }
      rewrite -RInt_Rmult.
      case_decide.
      { rewrite Rmult_1_l.
        rewrite Iverson_True; [|simpl; lia].
        rewrite Rmult_1_l.
        rewrite -RInt_Rmult'; f_equal.
        rewrite /RealDecrTrial_μ0.
        (* Compute *)
        replace (λ x : R, x ^ (n - (N + 1)) / fact (n - (N + 1)) - x ^ (n - (N + 1) + 1) / fact (n - (N + 1) + 1))
           with (λ x : R, x ^ (n - (N + 1)) * / fact (n - (N + 1)) - x ^ (n - (N + 1) + 1) * / fact (n - (N + 1) + 1));
          last first.
        { apply functional_extensionality. intros x. lra. }
        rewrite RInt_minus.
        2: {
          apply ex_RInt_mult; [|apply ex_RInt_const].
          apply ex_RInt_pow.
        }
        2: {
          apply ex_RInt_mult; [|apply ex_RInt_const].
          apply ex_RInt_pow.
        }
        rewrite /minus//=/plus/opp//=.
        rewrite -Rminus_def.
        rewrite -RInt_Rmult'.
        rewrite -RInt_Rmult'.
        f_equal.
        { rewrite RInt_pow.
          rewrite pow_i; [|lia].
          rewrite Rdiv_0_l.
          rewrite Rdiv_def.
          rewrite Rdiv_def.
          rewrite Rminus_0_r.
          rewrite Rmult_assoc.
          f_equal; [f_equal; lia|].
          rewrite -Rinv_mult; f_equal.
          replace (n - N)%nat with (S (n - (N + 1)))%nat by lia.
          rewrite fact_simpl.
          rewrite mult_INR; f_equal.
          f_equal. lia.
        }
        { rewrite RInt_pow.
          rewrite pow_i; [|lia].
          rewrite Rdiv_0_l.
          rewrite Rdiv_def.
          rewrite Rdiv_def.
          rewrite Rminus_0_r.
          rewrite Rmult_assoc.
          f_equal; [f_equal; lia|].
          rewrite -Rinv_mult; f_equal.
          replace (n - N + 1)%nat with (S (n - N))%nat by lia.
          rewrite fact_simpl.
          rewrite mult_INR; f_equal.
          { f_equal. lia. }
          { f_equal. f_equal. lia. }
        }
      }
      { rewrite Rmult_0_l Rmult_0_l.
        rewrite Iverson_False; [|simpl; lia].
        lra.
      }
    }
    { rewrite Rmult_1_l.
      rewrite -RInt_Rmult'.
      rewrite -Rmult_plus_distr_r; f_equal.
      rewrite H.
      rewrite /RealDecrTrial_μ.
      rewrite -RInt_Rmult.
      rewrite Iverson_False; [|simpl; lia].
      rewrite Iverson_True; [|simpl; lia].
      rewrite Rmult_0_l Rplus_0_l.
      rewrite Rmult_1_l.
      rewrite /RealDecrTrial_μ0.
      rewrite Nat.sub_diag pow_O //=.
      lra.
    }
  Admitted.


End credits.


Section trial.
  Context `{!erisGS Σ}.

  (* Tail-recursive geometric trial, which allocates new lazy reals in the loop. *)
  Definition lazyDecrR : val :=
    rec: "trial" "N" "x" :=
      let: "y" := init #() in
      if: (cmp "y" "x" = #(-1)) then
        "trial" ("N" + #1) "y" (* y < x *)
      else
        "N".

  Lemma wp_lazyDecrR_gen {M} (F : nat → R) (Hnn : ∀ n, 0 <= F n <= M) E :
    ⊢ ∀ N x rx, lazy_real x rx ∗ ⌜0 <= rx <= 1 ⌝ ∗ ↯ (RealDecrTrial_CreditV F N rx) -∗
                WP lazyDecrR #N x @ E {{ z, ∃ n : nat, ⌜z = #n⌝ ∗ ↯ (F n) ∗ lazy_real x rx }}.
  Proof.
    iLöb as "IH".
    rewrite {2}/lazyDecrR.
    iIntros (N x rx) "(Hx & % & Hε)".
    do 3 wp_pure.
    wp_apply wp_init; first done.
    iIntros (y) "Hv".
    iApply (wp_lazy_real_presample_adv_comp _ _ y _ (RealDecrTrial_CreditV F N rx) (g F N rx)); auto.
    { intros ??. apply g_nonneg; auto. apply Hnn. }
    { eapply g_expectation; auto. }
    iSplitL "Hv"; first done.
    iSplitL "Hε"; first done.
    iIntros (ry) "(% & Hε & Hy)".
    wp_pures.
    wp_apply (wp_cmp with "[Hx Hy]"); first iFrame.
    iIntros (vcmp) "(Hy & Hx & [[%Hcmp %Hie]|[%Hcmp %Hie]])".
    - rewrite Hcmp//=.
      do 3 wp_pure.
      rewrite /lazyDecrR.
      replace ((Z.add (Z.of_nat N) 1)) with (Z.of_nat (Nat.add N 1)) by lia.
      iSpecialize ("IH" $! (N+1)%nat y ry with "[Hy Hε]").
      { iFrame.
        iSplitR; first done.
        rewrite /g.
        iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply CreditV_nonneg; auto]. apply Hnn. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        rewrite Iverson_True; [by rewrite Rmult_1_l | rewrite /uncurry//=].
      }
      iFrame.
      iApply pgl_wp_mono; last done.
      iIntros (?) "(%z & ? & ? & ?)"; iExists _; auto.
    - rewrite Hcmp//=.
      do 2 wp_pure.
      iModIntro.
      iExists N; iSplitR; first by iPureIntro.
      iSplitR "Hx"; last done.
      rewrite /g.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply CreditV_nonneg; auto ]. apply Hnn. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      rewrite Iverson_True; [by rewrite Rmult_1_l | rewrite /uncurry//=; lra].
  Qed.


End trial.
