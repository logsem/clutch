From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import Coquelicot.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real indicators real_decr_trial.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.
   Definition BNEHalf_μ (b : bool) : R :=
     Iverson is_true b * exp (-1/2)%R +
     Iverson (not ∘ is_true) b * (1 - exp (-1/2)%R).

End pmf.

Section credits.
  Import Hierarchy.

  Definition BNEHalf_CreditV (F : bool → R) : R :=
    (F true) * BNEHalf_μ true + (F false) * BNEHalf_μ false.

  Lemma BNEHalf_μ_nn {b} : 0 <= BNEHalf_μ b.
  Proof.
    rewrite /BNEHalf_μ.
    apply Rplus_le_le_0_compat.
    { apply Rmult_le_pos; [apply Iverson_nonneg| auto ]. apply Rexp_nn. }
    { apply Rmult_le_pos; [apply Iverson_nonneg| auto ].
      apply error_credits.Rle_0_le_minus.
      have ? := @Rexp_range (Rdiv (-1) 2).
      lra.
    }
  Qed.

  Lemma BNEHalf_CreditV_nn {F} (Hnn : ∀ r, 0 <= F r) : 0 <= BNEHalf_CreditV F.
  Proof.
    rewrite /BNEHalf_CreditV.
    apply Rplus_le_le_0_compat.
    { apply Rmult_le_pos; auto. apply BNEHalf_μ_nn. }
    { apply Rmult_le_pos; auto. apply BNEHalf_μ_nn. }
  Qed.

  Local Definition LiftF (F : bool -> R) : nat -> R :=
    fun n => F (Z.eqb (n `rem` 2)%Z 1%Z).

  Local Definition g (F : bool → R) : R → R := fun r =>
    Iverson (fun x => Rle x 0.5) r * RealDecrTrial_CreditV (LiftF F) 0 r +
    Iverson (fun x  => not (Rle x 0.5)) r * F (true).

  Local Lemma g_nn {F r} (Hnn : ∀ r, 0 <= F r) (Hr : 0 <= r <= 1) : 0 <= g F r.
  Proof.
    rewrite /g.
    apply Rplus_le_le_0_compat.
    { apply Rmult_le_pos; [apply Iverson_nonneg| auto ].
      apply CreditV_nonneg; auto.
      intros ?; rewrite /LiftF//=.
    }
    { apply Rmult_le_pos; [apply Iverson_nonneg| auto ]. }
  Qed.

  Local Lemma ex_RInt_RealDecrTrial_CreditV {F} (Hf : forall n, 0 <= F n) : ex_RInt (RealDecrTrial_CreditV (LiftF F) 0) 0 1.
  Proof.
    apply (RealDecrTrial_CreditV_ex_RInt (F := (LiftF F)) (M := Rmax (F false) (F true))).
    intros n.
    split.
    { rewrite /LiftF; apply Hf. }
    { rewrite /LiftF.
      destruct ((n `rem` 2 =? 1)%Z).
      { apply Rmax_r. }
      { apply Rmax_l. }
    }
  Qed.

  Local Lemma g_ex_RInt {F} (Hf : forall b, 0 <= F b) : ex_RInt (g F) 0 1.
  Proof.
    rewrite /g.
    apply ex_RInt_add.
    { apply ex_RInt_mult.
      { apply ex_RInt_Iverson_le'. }
      { apply ex_RInt_RealDecrTrial_CreditV. done. }
    }
    { apply ex_RInt_mult.
      { apply ex_RInt_Iverson_nle'. }
      { apply ex_RInt_const. }
    }
  Qed.

  Local Lemma g_expectation {F M} (HF : ∀ x, 0 <= F x <= M) : RInt (g F) 0 1 = BNEHalf_CreditV F.
  Proof.
    rewrite /g.
    rewrite -RInt_add.
    3: {
      apply ex_RInt_mult; [apply ex_RInt_Iverson_nle'|].
      apply ex_RInt_const.
    }
    2: {
      apply ex_RInt_mult; [apply ex_RInt_Iverson_le'|].
      apply ex_RInt_RealDecrTrial_CreditV.
      apply HF.
    }
    rewrite RInt_Iverson_le; [|lra|].
    2: { eapply (ex_RInt_Chasles_1 (V := R_CompleteNormedModule)).
         2: { eapply ex_RInt_RealDecrTrial_CreditV. apply HF. }
         OK.
    }
    rewrite RInt_Iverson_ge'; [|lra| apply ex_RInt_const].
    rewrite RInt_const/scal//=/mult//=.
    rewrite /RealDecrTrial_CreditV.
    replace (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * LiftF F n)) 0 0.5)
       with (SeriesC (λ n : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n * LiftF F n) 0 0.5)); last first.
    { (* Deploy the Foob *) admit. }
    replace (λ n : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n * LiftF F n) 0 0.5)
       with (λ n : nat, LiftF F n * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5); last first.
    { apply functional_extensionality; intros n. rewrite -RInt_Rmult'.
      2: { apply RealDecrTrial_μ_ex_RInt. }
      by rewrite Rmult_comm /LiftF. }
    rewrite /LiftF.
    replace (SeriesC (λ n : nat, F (n `rem` 2 =? 1)%Z * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5))
       with ((SeriesC (λ n : nat, Iverson Zeven  n * F (n `rem` 2 =? 1)%Z * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5)) +
             (SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * F (n `rem` 2 =? 1)%Z * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5)));
        last first.
    { rewrite -SeriesC_plus.
      (* TODO: Next two cases are redundant and not very expedient *)
      3: {
        apply (ex_seriesC_le _ (fun n => M * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5)).
        { intros n.
          split.
          { apply Rmult_le_pos.
            { apply Rmult_le_pos; [apply Iverson_nonneg|apply HF]. }
            { apply RInt_ge_0; [lra | apply RealDecrTrial_μ_ex_RInt | ].
              intros x Hx. apply RealDecrTrial_μnn. lra. }
          }
          { apply Rmult_le_compat.
            { apply Rmult_le_pos; [apply Iverson_nonneg|apply HF]. }
            { apply RInt_ge_0; [lra | apply RealDecrTrial_μ_ex_RInt | ].
              intros x Hx. apply RealDecrTrial_μnn. lra. }
            { rewrite -(Rmult_1_l M).
              apply Rmult_le_compat.
              { apply Iverson_nonneg. }
              { apply HF. }
              { apply Iverson_le_1. }
              { apply HF. }
            }
            { lra. }
          }
        }
        { apply ex_seriesC_scal_l.
          eapply ex_seriesC_ext.
          { intro n; symmetry. eapply RealDecrTrial_μ_RInt. }
          have L : forall n, 0 <= RealDecrTrial_μ0 0.5 (n - 0 + 1) - RealDecrTrial_μ0 0 (n - 0 + 1).
          { intro n.
            rewrite Nat.sub_0_r.
            rewrite /RealDecrTrial_μ0.
            rewrite pow_i; [|lia].
            rewrite pow_i; [|lia].
            rewrite Rdiv_0_l.
            rewrite Rdiv_0_l.
            rewrite Rminus_0_r.
            rewrite Rminus_0_r.
            apply Rle_0_le_minus.
            rewrite Rdiv_def.
            rewrite Rdiv_def.
            apply Rmult_le_compat.
            { apply pow_le. lra. }
            { rewrite -(Rmult_1_l (/ fact (n + 1 + 1))).
              apply Rle_mult_inv_pos; try lra.
              apply INR_fact_lt_0. }
            { rewrite pow_add.
              rewrite -{2}(Rmult_1_r (0.5 ^ _)).
              apply Rmult_le_compat_l.
              { apply pow_le. lra. }
              { rewrite pow_1. lra. }
            }
            { apply Rcomplements.Rinv_le_contravar.
              { apply INR_fact_lt_0. }
              { replace (n + 1 + 1)%nat with (S (n + 1))%nat by lia.
                rewrite fact_simpl.
                rewrite -(Rmult_1_l (fact (n + 1))).
                rewrite -INR_1.
                rewrite -mult_INR.
                apply le_INR.
                lia.
              }
            }
          }
          apply (ex_seriesC_le _ (fun n => (RealDecrTrial_μ0 0.5 (n - 0 + 1) - RealDecrTrial_μ0 0 (n - 0 + 1)))).
          { intro n.
            split.
            { apply Rmult_le_pos; [apply Iverson_nonneg|apply L]. }
            { rewrite -{2}(Rmult_1_l (RealDecrTrial_μ0 0.5 (n - 0 + 1) - RealDecrTrial_μ0 0 (n - 0 + 1))).
              apply Rmult_le_compat.
              { apply Iverson_nonneg. }
              { apply L. }
              { apply Iverson_le_1. }
              { done. }
            }
          }
          replace (λ n : nat, RealDecrTrial_μ0 0.5 (n - 0 + 1) - RealDecrTrial_μ0 0 (n - 0 + 1))
            with  (λ n : nat, RealDecrTrial_μ0 0.5 (n + 1)); last first.
          { apply functional_extensionality; intro n.
            rewrite -(Rminus_0_r (RealDecrTrial_μ0 0.5 (n + 1))).
            f_equal.
            { by rewrite Nat.sub_0_r. }
            { rewrite Nat.sub_0_r.
              rewrite /RealDecrTrial_μ0.
              rewrite pow_i; [|lia].
              rewrite pow_i; [|lia].
              rewrite Rdiv_0_l.
              rewrite Rdiv_0_l.
              by rewrite Rminus_0_r.
            }
          }
          apply RealDecrTrial_μ0_ex_seriesC. OK.
        }
      }
      2: {
        apply (ex_seriesC_le _ (fun n => M * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5)).
        { intros n.
          split.
          { apply Rmult_le_pos.
            { apply Rmult_le_pos; [apply Iverson_nonneg|apply HF]. }
            { apply RInt_ge_0; [lra | apply RealDecrTrial_μ_ex_RInt | ].
              intros x Hx. apply RealDecrTrial_μnn. lra. }
          }
          { apply Rmult_le_compat.
            { apply Rmult_le_pos; [apply Iverson_nonneg|apply HF]. }
            { apply RInt_ge_0; [lra | apply RealDecrTrial_μ_ex_RInt | ].
              intros x Hx. apply RealDecrTrial_μnn. lra. }
            { rewrite -(Rmult_1_l M).
              apply Rmult_le_compat.
              { apply Iverson_nonneg. }
              { apply HF. }
              { apply Iverson_le_1. }
              { apply HF. }
            }
            { lra. }
          }
        }
        { apply ex_seriesC_scal_l.
          eapply ex_seriesC_ext.
          { intro n; symmetry. eapply RealDecrTrial_μ_RInt. }
          have L : forall n, 0 <= RealDecrTrial_μ0 0.5 (n - 0 + 1) - RealDecrTrial_μ0 0 (n - 0 + 1).
          { intro n.
            rewrite Nat.sub_0_r.
            rewrite /RealDecrTrial_μ0.
            rewrite pow_i; [|lia].
            rewrite pow_i; [|lia].
            rewrite Rdiv_0_l.
            rewrite Rdiv_0_l.
            rewrite Rminus_0_r.
            rewrite Rminus_0_r.
            apply Rle_0_le_minus.
            rewrite Rdiv_def.
            rewrite Rdiv_def.
            apply Rmult_le_compat.
            { apply pow_le. lra. }
            { rewrite -(Rmult_1_l (/ fact (n + 1 + 1))).
              apply Rle_mult_inv_pos; try lra.
              apply INR_fact_lt_0. }
            { rewrite pow_add.
              rewrite -{2}(Rmult_1_r (0.5 ^ _)).
              apply Rmult_le_compat_l.
              { apply pow_le. lra. }
              { rewrite pow_1. lra. }
            }
            { apply Rcomplements.Rinv_le_contravar.
              { apply INR_fact_lt_0. }
              { replace (n + 1 + 1)%nat with (S (n + 1))%nat by lia.
                rewrite fact_simpl.
                rewrite -(Rmult_1_l (fact (n + 1))).
                rewrite -INR_1.
                rewrite -mult_INR.
                apply le_INR.
                lia.
              }
            }
          }
          apply (ex_seriesC_le _ (fun n => (RealDecrTrial_μ0 0.5 (n - 0 + 1) - RealDecrTrial_μ0 0 (n - 0 + 1)))).
          { intro n.
            split.
            { apply Rmult_le_pos; [apply Iverson_nonneg|apply L]. }
            { rewrite -{2}(Rmult_1_l (RealDecrTrial_μ0 0.5 (n - 0 + 1) - RealDecrTrial_μ0 0 (n - 0 + 1))).
              apply Rmult_le_compat.
              { apply Iverson_nonneg. }
              { apply L. }
              { apply Iverson_le_1. }
              { done. }
            }
          }
          replace (λ n : nat, RealDecrTrial_μ0 0.5 (n - 0 + 1) - RealDecrTrial_μ0 0 (n - 0 + 1))
            with  (λ n : nat, RealDecrTrial_μ0 0.5 (n + 1)); last first.
          { apply functional_extensionality; intro n.
            rewrite -(Rminus_0_r (RealDecrTrial_μ0 0.5 (n + 1))).
            f_equal.
            { by rewrite Nat.sub_0_r. }
            { rewrite Nat.sub_0_r.
              rewrite /RealDecrTrial_μ0.
              rewrite pow_i; [|lia].
              rewrite pow_i; [|lia].
              rewrite Rdiv_0_l.
              rewrite Rdiv_0_l.
              by rewrite Rminus_0_r.
            }
          }
          apply (RealDecrTrial_μ0_ex_seriesC).
          OK.
        }
      }
      f_equal; apply functional_extensionality; intro n.
      rewrite Rmult_assoc Rmult_assoc.
      rewrite -Rmult_plus_distr_r.
      rewrite -{2}(Rmult_1_l (_* RInt _ _ _)).
      f_equal.
      apply Iverson_add_neg.
    }
    replace (SeriesC (λ n : nat, Iverson Zeven n * F (n `rem` 2 =? 1)%Z * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5))
       with (SeriesC (λ n : nat, (Iverson Zeven n * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5)) * F false );
       last first.
    { rewrite -SeriesC_scal_r.
      f_equal; apply functional_extensionality; intro n.
      rewrite /Iverson//=.
      case_decide; [|lra].
      rewrite Rmult_1_l Rmult_1_l Rmult_comm.
      f_equal; f_equal; symmetry.
      apply Zeven_bool_iff in H.
      eapply (ssrbool.introF (Z.eqb_spec _ _)).
      rewrite Zeven_mod in H.
      apply Zeq_bool_eq in H.
      apply (Z.rem_mod_eq_0 n 2 ) in H; [rewrite H; lia|lia].
    }
    replace (SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * F (n `rem` 2 =? 1)%Z * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5))
       with (SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5) * F true);
      last first.
    { rewrite -SeriesC_scal_r.
      f_equal; apply functional_extensionality; intro n.
      rewrite /Iverson//=.
      case_decide; [|lra].
      rewrite Rmult_1_l Rmult_1_l Rmult_comm.
      f_equal; f_equal; symmetry.
      eapply (ssrbool.introT (Z.eqb_spec _ _)).
      destruct (Zeven_odd_dec n); [intuition|].
      destruct (Zodd_ex _ z) as [m Hm].
      rewrite Hm.
      rewrite Z.add_rem; try lia.
      rewrite Z.mul_comm.
      rewrite Z.rem_mul; try lia.
      rewrite Zplus_0_l //=.
    }
    have HIntegral (n : nat) : RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5 = RealDecrTrial_μ0 (0.5) (n+1)%nat.
    { rewrite RealDecrTrial_μ_RInt.
      rewrite Iverson_True; [|simpl; lia].
      rewrite Rmult_1_l.
      rewrite Nat.sub_0_r.
      replace (RealDecrTrial_μ0 0 (n + 1)) with 0;  first lra.
      rewrite /RealDecrTrial_μ0.
      rewrite /RealDecrTrial_μ0.
      rewrite pow_i; [|lia].
      rewrite pow_i; [|lia].
      rewrite Rdiv_0_l.
      rewrite Rdiv_0_l.
      by rewrite Rminus_0_r.
    }
    replace (λ n : nat, Iverson Zeven n * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5)
       with (λ n : nat, Iverson Zeven n * RealDecrTrial_μ0 0.5 (n+1)%nat); last first.
    { f_equal; apply functional_extensionality; intro n; by rewrite HIntegral. }
    replace (λ n : nat, Iverson (not ∘ Zeven) n * RInt (λ x : R, RealDecrTrial_μ x 0 n) 0 0.5)
       with (λ n : nat, Iverson (not ∘ Zeven) n * RealDecrTrial_μ0 0.5 (n+1)%nat); last first.
    { f_equal; apply functional_extensionality; intro n; by rewrite HIntegral. }
    rewrite Rplus_assoc.
    rewrite -Rmult_plus_distr_r.
    rewrite Rplus_comm (Rmult_comm _ (F false)) (Rmult_comm _ (F true)).
    rewrite /BNEHalf_CreditV.
    f_equal; f_equal.
    { rewrite /RealDecrTrial_μ0.
      replace (λ n : nat, Iverson (not ∘ Zeven) n * (0.5 ^ (n + 1) / fact (n + 1) - 0.5 ^ (n + 1 + 1) / fact (n + 1 + 1)))
        with ((λ n : nat, Iverson Zeven n * ((- 0.5) ^ (n) / fact (n) + (- 0.5) ^ (n + 1 ) / fact (n + 1))) ∘ S); last first.
      { funext; intro n. simpl.
        replace (Iverson Zeven (S n)) with (Iverson (not ∘ Zeven) n ); last first.
        { rewrite /Iverson; case_decide; case_decide; OK.
          { exfalso.
            rewrite /comp//= in H.
            destruct (Zeven_odd_dec n); OK.
            apply Zeven_Sn in z.
            replace (Z.succ n) with (Z.of_nat (S n)) in z by OK.
            OK.
          }
          { exfalso.
            rewrite /comp//= in H.
            apply NNP_P in H.
            apply Zodd_Sn in H.
            apply (Zeven_not_Zodd _ H0).
            by replace (Z.of_nat (S n)) with (Z.succ n) by OK.
          }
        }
        rewrite /Iverson; case_decide; [|OK].
        repeat rewrite Rmult_1_l.
        rewrite Rminus_def.
        f_equal.
        { f_equal; OK.
          { rewrite tech_pow_Rmult; OK.
            replace (n + 1)%nat with (S n); OK.
            rewrite -even_pow_neg; last first.
            { replace (Z.of_nat (S n)) with (Z.succ n) by OK.
              apply Zeven_Sn.
              rewrite /compose//= in H.
              destruct (Zeven_odd_dec n); OK.
            }
            f_equal. OK.
          }
          { replace (n + 1)%nat with (S n)%nat by OK. OK. }
        }
        repeat rewrite Rdiv_def.
        rewrite Ropp_mult_distr_l.
        f_equal.
        { replace (n + 1 + 1)%nat with (S (S n)) by OK.
          replace (n + 1)%nat with (S n) by OK.
          simpl.
          rewrite Ropp_mult_distr_l.
          f_equal; OK.
          replace ((-0.5) ^ n) with (-((0.5) ^ n)); OK.
          rewrite -(@not_even_pow_neg (0.5)); OK.
          f_equal; OK.
        }
        f_equal.
        { replace (n + 1 + 1)%nat with (S (n + 1)%nat) by OK. OK. }
      }
      rewrite SeriesC_nat_shift_rev.
      2: { apply ex_seriesC_nat, (@Hexp_ex_even (-0.5)). }
      rewrite ExpSeriesEven.
      rewrite Iverson_True; OK.
      rewrite Rmult_1_l pow_O /fact //=.
      rewrite /BNEHalf_μ//=.
      rewrite Iverson_True; OK.
      rewrite Iverson_False; OK.
      replace ((-1 / 2)) with (-0.5) by OK.
      OK.
    }
    { rewrite /RealDecrTrial_μ0.
      replace (λ n : nat, Iverson Zeven n * (0.5 ^ (n + 1) / fact (n + 1) - 0.5 ^ (n + 1 + 1) / fact (n + 1 + 1)))
        with ((λ n : nat, (-1) * (Iverson (not ∘ Zeven) n * ((-0.5) ^ (n) / fact (n) + (-0.5) ^ (n + 1) / fact (n + 1)))) ∘ S); last first.
      { funext; intro n. simpl.
        replace (Iverson (not ∘ Zeven) (S n)) with (Iverson Zeven n); last first.
        { rewrite /Iverson; case_decide; case_decide; OK.
          { exfalso.
            have X : (not ∘ Zeven) (S n).
            { intro HK.
              apply Zodd_Sn in H.
              apply Zodd_not_Zeven in H.
              replace (Z.of_nat (S n)) with (Z.succ n) in HK by OK.
              OK.
            }
            OK.
          }
          { exfalso.
            have X : Zeven (S n).
            { replace (Z.of_nat (S n)) with (Z.succ n) by OK.
              apply Zeven_Sn.
              destruct (Zeven_odd_dec n); OK.
            }
            OK.
          }
        }
        rewrite /Iverson; case_decide; [|OK].
        repeat rewrite Rmult_1_l.
        rewrite Rminus_def.
        rewrite Rmult_plus_distr_l.
        f_equal.
        { do 2 rewrite -Rmult_assoc.
          rewrite Rdiv_def.
          f_equal; OK.
          { replace (n + 1)%nat with (S n) by OK.
            simpl.
            rewrite -(@even_pow_neg 0.5); OK.
            replace (- (0.5)) with (-0.5); OK.
          }
          { f_equal. replace (n + 1)%nat with (S n); OK. }
        }
        repeat rewrite Rdiv_def.
        rewrite Ropp_mult_distr_l.
        rewrite -Rmult_assoc.
        f_equal.
        { replace (n + 1 + 1)%nat with (S (S n)) by OK.
          replace (n + 1)%nat with (S n) by OK.
          simpl.
          rewrite Ropp_mult_distr_l.
          rewrite -(@even_pow_neg 0.5); OK.
          replace (- (0.5)) with (-0.5); OK.
        }
        f_equal.
        { replace (n + 1 + 1)%nat with (S (n + 1)%nat) by OK. OK. }
      }
      rewrite SeriesC_nat_shift_rev.
      2: { apply ex_seriesC_nat. apply ex_seriesC_scal_l. apply (@Hexp_ex_odd (-0.5)). }
      rewrite SeriesC_scal_l.
      rewrite ExpSeriesOdd.
      rewrite /BNEHalf_μ//=.
      rewrite Iverson_False; last first.
      { rewrite /comp//=. intuition. }
      rewrite Rmult_0_l Rmult_0_r Ropp_0 Rplus_0_l.
      rewrite Iverson_False; OK.
      rewrite Rmult_0_l Rplus_0_l.
      rewrite Iverson_True; OK.
      replace ((-1 / 2)) with (-0.5) by OK.
      OK.
    }
  Admitted.

End credits.


Section program.
  Context `{!erisGS Σ}.


  Import Hierarchy.

  (* A lazy real is less than or equal to one half, ie. the first bit is zero. *)
  Definition LeHalf : val :=
    λ: "x",
      let: "c1n" := get_chunk (Fst "x") (Snd "x") in
      let: "res" := cmpZ (Fst "c1n") #0 in
      (* First bit is 0: res is -1, number is at most 1/2, return #true
         First bit is 1: res is 0, number is at least 1/2, return #false *)
      "res" = #0.

  Definition LeHalf_spec (r : R) : bool := bool_decide (Rle r (0.5)%R).


  Theorem wp_LeHalf E v r :
    ⌜ r ≠ 0.5 ⌝ -∗ lazy_real v r -∗ WP LeHalf v @ E {{ vb, ⌜vb = #(LeHalf_spec r) ⌝ ∗ lazy_real v r }}.
  Proof.
    iIntros "%Hhalf Hr".
    iDestruct "Hr" as (l α f -> ->) "Hr".
    iDestruct "Hr" as (zs f') "(%Hf & Hc & Hα)".
    rewrite /LeHalf /get_chunk; wp_pures.
    destruct zs as [|z zs].
    { rewrite /chunk_list//=.
      wp_apply (wp_load with "Hc").
      iIntros "Hc".
      wp_pures.
      wp_apply (wp_rand_infinite_tape with "Hα").
      iIntros "Hα".
      wp_pures.
      wp_apply (wp_alloc with "[//]").
      iIntros (ℓ) "Hℓ".
      wp_pures.
      wp_apply (wp_store with "[Hc]"); first iFrame.
      iIntros "Hc'".
      wp_pures.
      wp_apply (wp_cmpZ with "[//]").
      iIntros "_".
      wp_pures.
      iModIntro.
      iSplit.
      { iPureIntro; simpl; f_equal.
        rewrite Hf /append_bin_seq /LeHalf_spec //=.
        replace (λ n : nat, f' n) with f' by done.
        destruct (LemDisj (f' 0%nat)).
        { rewrite H.
          simpl.
          case_bool_decide; OK.
          exfalso.
          apply H0.
          apply seq_bin_to_R_leading0.
          rewrite H.
          done.
        }
        { rewrite H.
          simpl.
          case_bool_decide; OK.
          exfalso.
          rewrite Hf //= in Hhalf.
          apply Hhalf.
          apply Rle_antisym; OK.
          apply seq_bin_to_R_leading1.
          rewrite H. done.
        }
      }
      iExists l, α, f.
      iSplitR; first done.
      iSplitR; first done.

      iExists (cons (f' 0%nat) []), (λ n : nat, f' (S n)).
      iFrame.
      iPureIntro.
      rewrite Hf /append_bin_seq//=.
      apply functional_extensionality; by intros [|].
    }
    { rewrite /chunk_list.
      iDestruct "Hc" as (l') "(Hc & Hlist)".
      wp_apply (wp_load with "Hc").
      iIntros "Hc".
      wp_pures.
      wp_apply (wp_cmpZ with "[//]").
      iIntros "_".
      wp_pures.
      iModIntro.
      iSplit.
      { iPureIntro; simpl; f_equal.
        destruct (LemDisj z).
        { rewrite H. simpl.
          rewrite /LeHalf_spec.
          case_bool_decide; OK.
          exfalso; apply H0.
          apply seq_bin_to_R_leading0.
          rewrite Hf.
          simpl.
          by rewrite H. }
        { rewrite H; simpl.
          rewrite /LeHalf_spec.
          case_bool_decide; OK.
          exfalso.
          rewrite Hf in Hhalf.
          apply Hhalf.
          apply Rle_antisym.
          { rewrite -Hf. done. }
          { apply seq_bin_to_R_leading1. simpl.  rewrite H. done. }
        }
      }
      { iExists l, α, f.
        iSplitR; first done.
        iSplitR; first done.
        unfold chunk_and_tape_seq.
        iExists (z::zs), f'.
        iFrame.
        done.
    }
  }
  Qed.

  Definition BNEHalf : val :=
    λ: "_",
    let: "x" := init #() in
    if: LeHalf "x" then
      let: "y" := lazyDecrR #Nat.zero "x" in
      ("y" `rem` #2%Z = #1%Z)
    else
      #true.

  Theorem wp_BNEHalf E {F M} (Hnn : ∀ r, 0 <= F r <= M) (* (Hex : ex_seriesC (LiftF F)) *) :
    ↯(BNEHalf_CreditV F) -∗ WP BNEHalf #() @ E {{ vb , ∃ b : bool, ⌜vb = #b ⌝ ∗ ↯(F b) }}.
  Proof.
    iIntros "Hε".
    unfold BNEHalf.
    wp_pure.
    wp_apply wp_init; first done.
    iIntros (x) "Hx".


    iApply (wp_lazy_real_presample_adv_comp _ _ x _ (BNEHalf_CreditV F) (poke (g F) 0.5 1)); auto.
    { intros ??.
      rewrite /poke; case_decide; try lra.
      apply g_nn; auto. apply Hnn. }
    { suffices H : @RInt R_CompleteNormedModule (poke (g F) 0.5 1) 0 1 = BNEHalf_CreditV F.
      { rewrite -H.
        apply (RInt_correct (V := R_CompleteNormedModule)).
        apply (ex_RInt_poke); OK.
        apply g_ex_RInt.
        apply Hnn.
      }
      rewrite -RInt_poke; OK.
      { eapply g_expectation; eapply Hnn. }
      { apply g_ex_RInt, Hnn. }
    }

    iFrame.
    iIntros (r) "(%Hrange & Hε & Hx)".

    rewrite /poke.
    case_decide.
    { iApply (wp_ec_spend _ _ _ (nnreal_one) with "[Hε]"); OK. }

    wp_pures.
    wp_bind (LeHalf _).
    iApply (pgl_wp_mono_frame with "[Hx] Hε"); last first.
    { iApply (wp_LeHalf with "[] [Hx]"); iFrame.
      iPureIntro.
      apply H.
    }

    rewrite /LeHalf_spec//=.
    iIntros (v) "(Hε & -> & Hr)".
    case_bool_decide.
    { wp_pures.
      rewrite /g//=.
      iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply CreditV_nonneg; auto]. intro n. apply Hnn. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      wp_bind (lazyDecrR _ _).
      iApply (pgl_wp_mono with "[Hr Hε]"); last first.
      { iApply (wp_lazyDecrR_gen (LiftF F)); first rewrite /LiftF//=.
        iFrame.
        iSplitR; first auto.
        rewrite Iverson_True; auto.
        rewrite Rmult_1_l.
        iFrame.
      }
      rewrite /LiftF//=.
      iIntros (vb) "(%n & -> & Hε & Hx)".
      wp_pures.
      iModIntro.
      iExists _; iFrame.
      iPureIntro.
      f_equal.
      destruct (n `rem` 2 =? 1)%Z as [|] eqn:Hb.
      { by rewrite (ssrbool.elimT (Z.eqb_spec _ _) Hb) //=. }
      { have Hb' := (ssrbool.elimF (Z.eqb_spec _ _) Hb).
        case_bool_decide; auto.
        exfalso.
        apply Hb'.
        inversion H1.
        done.
      }
    }
    { wp_pures.
      iModIntro.
      iExists true.
      iSplitR; first done.
      rewrite /g.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply CreditV_nonneg; auto ]. intro n. apply Hnn. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      rewrite Iverson_True; auto.
      rewrite Rmult_1_l.
      iFrame.
    }
  Qed.

End program.
