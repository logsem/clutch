From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real real_decr_trial.
From clutch.eris.examples Require Import math.
Set Default Proof Using "Type*".
#[local] Open Scope R.


Section pmf.
  Import Hierarchy.

  Lemma RealDecrTrial_μ0_PCts {n} : PCts (λ y : R, RealDecrTrial_μ0 y n) 0 1.
  Proof.
    rewrite /RealDecrTrial_μ0.
    apply PCts_cts.
    intros ??.
    apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
    by auto_derive.
  Qed.

  Lemma RealDecrTrial_μ_PCts {n} : PCts (λ y : R, RealDecrTrial_μ y 0 n) 0 1.
  Proof.
    rewrite /RealDecrTrial_μ.
    apply PCts_mult.
    { apply PCts_cts.
      intros ??.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
    apply RealDecrTrial_μ0_PCts.
  Qed.

  (** PMF of the negative exponential distribution *)
  Local Definition NegExp_ρ0 (k : nat) (x : R) : R :=
    Iverson (Icc 0 1) x * exp (-(x + k))%R.

  (** Shift the distribution to the right by (L : Nat) *)
  Local Definition NegExp_ρ (L : nat) (k : nat) (x : R) : R :=
    Iverson (le L) k * NegExp_ρ0 (k - L) x.

  Theorem NegExp_ρ0_not_supp {x k} (H : Rlt x 0%R) : NegExp_ρ0 k x = 0.
  Proof.
    rewrite /NegExp_ρ0 Iverson_False //=; OK.
    rewrite /Icc//=.
    rewrite Rmin_left; OK.
  Qed.

  Theorem NegExp_ρ0_supp {k x} (Hx : Icc 0 1 x) : NegExp_ρ0 k x = exp (-(x + k))%R.
  Proof. rewrite /NegExp_ρ0 Iverson_True //=; OK. Qed.

  Theorem NegExp_ρ_not_supp {x k L} (H : (k < L)%nat) : NegExp_ρ L k x = 0.
  Proof.  rewrite /NegExp_ρ Iverson_False //=; [lra|lia]. Qed.

  Theorem NegExp_ρ_supp {x k L} (H : L ≤ k) : NegExp_ρ L k x = NegExp_ρ0 (k - L) x.
  Proof. rewrite /NegExp_ρ Iverson_True //=; OK. Qed.

  Theorem NegExp_ρ_ub {L k x0} : NegExp_ρ L k x0 <= exp (-(k-L)%nat).
  Proof.
    rewrite /NegExp_ρ.
    rewrite /Iverson//=; case_decide; OK.
    2: { rewrite Rmult_0_l. apply Rexp_nn. }
    rewrite Rmult_1_l.
    rewrite /NegExp_ρ0.
    rewrite /Iverson//=; case_decide; OK.
    2: { rewrite Rmult_0_l. apply Rexp_nn. }
    rewrite Rmult_1_l.
    apply exp_mono.
    suffices ? : (k-L)%nat <= (x0 + (k - L)%nat) by  OK.
    have H1 : (k - L)%nat <= (k - L)%nat + x0.
    { rewrite /Icc in H0. rewrite Rmin_left in H0; OK. }
    etrans; first apply H1.
    rewrite Rplus_comm.
    apply Rplus_le_compat; OK.
  Qed.

  (* TODO: Move *)
  Lemma Icc_PCts : PCts (Iverson (Icc 0 1)) 0 1.
  Proof. Admitted.

  Lemma NegExp_ρ0_PCts {L k} : PCts (λ x : R, NegExp_ρ0 (k - L) x) 0 1.
    rewrite /NegExp_ρ0.
    apply PCts_mult.
    2: {
      apply PCts_cts.
      intros ??.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
    apply Icc_PCts.
  Qed.

  Lemma NegExp_ρ_PCts {L k} : PCts (NegExp_ρ L k) 0 1.
  Proof.
    rewrite /NegExp_ρ.
    apply PCts_mult.
    {
      apply PCts_cts.
      intros ??.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
    apply NegExp_ρ0_PCts.
  Qed.

  Lemma NegExp_ρ0_nn {L x} : 0 <= (NegExp_ρ0 L x).
  Proof.
    rewrite /NegExp_ρ0.
    apply Rmult_le_pos.
    { apply Iverson_nonneg. }
    { apply Rexp_nn. }
  Qed.

  Lemma NegExp_ρ0_le_1 {L x} : (NegExp_ρ0 L x) <= 1.
  Proof.
    rewrite /NegExp_ρ0.
    rewrite /Iverson//=.
    case_decide; OK.
    rewrite Rmult_1_l.
    apply Rexp_range.
    suffices HH : (0 <= x + L) by OK.
    apply Rplus_le_le_0_compat.
    2: { apply pos_INR. }
    rewrite /Icc in H.
    rewrite Rmin_left in H; OK.
  Qed.

  Lemma NegExp_ρ_nn {L k x} : 0 <= (NegExp_ρ L k x).
  Proof.
    rewrite /NegExp_ρ.
    apply Rmult_le_pos.
    { apply Iverson_nonneg. }
    { apply NegExp_ρ0_nn. }
  Qed.

  Lemma NegExp_ρ_le_1 {L k x} : (NegExp_ρ L k x) <= 1.
  Proof.
    rewrite /NegExp_ρ.
    rewrite -(Rmult_1_r 1).
    apply Rmult_le_compat.
    { apply Iverson_nonneg. }
    { apply NegExp_ρ0_nn. }
    { apply Iverson_le_1. }
    { apply NegExp_ρ0_le_1. }
  Qed.

End pmf.

Section credits.
  Import Hierarchy.

  Definition NegExp_CreditV (F : nat → R → R) (L : nat) : R :=
    SeriesC (fun (k : nat) => RInt (fun x => NegExp_ρ L k x * F k x) 0 1).

  (* NegExp_CreditV but no integers *)
  Definition NegExp_CreditV'' (F : nat → R → R) (L : nat) : R :=
    SeriesC (fun (k : nat) => RInt (fun x => Iverson (Ioo 0 1) x * NegExp_ρ L k x * F k x) 0 1).

  Lemma NegExp_CreditV_nn {F L} (HP : ∀ x, PCts (F x) 0 1) (HB : ∀ x y, (0 <= y <= 1) → 0 <= F x y) : 0 <= NegExp_CreditV F L.
  Proof.
    rewrite /NegExp_CreditV.
    apply SeriesC_ge_0'.
    intros ?.
    apply RInt_ge_0; OK.
    { apply ex_RInt_mult.
      { apply PCts_RInt, NegExp_ρ_PCts. }
      { apply PCts_RInt, HP. }
    }
    intros ??.
    apply Rmult_le_pos.
    { apply NegExp_ρ_nn. }
    { apply HB. OK. }
  Qed.

  Definition NegExp_CreditV' (F : R → R) : R :=
    RInt_gen (fun r => F r * exp (-r)) (at_point 0) (Rbar_locally Rbar.p_infty).

  Lemma NegExp_CreditV_NegExp_CreditV' {M} {F : R → R} (HF : IPCts F) (HBound : ∀ x, 0 <= F x <= M):
    NegExp_CreditV' F = NegExp_CreditV (fun n x => F (n+x)) 0.
  Proof.
    rewrite /NegExp_CreditV'.
    rewrite (RInt_sep (fun r => F r * exp (-r)) (fun n => M * exp (-n))).
    { rewrite /NegExp_CreditV.
      rewrite (FubiniIntegralSeriesC_Strong (fun n => M * exp (-n))); OK.
      { apply RInt_ext.
        intros ??.
        apply SeriesC_ext.
        intros n.
        rewrite Rmult_comm.
        f_equal; [| f_equal; OK].
        rewrite /NegExp_ρ.
        rewrite Iverson_True; OK.
        rewrite Rmult_1_l.
        rewrite /NegExp_ρ0.
        rewrite Iverson_True; OK.
        2: { rewrite /Icc; OK. }
        rewrite Rmult_1_l.
        repeat f_equal.
        OK.
      }
      { intros ???.
        apply Rmult_le_pos.
        { apply NegExp_ρ_nn. }
        { apply HBound. }
      }
      { apply ex_seriesC_scal_l.
        apply ex_exp_geo_series.
      }
      { intros ???.
        rewrite Rabs_right.
        2: {
          apply Rle_ge.
          apply Rmult_le_pos.
          { apply NegExp_ρ_nn. }
          { apply HBound. }
        }
      { rewrite Rmult_comm.
        apply Rmult_le_compat.
        { apply HBound. }
        { apply NegExp_ρ_nn. }
        { apply HBound. }
        etrans; first apply NegExp_ρ_ub.
        right.
        repeat f_equal; OK.
      }
    }
    { intros n.
      apply ex_RInt_mult.
      { apply PCts_RInt. apply NegExp_ρ_PCts. }
      { apply IPCts_RInt. apply IPCts_shift. apply HF. }
    }
  }
  { apply (@ex_RInt_gen_Ici_compare_IPCts _ (fun x => M * exp (- x))).
    { apply IPCts_cts.
      intros ?.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
    { apply IPCts_mult; OK.
      apply IPCts_cts.
      intros ?.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
    { intros ?.
      split.
      { apply Rmult_le_pos.
        { apply HBound. }
        { apply Rexp_nn. }
      }
      apply Rmult_le_compat; OK.
      { apply HBound. }
      { apply Rexp_nn. }
      { apply HBound. }
    }
    { apply ex_RInt_gen_exp. }
  }
  { apply ex_seriesC_scal_l.
    apply ex_exp_geo_series.
  }
  { intros ?.
    split.
    { apply Rmult_le_pos.
      { apply HBound. }
      { apply Rexp_nn. }
    }
    apply Rmult_le_compat; OK.
    { apply HBound. }
    { apply Rexp_nn. }
    { apply HBound. }
    apply exp_mono.
    suffices ? : n <= (x + n) by OK.
    OK.
  }
  { intros b.
    apply ex_RInt_mult.
    { apply IPCts_RInt; OK. }
    { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      intros ??.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
  }
Qed.


  Local Definition hx (F : nat → R → R) (x : R) (L : nat) : nat → R :=
    fun z => Iverson Zeven z * F L x + Iverson (not ∘ Zeven) z * NegExp_CreditV F (L + 1).

  Local Definition g (F : nat → R -> R) (L : nat) : R -> R := fun x =>
    RealDecrTrial_CreditV (hx F x L) 0 x.

  (* g, but with all integers poked to be 1 *)
  Local Definition g' (F : nat → R -> R) (L : nat) : R -> R :=
    poke (g F L) 1 1.

  Local Lemma hx_nonneg {F : nat → R → R} {L n r} (HP : ∀ x : nat, PCts (F x) 0 1) (HB : ∀ x y, (0 <= y <= 1) → 0 <= F x y) : 0 <= r <= 1 → 0 <= hx F r L n.
  Proof.
    intros ?.
    rewrite /hx.
    apply Rplus_le_le_0_compat.
    { apply Rmult_le_pos.
      { apply Iverson_nonneg. }
      { apply HB. OK. }
    }
    { apply Rmult_le_pos.
      { apply Iverson_nonneg. }
      { apply NegExp_CreditV_nn; OK. }
    }
  Qed.

  Local Lemma g_nonneg {F : nat → R -> R} {L : nat} (HP : ∀ x : nat, PCts (F x) 0 1) (HB : ∀ x y, (0 <= y <= 1) → 0 <= F x y) : ∀ r : R, 0 <= r <= 1 → 0 <= g F L r.
  Proof.
    intros ??.
    rewrite /g.
    apply CreditV_nonneg; OK.
    intros ?.
    apply hx_nonneg; OK.
  Qed.
  Local Definition B (F : nat → R → R) (L : nat) (x : R) (n : nat) (k : nat) (x0 : R) :=
      RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_ρ (L + 1) k x0 * F k x0.

  (** One possible upper bound for B that does not depend on x *)
  Local Definition BUB (M : R) (k : nat)  :=
      (1 / fact k) *  M.

  Lemma RealDecrTrial_μ0_ub {x n} : 0 <= x <= 1 → RealDecrTrial_μ0 x n <= 1 / fact n.
  Proof.
    intros ?.
    rewrite /RealDecrTrial_μ0.
    have  ? : 0 <= x ^ (n + 1) / fact (n + 1).
    { apply Rcomplements.Rdiv_le_0_compat.
      { apply pow_le. OK. }
      { apply INR_fact_lt_0. }
    }
    suffices ? : x ^ (n) / fact (n) <= 1 / fact n by OK.
    do 2 rewrite Rdiv_def.
    apply Rmult_le_compat.
    { apply pow_le. OK.  }
    { apply Rlt_le. apply Rinv_0_lt_compat.  apply INR_fact_lt_0. }
    { rewrite -(pow1 (n)%nat). apply pow_incr. OK. }
    right. repeat f_equal; OK.
  Qed.

  Lemma RealDecrTrial_μ_ub {x n} : 0 <= x <= 1 → RealDecrTrial_μ x 0 n <= 1 / fact n.
  Proof.
    intros ?.
    rewrite /RealDecrTrial_μ.
    rewrite -(Rmult_1_l (1 / fact n)).
    apply Rmult_le_compat.
    { apply Iverson_nonneg. }
    { apply RealDecrTrial_μ0nn. OK. }
    { apply Iverson_le_1. }
    rewrite /RealDecrTrial_μ0.
    have  ? : 0 <= x ^ (n - 0 + 1) / fact (n - 0 + 1).
    { apply Rcomplements.Rdiv_le_0_compat.
      { apply pow_le. OK. }
      { apply INR_fact_lt_0. }
    }
    suffices ? : x ^ (n - 0) / fact (n - 0) <= 1 / fact n by OK.
    do 2 rewrite Rdiv_def.
    apply Rmult_le_compat.
    { apply pow_le. OK.  }
    { apply Rlt_le. apply Rinv_0_lt_compat.  apply INR_fact_lt_0. }
    { rewrite -(pow1 (n - 0)%nat). apply pow_incr. OK. }
    right. repeat f_equal; OK.
  Qed.

  Local Lemma B_BUB {F L x n k} (M : R) (Hbound : ∀ n x, 0 <= F n x <= M):
    ∀ x0, 0 < x < 1 → 0 <= B F L x n k x0 <= BUB M n.
  Proof.
    intros ??.
    split.
    { apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
      { apply NegExp_ρ_nn. }
      { apply Hbound. }
    }
    { rewrite /B/BUB.
      apply Rmult_le_compat.
      2: apply Hbound.
      3: apply Hbound.
      { apply Rmult_le_pos; [apply Rmult_le_pos|].
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
        { apply NegExp_ρ_nn. }
      }
      rewrite -(Rmult_1_r (1 / fact n)).
      rewrite -(Rmult_1_r (1 / fact n)).
      apply Rmult_le_compat.
      { apply Rmult_le_pos.
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
      }
      { apply NegExp_ρ_nn. }
      2: { apply NegExp_ρ_le_1. }
      apply Rmult_le_compat.
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
      2: apply Iverson_le_1.
      apply RealDecrTrial_μ_ub.
      OK.
    }
  Qed.

  Local Lemma BUB_Series {M} : Series.ex_series (BUB M).
  Proof.
    rewrite /BUB.
    apply Series.ex_series_scal_r.
    replace (λ n : nat, 1 / fact n) with (λ n : nat, / fact n) by (funexti; OK).
    apply ex_exp_series.
  Qed.

  Local Lemma BUB_SeriesC {M} : ex_seriesC (BUB M).
  Proof. rewrite -ex_seriesC_nat. apply BUB_Series. Qed.

  Lemma B_PCts2 {F L n k} (HPcts : ∀ x1, PCts (F x1) 0 1) :
    PCts2 (λ x y : R, B F L x n k y) 0 1 0 1.
  Proof.
    rewrite /B.
    apply PCts2_mult; [apply PCts2_mult|].
    { apply PCts_const_x.
      apply PCts_cts.
      intros ??.
      apply @Continuity.continuous_mult.
      2: { apply @Continuity.continuous_const. }
      rewrite /RealDecrTrial_μ.
      apply @Continuity.continuous_mult.
      1: { apply @Continuity.continuous_const. }
      rewrite /RealDecrTrial_μ0.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
    { apply PCts_const_y. apply NegExp_ρ_PCts. }
    { apply PCts_const_y. apply HPcts. }
  Qed.


  Local Lemma g_ex_RInt M {F : nat → R → R} {L} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    ex_RInt (g F L) 0 1.
  Proof.
    rewrite /g/hx.
    rewrite /RealDecrTrial_CreditV.
    eapply (ex_RInt_SeriesC (fun n => (1 / fact n) * (1 * M + 1 * NegExp_CreditV F (L + 1)))); OK.
    { rewrite ex_seriesC_nat.
      apply ex_seriesC_scal_r.
      setoid_rewrite Rdiv_def.
      apply ex_seriesC_scal_l.
      rewrite -ex_seriesC_nat.
      apply ex_exp_series.
    }
    { intros ???.
      split.
      { apply Rmult_le_pos; [apply Rmult_le_pos|].
        { apply Iverson_nonneg. }
        { apply RealDecrTrial_μ0nn. OK. }
        apply Rplus_le_le_0_compat; apply Rmult_le_pos.
        { apply Iverson_nonneg. }
        { apply Hbound; OK. }
        { apply Iverson_nonneg. }
        { apply NegExp_CreditV_nn; OK. intros ???. apply Hbound. OK. }
      }
      apply Rmult_le_compat.
      { apply RealDecrTrial_μnn. OK. }
      2: { apply RealDecrTrial_μ_ub. OK. }
      { apply Rplus_le_le_0_compat; apply Rmult_le_pos.
        { apply Iverson_nonneg. }
        { apply Hbound; OK. }
        { apply Iverson_nonneg. }
        { apply NegExp_CreditV_nn; OK. intros ???. apply Hbound. OK. }
      }
      apply Rplus_le_compat.
      { apply Rmult_le_compat.
        { apply Iverson_nonneg. }
        { apply Hbound; OK. }
        { apply Iverson_le_1. }
        { apply Hbound; OK. }
      }
      { apply Rmult_le_compat.
        { apply Iverson_nonneg. }
        { apply NegExp_CreditV_nn; OK. intros ???. apply Hbound. OK. }
        { apply Iverson_le_1. }
        { OK. }
      }
    }
    { intros ?.
      apply ex_RInt_mult.
      { apply RealDecrTrial_μ_ex_RInt. }
      apply (ex_RInt_plus (V := R_CompleteNormedModule)).
      2: { apply ex_RInt_const. }
      apply ex_RInt_Rmult.
      apply PCts_RInt.
      apply HPcts.
    }
  Qed.

  Lemma QuadExists2 M {F L} {x} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    ex_RInt (λ x0 : R, SeriesC (λ n : nat, RInt (λ x1 : R, B F L x1 n x x0) 0 1)) 0 1.
  Proof.
    eapply (ex_RInt_SeriesC (fun n => 1 / fact n * 1 * exp (- (x - (L + 1))%nat) * M)); OK.
    { rewrite ex_seriesC_nat.
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_r.
      setoid_rewrite Rdiv_def.
      apply ex_seriesC_scal_l.
      rewrite -ex_seriesC_nat.
      apply ex_exp_series.
    }
    { intros ???.
      have HH : 0 <= RInt (λ x1 : R, B F L x1 n x x0) 0 1.
      { apply RInt_ge_0; OK.
        2: {
          intros ??.
          apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
          { apply RealDecrTrial_μnn. OK. }
          { apply Iverson_nonneg. }
          { apply NegExp_ρ_nn. }
          { apply Hbound; OK. }
        }
        rewrite /B.
        apply ex_RInt_mult; [apply ex_RInt_mult; [apply ex_RInt_mult|]|].
        { apply RealDecrTrial_μ_ex_RInt. }
        { apply ex_RInt_const. }
        { apply ex_RInt_const. }
        { apply ex_RInt_const. }
      }
      split; OK.
      rewrite -(Rabs_right _ (Rle_ge _ _ HH)).
      etrans.
      { rewrite /B.
        eapply (abs_RInt_le_const _ _ _ ((1 / fact n) * 1 * exp (- (x - (L + 1))%nat) * M)); OK.
        { apply ex_RInt_mult; [apply ex_RInt_mult; [apply ex_RInt_mult|]|].
          { apply RealDecrTrial_μ_ex_RInt. }
          { apply ex_RInt_const. }
          { apply ex_RInt_const. }
          { apply ex_RInt_const. }
        }
        { intros ??.
          rewrite (Rabs_right _ (Rle_ge _ _ _)).
          2: {
            apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
            { apply RealDecrTrial_μnn; OK. }
            { apply Iverson_nonneg. }
            { apply NegExp_ρ_nn. }
            { apply Hbound; OK. }
          }
          apply Rmult_le_compat.
          2: apply Hbound; OK.
          3: apply Hbound; OK.
          { apply Rmult_le_pos; [apply Rmult_le_pos|].
            { apply RealDecrTrial_μnn; OK. }
            { apply Iverson_nonneg. }
            { apply NegExp_ρ_nn. }
          }
          apply Rmult_le_compat.
          2: apply NegExp_ρ_nn.
          3: apply NegExp_ρ_ub.
          { apply Rmult_le_pos.
            { apply RealDecrTrial_μnn; OK. }
            { apply Iverson_nonneg. }
          }
          apply Rmult_le_compat.
          { apply RealDecrTrial_μnn; OK. }
          { apply Iverson_nonneg. }
          { apply RealDecrTrial_μ_ub; OK. }
          { apply Iverson_le_1; OK. }
        }
      }
      OK.
    }
    intros n.
    apply Fubini_Step_ex_x.
    rewrite /B.
    apply PCts2_mult; [apply PCts2_mult; [apply PCts2_mult|]|].
    { apply PCts_const_y. apply RealDecrTrial_μ_PCts. }
    { apply PCts_const_x.
      apply PCts_cts.
      intros ??.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
    { apply PCts_const_x. apply NegExp_ρ_PCts. }
    { apply PCts_const_x. apply HPcts. }
  Qed.

  (* Like quadExists 3 once I factor out all those terms from B *)
  Lemma QuadExists1  M {F L} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    ex_seriesC (λ k : nat, RInt (λ x0 : R, SeriesC (λ n : nat, RInt (λ x : R, B F L x n k x0) 0 1)) 0 1).
  Proof.

    (*



    rewrite /B.
    apply (ex_seriesC_le _ (λ k : nat, exp (- (k - (L + 1))%nat) * M * SeriesC (λ n : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n) 0 1))).
    2: {
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_r.
      apply (ex_SeriesC_nat_shiftN_r (L + 1)%nat).
      rewrite /compose//=.
      replace (λ x0 : nat, exp (- (x0 + (L + 1) - (L + 1))%nat))
        with (λ x0 : nat, exp (- x0)%nat).
      { apply ex_exp_geo_series. }
      funexti.
      do 3 f_equal.
      OK.
    }
    intros n.
      replace (λ x0 : R,
          SeriesC
            (λ n0 : nat,
               RInt (λ x : R, RealDecrTrial_μ x 0 n0 * Iverson (not ∘ Zeven) n0 * NegExp_ρ (L + 1) n x0 * F n x0) 0 1))
        with
        (λ x0 : R,
          NegExp_ρ (L + 1) n x0 * F n x0 *
          SeriesC
            (λ n0 : nat,
               RInt (λ x : R, RealDecrTrial_μ x 0 n0 * Iverson (not ∘ Zeven) n0 ) 0 1)).
      2: { funexti. rewrite -SeriesC_scal_l. f_equal; funexti.
           rewrite RInt_Rmult.
           { f_equal. funexti. OK. }
           apply ex_RInt_Rmult'.
           apply RealDecrTrial_μ_ex_RInt.
    }

    have HH : (0 <= RInt
(λ x0 : R,
       NegExp_ρ (L + 1) n x0 * F n x0 *
       SeriesC (λ n0 : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n0 * Iverson (not ∘ Zeven) n0) 0 1))  0 1).
    { apply RInt_ge_0; OK.
      { apply ex_RInt_Rmult'.
        apply ex_RInt_mult.
        { apply PCts_RInt. apply NegExp_ρ_PCts. }
        { apply PCts_RInt. apply HPcts. }
      }
      { intros ??.
        apply Rmult_le_pos; [apply Rmult_le_pos|].
        { apply NegExp_ρ_nn. }
        { apply Hbound; OK. }
        apply SeriesC_ge_0'.
        intros ?.
        apply RInt_ge_0; OK.
        { apply ex_RInt_mult.
          { apply RealDecrTrial_μ_ex_RInt. }
          { apply ex_RInt_const. }
        }
        intros ??.
        apply Rmult_le_pos.
        { apply RealDecrTrial_μnn; OK. }
        { apply Iverson_nonneg. }
      }
    }
    split; OK.
    rewrite -(Rabs_right _ (Rle_ge _ _ HH)).
    etrans.
    { eapply (abs_RInt_le_const _ _ _
        (SeriesC (λ n0 : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n0 * Iverson (not ∘ Zeven) n0 * exp (- (n - (L + 1))%nat) * M  ) 0 1))); OK.
      { apply ex_RInt_Rmult'.
        apply ex_RInt_mult.
        { apply PCts_RInt. apply NegExp_ρ_PCts. }
        { apply PCts_RInt. apply HPcts. }
      }
      intros ??.
      rewrite Rabs_right.
      2: {
        apply Rle_ge.
        apply Rmult_le_pos; [apply Rmult_le_pos|].
        { apply NegExp_ρ_nn. }
        { apply Hbound; OK. }
        apply SeriesC_ge_0'.
        intros ?.
        apply RInt_ge_0; OK.
        { apply ex_RInt_mult.
          { apply RealDecrTrial_μ_ex_RInt. }
          { apply ex_RInt_const. }
        }
        intros ??.
        apply Rmult_le_pos.
        { apply RealDecrTrial_μnn; OK. }
        { apply Iverson_nonneg. }
      }
      rewrite -SeriesC_scal_l.
      apply SeriesC_le.
      { intros ?.
        split.
        { apply Rmult_le_pos; [apply Rmult_le_pos|].
          { apply NegExp_ρ_nn. }
          { apply Hbound; OK. }
          apply RInt_ge_0; OK.
          { apply ex_RInt_mult.
            { apply RealDecrTrial_μ_ex_RInt. }
            { apply ex_RInt_const. }
          }
          intros ??.
          apply Rmult_le_pos.
          { apply RealDecrTrial_μnn; OK. }
          { apply Iverson_nonneg. }
        }
      { rewrite RInt_Rmult.
        2: {
          apply ex_RInt_mult.
          { apply PCts_RInt. apply RealDecrTrial_μ_PCts. }
          { apply PCts_RInt.
            apply PCts_cts.
            intros ??.
            apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
            by auto_derive.
          }
      }
      apply RInt_le; OK.
      { apply ex_RInt_mult; [|apply ex_RInt_mult].
        { apply ex_RInt_const. }
        { apply PCts_RInt. apply RealDecrTrial_μ_PCts. }
        { apply ex_RInt_const. }
      }
      { apply ex_RInt_mult; [apply ex_RInt_mult; [apply ex_RInt_mult|]|].
        { apply PCts_RInt. apply RealDecrTrial_μ_PCts. }
        { apply ex_RInt_const. }
        { apply ex_RInt_const. }
        { apply ex_RInt_const. }
      }
      intros ??.
      rewrite Rmult_comm.
      repeat rewrite Rmult_assoc.
      apply Rmult_le_compat; OK.
      { apply Iverson_nonneg. }
      { apply Rmult_le_pos; [|apply Rmult_le_pos; [| apply Rmult_le_pos; [|apply Rmult_le_pos]]].
        { apply RealDecrTrial_μ0nn. OK. }
        { apply Iverson_nonneg. }
        { apply Iverson_nonneg. }
        { apply Iverson_nonneg. }
        apply Rmult_le_pos.
        { apply Rexp_nn. }
        { apply Hbound; OK. }
      }
      apply Rmult_le_compat; OK.
      { apply RealDecrTrial_μ0nn. OK. }
      { apply Rmult_le_pos; [| apply Rmult_le_pos; [|apply Rmult_le_pos]].
        { apply Iverson_nonneg. }
        { apply Iverson_nonneg. }
        { apply Iverson_nonneg. }
        apply Rmult_le_pos.
        { apply Rexp_nn. }
        { apply Hbound; OK. }
      }
      apply Rmult_le_compat; OK.
      { apply Iverson_nonneg. }
      { apply Rmult_le_pos; [|apply Rmult_le_pos].
        { apply Iverson_nonneg. }
        { apply Iverson_nonneg. }
        apply Rmult_le_pos.
        { apply Rexp_nn. }
        { apply Hbound; OK. }
      }
      rewrite /Iverson//=; case_decide; OK.
      2: {
        rewrite Rmult_0_l.
        apply Rmult_le_pos.
        { apply Rexp_nn. }
        { have HHH : (0 <= 0 <= 1) by OK. have Hbound' := Hbound 0%nat 0 HHH. OK. }
      }
      rewrite Rmult_1_l.
      case_decide; OK.
      2: {
        rewrite Rmult_0_l.
        apply Rmult_le_pos.
        { apply Rexp_nn. }
        { have HHH : (0 <= 0 <= 1) by OK. have Hbound' := Hbound 0%nat 0 HHH. OK. }
      }
      rewrite Rmult_1_l.
      apply Rmult_le_compat; OK.
      { apply Rexp_nn. }
      { apply Hbound; OK. }
      2: { apply Hbound; OK. }
      apply exp_mono.
      rewrite /Icc in H2.
      rewrite Rmin_left in H2; OK.
    }
  }
  replace (λ n0 : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n0 * Iverson (not ∘ Zeven) n0 * exp (- (n - (L + 1))%nat) * M) 0 1)
     with (λ n0 : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n0 * Iverson (not ∘ Zeven) n0 * (exp (- (n - (L + 1))%nat) * M)) 0 1).
  2: { funexti. f_equal; funexti; OK. }
  replace (λ n0 : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n0 * Iverson (not ∘ Zeven) n0 * (exp (- (n - (L + 1))%nat) * M)) 0 1)
     with (λ n0 : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n0 * Iverson (not ∘ Zeven) n0) 0 1 * exp (- (n - (L + 1))%nat) * M ).
  2: {
    funexti.
    symmetry.
    rewrite -RInt_Rmult'; OK.
    apply ex_RInt_mult.
    { apply PCts_RInt. apply RealDecrTrial_μ_PCts. }
    { apply ex_RInt_const. }
  }
  apply ex_seriesC_scal_r.
  apply ex_seriesC_scal_r.
  apply (ex_seriesC_le _ (fun x => (1 / fact x) * 1)).
  2: {
    apply ex_seriesC_scal_r.
    setoid_rewrite Rdiv_def.
    apply ex_seriesC_scal_l.
    rewrite -ex_seriesC_nat.
    apply ex_exp_series.
  }
  intros ?.
  split.
  { apply RInt_ge_0; OK.
    { apply ex_RInt_mult.
      { apply PCts_RInt. apply RealDecrTrial_μ_PCts. }
      { apply ex_RInt_const. }
    }
    { intros ??.
      apply Rmult_le_pos.
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
    }
  }
  have HHH : 0 <= RInt (λ x : R, RealDecrTrial_μ x 0 n0 * Iverson (not ∘ Zeven) n0) 0 1.
  { apply RInt_ge_0; OK.
    { apply ex_RInt_mult.
      { apply PCts_RInt. apply RealDecrTrial_μ_PCts. }
      { apply ex_RInt_const. }
    }
    { intros ??.
      apply Rmult_le_pos.
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
    }
  }
  rewrite -(Rabs_right _ (Rle_ge _ _ HHH)).
  etrans.
  { eapply (abs_RInt_le_const _ _ _ ((1 / fact n0) * 1)); OK.
    { apply ex_RInt_mult.
      { apply PCts_RInt. apply RealDecrTrial_μ_PCts. }
      { apply ex_RInt_const. }
    }
    intros ??.
    rewrite (Rabs_right).
    2: {
      apply Rle_ge.
      apply Rmult_le_pos.
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
    }
    apply Rmult_le_compat; OK.
    { apply RealDecrTrial_μnn; OK. }
    { apply Iverson_nonneg. }
    { apply RealDecrTrial_μ_ub. OK. }
    { apply Iverson_le_1. }
  }
  OK.
  }
  rewrite Rminus_0_r.
  rewrite Rmult_1_l.
  rewrite -SeriesC_scal_l.
  apply SeriesC_le.
  2: {
    apply ex_seriesC_scal_l.
    apply (ex_seriesC_le _ (λ x : nat, 1 / fact x)).
    2: {
    setoid_rewrite Rdiv_def.
    apply ex_seriesC_scal_l.
    rewrite -ex_seriesC_nat.
    apply ex_exp_series.
    }
    intros ?.
    have HHH : 0 <= RInt (λ x : R, RealDecrTrial_μ x 0 n0 * Iverson (not ∘ Zeven) n0) 0 1.
    { apply RInt_ge_0; OK.
      { apply ex_RInt_mult.
        { apply PCts_RInt. apply RealDecrTrial_μ_PCts. }
        { apply ex_RInt_const. }
      }
      { intros ??.
        apply Rmult_le_pos.
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
      }
    }
    split; OK.
    rewrite -(Rabs_right _ (Rle_ge _ _ HHH)).
    etrans.
    { eapply (abs_RInt_le_const _ _ _ ((1 / fact n0) * 1)); OK.
      { apply ex_RInt_mult.
        { apply PCts_RInt. apply RealDecrTrial_μ_PCts. }
        { apply ex_RInt_const. }
      }
      intros ??.
      rewrite (Rabs_right).
      2: {
        apply Rle_ge.
        apply Rmult_le_pos.
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
      }
      apply Rmult_le_compat; OK.
      { apply RealDecrTrial_μnn; OK. }
      { apply Iverson_nonneg. }
      { apply RealDecrTrial_μ_ub. OK. }
      { apply Iverson_le_1. }
    }
    OK.
  }
  intros ?.
    have HHH : 0 <= RInt (λ x : R, RealDecrTrial_μ x 0 n0 * Iverson (not ∘ Zeven) n0 * exp (- (n - (L + 1))%nat) * M) 0 1.
    { apply RInt_ge_0; OK.
      { apply ex_RInt_mult.
        2: { apply ex_RInt_const. }
        apply ex_RInt_mult.
        2: { apply ex_RInt_const. }
        apply ex_RInt_mult.
        { apply PCts_RInt. apply RealDecrTrial_μ_PCts. }
        { apply ex_RInt_const. }
      }
      { intros ??.
        apply Rmult_le_pos.
        2: { have HHH : (0 <= 0 <= 1) by OK. have Hbound' := Hbound 0%nat 0 HHH. OK. }
        apply Rmult_le_pos.
        2: { apply Rexp_nn. }
        apply Rmult_le_pos.
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
      }
    }
    split; OK.
    rewrite -(Rabs_right _ (Rle_ge _ _ HHH)).
    etrans.
    { eapply (abs_RInt_le_const _ _ _ ((1 / fact n0) * 1 * exp (- (n - (L + 1))%nat) * M)); OK.
      { apply ex_RInt_mult.
        2: { apply ex_RInt_const. }
        apply ex_RInt_mult.
        2: { apply ex_RInt_const. }
        apply ex_RInt_mult.
        { apply PCts_RInt. apply RealDecrTrial_μ_PCts. }
        { apply ex_RInt_const. }
      }
      intros ??.
      rewrite Rabs_right.
      2: {
        apply Rle_ge.
        apply Rmult_le_pos.
        2: { have HHHH : (0 <= 0 <= 1) by OK. have Hbound' := Hbound 0%nat 0 HHHH. OK. }
        apply Rmult_le_pos.
        2: { apply Rexp_nn. }
        apply Rmult_le_pos.
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
      }
      apply Rmult_le_compat; OK.
      2: { have HHHH : (0 <= 0 <= 1) by OK. have Hbound' := Hbound 0%nat 0 HHHH. OK. }
      { apply Rmult_le_pos.
        2: { apply Rexp_nn. }
        apply Rmult_le_pos.
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
      }
      apply Rmult_le_compat; OK.
      { apply Rmult_le_pos.
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
      }
      { apply Rexp_nn. }
      apply Rmult_le_compat; OK.
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
      { apply RealDecrTrial_μ_ub. OK. }
      { apply Iverson_le_1. }
    }
    rewrite Rminus_0_r.
    rewrite Rmult_1_l.
    replace (1 / fact n0 * 1 * exp (- (n - (L + 1))%nat) * M)
      with  (1 / fact n0 * 1 * exp (- (n - (L + 1))%nat) * M)

    OK.

     *)
  Admitted.

  Lemma QuadExists3 M {F : nat → R → R} {L} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    ex_RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson Zeven n * F L x)) 0 1.
  Proof.
    apply (ex_RInt_SeriesC (fun n => (1 / fact n) * 1 * M)); OK.
    { rewrite ex_seriesC_nat.
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_r.
      setoid_rewrite Rdiv_def.
      apply ex_seriesC_scal_l.
      rewrite -ex_seriesC_nat.
      apply ex_exp_series.
    }
    2: {
      intros n.
      apply ex_RInt_mult; [apply ex_RInt_mult|].
      { apply RealDecrTrial_μ_ex_RInt. }
      { apply ex_RInt_const. }
      { apply PCts_RInt. apply HPcts.  }
    }
    intros ???.
    split.
    { apply Rmult_le_pos; [apply Rmult_le_pos|].
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
      { apply Hbound; OK. }
    }
    { apply Rmult_le_compat.
      2: apply Hbound; OK.
      3: apply Hbound; OK.
      { apply Rmult_le_pos.
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
      }
      apply Rmult_le_compat.
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
      { apply RealDecrTrial_μ_ub; OK. }
      { apply Iverson_le_1. }
    }
  Qed.

  Lemma QuadExists4 M {F : nat → R → R} {L} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    (ex_RInt (λ x : R, SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_ρ (L + 1) k x0 * F k x0) 0 1))) 0 1).
  Proof.
  Admitted.

  (** QuadExchange1: Corresponds to HR4 in gauss.v.
      Exchanges the outermost integral with the outermost series.
      Proof: Use FubiniIntegralSeries_Strong with an appropriate bounding sequence.
      Need to show: (1) non-negativity of integrand, (2) existence of bounding series,
      (3) pointwise bound on integrands. *)
  Local Lemma QuadExchange1 M {F L} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    (RInt (λ x : R, SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1))) 0 1) =
    (SeriesC (λ n : nat, RInt (λ x : R, SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1)) 0 1)).
  Proof.
    replace (RInt (λ x : R, SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1))) 0 1)
       with (RInt (λ x : R, Series.Series (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1))) 0 1).
    2: { f_equal; funexti. rewrite SeriesC_nat. done. }
    rewrite SeriesC_nat.
    symmetry.
    have L3 : ∀ n n0 : nat, PCts2 (λ x y : R, B F L x n n0 y) 0 1 0 1.
    { intros ??.
      apply PCts2_mult; [apply PCts2_mult; [apply PCts2_mult|]|].
      { apply PCts_const_x. apply RealDecrTrial_μ_PCts. }
      { apply PCts_const_x.
        apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply PCts_const_y. apply NegExp_ρ_PCts. }
      { apply PCts_const_y. apply HPcts. }
    }
    have L4 : ∀ n : nat, ∀ x x0, PCts (λ x1 : R, B F L x n x0 x1) 0 1.
    { intros ???.
      apply PCts_mult; [apply PCts_mult; [apply PCts_mult|]|].
      { apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply NegExp_ρ_PCts. }
      { apply HPcts. }
    }

    have L2 : ∀ n n0 : nat, ex_RInt (λ x : R, RInt (λ x0 : R, B F L x n n0 x0) 0 1) 0 1.
    { intros ??. apply Fubini_Step_ex_x; OK.  }
    have L1 : ∀ n x, 0 < x < 1 → 0 <= SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1).
    { intros ???.
      apply SeriesC_ge_0'.
      intros ?.
      apply RInt_ge_0; OK.
      { apply PCts_RInt. apply L4. }
      intros ??.
      apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
      { apply NegExp_ρ_nn. }
      { apply Hbound. OK. }
    }
    have L5 : ∀ n n0 : nat, ∀ x x0 : R, 0 <= x <= 1 → 0 <= x0 <= 1 → 0 <= B F L x n n0 x0.
    { intros ??????.
      rewrite /B.
      apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
        { apply NegExp_ρ_nn. }
        { apply Hbound. OK. }
    }
    have L6 : ∀ x n n0 t, 0 <= x <= 1 → 0 <= t <= 1 → B F L x n n0 t <= 1 * 1 * exp (- (n0 - (L + 1))%nat) * M.
    { intros ??????.
      rewrite /B.
      apply Rmult_le_compat.
      2: apply Hbound; OK.
      3: apply Hbound; OK.
      { apply Rmult_le_pos; [apply Rmult_le_pos|].
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
        { apply NegExp_ρ_nn. }
      }
      apply Rmult_le_compat.
      { apply Rmult_le_pos.
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
      }
      { apply NegExp_ρ_nn. }
      2: { apply NegExp_ρ_ub. }
      apply Rmult_le_compat.
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
      2: apply Iverson_le_1.
      apply RealDecrTrial_μ_le_1.
      OK.
    }
    eapply (FubiniIntegralSeries_Strong (fun k : nat => (1 / fact k) * 1 * SeriesC (λ x0 : nat, RInt (λ x1 : R, NegExp_ρ (L + 1) x0 x1 * F x0 x1) 0 1))); OK.
    { rewrite ex_seriesC_nat.
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_r.
      setoid_rewrite Rdiv_def.
      apply ex_seriesC_scal_l.
      rewrite -ex_seriesC_nat.
      apply ex_exp_series.
    }
    { intros ???.
      rewrite Rabs_right.
      2: { by apply Rle_ge, L1. }
      rewrite /B.
      replace (λ k : nat, RInt (λ x0 : R, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_ρ (L + 1) k x0 * F k x0) 0 1)
         with (λ k : nat, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * RInt (λ x0 : R, NegExp_ρ (L + 1) k x0 * F k x0) 0 1).
      2: {
        funexti.
        rewrite RInt_Rmult. { f_equal; funexti; OK. }
        apply ex_RInt_mult.
        { apply PCts_RInt. apply NegExp_ρ_PCts. }
        { apply PCts_RInt. apply HPcts. }
      }
      rewrite SeriesC_scal_l.
      apply Rmult_le_compat.
      { apply Rmult_le_pos.
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
      }
      { apply SeriesC_ge_0'.
        intros ?.
        apply RInt_ge_0; OK.
        {  apply ex_RInt_mult.
           { apply PCts_RInt. apply NegExp_ρ_PCts. }
           { apply PCts_RInt. apply HPcts. }
        }
        intros ??.
        apply Rmult_le_pos.
        { apply NegExp_ρ_nn; OK. }
        { apply Hbound. OK. }
      }
      { apply Rmult_le_compat; OK.
        { apply RealDecrTrial_μnn; OK. }
        { apply Iverson_nonneg. }
        { apply RealDecrTrial_μ_ub; OK. }
        { apply Iverson_le_1. }
      }
      { OK. }
    }
    { intros n.
      eapply (ex_RInt_SeriesC (fun n0 => ((* 1 / fact n*) 1 * 1 * exp (- (n0 - (L + 1))%nat) * M))); OK.
      { rewrite ex_seriesC_nat.
        apply ex_seriesC_scal_r.
        apply ex_seriesC_scal_l.
        apply (ex_SeriesC_nat_shiftN_r (L + 1)%nat).
        rewrite /compose//=.
        replace (λ x0 : nat, exp (- (x0 + (L + 1) - (L + 1))%nat))
          with (λ x0 : nat, exp (- x0)%nat).
        { apply ex_exp_geo_series. }
        funexti.
        do 3 f_equal.
        OK.
      }
      { intros ???.
        split.
        { apply RInt_ge_0; OK.
          2: { intros ??. apply L5; OK. }
          apply PCts_RInt; OK.
        }
        { have HH : 0 <= RInt (λ x0 : R, B F L x n n0 x0) 0 1.
          { apply RInt_ge_0; OK.
            { apply PCts_RInt;  OK. }
            intros ??.
            apply L5; OK.
          }
          rewrite -(Rabs_right _ (Rle_ge _ _ HH)).
          etrans.
          { eapply (abs_RInt_le_const _ _ _ (1 * 1 * exp (- (n0 - (L + 1))%nat) * M)); OK.
            { apply PCts_RInt;  OK. }
            intros ??.
            rewrite Rabs_right.
            2: { apply Rle_ge; OK.
                 rewrite /B.
                 apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
                 { apply RealDecrTrial_μnn. OK. }
                 { apply Iverson_nonneg. }
                 { apply NegExp_ρ_nn. }
                 { apply Hbound. OK. }
            }
            apply L6; OK.
        }
        OK.
      }
    }
  }
  Qed.

  (** QuadExchange2: Corresponds to HR1 in gauss.v.
      Exchanges the inner series (over k) with the integral (over x).
      Proof: Apply SeriesC_ext to reduce to a single n, then use FubiniIntegralSeries_Strong
      for each fixed n. Similar conditions as QuadExchange1. *)
  Local Lemma QuadExchange2 M {F L} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    (SeriesC (λ n : nat, RInt (λ x : R, SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1)) 0 1)) =
    (SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x : R, RInt (λ x0 : R, B F L x n k x0) 0 1) 0 1))).
  Proof.
    apply SeriesC_ext; intros n.
    replace (λ x : R, SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1))
       with (λ x : R, Series.Series (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1)).
    2: { f_equal; funexti. rewrite SeriesC_nat. done. }
    rewrite SeriesC_nat.
    symmetry.

    have L3 : ∀ n n0 : nat, PCts2 (λ x y : R, B F L x n n0 y) 0 1 0 1.
    { intros ??.
      apply PCts2_mult; [apply PCts2_mult; [apply PCts2_mult|]|].
      { apply PCts_const_x. apply RealDecrTrial_μ_PCts. }
      { apply PCts_const_x.
        apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply PCts_const_y. apply NegExp_ρ_PCts. }
      { apply PCts_const_y. apply HPcts. }
    }

    have L5 : ∀ n n0 : nat, ∀ x x0 : R, 0 <= x <= 1 → 0 <= x0 <= 1 → 0 <= B F L x n n0 x0.
    { intros ??????.
      rewrite /B.
      apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
        { apply NegExp_ρ_nn. }
        { apply Hbound. OK. }
    }
    have L4 : ∀ n : nat, ∀ x x0, PCts (λ x1 : R, B F L x n x0 x1) 0 1.
    { intros ???.
      apply PCts_mult; [apply PCts_mult; [apply PCts_mult|]|].
      { apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply NegExp_ρ_PCts. }
      { apply HPcts. }
    }

    have L1 : ∀ n x, 0 < x < 1 → 0 <= SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1).
    { intros ???.
      apply SeriesC_ge_0'.
      intros ?.
      apply RInt_ge_0; OK.
      { apply PCts_RInt. apply L4. }
      intros ??.
      apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
      { apply NegExp_ρ_nn. }
      { apply Hbound. OK. }
    }


    eapply (FubiniIntegralSeries_Strong (fun n0 => ((* 1 / fact n*) 1 * 1 * exp (- (n0 - (L + 1))%nat) * M))); OK.
    { intros ???.
      apply RInt_ge_0; OK.
      { apply PCts_RInt. apply L4. }
      intros ??. apply L5; OK.
    }
    { rewrite ex_seriesC_nat.
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_l.
      apply (ex_SeriesC_nat_shiftN_r (L + 1)%nat).
      rewrite /compose//=.
      replace (λ x0 : nat, exp (- (x0 + (L + 1) - (L + 1))%nat))
        with (λ x0 : nat, exp (- x0)%nat).
      { apply ex_exp_geo_series. }
      funexti.
      do 3 f_equal.
      OK.
    }
    { intros ???.
      rewrite Rabs_right.
      2: {
        apply Rle_ge.
        apply RInt_ge_0; OK.
        { apply PCts_RInt. apply L4. }
        intros ??. apply L5; OK.
      }
      rewrite /B.
      replace (RInt (λ x0 : R, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_ρ (L + 1) n0 x0 * F n0 x0) 0 1)
         with (RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * RInt (λ x0 : R, NegExp_ρ (L + 1) n0 x0 * F n0 x0) 0 1).
      2: {
        rewrite RInt_Rmult. { f_equal; funexti; OK. }
        apply ex_RInt_mult.
        { apply PCts_RInt. apply NegExp_ρ_PCts. }
        { apply PCts_RInt. apply HPcts. }
      }
      have HH : 0 <= RInt (λ x0 : R, NegExp_ρ (L + 1) n0 x0 * F n0 x0) 0 1.
      { apply RInt_ge_0; OK.
        {  apply ex_RInt_mult.
           { apply PCts_RInt. apply NegExp_ρ_PCts. }
           { apply PCts_RInt. apply HPcts. }
        }
        intros ??.
        apply Rmult_le_pos.
        { apply NegExp_ρ_nn; OK. }
        { apply Hbound. OK. }
      }
      replace (1 * 1 * exp (- (n0 - (L + 1))%nat) * M) with (1 * 1 * (exp (- (n0 - (L + 1))%nat) * M)) by OK.
      apply Rmult_le_compat; OK.
      { apply Rmult_le_pos.
        { apply RealDecrTrial_μnn; OK. }
        { apply Iverson_nonneg. }
      }
      { apply Rmult_le_compat; OK.
        { apply RealDecrTrial_μnn; OK. }
        { apply Iverson_nonneg. }
        { apply RealDecrTrial_μ_le_1; OK. }
        { apply Iverson_le_1. }
      }
      rewrite -(Rabs_right _ (Rle_ge _ _ HH)).
      etrans.
      { eapply (abs_RInt_le_const _ _ _ (exp (- (n0 - (L + 1))%nat) * M)); OK.
        { apply PCts_RInt;  OK.
          apply PCts_mult.
          { apply NegExp_ρ_PCts. }
          { apply HPcts. }
        }
        intros ??.
        rewrite Rabs_right.
        2: {
          apply Rle_ge; OK.
          rewrite /B.
          apply Rmult_le_pos.
          { apply NegExp_ρ_nn. }
          { apply Hbound. OK. }
        }
        apply Rmult_le_compat.
        { apply NegExp_ρ_nn. }
        { apply Hbound; OK. }
        { apply NegExp_ρ_ub; OK. }
        { apply Hbound; OK. }
     }
     OK.
    }
    { intros ?. apply Fubini_Step_ex_x; OK.  }
Qed.

  (** QuadExchange3: Corresponds to HR3 in gauss.v.
      Swaps the two innermost integrals (Fubini's theorem).
      Proof: Apply SeriesC_ext twice to reduce to fixed n and k, then use Fubini_Step_eq.
      Need to show B is piecewise continuous in both variables (PCts2). *)
  Local Lemma QuadExchange3 {F L} (HPcts : ∀ x1, PCts (F x1) 0 1) :
    (SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x : R, RInt (λ x0 : R, B F L x n k x0) 0 1) 0 1))) =
    (SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1))).
  Proof.
    apply SeriesC_ext; intros n.
    apply SeriesC_ext; intros k.
    apply Fubini_Step_eq.
    apply B_PCts2.
    apply HPcts.
  Qed.

  (** QuadExchange4: Corresponds to HR2 in gauss.v.
      Swaps the two outer series (n ↔ k).
      Proof: Define B' : nat × nat → R := fun '(n,k) => RInt(...). Show the double series
      converges absolutely, then apply series commutativity (Fubini for series). *)
  Local Lemma QuadExchange4 M {F L} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    (SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1))) =
    (SeriesC (λ k : nat, SeriesC (λ n : nat, RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1))).
  Proof.
    have HM : 0 <= M.
    { have X : 0 <= 0 <= 1 by OK. have ? := Hbound 0%nat 0 X. OK. }
    rewrite SeriesC_nat.
    rewrite SeriesC_nat.
    replace (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1))
       with (λ n : nat, Series.Series (λ k : nat, RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1)).
    2: { f_equal; funexti. rewrite SeriesC_nat. done. }
    replace (λ k : nat, SeriesC (λ n : nat, RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1))
       with (λ k : nat, Series.Series (λ n : nat, RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1)).
    2: { f_equal; funexti. rewrite SeriesC_nat. done. }

    pose BB : nat * nat → R := fun '(n, k) => RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1.
    suffices HB : Series.Series (λ b : nat, Series.Series (λ a : nat, BB (a, b))) = Series.Series (λ a : nat, Series.Series (λ b : nat, BB (a, b))).
    { rewrite /BB in HB.
      rewrite HB.
      f_equal; funexti.
    }

    have L3 : ∀ a b, PCts2 (λ x y : R, B F L y a b x) 0 1 0 1.
    { intros ??.
      apply PCts2_mult; [apply PCts2_mult; [apply PCts2_mult|]|].
      { apply PCts_const_y. apply RealDecrTrial_μ_PCts. }
      { apply PCts_const_y.
        apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply PCts_const_x. apply NegExp_ρ_PCts. }
      { apply PCts_const_x. apply HPcts. }
    }

    have L4 : ∀ (a : nat) (b : nat), ∀ x, PCts (λ x0 : R, B F L x0 a b x) 0 1.
    { intros ???.
      apply PCts_mult; [apply PCts_mult; [apply PCts_mult|]|].
      { apply RealDecrTrial_μ_PCts. }
      { apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
    }

    have L5 : ∀ n n0 : nat, ∀ x x0 : R, 0 <= x <= 1 → 0 <= x0 <= 1 → 0 <= B F L x n n0 x0.
    { intros ??????.
      rewrite /B.
      apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
        { apply NegExp_ρ_nn. }
        { apply Hbound. OK. }
    }

    have HB2 : ∀ a b, ex_RInt (λ x0 : R, RInt (λ x : R, B F L x a b x0) 0 1) 0 1.
    { intros ??.
      apply Fubini_Step_ex_x.
      apply L3.
    }

    have HB1 : ∀ a b : nat, 0 <= BB (a, b).
    { intros ??.
      rewrite /BB.
      apply RInt_ge_0; OK.
      intros ??.
      apply RInt_ge_0; OK.
      { apply PCts_RInt. apply L4. }
      intros ??.
      apply L5; OK.
    }

    have HH1 : ∀ a b x0, 0 <= x0 <= 1 → 0 <= RInt (λ x : R, B F L x a b x0) 0 1.
    { intros ????.
      apply RInt_ge_0; OK.
      { apply PCts_RInt. apply L4. }
      intros ??.
      apply L5; OK.
    }

    have HH2 : ∀ a b, 0 <= RInt (λ x0 : R, RInt (λ x : R, B F L x a b x0) 0 1) 0 1.
    { intros ??.
      apply RInt_ge_0; OK.
      intros ??.
      apply RInt_ge_0; OK.
      2: {  intros ??. apply L5; OK. }
      { apply PCts_RInt. apply L4. }
    }

    have HBB : ∀ a b t t0, 0 <= t <= 1 → 0 <= t0 <= 1 → B F L t0 a b t <= 1 / fact a * 1 * exp (- (b - (L + 1))%nat) * M.
    { intros ??????.
      rewrite /B.
      apply Rmult_le_compat.
      2: apply Hbound; OK.
      3: apply Hbound; OK.
      { apply Rmult_le_pos; [apply Rmult_le_pos|].
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
        { apply NegExp_ρ_nn. }
      }
      apply Rmult_le_compat.
      { apply Rmult_le_pos.
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
      }
      { apply NegExp_ρ_nn. }
      2: { apply NegExp_ρ_ub. }
      apply Rmult_le_compat.
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
      2: apply Iverson_le_1.
      apply RealDecrTrial_μ_ub.
      OK.
    }

    have HB3 : ∀ a b : nat, BB (a, b) <= (1 / fact a) * 1 * exp (- (b - (L + 1))%nat) * M.
    { intros ??.
      rewrite /BB.
      rewrite -(Rabs_right _ (Rle_ge _ _ (HH2 _ _))).
      etrans.
      { rewrite /B.
        eapply (abs_RInt_le_const _ _ _ ((1 / fact a) * 1 * exp (- (b - (L + 1))%nat) * M)); OK.
        { apply HB2. }
        { intros ??.
          etrans.
          { eapply (abs_RInt_le_const _ _ _ ((1 / fact a) * 1 * exp (- (b - (L + 1))%nat) * M)); OK.
            { apply PCts_RInt. apply L4. }
            intros ??.
            rewrite (Rabs_right _ (Rle_ge _ _ (L5 _ _ _ _ _ _))); OK.
          }
          { OK. }
        }
      }
      OK.
    }

    apply (@fubini_pos_series BB); OK.
    { intros n.
      rewrite ex_seriesC_nat.
      apply (ex_seriesC_le _ (fun b => (* (1 / fact a) *) 1 * 1 * exp (- (b - (L + 1))%nat) * M)).
      { intros ?; split.
        { apply HB1. }
        etrans; first apply HB3.
        apply Rmult_le_compat; OK.
        { apply Rmult_le_pos; [apply Rmult_le_pos|]; OK.
          { apply Rdiv_INR_ge_0.  }
          { apply Rexp_nn. }
        }
        apply Rmult_le_compat; OK.
        { apply Rmult_le_pos; OK.
          apply Rdiv_INR_ge_0.
        }
        { apply Rexp_nn. }
        repeat rewrite Rmult_1_r.
        rewrite Rdiv_def.
        rewrite Rmult_1_l.
        replace 1 with (/ 1) by OK.
        apply Rinv_le_contravar; OK.
        replace 1 with (INR 1%nat) by OK.
        apply le_INR.
        rewrite Nat.le_succ_l.
        apply lt_O_fact.
      }
      { apply ex_seriesC_scal_r.
        apply ex_seriesC_scal_l.
        apply (ex_SeriesC_nat_shiftN_r (L + 1)%nat).
        rewrite /compose//=.
        replace (λ x0 : nat, exp (- (x0 + (L + 1) - (L + 1))%nat))
          with (λ x0 : nat, exp (- x0)%nat).
        { apply ex_exp_geo_series. }
        funexti.
        do 3 f_equal.
        OK.
      }
    }
    { rewrite ex_seriesC_nat.
      apply (ex_seriesC_le _ (fun (n : nat) => / fact n * SeriesC (λ n0 : nat, 1 * 1 * exp (- (n0 - (L + 1))%nat) * M) )).
      { intros ?.
        rewrite -SeriesC_nat.
        split.
        { apply SeriesC_ge_0'.
          intros ?.
          apply HB1.
        }
        etrans.
        { apply SeriesC_le.
          { intros ?.
            split.
            { apply HB1. }
            { apply HB3. }
          }
          apply ex_seriesC_scal_r.
          apply ex_seriesC_scal_l.
          apply (ex_SeriesC_nat_shiftN_r (L + 1)%nat).
          rewrite /compose//=.
          replace (λ x0 : nat, exp (- (x0 + (L + 1) - (L + 1))%nat))
            with (λ x0 : nat, exp (- x0)%nat).
          { apply ex_exp_geo_series. }
          funexti.
          do 3 f_equal.
          OK.
        }
        right.
        rewrite -SeriesC_scal_l.
        apply SeriesC_ext; intros ?.
        OK.
      }
      { apply ex_seriesC_scal_r.
        rewrite -ex_seriesC_nat.
        apply ex_exp_series.
      }
    }
  Qed.

  (** QuadExchange5: Corresponds to HR5 in gauss.v.
      Exchanges the series (over n) with the integral (over x0).
      Proof: Apply SeriesC_ext to reduce to fixed k, then use FubiniIntegralSeries_Strong
      with bounding sequence. The key is showing the series of integrals dominates. *)
  Local Lemma QuadExchange5 M {F L} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    (SeriesC (λ k : nat, SeriesC (λ n : nat, RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1))) =
    (SeriesC (λ k : nat, RInt (λ x0 : R, SeriesC (λ n : nat, RInt (λ x : R, B F L x n k x0) 0 1)) 0 1)).
  Proof.
    apply SeriesC_ext; intros k.
    rewrite SeriesC_nat.
    replace (λ x0 : R, SeriesC (λ n : nat, RInt (λ x : R, B F L x n k x0) 0 1))
       with (λ x0 : R, Series.Series (λ n : nat, RInt (λ x : R, B F L x n k x0) 0 1)).
    2: { f_equal; funexti. rewrite SeriesC_nat. done. }
    symmetry.

    have L3 : ∀ n n0 : nat,  PCts2 (λ x y : R, B F L y n k x) 0 1 0 1 .
    { intros ??.
      apply PCts2_mult; [apply PCts2_mult; [apply PCts2_mult|]|].
      { apply PCts_const_y. apply RealDecrTrial_μ_PCts. }
      { apply PCts_const_x.
        apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply PCts_const_x. apply NegExp_ρ_PCts. }
      { apply PCts_const_x. apply HPcts. }
    }

    have L5 : ∀ n n0 : nat, ∀ x x0 : R, 0 <= x <= 1 → 0 <= x0 <= 1 → 0 <= B F L x n n0 x0.
    { intros ??????.
      rewrite /B.
      apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
        { apply RealDecrTrial_μnn. OK. }
        { apply Iverson_nonneg. }
        { apply NegExp_ρ_nn. }
        { apply Hbound. OK. }
    }
    have L4 : ∀ n : nat, ∀ x1 x0, PCts (λ x : R, B F L x n x0 x1) 0 1.
    { intros ???.
      apply PCts_mult; [apply PCts_mult; [apply PCts_mult|]|].
      { apply RealDecrTrial_μ_PCts. }
      { apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply PCts_cts.
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
    }

    have L1 : ∀ n x0, 0 < x0 < 1 → 0 <= SeriesC (λ k : nat, RInt (λ x : R, B F L x n k x0) 0 1).
    { intros ???.
      apply SeriesC_ge_0'.
      intros ?.
      apply RInt_ge_0; OK.
      { apply PCts_RInt. apply L4. }
      intros ??.
      apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
      { apply RealDecrTrial_μnn. OK. }
      { apply Iverson_nonneg. }
      { apply NegExp_ρ_nn. }
      { apply Hbound. OK. }
    }

    symmetry.
    eapply (FubiniIntegralSeries_Strong (fun n0 => ((1 / fact n0 * 1 * (* exp (- (n0 - (L + 1))%nat) *) 1 * M)))); OK.
    { intros ???.
      apply RInt_ge_0; OK.
      { apply PCts_RInt. apply L4. }
      intros ??. apply L5; OK.
    }
    { rewrite ex_seriesC_nat.
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_r.
      setoid_rewrite Rdiv_def.
      apply ex_seriesC_scal_l.
      rewrite -ex_seriesC_nat.
      apply ex_exp_series.
    }
    { intros ???.
      rewrite Rabs_right.
      2: {
        apply Rle_ge.
        apply RInt_ge_0; OK.
        { apply PCts_RInt. apply L4. }
        intros ??. apply L5; OK.
      }
      rewrite /B.
      replace (λ x0 : R, RealDecrTrial_μ x0 0 n * Iverson (not ∘ Zeven) n * NegExp_ρ (L + 1) k x * F k x)
        with (λ x0 : R, RealDecrTrial_μ x0 0 n * (Iverson (not ∘ Zeven) n * (NegExp_ρ (L + 1) k x * F k x))) by (funexti; OK).
      rewrite -RInt_Rmult'.
      2: {
        apply ex_RInt_mult.
        { apply ex_RInt_const. }
        { apply PCts_RInt. apply RealDecrTrial_μ0_PCts. }
      }
      have HH : 0 <= RInt (λ x0 : R, RealDecrTrial_μ x0 0 n) 0 1.
      { apply RInt_ge_0; OK.
        { apply PCts_RInt. apply RealDecrTrial_μ_PCts. }
        intros ??. apply RealDecrTrial_μnn. OK.
      }
      replace (1 / fact n * 1 * 1 * M) with (1 / fact n * (1 * 1 * M)) by OK.
      apply Rmult_le_compat; OK.
      { apply Rmult_le_pos.
        { apply Iverson_nonneg. }
        apply Rmult_le_pos.
        { apply NegExp_ρ_nn. }
        { apply Hbound; OK. }
      }
      2: {
        rewrite Rmult_assoc.
        apply Rmult_le_compat; OK.
        { apply Iverson_nonneg. }
        { apply Rmult_le_pos.
          { apply NegExp_ρ_nn. }
          { apply Hbound; OK. }
        }
        { apply Iverson_le_1. }
        apply Rmult_le_compat; OK.
        { apply NegExp_ρ_nn. }
        { apply Hbound; OK. }
        { apply NegExp_ρ_le_1. }
        { apply Hbound. OK. }
      }
      rewrite -(Rabs_right _ (Rle_ge _ _ HH)).
      etrans.
      { eapply (abs_RInt_le_const _ _ _ (/ fact n)); OK.
        { apply PCts_RInt;  OK.
          apply RealDecrTrial_μ_PCts.
        }
        intros ??.
        rewrite Rabs_right.
        2: {
          apply Rle_ge; OK.
          apply RealDecrTrial_μnn; OK.
        }
        replace (/ fact n) with (1 / fact n) by OK.
        apply RealDecrTrial_μ_ub; OK.
     }
     OK.
    }
    { intros ?. apply Fubini_Step_ex_x; OK. }
  Qed.


  Local Lemma QuadExchange6  M {F : nat → R → R} {L} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    RInt (λ x0 : R, SeriesC (λ x : nat, RealDecrTrial_μ0 x0 x * Iverson Zeven x * F L x0)) 0 1 =
    SeriesC (λ x : nat, RInt (λ x0 : R, RealDecrTrial_μ0 x0 x * Iverson Zeven x * F L x0) 0 1).
  Proof.
    have HP : ∀ (x : R) (n : nat), 0 < x < 1 → 0 <= RealDecrTrial_μ0 x n * Iverson Zeven n * F L x.
    { intros ???.
      apply Rmult_le_pos; [apply Rmult_le_pos|].
      { apply RealDecrTrial_μ0nn; OK. }
      { apply Iverson_nonneg. }
      { apply Hbound; OK. }
    }
    symmetry.
    apply (FubiniIntegralSeriesC_Strong (fun n => 1 / (fact n) * 1 * M)); OK.
    2: {
      intros ???.
      rewrite Rabs_right.
      { apply Rmult_le_compat.
        2: apply Hbound; OK.
        3: apply Hbound; OK.
        { apply Rmult_le_pos.
          { apply RealDecrTrial_μ0nn; OK. }
          { apply Iverson_nonneg. }
        }
        apply Rmult_le_compat.
        { apply RealDecrTrial_μ0nn; OK. }
        { apply Iverson_nonneg. }
        { apply RealDecrTrial_μ0_ub; OK. }
        { apply Iverson_le_1. }
      }
      { apply Rle_ge.
        apply Rmult_le_pos; [apply Rmult_le_pos|].
        { apply RealDecrTrial_μ0nn; OK. }
        { apply Iverson_nonneg. }
        { apply Hbound; OK. }
      }
    }
    { setoid_rewrite Rdiv_def.
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_l.
      rewrite -ex_seriesC_nat.
      apply ex_exp_series.
    }
    { intros ?.
      apply ex_RInt_mult.
      2: { apply PCts_RInt; apply HPcts. }
      apply ex_RInt_Rmult'.
      apply PCts_RInt.
      apply RealDecrTrial_μ0_PCts.
    }
  Qed.

  Local Lemma QuadExchange7 M {F L} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    (SeriesC (λ k : nat, RInt (λ x : R, Iverson (eq L) k * exp (- (x + (k - L)%nat)) * F k x) 0 1)) =
    (RInt (λ x : R, SeriesC (λ k : nat, Iverson (eq L) k * (exp (- (x + (k - L)%nat)) * F k x))) 0 1).
  Proof.
    have HP : ∀ (x : R) (k : nat), 0 < x < 1 → 0 <= Iverson (eq L) k * exp (- (x + (k - L)%nat)) * F k x.
    { intros ???.
      apply Rmult_le_pos; [apply Rmult_le_pos|].
      { apply Iverson_nonneg. }
      { apply Rexp_nn. }
      { apply Hbound; OK. }
    }
    symmetry.
    replace (λ x : R, SeriesC (λ k : nat, Iverson (eq L) k * (exp (- (x + (k - L)%nat)) * F k x)))
       with (λ x : R, SeriesC (λ k : nat, Iverson (eq L) k * exp (- (x + (k - L)%nat)) * F k x)).
    2: { funexti. f_equal; funexti; OK. }
    symmetry.
    apply (FubiniIntegralSeriesC_Strong (fun n => 1 * exp (- ((n - L)%nat)) * M)); OK.
    2: {
      intros ???.
      rewrite Rabs_right.
      { apply Rmult_le_compat.
        2: apply Hbound; OK.
        3: apply Hbound; OK.
        { apply Rmult_le_pos.
          { apply Iverson_nonneg. }
          { apply Rexp_nn. }
        }
        apply Rmult_le_compat.
        { apply Iverson_nonneg. }
        { apply Rexp_nn. }
        { apply Iverson_le_1. }
        { apply exp_mono.
          suffices ? : 0 <= x by OK.
          OK.
        }
      }
      { apply Rle_ge.
        apply Rmult_le_pos; [apply Rmult_le_pos|].
        { apply Iverson_nonneg. }
        { apply Rexp_nn. }
        { apply Hbound; OK. }
      }
    }
    { apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_l.
      apply (ex_SeriesC_nat_shiftN_r (L)%nat).
      rewrite /compose//=.
      replace (λ x0 : nat, exp (- (x0 + (L) - (L))%nat))
        with (λ x0 : nat, exp (- x0)%nat).
      { apply ex_exp_geo_series. }
      funexti.
      do 3 f_equal.
      OK.
    }
    { intros ?.
      apply ex_RInt_mult.
      2: { apply PCts_RInt; apply HPcts. }
      apply ex_RInt_Rmult.
      apply PCts_RInt.
      apply PCts_cts.
      intros ??.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
  Qed.

  Local Lemma QuadExchange8 M {F : nat → R → R} {L} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson Zeven n * F L x)) 0 1) =
    (SeriesC (λ n : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n * Iverson Zeven n * F L x) 0 1)).
  Proof.
    have HP : ∀ (x : R) (n : nat), 0 < x < 1 → 0 <= RealDecrTrial_μ x 0 n * Iverson Zeven n * F L x.
    { intros ???.
      apply Rmult_le_pos; [apply Rmult_le_pos|].
      { apply RealDecrTrial_μnn; OK. }
      { apply Iverson_nonneg. }
      { apply Hbound; OK. }
    }
    symmetry.
    apply (FubiniIntegralSeriesC_Strong (fun n => 1 / (fact n) * 1 * M)); OK.
    2: {
      intros ???.
      rewrite Rabs_right.
      { apply Rmult_le_compat.
        2: apply Hbound; OK.
        3: apply Hbound; OK.
        { apply Rmult_le_pos.
          { apply RealDecrTrial_μnn; OK. }
          { apply Iverson_nonneg. }
        }
        apply Rmult_le_compat.
        { apply RealDecrTrial_μnn; OK. }
        { apply Iverson_nonneg. }
        { apply RealDecrTrial_μ_ub; OK. }
        { apply Iverson_le_1. }
      }
      { apply Rle_ge.
        apply Rmult_le_pos; [apply Rmult_le_pos|].
        { apply RealDecrTrial_μnn; OK. }
        { apply Iverson_nonneg. }
        { apply Hbound; OK. }
      }
    }
    { setoid_rewrite Rdiv_def.
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_l.
      rewrite -ex_seriesC_nat.
      apply ex_exp_series.
    }
    { intros ?.
      apply ex_RInt_mult.
      2: { apply PCts_RInt; apply HPcts. }
      apply ex_RInt_Rmult'.
      apply PCts_RInt.
      apply RealDecrTrial_μ_PCts.
    }
  Qed.

  Local Lemma g_expectation M {F : nat → R → R} {L} (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    is_RInt (g F L) 0 1 (NegExp_CreditV F L).
  Proof.
    (* have Hex : ∀ (a b : R), ex_RInt F a b.
    { intros ??. apply PCts_RInt. by apply IPCts_PCts. } *)
    suffices H : RInt (g F L) 0 1 = NegExp_CreditV F L.
    { rewrite -H. apply (RInt_correct (V := R_CompleteNormedModule)).
      eapply (g_ex_RInt); OK. }

    (* Unfold everything that involves F *)
    rewrite /g.
    rewrite /hx.
    rewrite /RealDecrTrial_CreditV.
    rewrite /NegExp_CreditV.

    (* Step 1: Split the series *)
    replace
      (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * (Iverson Zeven n * F L x + Iverson (not ∘ Zeven) n * SeriesC (λ k : nat, RInt (λ x0 : R, NegExp_ρ (L + 1) k x0 * F k x0) 0 1)))) 0 1)
        with
      (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson Zeven n * F L x) +
                SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_ρ (L + 1) k x0 * F k x0) 0 1))) 0 1); last first.
    { apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite -SeriesC_plus.
      2: {
        apply (ex_seriesC_le _ (BUB M)); [|apply BUB_SeriesC].
        intros n; split.
        { apply Rmult_le_pos; [apply Rmult_le_pos|]; OK.
          { apply RealDecrTrial_μnn. OK. }
          { apply Iverson_nonneg. }
          { apply Hbound. OK. }
        }
        { apply Rmult_le_compat.
          { apply Rmult_le_pos.
            { apply RealDecrTrial_μnn. OK. }
            { apply Iverson_nonneg. }
          }
          { apply Hbound; OK. }
          { rewrite -(Rmult_1_r (1 / fact n)).
            apply Rmult_le_compat.
            { apply RealDecrTrial_μnn. OK. }
            { apply Iverson_nonneg. }
            { apply RealDecrTrial_μ_ub. OK. }
            { apply Iverson_le_1. }
          }
          { apply Hbound; OK. }
        }
      }
      2: {
        apply (ex_seriesC_le _ (λ n : nat, SeriesC (λ k : nat, (1 / fact n) * (exp (-(k-(L + 1))%nat)) * M) )).
        { intros ?.
          split.
          { apply SeriesC_ge_0'.
            intros ?.
            apply RInt_ge_0; OK.
            { apply ex_RInt_mult; [apply ex_RInt_mult|].
              { apply ex_RInt_const. }
              { apply PCts_RInt, NegExp_ρ_PCts. }
              { apply PCts_RInt, HPcts. }
            }
            { intros ??.
              apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
              { apply RealDecrTrial_μnn; OK. }
              { apply Iverson_nonneg. }
              { apply NegExp_ρ_nn. }
              { apply Hbound; OK. }
            }
          }
          apply SeriesC_le.
          { intros n0.
            have HH : (0 <= RInt (λ x0 : R, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_ρ (L + 1) n0 x0 * F n0 x0) 0 1).
            { apply RInt_ge_0; OK.
              { apply ex_RInt_mult; [apply ex_RInt_mult|].
                { apply ex_RInt_const. }
                { apply PCts_RInt, NegExp_ρ_PCts. }
                { apply PCts_RInt, HPcts. }
              }
              { intros ??.
                apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
                { apply RealDecrTrial_μnn; OK. }
                { apply Iverson_nonneg. }
                { apply NegExp_ρ_nn. }
                { apply Hbound; OK. }
              }
            }
            split; OK.
            rewrite -(Rabs_right _ (Rle_ge _ _ HH)).
            etrans.
            { eapply (abs_RInt_le_const _ _ _ ((1 / fact n) * exp (- (n0 - (L + 1))%nat) * M)); OK.
              { apply ex_RInt_mult; [apply ex_RInt_mult|].
                { apply ex_RInt_const. }
                { apply PCts_RInt, NegExp_ρ_PCts. }
                { apply PCts_RInt, HPcts. }
              }
              { intros ??.
                rewrite (Rabs_right _ (Rle_ge _ _ _)).
                2: {
                  apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
                  { apply RealDecrTrial_μnn; OK. }
                  { apply Iverson_nonneg. }
                  { apply NegExp_ρ_nn. }
                  { apply Hbound; OK. }
                }
                apply Rmult_le_compat.
                2: apply Hbound; OK.
                3: apply Hbound; OK.
                { apply Rmult_le_pos; [apply Rmult_le_pos|].
                  { apply RealDecrTrial_μnn; OK. }
                  { apply Iverson_nonneg. }
                  { apply NegExp_ρ_nn. }
                }
                apply Rmult_le_compat.
                2: apply NegExp_ρ_nn.
                3: apply NegExp_ρ_ub.
                { apply Rmult_le_pos.
                  { apply RealDecrTrial_μnn; OK. }
                  { apply Iverson_nonneg. }
                }
                rewrite -(Rmult_1_r (1 / _)).
                apply Rmult_le_compat.
                { apply RealDecrTrial_μnn; OK. }
                { apply Iverson_nonneg. }
                { apply RealDecrTrial_μ_ub; OK. }
                { apply Iverson_le_1; OK. }
              }
            }
            { rewrite Rminus_0_r Rmult_1_l. right. OK. }
          }
          { apply ex_seriesC_scal_r.
            apply ex_seriesC_scal_l.
            apply (ex_SeriesC_nat_shiftN_r (L + 1)%nat).
            rewrite /compose//=.
            replace (λ x0 : nat, exp (- (x0 + (L + 1) - (L + 1))%nat))
               with (λ x0 : nat, exp (- x0)%nat).
            { apply ex_exp_geo_series. }
            funexti.
            do 3 f_equal.
            OK.
          }
        }
        { replace (λ n : nat, SeriesC (λ k : nat, 1 / fact n * exp (- (k - (L + 1))%nat) * M))
             with (λ n : nat,  / fact n * SeriesC (λ k : nat, exp (- (k - (L + 1))%nat) * M)).
          2: {
            funexti.
            rewrite -SeriesC_scal_l.
            apply SeriesC_ext; intros ?; OK.
          }
          apply ex_seriesC_scal_r.
          rewrite -ex_seriesC_nat.
          apply ex_exp_series.
        }
      }
      apply SeriesC_ext.
      intros n.
      rewrite Rmult_plus_distr_l.
      f_equal; OK.
      rewrite -SeriesC_scal_l.
      rewrite -SeriesC_scal_l.
      apply SeriesC_ext; intros ?.
      rewrite RInt_Rmult.
      2: {
        apply ex_RInt_mult.
        { apply PCts_RInt, NegExp_ρ_PCts. }
        { apply PCts_RInt, HPcts. }
      }
      rewrite RInt_Rmult.
      2: {
        apply ex_RInt_Rmult.
        apply ex_RInt_mult.
        { apply PCts_RInt, NegExp_ρ_PCts. }
        { apply PCts_RInt, HPcts. }
      }
      apply RInt_ext; intros ??. OK.
    }
    rewrite RInt_plus.
    2: { eapply QuadExists3; OK. }
    2: { eapply QuadExists4; OK. }
    rewrite /plus//=.

    (* Step 2: Quadruple limit exchange *)
    replace (RInt (λ x : R, SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_ρ (L + 1) k x0 * F k x0) 0 1))) 0 1)
       with (RInt (λ x : R, SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1))) 0 1); last first.
    { repeat f_equal. }

    rewrite (QuadExchange1 M); OK.
    rewrite (QuadExchange2 M); OK.
    rewrite QuadExchange3; OK.
    rewrite (QuadExchange4 M); OK.
    rewrite (QuadExchange5 M); OK.

    (* Step 3: Exchange on the RHS *)
    rewrite (QuadExchange8 M); OK.

    (* Step 4: Combine the outer two series *)
    rewrite -SeriesC_plus.
    2: {
      apply (ex_seriesC_le _ (λ n : nat, (/ fact n) * M)).
      { intros ?.
        have HH : (0 <= RInt (λ x : R, RealDecrTrial_μ x 0 n * Iverson (Zeven) n * F L x) 0 1).
        { apply RInt_ge_0; OK.
          { apply ex_RInt_mult; [apply ex_RInt_mult|].
            { apply RealDecrTrial_μ_ex_RInt. }
            { apply ex_RInt_const. }
            { apply PCts_RInt, HPcts. }
          }
          { intros ??.
            apply Rmult_le_pos; [apply Rmult_le_pos|].
            { apply RealDecrTrial_μnn; OK. }
            { apply Iverson_nonneg. }
            { apply Hbound; OK. }
          }
        }
        split; OK.
        rewrite -(Rabs_right _ (Rle_ge _ _ HH)).
        etrans.
        { eapply (abs_RInt_le_const _ _ _ ((1 / fact n) * 1 * M)); OK.
          { apply ex_RInt_mult; [apply ex_RInt_mult|].
            { apply RealDecrTrial_μ_ex_RInt. }
            { apply ex_RInt_const. }
            { apply PCts_RInt, HPcts. }
          }
          { intros ??.
            rewrite (Rabs_right _ (Rle_ge _ _ _)).
            2: {
              apply Rmult_le_pos; [apply Rmult_le_pos|].
              { apply RealDecrTrial_μnn; OK. }
              { apply Iverson_nonneg. }
              { apply Hbound; OK. }
            }
            apply Rmult_le_compat.
            2: apply Hbound; OK.
            3: apply Hbound; OK.
            { apply Rmult_le_pos.
              { apply RealDecrTrial_μnn; OK. }
              { apply Iverson_nonneg. }
            }
            apply Rmult_le_compat.
            { apply RealDecrTrial_μnn; OK. }
            { apply Iverson_nonneg. }
            { apply RealDecrTrial_μ_ub; OK. }
            { apply Iverson_le_1; OK. }
          }
        }
        { rewrite Rminus_0_r Rmult_1_l. right. OK. }
        }
        { apply ex_seriesC_scal_r.
          rewrite -ex_seriesC_nat.
          apply ex_exp_series.
        }
    }
    2: { eapply QuadExists1; OK. }

    (* Step 5: Combine the outer two integrals *)
    replace (λ x : nat,
       RInt (λ x0 : R, RealDecrTrial_μ x0 0 x * Iverson Zeven x * F L x0) 0 1 +
       RInt (λ x0 : R, @SeriesC nat numbers.Nat.eq_dec nat_countable (λ n : nat, RInt (λ x1 : R, B F L x1 n x x0) 0 1)) 0 1) with
      (λ x : nat,
       RInt (λ x0 : R, RealDecrTrial_μ x0 0 x * Iverson Zeven x * F L x0 + SeriesC (λ n : nat, RInt (λ x1 : R, B F L x1 n x x0) 0 1)) 0 1); last first.
    { funexti.
      rewrite (RInt_plus (V := R_CompleteNormedModule)); OK.
      { apply ex_RInt_mult.
        2: { apply PCts_RInt, HPcts. }
        apply ex_RInt_Rmult'.
        apply RealDecrTrial_μ_ex_RInt.
      }
      { eapply QuadExists2; OK. }
    }

    (* Step 6: Factor constant terms out of B *)
    rewrite /B.
    replace
      (λ x : nat,
       RInt
         (λ x0 : R,
            RealDecrTrial_μ x0 0 x * Iverson Zeven x * F L x0 +
            SeriesC
              (λ n : nat,
                 RInt (λ x1 : R, RealDecrTrial_μ x1 0 n * Iverson (not ∘ Zeven) n * NegExp_ρ (L + 1) x x0 * F x x0) 0 1))
         0 1) with
      (λ x : nat, RInt (λ x0 : R,
            RealDecrTrial_μ x0 0 x * Iverson Zeven x * F L x0 +
            NegExp_ρ (L + 1) x x0 * F x x0 *
            SeriesC
              (λ n : nat,
                 RInt (λ x1 : R, RealDecrTrial_μ x1 0 n * Iverson (not ∘ Zeven) n) 0 1))
         0 1); last first.
    { funexti.
      apply RInt_ext.
      intros ?.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ?.
      f_equal.
      rewrite -SeriesC_scal_l.
      apply SeriesC_ext; intros ?.
      rewrite RInt_Rmult.
      2: {
        apply ex_RInt_Rmult'.
        apply RealDecrTrial_μ_ex_RInt.
      }
      apply RInt_ext.
      intros ??.
      lra.
    }


    (* Separate the sum *)

    have Hclosed : (SeriesC (λ n : nat, RInt (λ x1 : R, RealDecrTrial_μ x1 0 n * Iverson (not ∘ Zeven) n) 0 1)) = exp (-1).
    { replace (λ n : nat, RInt (λ x1 : R, RealDecrTrial_μ x1 0 n * Iverson (not ∘ Zeven) n) 0 1)
         with (λ n : nat, Iverson (not ∘ Zeven) n * RInt (λ x1 : R, RealDecrTrial_μ x1 0 n) 0 1); last first.
      { apply functional_extensionality; intros n.
        rewrite RInt_Rmult. { f_equal. funexti. OK. }
        apply RealDecrTrial_μ_ex_RInt.
      }
      erewrite (SeriesC_ext
          (λ n : nat, Iverson (not ∘ Zeven) n * RInt (λ x1 : R, RealDecrTrial_μ x1 0 n) 0 1)
          (fun n => Iverson (not ∘ Zeven) n * (RealDecrTrial_μ0 1 (n + 1) - RealDecrTrial_μ0 0 (n + 1)))).
      2: {
        intros ?.
        f_equal.
        rewrite RealDecrTrial_μ_RInt.
        rewrite Iverson_True; OK.
        2: { rewrite /uncurry //=. OK. }
        rewrite Rmult_1_l.
        repeat f_equal; OK.
      }
      replace (λ n : nat, Iverson (not ∘ Zeven) n * (RealDecrTrial_μ0 1 (n + 1) - RealDecrTrial_μ0 0 (n + 1)))
         with (λ n : nat, Iverson (not ∘ Zeven) n * (RealDecrTrial_μ0 1 (n + 1))).
      2: {
        funexti.
        f_equal.
        rewrite /RealDecrTrial_μ0.
        rewrite pow_ne_zero; OK.
        rewrite pow_ne_zero; OK.
      }
      rewrite /RealDecrTrial_μ0.
      replace (SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * (1 ^ (n + 1) / fact (n + 1) - 1 ^ (n + 1 + 1) / fact (n + 1 + 1)))) with
              (SeriesC ((λ n : nat, Iverson (Zeven) n * (1 ^ (n) / fact (n) - (1) ^ (n + 1) / fact (n + 1))) ∘ S)).
      2: {
        apply SeriesC_ext.
        intros n.
        Opaque fact.
        rewrite //=.
        f_equal.
        { by rewrite Iverson_Zeven_Sn'. }
        repeat f_equal; OK; repeat rewrite pow1; OK.
        Transparent fact.
      }
      replace (λ n : nat, Iverson Zeven n * (1 ^ n / fact n - 1 ^ (n + 1) / fact (n + 1)))
         with (λ n : nat, Iverson Zeven n * ((-1) ^ n / fact n + (-1) ^ (n + 1) / fact (n + 1))).
      2: {
        funexti.
        rewrite /Iverson//=.
        case_decide; OK.
        repeat rewrite Rmult_1_l.
        rewrite even_pow_neg; OK.
        rewrite Zodd_neg_pow.
        2: {
          replace (x + 1)%nat with (S x) by OK.
          rewrite Nat2Z.inj_succ.
          apply Zodd_Sn.
          done.
        }
        rewrite //=.
        rewrite Rminus_def.
        f_equal.
        rewrite Rdiv_def.
        rewrite pow1.
        lra.
      }
      rewrite SeriesC_nat_shift_rev.
      2: {
        rewrite ex_seriesC_nat.
        apply Hexp_ex_even.
      }
      rewrite Iverson_True; OK.
      rewrite Rmult_1_l.
      rewrite pow_O.
      rewrite {1}/fact//=.
      rewrite ExpSeriesEven.
      OK.
    }
    replace (SeriesC (λ x : nat, RInt (λ x0 : R, RealDecrTrial_μ x0 0 x * Iverson Zeven x * F L x0 + NegExp_ρ (L + 1) x x0 * F x x0 * SeriesC (λ n : nat, RInt (λ x1 : R, RealDecrTrial_μ x1 0 n * Iverson (not ∘ Zeven) n) 0 1)) 0 1))
      with  (SeriesC (λ x : nat, RInt (λ x0 : R, RealDecrTrial_μ x0 0 x * Iverson Zeven x * F L x0 + NegExp_ρ (L + 1) x x0 * F x x0 * exp (-1)) 0 1)).
    2:  { f_equal; funexti. f_equal; funexti.  rewrite Hclosed. OK. }

    rewrite /RealDecrTrial_μ.
    rewrite /NegExp_ρ.
    rewrite /NegExp_ρ0.

    (* Simplify LHS *)
    replace (SeriesC (λ x : nat, RInt (λ x0 : R, Iverson (uncurry le) (0%nat, x) * RealDecrTrial_μ0 x0 (x - 0) * Iverson Zeven x * F L x0 + Iverson (le (L + 1)) x * (Iverson (Icc 0 1) x0 * exp (- (x0 + (x - (L + 1))%nat))) * F x x0 * exp (-1)) 0 1))
       with (SeriesC (λ x : nat, RInt (λ x0 : R, RealDecrTrial_μ0 x0 x * Iverson Zeven x * F L x0 + Iverson (le (L + 1)) x * (exp (- (x0 + (x - L)%nat))) * F x x0) 0 1)).
    2: {
      apply SeriesC_ext.
      intros ?.
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      symmetry.
      rewrite Iverson_True.
      2: { rewrite /uncurry//=. OK. }
      rewrite Rmult_1_l.
      f_equal.
      { repeat f_equal. OK. }
      repeat rewrite Rmult_assoc.
      rewrite {1}/Iverson.
      rewrite {2}/Iverson.
      case_decide; OK.
      rewrite Iverson_True.
      2: { rewrite /Icc//=. rewrite Rmin_left; OK. rewrite Rmax_right; OK.  }
      do 3 rewrite Rmult_1_l.
      rewrite Rmult_comm Rmult_assoc Rmult_comm.
      f_equal.
      rewrite -exp_plus.
      f_equal.
      rewrite minus_INR; OK.
      rewrite minus_INR; OK.
      rewrite plus_INR.
      rewrite //=.
      OK.
    }

    (* Simplify RHS *)
    replace (SeriesC (λ k : nat, RInt (λ x : R, Iverson (le L) k * (Iverson (Icc 0 1) x * exp (- (x + (k - L)%nat))) * F k x) 0 1))
       with (SeriesC (λ k : nat, RInt (λ x : R, Iverson (le L) k * exp (- (x + (k - L)%nat)) * F k x) 0 1)).
    2: {
      apply SeriesC_ext.
      intros ?.
      apply RInt_ext.
      intros ??.
      f_equal.
      f_equal.
      rewrite Iverson_True; OK.
      rewrite /Icc//=.
      OK.
    }

    (* Split series on LHS *)
    replace (SeriesC (λ x : nat, RInt (λ x0 : R, RealDecrTrial_μ0 x0 x * Iverson Zeven x * F L x0 + Iverson (le (L + 1)) x * exp (- (x0 + (x - L)%nat)) * F x x0) 0 1))
      with (SeriesC (λ x : nat, RInt (λ x0 : R, RealDecrTrial_μ0 x0 x * Iverson Zeven x * F L x0) 0 1) +
           SeriesC (λ x : nat, RInt (λ x0 : R, Iverson (le (L + 1)) x * exp (- (x0 + (x - L)%nat)) * F x x0) 0 1)).
    2: {
      rewrite -SeriesC_plus.
      2: {

        apply (ex_seriesC_le _ (λ n : nat, (1 / fact n) * 1 * M)).
        { intros ?.
          have HH : (0 <= RInt (λ x0 : R, RealDecrTrial_μ0 x0 n * Iverson Zeven n * F L x0) 0 1).
            { apply RInt_ge_0; OK.
              { apply ex_RInt_mult; [apply ex_RInt_mult|].
                { apply RealDecrTrial_μ0_ex_RInt. }
                { apply ex_RInt_const. }
                { apply PCts_RInt, HPcts. }
              }
              { intros ??.
                apply Rmult_le_pos; [apply Rmult_le_pos|].
                { apply RealDecrTrial_μ0nn; OK. }
                { apply Iverson_nonneg. }
                { apply Hbound; OK. }
              }
            }
            split; OK.
            rewrite -(Rabs_right _ (Rle_ge _ _ HH)).
            etrans.
            { eapply (abs_RInt_le_const _ _ _ ((1 / fact n) * 1 * M)); OK.
              { apply ex_RInt_mult; [apply ex_RInt_mult|].
                { apply RealDecrTrial_μ0_ex_RInt. }
                { apply ex_RInt_const. }
                { apply PCts_RInt, HPcts. }
              }
              { intros ??.
                rewrite (Rabs_right _ (Rle_ge _ _ _)).
                2: {
                  apply Rmult_le_pos; [apply Rmult_le_pos|].
                  { apply RealDecrTrial_μ0nn; OK. }
                  { apply Iverson_nonneg. }
                  { apply Hbound; OK. }
                }
                apply Rmult_le_compat.
                2: apply Hbound; OK.
                3: apply Hbound; OK.
                { apply Rmult_le_pos.
                  { apply RealDecrTrial_μ0nn; OK. }
                  { apply Iverson_nonneg. }
                }
                apply Rmult_le_compat.
                { apply RealDecrTrial_μ0nn; OK. }
                { apply Iverson_nonneg. }
                { apply RealDecrTrial_μ0_ub; OK. }
                { apply Iverson_le_1; OK. }
              }
            }
            { rewrite Rminus_0_r Rmult_1_l. right. OK. }
          }
          { apply ex_seriesC_scal_r.
            apply ex_seriesC_scal_r.
            setoid_rewrite Rdiv_def.
            apply ex_seriesC_scal_l.
            rewrite -ex_seriesC_nat.
            apply ex_exp_series.
        }
      }
      2: {
        apply (ex_seriesC_le _ (λ x : nat, exp (- ((x - L)%nat)) * M)).
        2: {
          apply ex_seriesC_scal_r.
          apply (ex_SeriesC_nat_shiftN_r L).
          rewrite /compose//=.
          replace (λ x : nat, exp (- (x + L - L)%nat)) with (λ x : nat, exp (- x)).
          { apply ex_exp_geo_series. }
          funexti.
          do 3 f_equal.
          rewrite //=; OK.
        }
        intros ?.
        have HH : (0 <= RInt (λ x0 : R, Iverson (le (L + 1)) n * exp (- (x0 + (n - L)%nat)) * F n x0) 0 1).
        { apply RInt_ge_0; OK.
          { apply ex_RInt_mult; [apply ex_RInt_mult|].
            { apply ex_RInt_const. }
            { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
              intros ??.
              apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
              by auto_derive.
            }
            { apply PCts_RInt, HPcts. }
          }
          { intros ??.
            apply Rmult_le_pos; [apply Rmult_le_pos|].
            { apply Iverson_nonneg. }
            { apply Rexp_nn. }
            { apply Hbound; OK. }
          }
        }
        split; OK.
        rewrite -(Rabs_right _ (Rle_ge _ _ HH)).
        etrans.
        { eapply (abs_RInt_le_const _ _ _ (1 * exp (- ((n - L)%nat)) * M)); OK.
          { apply ex_RInt_mult; [apply ex_RInt_mult|].
            { apply ex_RInt_const. }
            { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
              intros ??.
              apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
              by auto_derive.
            }
            { apply PCts_RInt, HPcts. }
          }
          { intros ??.
            rewrite (Rabs_right _ (Rle_ge _ _ _)).
            2: {
              apply Rmult_le_pos; [apply Rmult_le_pos|].
              { apply Iverson_nonneg. }
              { apply Rexp_nn. }
              { apply Hbound; OK. }
            }
            apply Rmult_le_compat.
            2: apply Hbound; OK.
            3: apply Hbound; OK.
            { apply Rmult_le_pos.
              { apply Iverson_nonneg. }
              { apply Rexp_nn. }
            }
            apply Rmult_le_compat.
            { apply Iverson_nonneg. }
            { apply Rexp_nn. }
            { apply Iverson_le_1; OK. }
            { apply exp_mono. OK. }
          }
        }
        { rewrite Rminus_0_r Rmult_1_l. right. OK. }
      }
      apply SeriesC_ext.
      intros ?.
      rewrite RInt_plus.
      2: {
        apply ex_RInt_mult.
        2: { apply PCts_RInt, HPcts. }
        apply ex_RInt_Rmult'.
        apply RealDecrTrial_μ0_ex_RInt.
      }
      2: {
        apply ex_RInt_mult.
        2: { apply PCts_RInt, HPcts. }
        apply ex_RInt_Rmult.
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      done.
    }

    (* Split series on RHS *)
    replace (SeriesC (λ k : nat, RInt (λ x : R, Iverson (le L) k * exp (- (x + (k - L)%nat)) * F k x) 0 1))
       with (SeriesC (λ k : nat, RInt (λ x : R, Iverson (le (L + 1)) k * exp (- (x + (k - L)%nat)) * F k x) 0 1) +
             SeriesC (λ k : nat, RInt (λ x : R, Iverson (eq L) k * exp (- (x + (k - L)%nat)) * F k x) 0 1)).
    2: {
      rewrite -SeriesC_plus.
      2: {
        apply (ex_seriesC_le _ (λ x : nat, exp (- ((x - L)%nat)) * M)).
        2: {
          apply ex_seriesC_scal_r.
          apply (ex_SeriesC_nat_shiftN_r L).
          rewrite /compose//=.
          replace (λ x : nat, exp (- (x + L - L)%nat)) with (λ x : nat, exp (- x)).
          { apply ex_exp_geo_series. }
          funexti.
          do 3 f_equal.
          rewrite //=; OK.
        }
        intros ?.
        have HH : (0 <= RInt (λ x0 : R, Iverson (le (L + 1)) n * exp (- (x0 + (n - L)%nat)) * F n x0) 0 1).
        { apply RInt_ge_0; OK.
          { apply ex_RInt_mult; [apply ex_RInt_mult|].
            { apply ex_RInt_const. }
            { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
              intros ??.
              apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
              by auto_derive.
            }
            { apply PCts_RInt, HPcts. }
          }
          { intros ??.
            apply Rmult_le_pos; [apply Rmult_le_pos|].
            { apply Iverson_nonneg. }
            { apply Rexp_nn. }
            { apply Hbound; OK. }
          }
        }
        split; OK.
        rewrite -(Rabs_right _ (Rle_ge _ _ HH)).
        etrans.
        { eapply (abs_RInt_le_const _ _ _ (1 * exp (- ((n - L)%nat)) * M)); OK.
          { apply ex_RInt_mult; [apply ex_RInt_mult|].
            { apply ex_RInt_const. }
            { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
              intros ??.
              apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
              by auto_derive.
            }
            { apply PCts_RInt, HPcts. }
          }
          { intros ??.
            rewrite (Rabs_right _ (Rle_ge _ _ _)).
            2: {
              apply Rmult_le_pos; [apply Rmult_le_pos|].
              { apply Iverson_nonneg. }
              { apply Rexp_nn. }
              { apply Hbound; OK. }
            }
            apply Rmult_le_compat.
            2: apply Hbound; OK.
            3: apply Hbound; OK.
            { apply Rmult_le_pos.
              { apply Iverson_nonneg. }
              { apply Rexp_nn. }
            }
            apply Rmult_le_compat.
            { apply Iverson_nonneg. }
            { apply Rexp_nn. }
            { apply Iverson_le_1; OK. }
            { apply exp_mono. OK. }
          }
        }
        { rewrite Rminus_0_r Rmult_1_l. right. OK. }
      }
      2: {
        apply (ex_seriesC_le _ (λ x : nat, exp (- ((x - L)%nat)) * M)).
        2: {
          apply ex_seriesC_scal_r.
          apply (ex_SeriesC_nat_shiftN_r L).
          rewrite /compose//=.
          replace (λ x : nat, exp (- (x + L - L)%nat)) with (λ x : nat, exp (- x)).
          { apply ex_exp_geo_series. }
          funexti.
          do 3 f_equal.
          rewrite //=; OK.
        }
        intros ?.
        have HH : (0 <= RInt (λ x0 : R, Iverson (eq L) n * exp (- (x0 + (n - L)%nat)) * F n x0) 0 1).
        { apply RInt_ge_0; OK.
          { apply ex_RInt_mult; [apply ex_RInt_mult|].
            { apply ex_RInt_const. }
            { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
              intros ??.
              apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
              by auto_derive.
            }
            { apply PCts_RInt, HPcts. }
          }
          { intros ??.
            apply Rmult_le_pos; [apply Rmult_le_pos|].
            { apply Iverson_nonneg. }
            { apply Rexp_nn. }
            { apply Hbound; OK. }
          }
        }
        split; OK.
        rewrite -(Rabs_right _ (Rle_ge _ _ HH)).
        etrans.
        { eapply (abs_RInt_le_const _ _ _ (1 * exp (- ((n - L)%nat)) * M)); OK.
          { apply ex_RInt_mult; [apply ex_RInt_mult|].
            { apply ex_RInt_const. }
            { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
              intros ??.
              apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
              by auto_derive.
            }
            { apply PCts_RInt, HPcts. }
          }
          { intros ??.
            rewrite (Rabs_right _ (Rle_ge _ _ _)).
            2: {
              apply Rmult_le_pos; [apply Rmult_le_pos|].
              { apply Iverson_nonneg. }
              { apply Rexp_nn. }
              { apply Hbound; OK. }
            }
            apply Rmult_le_compat.
            2: apply Hbound; OK.
            3: apply Hbound; OK.
            { apply Rmult_le_pos.
              { apply Iverson_nonneg. }
              { apply Rexp_nn. }
            }
            apply Rmult_le_compat.
            { apply Iverson_nonneg. }
            { apply Rexp_nn. }
            { apply Iverson_le_1; OK. }
            { apply exp_mono. OK. }
          }
        }
        { rewrite Rminus_0_r Rmult_1_l. right. OK. }
      }
      apply SeriesC_ext.
      intros ?.
      replace (RInt (λ x : R, Iverson (le (L + 1)) n * exp (- (x + (n - L)%nat)) * F n x) 0 1 + RInt (λ x : R, Iverson (eq L) n * exp (- (x + (n - L)%nat)) * F n x) 0 1)
        with  (plus (RInt (λ x : R, Iverson (le (L + 1)) n * exp (- (x + (n - L)%nat)) * F n x) 0 1) (RInt (λ x : R, Iverson (eq L) n * exp (- (x + (n - L)%nat)) * F n x) 0 1)).
      2: { by rewrite //=. }
      rewrite -(RInt_plus (V := R_CompleteNormedModule)).
      2: {
        apply ex_RInt_mult.
        2: { apply PCts_RInt, HPcts. }
        apply ex_RInt_Rmult.
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      2: {
        apply ex_RInt_mult.
        2: { apply PCts_RInt, HPcts. }
        apply ex_RInt_Rmult.
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite /plus//=.
      repeat rewrite Rmult_assoc.
      rewrite -Rmult_plus_distr_r.
      f_equal.
      rewrite /Iverson//=.
      case_decide; case_decide; case_decide; OK.
    }

    (* Now each term can be treated separately *)
    rewrite Rplus_comm.
    f_equal.
    rewrite (QuadExchange7 M); OK.
    rewrite -(QuadExchange6 M); OK.
    apply RInt_ext.
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    intros ??.
    rewrite SeriesC_scal_r.
    erewrite (SeriesC_Iverson_singleton L); OK.
    f_equal.
    rewrite Nat.sub_diag.
    rewrite //=.
    rewrite Rplus_0_r.
    rewrite -ExpSeriesEven.
    apply SeriesC_ext.
    intros ?.
    rewrite Rmult_comm.
    rewrite /Iverson//=.
    case_decide; OK.
    f_equal.
    rewrite /RealDecrTrial_μ0.
    rewrite even_pow_neg; OK.
    rewrite Rminus_def.
    f_equal; OK.
    repeat rewrite Rdiv_def.
    rewrite Ropp_mult_distr_l.
    f_equal.
    replace (- x ^ (n + 1)) with ((-1) * x ^ (n + 1)) by OK.
    replace ((- x) ^ (n + 1)) with (((-1) * x) ^ (n + 1)).
    2: { f_equal. OK. }
    rewrite Rpow_mult_distr.
    f_equal.
    rewrite Zodd_neg_pow; OK.
    replace (n + 1)%nat with (S n) by OK.
    rewrite Nat2Z.inj_succ.
    by apply Zodd_Sn.
  Qed.

  Local Lemma g'_expectation M {F : nat → R → R} {L}
    (HPcts : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= x <= 1 → 0 <= F n x <= M) :
    is_RInt (g' F L) 0 1 (NegExp_CreditV F L).
  Proof.
    apply (is_RInt_ext (g F L)).
    2: { eapply g_expectation; OK. }
    intros ??.
    rewrite /g'.
    rewrite Rmin_left in H; OK.
    rewrite Rmax_right in H; OK.
    rewrite /poke.
    case_decide; OK.
  Qed.

End credits.

Section program.
  Context `{!erisGS Σ}.
  Import Hierarchy.

  (* Tail-recursive Negative Exponential sampling*)
  Definition NegExp : val :=
    rec: "trial" "L" :=
      let: "x" := init #() in
      let: "y" := lazyDecrR #Nat.zero "x" in
      if: ("y" `rem` #2%Z = #0%Z) then
        ("L", "x")
      else
        "trial" ("L" + #1%Z).

  Lemma wp_NegExp_gen E (F : nat → R → R) {M} (Hnn : ∀ a b, 0 <= b <= 1 → 0 <= F a b <= M) (HP : ∀ x1 : nat, PCts (F x1) 0 1)  :
    ⊢ ∀ L, ↯ (NegExp_CreditV F L) -∗
           WP NegExp #L @ E
      {{ p, ∃ (vz : nat) (vr : R) (ℓ : val), ⌜p = PairV #(Z.of_nat vz)ℓ⌝ ∗ lazy_real ℓ vr ∗ ⌜0 <= vr < 1 ⌝ ∗ ↯(F vz vr)}}.
  Proof.
    (* have Hex : ∀ a b, ex_RInt F a b.
    { intros ??. apply PCts_RInt. by apply IPCts_PCts. } *)
    iLöb as "IH".
    iIntros (L) "Hε".
    rewrite {2}/NegExp.
    wp_pure.
    wp_apply wp_init; first done.
    iIntros (x) "Hx".
    iApply (wp_lazy_real_presample_adv_comp _ _ x _ (NegExp_CreditV F L) (g' F L)); auto.
    { intros ??.
      rewrite /g'/poke.
      case_decide; OK.
      apply g_nonneg; eauto.
      intros ???.
      apply Hnn.
      OK.
    }
    { eapply g'_expectation; OK. }
    iFrame.
    iIntros (xr) "(%Hrange & Hε & Hx)".

    (* Now: poke out the cases where we sampled 0 or 1 *)
    rewrite /g'/poke//=.
    case_decide.
    { iExFalso. iApply (ec_contradict with "Hε"). OK. }
    do 2 wp_pure.
    wp_bind (lazyDecrR _ _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hx Hε] IH"); last first.
    { iApply (wp_lazyDecrR_gen (hx F xr L) _ E $! _ x xr).
      by rewrite /g; iFrame.
      Unshelve.
      1: { exact (F L xr  + (NegExp_CreditV F (L + 1))). }
      1: {
        rewrite /hx.
        intro n.
        split.
        { apply Rplus_le_le_0_compat; apply Rmult_le_pos; try apply Iverson_nonneg.
          { apply Hnn.  OK. }
          { eapply NegExp_CreditV_nn; OK.
            intros ???. apply Hnn; OK.

          }
        }
        { apply Rplus_le_compat.
          { rewrite -{2}(Rmult_1_l (F L xr)).
            apply Rmult_le_compat_r; [|apply Iverson_le_1].
            apply Hnn; OK.
          }
          { rewrite -{2}(Rmult_1_l (NegExp_CreditV F (L + 1))).
            apply Rmult_le_compat_r; [|apply Iverson_le_1].
            eapply NegExp_CreditV_nn; OK.
            intros ???. apply Hnn; OK.
          }
        }
      }
    }
    iIntros (v) "(#IH & [%l (%Hv & Hε & Hx)])"; rewrite Hv.
    wp_pures.
    case_bool_decide.
    { have Heven : Zeven l.
      { inversion H0 as [H'].
        apply Z.rem_mod_eq_0 in H'; [|lia].
        by apply Zeven_bool_iff; rewrite Zeven_mod H' //. }
      wp_pures.
      iModIntro.
      iExists L, xr, x.
      iFrame.
      iSplitR; first done.
      unfold hx.
      iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ].  OK. }
      { apply Rmult_le_pos; [apply Iverson_nonneg |]. apply NegExp_CreditV_nn; OK.
        intros ???. apply Hnn; OK.
      }
      rewrite Iverson_True; last done.
      rewrite Rmult_1_l; iFrame.
      iPureIntro. OK.
    }
    { do 2 wp_pure.
      rewrite {1}/NegExp.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]; OK. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | eapply NegExp_CreditV_nn; OK ].
        intros ???. apply Hnn; OK.
      }
      rewrite Iverson_True; last first.
      { intro Hk; apply H0. f_equal.
        apply Zeven_bool_iff in Hk.
        rewrite Zeven_mod in Hk.
        apply Zeq_bool_eq in Hk.
        apply (Z.rem_mod_eq_0 l 2 ) in Hk; [by f_equal|lia].
      }
      rewrite Rmult_1_l.
      iSpecialize ("IH" $! (Nat.add L 1) with "Hε").
      rewrite Nat2Z.inj_add.
      iApply "IH".
    }
  Qed.

  (* NB. If this works, we don't need to generalize the theorem (or Gauss) to IPCts. *)
  Lemma wp_NegExp_gen' E (F : R → R) {M} (Hnn : ∀ x, 0 <= F x <= M) (HP : IPCts F)  :
    ⊢ ↯ (NegExp_CreditV' F) -∗ WP NegExp #0 @ E
      {{ p, ∃ (r : R) (ℓ : val), ⌜p = PairV #(Int_part r) ℓ⌝ ∗ lazy_real ℓ (frac_part r) ∗ ↯(F r)}}.
  Proof.
    iIntros "Hε".
    have H1 : (∀ (a : nat) (b : R), 0 <= b <= 1 → 0 <= F (a + b) <= M).
    { intros ???. apply Hnn.  }
    have H2 : (∀ x1 : nat, PCts (λ r : R, F (x1 + r)) 0 1).
    { intros ?.
      apply IPCts_PCts.
      by apply IPCts_shift.
    }
    (* Here, we actually also want to use the credits to avoid any integer *)
    iApply (pgl_wp_mono with "[Hε]").
    2: {
      iApply (wp_NegExp_gen E (fun n r => F (n+r)) H1 H2 $! 0%nat).
      iApply (ec_eq with "Hε").
      rewrite (@NegExp_CreditV_NegExp_CreditV' M); OK.
    }
    intros v.
    rewrite //=.
    iIntros "[%vz [%vr [%l [%Hl3 [H4 [%H6 H5]]]]]]".
    iExists (Z.to_nat vz + vr).
    iExists l.
    iFrame.
    iSplitR.
    { iPureIntro.
      rewrite Hl3 //=.
      repeat f_equal.
      rewrite plus_Int_part2.
      { rewrite Int_part_INR.
        rewrite -(Int_part_spec vr 0%Z).
        { rewrite Z2Nat.id; OK. }
        split; OK.
      }
      { have Hm : 0 <= 0 < 1 by OK.
        have Hm' : INR (Z.to_nat (Z.of_nat vz)) = IZR (Z.of_nat vz) + 0.
        { rewrite Nat2Z.id Rplus_0_r INR_IZR_INZ. OK. }
        destruct (Int_part_frac_part_spec (INR (Z.to_nat (Z.of_nat vz))) vz 0%R Hm Hm').
        rewrite -H0 Rplus_0_l.
        apply base_fp.
      }
    }
    { replace (frac_part (Z.to_nat vz + vr)) with vr.
      2: {
        destruct (Int_part_frac_part_spec (INR (Z.to_nat (Z.of_nat vz)) + vr) vz vr); OK.
        rewrite Nat2Z.id INR_IZR_INZ. OK.
      }
      iFrame.
      iApply (ec_eq with "H5").
      f_equal.
      f_equal.
      rewrite Nat2Z.id INR_IZR_INZ. OK.
    }
  Qed.

End program.


Section AccuracyBound.
  Context `{!erisGS Σ}.
  Import Hierarchy.

  (* A function which is 1 outside of the range [0, L] *)
  Definition AccF (L : R) : R → R := (fun x => Iverson (Iio 0) x + Iverson (Ioi L) x).

  Lemma AccF_IPCts L (HL : 0 <= L) : IPCts (AccF L).
  Proof.
    rewrite /IPCts.
    exists (fun _ => 1).
    exists (List.cons (fun _ => -1, 0, L) List.nil).
    split; last split.
    { intros ?.
      rewrite /fsum//=.
      rewrite /AccF.
      symmetry.
      rewrite {1}/Iverson.
      case_decide; rewrite /Icc//= in H; rewrite Rmin_left in H; OK; rewrite Rmax_right in H; OK.
      { rewrite Iverson_False.
        2: { rewrite /Iio. OK. }
        rewrite Iverson_False.
        2: { rewrite /Ioi. OK. }
        OK.
      }
      { rewrite {1} /Iverson.
        rewrite /Ioi//=.
        case_decide; rewrite /Iio in H0.
        { rewrite Iverson_False; OK. }
        { rewrite Iverson_True; OK. }
      }
    }
    { apply Forall_singleton.
      rewrite /IntervalFun_continuity.
      intros ??.
      apply Continuity.continuous_const.
    }
    {
      intros ?.
      apply Continuity.continuous_const.
    }
  Qed.

  Lemma NegExp_Int_AccF {L} :
    RInt_gen (λ r : R, AccF L r * exp (- r)) (at_point 0) (Rbar_locally Rbar.p_infty) = exp (- L).
  Proof.
    rewrite -NegExp_Int.
    (* Chasles *)
  Admitted.

  Lemma wp_NegExp_Accuracy E (β : R) (Hβ : 0 < β <= 1) :
    ⊢ ↯ β -∗ WP NegExp #0 @ E
        {{ p, ∃ (r : R) (ℓ : val), ⌜p = PairV #(Int_part r) ℓ⌝ ∗ lazy_real ℓ (frac_part r) ∗ ⌜0 <= r <= ln ( / β) ⌝}}.
  Proof.
    iIntros "Hε".
    iApply (pgl_wp_mono with "[Hε]").
    2: {
      iApply (wp_NegExp_gen' (M := (1 + 1)) E (AccF (ln (/ β)))).
      { intros x. rewrite /AccF.
        split.
        { apply Rplus_le_le_0_compat; apply Iverson_nonneg. }
        { apply Rplus_le_compat; apply Iverson_le_1. }
      }
      { apply AccF_IPCts.
        rewrite ln_Rinv; OK.
        suffices ? : ln β <= 0 by OK.
        rewrite -ln_1.
        apply Rcomplements.ln_le; OK.
      }
      { iApply (ec_eq with "Hε").
        rewrite /NegExp_CreditV'.
        rewrite NegExp_Int_AccF.
        rewrite ln_Rinv; OK.
        rewrite Ropp_involutive.
        rewrite exp_ln; OK.
      }
    }
    intros v.
    iIntros "[%r [%l [%H1 [H2 H3]]]]".
    iExists r.
    iExists l.
    iFrame.
    iSplitR.
    { rewrite H1. done. }
    rewrite /AccF/Iverson.
    case_decide.
    { iExFalso. iApply (ec_contradict with "H3"). case_decide; OK. }
    case_decide.
    { iExFalso. iApply (ec_contradict with "H3"). OK. }
    rewrite /Iio//= in H.
    rewrite /Ioi//= in H0.
    iPureIntro.
    split; OK.
  Qed.

End AccuracyBound.
