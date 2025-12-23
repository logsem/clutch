From clutch.eris.examples.math Require Import prelude series iverson sets improper piecewise.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** exp is nonnegative *)
Lemma Rexp_nn {z} : 0 <= exp z.
Proof. pose proof (exp_pos z); lra. Qed.
(* Proof. have ? := exp_pos z. lra. Qed. *)

(** exp x ∈ [0, 1] for x ≤ 0 *)
Lemma Rexp_range {z : R} : z <= 0 -> 0 <= exp z <= 1.
Proof.
  split; [apply Rexp_nn|].
  replace z with ((-1) * (-z)) by lra.
  replace (exp (-1 * - z)) with (/ exp (- z) ); last first.
  { apply (Rmult_eq_reg_l (exp (- z))).
    2: { pose proof (exp_pos (- z)); lra. }
    rewrite -Rdiv_def Rdiv_diag.
    2: { pose proof (exp_pos (- z)); lra. }
    rewrite -exp_plus.
    (* 2: { have ? := exp_pos (- z). lra. } *)
    (* 2: { have ? := exp_pos (- z). lra. } *)
    replace (- z + -1 * - z) with 0 by lra.
    by rewrite exp_0.
  }
  rewrite -Rinv_1.
  apply Rinv_le_contravar; [lra|].
  eapply Rle_trans.
  2: { eapply exp_ineq1_le. }
  lra.
Qed.

(** Strict monotonicity of exp *)
Lemma exp_mono_strict {x y : R} : x < y → exp x < exp y.
Proof. apply exp_increasing. Qed.

(** Monotonicity of exp *)
Lemma exp_mono {x y : R} : x <= y → exp x <= exp y.
Proof.
  intros H.
  destruct H.
  { apply exp_increasing in H. lra. }
  { by rewrite H. }
Qed.


Section ExpPowerSeries.

(** Even and odd subseries of the exponential series *)

(** Even powers are nonnegative *)
Lemma Zeven_pow {x} {n : nat} (H : Zeven (Z.of_nat n)) : 0 <= x ^ n.
Proof.
  destruct (Zeven_ex _ H) as [m Hm].
  rewrite -(Nat2Z.id n) Hm.
  rewrite Z2Nat.inj_mul; try lia.
  rewrite pow_mult.
  apply pow_le.
  apply pow2_ge_0.
Qed.

(** Odd powers of (-1) are (-1) *)
Lemma Zodd_neg_pow {n : nat} (H : Zodd (Z.of_nat n)) : (-1) ^ n = (-1).
Proof.
  destruct (Zodd_ex _ H) as [m Hm].
  rewrite -(Nat2Z.id n) Hm.
  rewrite Z2Nat.inj_add; try lia.
  rewrite Z2Nat.inj_mul; try lia.
  rewrite pow_add.
  rewrite pow_1.
  rewrite pow_mult.
  replace (((-1) ^ Z.to_nat 2)) with 1.
  { rewrite pow1. lra. }
  simpl. lra.
Qed.

(** Power series of exp *)
Definition Hpow x : R := @SeriesC _ numbers.Nat.eq_dec nat_countable (λ k : nat, x ^ k / fact k).

(** Even subseries of exp *)
Definition HpowE x : R := @SeriesC _ numbers.Nat.eq_dec nat_countable (λ k : nat, Iverson Zeven k * x ^ k / fact k).

(** Odd subseries of exp *)
Definition HpowO x : R := @SeriesC _ numbers.Nat.eq_dec nat_countable (λ k : nat, Iverson (not ∘ Zeven) k * x ^ k / fact k).

(** Shifted odd subseries of exp *)
Definition HpowOS x : R := @SeriesC _ numbers.Nat.eq_dec nat_countable ((λ k : nat, Iverson (not ∘ Zeven) k * x ^ k / fact k) ∘ S).

(** Shifted even subseries of exp *)
Definition HpowES x : R := @SeriesC _ numbers.Nat.eq_dec nat_countable ((λ k : nat, Iverson Zeven k * x ^ k / fact k) ∘ S).

(** Closed form for power series of exp *)
Lemma Hpow_cf {x} : Hpow x = exp x.
Proof. by rewrite /Hpow SeriesC_Series_nat -PSeries.PSeries_eq ElemFct.exp_Reals. Qed.

(** Existence of the exp power series *)
Lemma Hpow_ex : forall y, ex_seriesC (λ k : nat, y ^ k / fact k).
Proof.
  intro y.
  replace (λ k : nat, y ^ k / fact k) with (λ k : nat, / fact k * y ^ k); last first.
  { apply functional_extensionality. intros ?. lra. }
  have Hex : PSeries.ex_pseries (fun k => / fact k) y.
  { apply PSeries.CV_disk_correct.
    apply (PSeries.CV_disk_DAlembert _ _ 0); [| | intuition].
    { intros n.
      have ? : 0 < / fact n; [|lra].
      apply Rinv_0_lt_compat.
      apply INR_fact_lt_0.
    }
    { rewrite Lim_seq.is_lim_seq_Reals. apply Alembert_exp. }
  }
  rewrite PSeries.ex_pseries_R in Hex.
  by rewrite ex_seriesC_nat in Hex.
Qed.


(** Existence of even subseries of exp *)
Lemma HpowE_ex {x} : ex_seriesC (λ k : nat, Iverson Zeven k * x ^ k / fact k).
Proof.
  apply (ex_seriesC_le _ (λ k : nat, (Rabs x) ^ k / fact k)); last apply Hpow_ex.
  intros n.
  split.
  { rewrite /Iverson.
    case_decide; [|lra].
    rewrite Rmult_1_l.
    apply Rcomplements.Rdiv_le_0_compat; [|apply INR_fact_lt_0].
    by apply Zeven_pow.
  }
  { rewrite /Iverson.
    case_decide.
    { rewrite Rmult_1_l.
      rewrite Rdiv_def.
      apply Rmult_le_compat_r.
      { have HH := INR_fact_lt_0 n. apply Rinv_0_lt_compat in HH. lra. }
      apply pow_maj_Rabs.
      lra.
    }
    { rewrite Rmult_0_l Rdiv_0_l.
      apply Rcomplements.Rdiv_le_0_compat; [|apply INR_fact_lt_0].
      apply pow_le.
      apply Rabs_pos.
    }
  }
Qed.


(** Existence of odd subseries of exp *)
Lemma HpowO_ex {x} : ex_seriesC (λ k : nat, Iverson (not ∘ Zeven) k * x ^ k / fact k).
Proof.
  destruct (decide (Rle 0 x)).
  { apply (ex_seriesC_le _ (λ k : nat, (Rabs x) ^ k / fact k)); last apply Hpow_ex.
    intro n; split.
    { rewrite /Iverson.
      case_decide; [|lra].
      rewrite Rmult_1_l.
      apply Rcomplements.Rdiv_le_0_compat; [|apply INR_fact_lt_0].
      apply pow_le.
      lra.
    }
    { rewrite /Iverson.
      case_decide.
      { rewrite Rmult_1_l.
        rewrite Rdiv_def.
        apply Rmult_le_compat_r.
        { have HH := INR_fact_lt_0 n. apply Rinv_0_lt_compat in HH. lra. }
        apply pow_maj_Rabs.
        lra.
      }
      { rewrite Rmult_0_l Rdiv_0_l.
        apply Rcomplements.Rdiv_le_0_compat; [|apply INR_fact_lt_0].
        apply pow_le.
        apply Rabs_pos.
      }
    }
  }
  { pose x' := (-1) * x.
    replace (λ k : nat, Iverson (not ∘ Zeven) k * x ^ k / fact k)
       with (λ k : nat, (-1) * (Iverson (not ∘ Zeven) k * x' ^ k / fact k)); last first.
    { apply functional_extensionality. intros k. rewrite /x'.
      rewrite /Iverson.
      case_decide.
      { rewrite Rmult_1_l Rmult_1_l.
        rewrite Rpow_mult_distr.
        rewrite Zodd_neg_pow; [lra|].
        destruct (Zeven_odd_dec k); intuition.
        exfalso; apply H; intuition.
      }
      { by rewrite Rmult_0_l Rmult_0_l Rdiv_0_l Rmult_0_r. }
    }
    apply ex_seriesC_scal_l.
    apply (ex_seriesC_le _ (λ k : nat, (Rabs x') ^ k / fact k)); last apply Hpow_ex.
    intro n'; split.
    { rewrite /Iverson.
      case_decide; [|lra].
      rewrite Rmult_1_l.
      apply Rcomplements.Rdiv_le_0_compat; [|apply INR_fact_lt_0].
      apply pow_le.
      rewrite /x'.
      lra.
    }
    { rewrite /Iverson.
      case_decide.
      { rewrite Rmult_1_l.
        rewrite Rdiv_def.
        apply Rmult_le_compat_r.
        { have HH := INR_fact_lt_0 n'. apply Rinv_0_lt_compat in HH. lra. }
        apply pow_maj_Rabs.
        lra.
      }
      { rewrite Rmult_0_l Rdiv_0_l.
        apply Rcomplements.Rdiv_le_0_compat; [|apply INR_fact_lt_0].
        apply pow_le.
        apply Rabs_pos.
      }
    }
  }
Qed.

(** Existence of odd shifted subseries of exp *)
Lemma HpowOS_ex {x} : ex_seriesC ((λ k : nat, Iverson (not ∘ Zeven) k * x ^ k / fact k) ∘ S).
Proof. apply ex_SeriesC_nat_shift. apply HpowO_ex. Qed.

(** Existence of even shifted subseries of exp *)
Lemma HpowES_ex {x} : ex_seriesC ((λ k : nat, Iverson Zeven k * x ^ k / fact k) ∘ S).
Proof. apply ex_SeriesC_nat_shift. apply HpowE_ex. Qed.

(** The power series for exp can be split into series for its odd and even subseries *)
Lemma Hpow_eq {x} : Hpow x = HpowE x + HpowO x.
Proof.
  rewrite /Hpow/HpowE/HpowO.
  rewrite -SeriesC_plus; [| apply HpowE_ex | apply HpowO_ex].
  apply SeriesC_ext. intros n. rewrite //=.
  rewrite -Rmult_plus_distr_r.
  rewrite -Rmult_plus_distr_r.
  rewrite Rmult_assoc.
  rewrite -(Rmult_1_l (x ^ n / fact n)).
  f_equal.
  by rewrite Iverson_add_neg.
Qed.

(** The odd subseries of exp equals the odd shifted subseries *)
Lemma HpowO_eq {x} : HpowO x = HpowOS x.
Proof.
  rewrite /HpowO/HpowOS.
  rewrite SeriesC_nat_shift.
  2: { apply ex_seriesC_nat. apply HpowO_ex. }
  rewrite Iverson_False; [|simpl; intuition].
  by rewrite Rmult_0_l Rdiv_def Rmult_0_l Rplus_0_l.
Qed.

(** The even subseries of exp equals the even shifted subseries plus the first term *)
Lemma HpowE_eq {x} : HpowE x = 1 + HpowES x.
Proof.
  rewrite /HpowE/HpowES.
  rewrite SeriesC_nat_shift.
  2: { apply ex_seriesC_nat. apply HpowE_ex. }
  rewrite Iverson_True; [|simpl; intuition].
  f_equal.
  rewrite //=. lra.
Qed.

(** Closed form for even subseries of real decr trial series *)
Lemma ExpSeriesEven {x} : SeriesC (λ n : nat, Iverson Zeven n * (x^n/(fact n) + x^(n+1)%nat/(fact (n+1)%nat))) = exp x.
Proof.
    rewrite -Hpow_cf.
    rewrite Hpow_eq.
    rewrite HpowO_eq.
    rewrite /HpowOS/HpowE.
    rewrite -SeriesC_plus; [| apply HpowE_ex | apply HpowOS_ex ].
    apply SeriesC_ext. intros n. rewrite //=.
    rewrite Iverson_Zeven_Sn.
    repeat rewrite Rdiv_def.
    rewrite Rmult_assoc.
    rewrite Rmult_assoc.
    rewrite -Rmult_plus_distr_l.
    do 3 f_equal.
    { by rewrite pow_add Rmult_comm pow_1. }
    { f_equal. by rewrite -{1}(Nat.mul_1_l (fact n)) -Nat.mul_add_distr_r Nat.add_1_l Nat.add_1_r -fact_simpl. }
  Qed.

(** Closed form for odd subseries of real decr trial series *)
  Lemma ExpSeriesOdd {x} : SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * (x^n/(fact n) + x^(n+1)%nat/(fact (n+1)%nat))) = -1 + exp x .
  Proof.
    rewrite -Hpow_cf.
    rewrite Hpow_eq.
    rewrite HpowE_eq.
    repeat rewrite -Rplus_assoc.
    rewrite Rplus_opp_l Rplus_0_l.
    rewrite /HpowES/HpowO.
    rewrite -SeriesC_plus; [| apply HpowES_ex | apply HpowO_ex ].
    apply SeriesC_ext. intros n. rewrite //=.
    rewrite Iverson_Zeven_Sn'.
    repeat rewrite Rdiv_def.
    repeat rewrite Rmult_assoc.
    rewrite -Rmult_plus_distr_l.
    do 1 f_equal.
    rewrite Rplus_comm.
    f_equal.
    repeat rewrite -Rmult_assoc.
    f_equal.
    { by rewrite pow_add Rmult_comm pow_1. }
    { f_equal. by rewrite -{1}(Nat.mul_1_l (fact n)) -Nat.mul_add_distr_r Nat.add_1_l Nat.add_1_r -fact_simpl. }
  Qed.

(** Existence for even subseries of real decr trial series *)
  Lemma Hexp_ex_even {x} : ex_seriesC (λ n : nat, Iverson Zeven n * (x ^ n / fact n + x ^ (n + 1) / fact (n + 1))).
  Proof.
    apply (ex_seriesC_ext (λ n : nat, Iverson Zeven n * x ^ n / fact n + Iverson Zeven n * x ^ (n + 1) / fact (n + 1))).
    { intro n. lra. }
    apply ex_seriesC_plus.
    { apply HpowE_ex. }
    replace (λ x0 : nat, Iverson Zeven x0 * x ^ (x0 + 1) / fact (x0 + 1)) with ((λ x0 : nat, Iverson (not ∘ Zeven) x0 * x ^ x0 / fact x0 ) ∘ S).
    { apply HpowOS_ex. }
    apply functional_extensionality.
    intros ?.
    Opaque fact.
    Opaque pow.
    simpl; f_equal; last (f_equal; f_equal; lia).
    f_equal; last (f_equal; lia).
    Transparent fact.
    Transparent pow.
    rewrite /Iverson.
    case_decide; case_decide; try done; exfalso.
    Opaque Zeven.
    { simpl in H.
      destruct (Zeven_odd_dec x0); try by intuition.
      apply Zeven_Sn in z.
      replace (Z.succ (Z.of_nat x0)) with (Z.of_nat (S x0)) in z by lia.
      done.
    }
    { simpl in H.
      apply Zodd_Sn in H0.
      replace (Z.succ (Z.of_nat x0)) with (Z.of_nat (S x0)) in H0 by lia.
      apply Zodd_not_Zeven in H0.
      done.
    }
  Qed.

(** Existence for odd subseries of real decr trial series *)
  Lemma Hexp_ex_odd {x} : ex_seriesC (λ n : nat, Iverson (not ∘ Zeven) n * (x ^ n / fact n + x ^ (n + 1) / fact (n + 1))).
  Proof.
    apply (ex_seriesC_ext (λ n : nat, Iverson (not ∘ Zeven) n * x ^ n / fact n + Iverson (not ∘ Zeven) n * x ^ (n + 1) / fact (n + 1))).
    { intro n. lra. }
    apply ex_seriesC_plus.
    { apply HpowO_ex. }
    replace (λ x0 : nat, Iverson (not ∘ Zeven) x0 * x ^ (x0 + 1) / fact (x0 + 1)) with ((λ x0 : nat, Iverson (Zeven) x0 * x ^ x0 / fact x0 ) ∘ S).
    { apply HpowES_ex. }
    apply functional_extensionality.
    intros ?.
    Opaque fact.
    Opaque pow.
    simpl; f_equal; last (f_equal; f_equal; lia).
    f_equal; last (f_equal; lia).
    Transparent fact.
    Transparent pow.
    rewrite /Iverson.
    case_decide; case_decide; try done; exfalso.
    Opaque Zeven.
    { simpl in H0.
      apply NNP_P in H0.
      apply Zodd_Sn in H0.
      replace (Z.succ (Z.of_nat x0)) with (Z.of_nat (S x0)) in H0 by lia.
      apply Zodd_not_Zeven in H0.
      done.
    }
    { simpl in H0.
      destruct (Zeven_odd_dec x0); try by intuition.
      apply Zeven_Sn in z.
      replace (Z.succ (Z.of_nat x0)) with (Z.of_nat (S x0)) in z by lia.
      done.
    }
  Qed.

End ExpPowerSeries.

(** Factorial reciprocal series exists *)
Lemma ex_exp_series : Series.ex_series (λ n : nat, / fact n).
Proof.
  apply ex_seriesC_nat.
  eapply ex_seriesC_ext; [|apply (@Hpow_ex 1)].
  intros n. simpl.
  rewrite pow1.
  lra.
Qed.

(** Shifted factorial reciprocal series exists *)
Lemma ex_exp_series' {M : nat} : Series.ex_series (λ n : nat, / fact (n - M)).
Proof.
  apply ex_seriesC_nat.
  apply (ex_SeriesC_nat_shiftN_r M).
  rewrite /compose//=.
  eapply ex_seriesC_ext.
  2: { rewrite -ex_seriesC_nat. apply ex_exp_series. }
  intros. rewrite //=.
  f_equal.
  f_equal.
  f_equal.
  lia.
Qed.

(** Geometric series involving exp exists *)
Lemma exp_neg_RInt : ex_RInt (λ x : R, exp (- x ^ 2 / 2)) 0 1.
Proof.
  eapply (ex_RInt_continuous (V := R_CompleteNormedModule)).
  intros ??.
  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
  by auto_derive.
Qed.

(** Definite integral of terms in the exp power series *)
Lemma RInt_pow_fact {a b : R} (M : nat) :
  RInt (fun x1 : R => x1 ^ M / fact M) a b = b ^ (M + 1) / fact (M + 1) - a ^ (M + 1) / fact (M + 1).
Proof.
  replace (fun x1 : R => x1 ^ M / fact M) with (Derive.Derive (fun x1 : R => x1 ^ (M + 1) / fact (M + 1))); last first.
  { replace (fun x1 : R => x1 ^ (M + 1) / fact (M + 1)) with (fun x1 : R => x1 ^ (M + 1) * / fact (M + 1)); last first.
    { apply functional_extensionality; intros ?; lra. }
    apply functional_extensionality; intros ?.
    rewrite Derive.Derive_scal_l.
    rewrite Derive.Derive_pow; [|by auto_derive].
    rewrite Derive.Derive_id.
    rewrite Rmult_1_r.
    rewrite (Rmult_comm _ (x ^ Init.Nat.pred (M + 1))).
    rewrite Rdiv_def Rmult_assoc.
    f_equal.
    { f_equal.
      rewrite -Nat.add_pred_r; [|lia].
      lia.
    }
    rewrite Nat.add_1_r.
    rewrite fact_simpl.
    rewrite mult_INR.
    rewrite Rinv_mult.
    rewrite -Rmult_assoc.
    rewrite (Rinv_r); [lra|].
    pose proof (pos_INR_S M); lra.
    (* have ? := pos_INR_S M. lra. *)
}
rewrite RInt_Derive.
{ lra. }
{ intros ??. by auto_derive. }
{ intros ??.
  replace (fun x1 : R => x1 ^ (M + 1) / fact (M + 1)) with (fun x1 : R => x1 ^ (M + 1) * / fact (M + 1)); last first.
  { apply functional_extensionality; intros ?; lra. }
  replace (Derive.Derive (λ x1 : R, x1 ^ (M + 1) * / fact (M + 1))) with (fun x1 : R => x1 ^ M / fact M).
  { apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)). by auto_derive. }
  apply functional_extensionality; intros ?.
  rewrite Derive.Derive_scal_l.
  rewrite Derive.Derive_pow; [|by auto_derive].
  rewrite Derive.Derive_id.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm _ (x0 ^ Init.Nat.pred (M + 1))).
  rewrite Rdiv_def Rmult_assoc.
  f_equal.
  { f_equal.
    rewrite -Nat.add_pred_r; [|lia].
    lia.
  }
  rewrite Nat.add_1_r.
  rewrite fact_simpl.
  rewrite mult_INR.
  rewrite Rinv_mult.
  rewrite -Rmult_assoc.
  rewrite (Rinv_r); [lra|].
  pose proof (pos_INR_S M); lra.
  (* have ? := pos_INR_S M. lra. *)
}
Qed.

(** Exp is injective *)
Lemma exp_inj {x y : R} : exp x = exp y → x = y.
Proof. apply exp_inv. Qed.

(** Derivative of the negative exponential *)
Lemma Derive_exp_neg {x : R} : Derive.Derive (λ x1 : R, exp (- x1)) x = - exp (- x).
Proof.
  rewrite Derive.Derive_comp; try by auto_derive.
  rewrite Derive.Derive_opp.
  rewrite Derive.Derive_id.
  suffices H : Derive.Derive exp (- x) = exp (- x) by lra.
  rewrite (Derive.is_derive_unique exp (- x) (exp (- x))); first done.
  apply ElemFct.is_derive_exp.
Qed.

(** Key lemma: exp(-b) → 0 as b → ∞ *)
Lemma is_lim_exp_neg_infty : Continuity.is_lim (λ b : R, exp (- b)) Rbar.p_infty (Rbar.Finite 0).
Proof.
  have H : filterlim exp (Rbar_locally Rbar.m_infty) (Rbar_locally (Rbar.Finite 0)).
  { apply ElemFct.is_lim_exp_m. }
  have Hopp : Continuity.is_lim (λ b, - b) Rbar.p_infty Rbar.m_infty.
  { have Hid := Continuity.is_lim_id Rbar.p_infty.
    have Hopp' := Continuity.is_lim_opp (λ y, y) Rbar.p_infty Rbar.p_infty Hid.
    replace (Rbar.Rbar_opp Rbar.p_infty) with Rbar.m_infty in Hopp' by done.
    apply Hopp'. }
  rewrite /Continuity.is_lim in Hopp.
  apply (filterlim_comp R R R (λ b, - b) exp (Rbar_locally' Rbar.p_infty) (Rbar_locally Rbar.m_infty) (Rbar_locally (Rbar.Finite 0))).
  - apply Hopp.
  - apply H.
Qed.

Lemma ex_RInt_gen_exp {M} : ex_RInt_gen (λ x : R, M * exp (- x)) (at_point 0) (Rbar_locally Rbar.p_infty).
Proof.
  have Hex : ∀ b, ex_RInt (λ x : R, M * exp (- x)) 0 b.
  { intros b.
    apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
    intros z Hz.
    apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
    by auto_derive. }
  apply RInt_gen_ex_Ici.
  2: { intros b. apply Hex. }
  exists M.
  have Hint : ∀ b, is_RInt (λ x : R, M * exp (- x)) 0 b (M * (1 - exp (- b))).
  { intros b.
    replace (M * (1 - exp (- b))) with (M - M * exp (- b)) by lra.
    have E0 : exp (- 0) = 1 by (rewrite Ropp_0; apply exp_0).
    replace (M - M * exp (- b)) with (- M * exp (- b) - - M * exp (- 0)) by (rewrite E0; lra).
    apply (is_RInt_derive (V := R_CompleteNormedModule) (λ x : R, - M * exp (- x)) (λ x : R, M * exp (- x))).
    - intros x0 Hx0. auto_derive; [done | lra].
    - intros x0 Hx0. apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)). by auto_derive.
  }
  rewrite /filterlimi /= /filter_le /= /filtermapi /=.
  intros P HP.
  rewrite /locally in HP. destruct HP as [eps HP].
  have Hlim := is_lim_exp_neg_infty.
  rewrite /Continuity.is_lim in Hlim.
  destruct (Req_dec M 0) as [HM0|HMnz].
  - exists 0. intros x Hx.
    exists (M * (1 - exp (- x))).
    split.
    + apply Hint.
    + apply HP.
      subst M.
      replace (0 * (1 - exp (- x))) with 0 by lra.
      rewrite /ball /= /AbsRing_ball /= /abs /= /minus /plus /opp /=.
      replace (0 + - 0) with 0 by lra.
      rewrite Rabs_R0. apply cond_pos.
  - have Heps' : 0 < eps / Rabs M.
    { apply Rdiv_lt_0_compat; [apply cond_pos | apply Rabs_pos_lt; apply HMnz]. }
    have Hball : Rbar_locally (Rbar.Finite 0) (ball 0 (mkposreal (eps / Rabs M) Heps')).
    { exists (mkposreal (eps / Rabs M) Heps'). intros ?. done. }
    specialize (Hlim (ball 0 (mkposreal (eps / Rabs M) Heps')) Hball).
    rewrite /filtermap in Hlim.
    rewrite /Rbar_locally' in Hlim.
    destruct Hlim as [M0 Hlim].
    exists (Rmax M0 0).
    intros x Hx.
    exists (M * (1 - exp (- x))).
    split.
    + apply Hint.
    + apply HP.
      rewrite /ball /= /AbsRing_ball /= /abs /= /minus /plus /opp /=.
      replace (M * (1 - exp (- x)) + - M) with (- M * exp (- x)) by lra.
      have HexpBall : Rabs (exp (- x)) < eps / Rabs M.
      { have H := Hlim x.
        have Hx0 : M0 < x by (apply Rmax_Rlt in Hx; lra).
        specialize (H Hx0).
        rewrite /ball /= /AbsRing_ball /= /abs /= /minus /plus /opp /= in H.
        replace (exp (- x) + - 0) with (exp (- x)) in H by lra.
        simpl in H. apply H. }
      rewrite Rabs_mult.
      replace (Rabs (- M)) with (Rabs M) by (rewrite Rabs_Ropp; done).
      rewrite Rmult_comm.
      apply Rmult_lt_reg_r with (r := / Rabs M).
      { apply Rinv_0_lt_compat, Rabs_pos_lt, HMnz. }
      rewrite Rmult_assoc Rinv_r; [|apply Rgt_not_eq, Rabs_pos_lt, HMnz].
      rewrite Rmult_1_r.
      field_simplify; [|apply Rgt_not_eq, Rabs_pos_lt, HMnz].
      apply HexpBall.
Qed.

Lemma NegExp_Int {L} :
 RInt_gen (fun r => exp (-r)) (at_point L) (Rbar_locally Rbar.p_infty) = exp (- L).
Proof.
  have Hex : ∀ b,  ex_RInt (λ r : R, exp (- r)) L b.
  { intros b.
    apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
    intros z Hz.
    apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
    by auto_derive. }
  have Hint : ∀ b,  is_RInt (λ r : R, exp (- r)) L b (exp (- L) - exp (- b)).
  { intros b Hb.
    replace (exp (- L) - exp (- b)) with (- exp (- b) - - exp (- L)) by lra.
    apply (is_RInt_derive (V := R_CompleteNormedModule) (λ r : R, - exp (- r)) (λ r : R, exp (- r))).
    - intros x0 Hx0. auto_derive; [done | lra].
    - intros x0 Hx0. apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)). by auto_derive. }
  have Hlimit : filterlimi (λ b : R, is_RInt (λ r : R, exp (- r)) L b) (Rbar_locally Rbar.p_infty) (locally (exp (- L))).
  { rewrite /filterlimi /= /filter_le /= /filtermapi /=.
    intros P HP.
    rewrite /locally in HP. destruct HP as [eps HP].
    have Hlim := is_lim_exp_neg_infty.
    rewrite /Continuity.is_lim in Hlim.
    have Hball : Rbar_locally (Rbar.Finite 0) (ball 0 eps).
    { exists eps. intros ?. done. }
    specialize (Hlim (ball 0 eps) Hball).
    rewrite /filtermap in Hlim.
    rewrite /Rbar_locally' in Hlim.
    destruct Hlim as [M0 Hlim].
    exists (Rmax M0 L).
    intros x Hx.
    exists (exp (- L) - exp (- x)).
    split.
    - apply Hint.
    - apply HP.
      rewrite /ball /= /AbsRing_ball /= /abs /= /minus /plus /opp /=.
      replace (exp (- L) - exp (- x) + - exp (- L)) with (- exp (- x)) by lra.
      rewrite Rabs_Ropp.
      have : M0 < x by (apply Rmax_Rlt in Hx; lra).
      intros Hx0.
      specialize (Hlim x Hx0).
      rewrite /ball /= /AbsRing_ball /= /abs /= /minus /plus /opp /= in Hlim.
      replace (exp (- x) + - 0) with (exp (- x)) in Hlim by lra.
      apply Hlim. }
  rewrite filterlim_RInt_gen.
  2: { intros b. apply Hex. }
  have Hlim2 : filterlim (λ b : R, RInt (λ r : R, exp (- r)) L b) (Rbar_locally Rbar.p_infty) (locally (exp (- L))).
  { rewrite /filterlim /= /filter_le /= /filtermap /=.
    intros P HP.
    rewrite /filterlimi /= /filter_le /= /filtermapi /= in Hlimit.
    destruct (Hlimit P HP) as [M0 HM0].
    exists M0.
    intros x Hx.
    specialize (HM0 x Hx).
    destruct HM0 as [y [Hisy Py]].
    rewrite (is_RInt_unique (λ r : R, exp (- r)) L x y Hisy).
    apply Py.
  }
  apply (@iota_filterlim_locally R_AbsRing R_CompleteNormedModule R (Rbar_locally Rbar.p_infty)).
  - apply Proper_StrongProper, Rbar_locally_filter.
  - apply Hlim2.
Qed.

Lemma neg_exp_accuracy_chasles {L} :
  0<=L ->
  RInt_gen (λ r : R, (Iverson (Iio 0) r + Iverson (Ioi L) r) * exp (- r)) (at_point 0) (Rbar_locally Rbar.p_infty) =
  RInt_gen (λ r : R, exp (- r)) (at_point L) (Rbar_locally Rbar.p_infty).
Proof.
  (* Step 1: Simplify LHS: on [0,∞), Iverson (Iio 0) r = 0 *)
  assert (ex_RInt_gen (λ r, Iverson (Iio 0) r  * exp (- r)) (at_point 0) (Rbar_locally Rbar.p_infty)).
  { eapply (ex_RInt_gen_Ici_compare_PCts (F:=λ x, 1* exp (-x))).
    - intros.
      apply IPCts_PCts.
      apply IPCts_cts.
      intros.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    - intros.
      apply PCts_mult.
      + apply IPCts_PCts.
        apply IPCts_Iio.
      + apply IPCts_PCts.
        apply IPCts_cts.
        intros.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
    - intros.
      split.
      + apply Rmult_le_pos.
        * apply Iverson_nonneg.
        * apply Rexp_nn.
      + apply Rmult_le_compat_r.
        * apply Rexp_nn.
        * apply Iverson_le_1.
    - apply ex_RInt_gen_exp. }
  assert (ex_RInt_gen (λ x : R, Iverson (Ioi L) x * exp (- x)) (at_point 0) (Rbar_locally Rbar.p_infty)).
  { eapply (ex_RInt_gen_Ici_compare_PCts (F:=λ x, 1* exp (-x))).
    - intros.
      apply IPCts_PCts.
      apply IPCts_cts.
      intros.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    - intros.
      apply PCts_mult.
      + apply IPCts_PCts.
        apply IPCts_Ioi.
      + apply IPCts_PCts.
        apply IPCts_cts.
        intros.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
    - intros.
      split.
      + apply Rmult_le_pos.
        * apply Iverson_nonneg.
        * apply Rexp_nn.
      + apply Rmult_le_compat_r.
        * apply Rexp_nn.
        * apply Iverson_le_1.
    - apply ex_RInt_gen_exp. }
  erewrite (@RInt_gen_ext_eq_Ici
    (λ r : R, (Iverson (Iio 0) r + Iverson (Ioi L) r) * exp (- r))
    (λ r : R, Iverson (Ioi L) r * exp (- r)) 0).
  2: { intros x Hx. rewrite Iverson_False. { lra. } rewrite /Iio. lra. }
  2: {
    eapply (ex_RInt_gen_ext_eq_Ioi (f:=(λ r : R, Iverson (Iio 0) r  * exp (- r) + Iverson (Ioi L) r * exp (- r)) )); first (intros; lra).
    by apply ex_RInt_gen_plus.
  } 

  (* Step 2: Now prove: ∫[0,∞) Iverson (Ioi L) r * exp(-r) = ∫[L,∞) exp(-r) *)

  (* Strategy: Show RHS = ∫[L,∞) Iverson (Ioi L) r * exp(-r) on [L,∞)
       Then relate this to LHS using Chasles to show ∫[0,L] part is 0 *)
  symmetry.
  erewrite (@RInt_gen_ext_eq_Ioi
              (λ r : R, exp (- r))
              (λ r : R, Iverson (Ioi L) r * exp (- r)) L).

  (* Need to prove: exp(-x) = Iverson (Ioi L) x * exp(-x) for x >= L *)
  2: { intros. rewrite Iverson_True; first lra.
       by rewrite /Ioi. 
  } 

  (* Need existence of ∫[L,∞) exp(-r) *)
  2: {
    apply: (ex_RInt_gen_ext_eq_Ici (f:= λ r, 1*exp (-r))); first (intros; lra).
    eapply ex_RInt_gen_Chasles; last apply ex_RInt_gen_exp.
    rewrite ex_RInt_gen_at_point.
    apply IPCts_RInt.
    apply IPCts_cts.
    intros.
    apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
    by auto_derive.
  }
  erewrite <-RInt_gen_Chasles; last done; last first.
  { apply ex_RInt_gen_at_point.
    apply PCts_RInt.
    apply PCts_mult.
    - apply IPCts_PCts.
      apply IPCts_Ioi.
    - apply IPCts_PCts.
      apply IPCts_cts.
      intros.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive. }
  replace (RInt_gen _ (at_point _) (at_point _)) with 0; first by rewrite plus_zero_l.
  symmetry.
  erewrite (RInt_gen_ext _ (λ _, 0)).
  - rewrite RInt_gen_at_point.
    + rewrite RInt_const.
      rewrite /scal/=/mult/=. lra.
    + apply ex_RInt_const.
  - eapply (Filter_prod _ _ _ (λ x, x<=L) (λ x, 0<=x<=L)); try done.
    + by rewrite /at_point.
    + intros.
      rewrite Iverson_False; first lra.
      simpl in *.
      unfold Ioi, Rmin, Rmax in *. simpl in *.
      case_match; lra.
  - apply ex_RInt_gen_at_point.
    apply PCts_RInt.
    apply PCts_mult.
    + apply IPCts_PCts.
      apply IPCts_Ioi.
    + apply IPCts_PCts.
      apply IPCts_cts.
      intros.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
Qed. 

Lemma ex_exp_geo_series : ex_seriesC (λ x : nat, exp (- x)).
Proof.
  apply (ex_seriesC_ext (λ n : nat, (exp (-1)) ^ n)).
  { intros n. rewrite exp_pow. f_equal. lra. }
  have H : Rabs (exp (-1)) < 1.
  { rewrite Rabs_pos_eq.
    - replace 1 with (exp 0) by apply exp_0.
      apply exp_mono_strict. lra.
    - apply Rexp_nn. }
  have H' := Series.ex_series_geom (exp (-1)) H.
  by rewrite -ex_seriesC_nat.
Qed.
