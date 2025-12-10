From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real indicators real_decr_trial bern_geo half_bern_neg_exp bern_iter selector.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.
  Import Hierarchy.

  Definition Norm1 : R := SeriesC (fun (k : nat) => exp ((-k^2)/2)).

  Definition G1_μ : nat → R := fun k => exp ((-k^2)/2) / Norm1.

  Definition Norm2 : R := RInt (fun x => SeriesC (fun (k : nat) => exp ((-(x+k)^2)/2))) 0 1.

  Definition G2_μ : nat -> R → R := fun k x => exp ((-(x+k)^2)/2) / Norm2.

End pmf.


Section credits.
  Import Hierarchy.

  (*
  Lemma ex_seriesC_lemma1 : ex_seriesC (λ x : nat, exp (- (x * (x - 1))%nat / 2)).
  Proof. A dmitted.

   *)

  Definition G1_CreditV (F : nat → R) := SeriesC (fun (k : nat) => G1_μ k * F k).

  Definition G2_CreditV (F : nat → R → R) :=
    SeriesC (fun (k : nat) => RInt (fun x => G2_μ k x * F k x) 0 1).

  Definition G1_h (F : nat → R) (k : nat) : bool -> R :=
    fun b => Iverson is_true b * F k + Iverson (not ∘ is_true) b * G1_CreditV F.

  Definition G1_f (F : nat → R) : nat -> R := fun k =>
    (exp (-(k*(k-1))%nat/2)) * G1_h F k true + (1 - (exp (-(k*(k-1))%nat/2))) * G1_h F k false.

  Definition G2_s (F : nat → R → R) (k : nat) (x : R) : bool → R := fun b =>
     Iverson is_true b * F k x +
     Iverson (not ∘ is_true) b * G2_CreditV F.

  Definition G2_g (F : nat → R → R) (k : nat) : R → R := fun x =>
    (exp (-x*(2*k+x)/2)) * G2_s F k x true +
    (1 - exp (-x*(2*k+x)/2)) * G2_s F k x false.

  Definition G2_f (F : nat → R → R) : nat → R := fun k =>
     RInt (G2_g F k) 0 1.

  Lemma Norm1_ex :  ex_seriesC (λ k : nat, exp (- k ^ 2 / 2)).
  Proof.
    eapply (ex_seriesC_le _ (λ k : nat, (exp (-1/2)) ^ k)).
    { intro n. split.
      { apply Rexp_nn. }
      { rewrite exp_pow.
        apply exp_mono.
        replace (- n ^ 2 / 2) with (-((1/2)*n^2)) by lra.
        replace (-1 / 2 * n) with (-(1 / 2 * n)) by lra.
        apply Ropp_le_contravar.
        apply Rmult_le_compat_l; [lra|].
        rewrite -pow_INR.
        apply le_INR.
        rewrite Nat.pow_2_r.
        destruct n; [lia|].
        lia.
      }
    }
    rewrite -ex_seriesC_nat.
    apply Series.ex_series_geom.
    rewrite Rabs_right.
    { rewrite -exp_0.
      apply exp_mono_strict.
      lra.
    }
    { apply Rle_ge.
      apply Rexp_nn.
    }
  Qed.

  Lemma Norm1_nn : 0 < Norm1.
  Proof.
    rewrite /Norm1.
    apply (Rlt_le_trans _ (SeriesC (λ k : nat, if bool_decide (1%nat = k) then exp (- 1 ^ 2 / 2) else 0))).
    { rewrite SeriesC_singleton'.
      rewrite pow1.
      apply exp_pos.
    }
    { eapply SeriesC_le'.
      { intro n. case_bool_decide.
        { rewrite -H.  apply Req_le_sym. f_equal. }
        { apply Rexp_nn. }
      }
      { apply ex_seriesC_singleton'. }
      { apply Norm1_ex. }
    }
  Qed.

  Lemma G1_μ_nn {x}  : 0 <= G1_μ x.
  Proof.
    rewrite /G1_μ.
    apply Rle_mult_inv_pos; [|apply Norm1_nn].
    apply Rexp_range.
    apply Rcomplements.Rmult_le_0_r; last lra.
    have ? : 0 <= x^2.  { apply pow_le. apply pos_INR. }
    lra.
  Qed.

  Theorem Norm2_ex' {y : R} : 0 <= y <= 1 → ex_seriesC (λ x0 : nat, exp (- (y + x0) ^ 2 / 2)).
  Proof.
    intros H.
    apply (ex_seriesC_le _ (λ x0 : nat, exp (- (x0) ^ 2 / 2))).
    { intros n; split. { apply Rexp_nn. }
      apply exp_mono.
      rewrite Rdiv_def.
      apply Rmult_le_compat_r; OK.
      apply Ropp_le_contravar.
      apply pow_incr.
      split; OK.
      apply pos_INR.
    }
    apply Norm1_ex.
  Qed.


  Lemma ExpAddSeries_RInt : ex_RInt (λ x : R, SeriesC (λ k : nat, exp (- (x + k) ^ 2 / 2))) 0 1.
  Proof.
    eapply (ex_RInt_SeriesC (fun n => exp (- (0 + n) ^ 2 / 2))); OK.
    { rewrite ex_seriesC_nat. eapply Norm2_ex'. OK. }
    { intros ???.
      split.
      { apply Rexp_nn. }
      apply exp_mono.
      do 2 rewrite Rdiv_def.
      replace (- (x + n) ^ 2 * / 2) with ((-1 / 2) * (x + n) ^ 2) by OK.
      replace (- (0 + n) ^ 2 * / 2) with ((-1 / 2) * (0 + n) ^ 2) by OK.
      apply Rmult_le_compat_neg_l; OK.
      apply pow_incr; OK.
      split; OK.
      rewrite Rplus_0_l; apply pos_INR.
    }
    { intros n.
      apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      intros ??.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
  Qed.

  Lemma Norm2_nn : 0 < Norm2.
  Proof.
    rewrite /Norm2.
    (* LB the sequence by its first element? *)
    (* Then LB the integral by some stupid step function or something *)

    eapply (Rlt_le_trans _ (RInt (λ x : R, SeriesC (λ k : nat, if (bool_decide (k = 0%nat)) then (exp (- x ^ 2 / 2)) else 0)) 0 1)).
    { replace (λ x : R, SeriesC (λ k : nat, if bool_decide (k = 0%nat) then exp (- x ^ 2 / 2) else 0))
         with (λ x : R,  exp (- x ^ 2 / 2)); last first.
      { apply functional_extensionality; intros x. by rewrite SeriesC_singleton. }
      eapply Rlt_le_trans.
      2: { eapply (RInt_le (fun _ => exp (- 1 ^ 2 / 2))); OK.
           { apply ex_RInt_const. }
           { apply exp_neg_RInt. }
           { intros ? ?. apply exp_mono; OK.
             do 2 rewrite Rdiv_def.
             rewrite -Ropp_mult_distr_l.
             rewrite -Ropp_mult_distr_l.
             apply Ropp_le_contravar.
             apply Rmult_le_compat_r; OK.
             apply pow_incr; lra.
            }
      }
      { rewrite RInt_const.
        rewrite /scal///=/mult//= Rmult_1_l Rmult_1_l Rminus_0_r Rmult_1_l.
        apply exp_pos.
      }
    }
    { apply RInt_le; [lra | | | ].
      { replace (λ x : R, SeriesC (λ k : nat, if bool_decide (k = 0%nat) then exp (- x ^ 2 / 2) else 0))
           with (λ x : R,  exp (- x ^ 2 / 2)); last first.
        { apply functional_extensionality; intros x. by rewrite SeriesC_singleton. }
        { apply (@ex_RInt_continuous R_CompleteNormedModule).
          intros z Hz.
          apply ElemFct.continuous_exp_comp.
          replace (λ x : R_UniformSpace, - x ^ 2 / 2) with (λ x : R_UniformSpace, (x * x) * (-1 / 2)); last (apply functional_extensionality; intros ?; lra).
          apply (@Continuity.continuous_mult R_CompleteNormedModule).
          { apply (@Continuity.continuous_mult R_CompleteNormedModule); apply Continuity.continuous_id. }
          { apply Continuity.continuous_const. }
        }
      }
      { apply ExpAddSeries_RInt. }
      { intros x Hx.
        apply SeriesC_le'.
        { intro n. case_bool_decide.
          { by rewrite H INR_0 Rplus_0_r. }
          { apply Rexp_nn. }
        }
        { apply ex_seriesC_singleton. }
        { (* Upper bound like the other one *)
          apply (ex_seriesC_le _ (λ k : nat, exp (- (k) ^ 2 / 2))).
          { intros n.
            split; [apply Rexp_nn|].
            apply exp_mono.
            do 2 rewrite /Rdiv_def.
            apply Rmult_le_compat_r; OK.
            apply Ropp_le_contravar.
            apply pow_incr.
            split; [apply pos_INR|].
            OK.
        }
        { apply Norm1_ex. }
      }
    }
  }
  Qed.


  Lemma G2_μ_nn {x k} (Hx : 0 <= x <= 1) : 0 <= G2_μ k x.
  Proof.
    rewrite /G2_μ.
    apply Rle_mult_inv_pos; [|apply Norm2_nn].
    apply Rexp_range.
    apply Rcomplements.Rmult_le_0_r; last lra.
    have ? : 0 <= (k + x)^2.  { apply pow_le. apply Rplus_le_le_0_compat; try lra. apply pos_INR. }
    lra.
  Qed.

  Lemma G1_CreditV_nn {F} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_CreditV F.
  Proof.
    rewrite /G1_CreditV.
    apply SeriesC_ge_0'; intros x'.
    apply Rmult_le_pos; [|auto].
    apply G1_μ_nn.
  Qed.

  Lemma G1_μ_pmf : SeriesC G1_μ = 1.
  Proof.
    rewrite /G1_μ.
    replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with ((λ k : nat, exp (- k ^ 2 / 2) * / Norm1)) by (funexti; OK).
    rewrite SeriesC_scal_r.
    rewrite /Norm1.
    rewrite Rmult_inv_r; OK.
    suffices H : (@SeriesC nat numbers.Nat.eq_dec nat_countable (λ x : nat, exp (- x ^ 2 / 2)) > 0) by OK.
    apply (SeriesC_pos _ 0%nat).
    { intros ?; apply Rexp_nn. }
    { apply Norm1_ex. }
    simpl.
    rewrite Rmult_0_l.
    rewrite Ropp_0.
    rewrite Rdiv_def.
    rewrite Rmult_0_l.
    rewrite exp_0.
    OK.
  Qed.

  Lemma G1_CreditV_ub {F} {M : R} (Hnn : ∀ r, 0 <= F r <= M) : G1_CreditV F <= M.
  Proof.
    have ? : 0 <= M. { specialize Hnn with 0%nat. OK. }
    rewrite /G1_CreditV.
    etrans; first apply (SeriesC_le _ (λ k : nat, G1_μ k * M)).
    { intros n. split.
      { apply Rmult_le_pos; [apply G1_μ_nn | apply Hnn]. }
     apply Rmult_le_compat; OK; [apply G1_μ_nn | apply Hnn | apply Hnn].
    }
    { apply ex_seriesC_scal_r.
      rewrite /G1_μ.
      replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with (λ k : nat, exp (- k ^ 2 / 2) * / Norm1) by (funexti; OK).
      apply ex_seriesC_scal_r.
      apply Norm1_ex.
    }
    rewrite SeriesC_scal_r.
    rewrite -{2}(Rmult_1_l M).
    have ? := G1_μ_pmf.
    apply Rmult_le_compat; OK.
  Qed.

  Lemma G1_h_nn {F k b} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_h F k b.
  Proof.
    rewrite /G1_h.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg| auto ]).
    apply G1_CreditV_nn; auto.
  Qed.

  Lemma G1_h_ub {F k b M} (Hnn : ∀ r, 0 <= F r <= M) : G1_h F k b <= M.
  Proof.
    rewrite /G1_h.
    destruct b.
    { rewrite Iverson_True; OK.
      rewrite Iverson_False; OK.
      rewrite Rmult_1_l Rmult_0_l.
      rewrite Rplus_0_r.
      apply Hnn.
    }
    { rewrite Iverson_False; OK.
      rewrite Iverson_True; OK.
      rewrite Rmult_1_l Rmult_0_l.
      rewrite Rplus_0_l.
      apply G1_CreditV_ub; OK.
    }
  Qed.

  Lemma G1_f_ub {F k M} (Hnn : ∀ r, 0 <= F r <= M) : G1_f F k <= M.
  Proof.
    rewrite /G1_f.
    apply (Rle_trans _  (exp (- (k * (k - 1))%nat / 2) * M + (1 - exp (- (k * (k - 1))%nat / 2)) * M)).
    { apply Rplus_le_compat.
      { apply Rmult_le_compat; OK.
        { apply Rexp_nn. }
        { apply G1_h_nn; apply Hnn. }
        { apply G1_h_ub, Hnn. }
      }
      { apply Rmult_le_compat; OK.
        { apply Rle_0_le_minus, Rexp_range. apply Rcomplements.Rmult_le_0_r; OK. rewrite -Ropp_0. apply Ropp_le_contravar, pos_INR.  }
        { apply G1_h_nn; apply Hnn. }
        { apply G1_h_ub, Hnn. }
      }
    }
    rewrite -(Rmult_plus_distr_r).
    OK.
  Qed.

  Lemma G2_exRInt {x'} : ex_RInt (λ x : R, G2_μ x' x) 0 1.
  Proof.
    rewrite /G2_μ.
    replace (λ y : R, exp (- (y + x') ^ 2 / 2) / Norm2) with (λ y : R, exp ((-1) * (y + x') * (y + x') * / 2) * / Norm2); last first.
    { apply functional_extensionality; intros ?; simpl.
      repeat rewrite Rdiv_def. f_equal. f_equal. f_equal. lra. }
    apply ex_RInt_Rmult'.
    apply (@ex_RInt_continuous R_CompleteNormedModule).
    intros z Hz.
    apply ElemFct.continuous_exp_comp.
    apply (@Continuity.continuous_mult R_CompleteNormedModule); [|apply Continuity.continuous_const].
    apply (@Continuity.continuous_mult R_CompleteNormedModule);
      last (apply (@Continuity.continuous_plus R_CompleteNormedModule); [apply Continuity.continuous_id|apply Continuity.continuous_const]).
    apply (@Continuity.continuous_mult R_CompleteNormedModule);
      last (apply (@Continuity.continuous_plus R_CompleteNormedModule); [apply Continuity.continuous_id|apply Continuity.continuous_const]).
    apply Continuity.continuous_const.
  Qed.

  Lemma G2_CreditV_nn {F} (Hnn : ∀ k r, 0 <= F k r) (Hint : forall x', ex_RInt (F x') 0 1) : 0 <= G2_CreditV F.
  Proof.
    rewrite /G2_CreditV.
    apply SeriesC_ge_0'; intros x'.
    apply RInt_ge_0; try lra.
    { apply ex_RInt_mult; [|apply Hint].
      apply G2_exRInt; auto. }
    intros x Hx.
    apply Rmult_le_pos; [|auto].
    apply G2_μ_nn; auto.
    lra.
  Qed.

  Lemma G2_s_nn {F k x b} (Hnn : ∀ a b , 0 <= F a b) (Hint : ∀ x' : nat, ex_RInt (F x') 0 1) : 0 <= G2_s F k x b.
  Proof.
    rewrite /G2_s.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg| auto ]).
    apply G2_CreditV_nn; auto.
  Qed.

  Lemma G2_g_nn {F k x} (Hnn : ∀ a b , 0 <= F a b) (Hx : 0 <= x <= 1) (Hint :   ∀ x' : nat, ex_RInt (F x') 0 1) : 0 <= G2_g F k x.
  Proof.
    rewrite /G2_g.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [|apply G2_s_nn; auto]).
    { apply Rexp_range.
      apply Rcomplements.Rmult_le_0_r; last lra.
      have ? : 0 <= x * (2 * k + x); last lra.
      apply Rmult_le_pos; [lra|].
      apply Rplus_le_le_0_compat; [|lra].
      apply Rmult_le_pos; [lra|apply pos_INR].
    }
    { apply error_credits.Rle_0_le_minus.
      apply Rexp_range.
      have ? : 0 <= x * (2 * k + x); last lra.
      apply Rmult_le_pos; [lra|].
      apply Rplus_le_le_0_compat; [|lra].
      apply Rmult_le_pos; [lra|apply pos_INR].
    }
  Qed.

  Lemma G2_g_exRInt {F k} (Hex : ex_RInt (λ y : R, F k y) 0 1) : ex_RInt (G2_g F k) 0 1.
  Proof.
    rewrite /G2_g.
    apply (ex_RInt_plus (V := R_CompleteNormedModule)).
    { apply ex_RInt_mult.
      { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros z Hz.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { rewrite /G2_s.
        rewrite Iverson_True; OK.
        rewrite Iverson_False; OK.
        replace (λ y : R, 1 * F k y + 0 * G2_CreditV F) with (λ y : R, F k y) by (funexti; OK).
        done.
      }
    }
    { apply ex_RInt_mult.
      { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros z Hz.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { rewrite /G2_s.
        rewrite Iverson_False; OK.
        rewrite Iverson_True; OK.
        replace (λ y : R, 0 * F k y + 1 * G2_CreditV F) with (λ y : R, G2_CreditV F) by (funexti; OK).
        apply ex_RInt_const.
      }
    }
  Qed.

  Lemma G2_f_nn {F k} (Hnn : ∀ a b , 0 <= F a b) (Hint : ∀ x' : nat, ex_RInt (F x') 0 1) : 0 <= G2_f F k.
  Proof.
    rewrite /G2_f.
    apply RInt_ge_0; try lra.
    { apply G2_g_exRInt; auto. }
    intros x Hx.
    apply G2_g_nn; auto. lra.
  Qed.



  Lemma G2_CreditV_ub {F} {M : R} (Hnn : ∀ (x : nat) (k : R), 0 <= F x k <= M) (Hint : ∀ x' : nat, ex_RInt (F x') 0 1) :
    G2_CreditV F <= M.
  Proof.
    have ? : 0 <= M. { specialize Hnn with 0%nat 0%R. OK. }
    rewrite /G2_CreditV.
    etrans.
    { eapply (SeriesC_le _ (λ k : nat, RInt (λ x : R, G2_μ k x * M) 0 1)).
      { intros n.
        split.
        { apply RInt_ge_0; OK.
          { apply ex_RInt_mult; [apply G2_exRInt; OK | apply Hint]. }
          { intros ??. apply Rmult_le_pos; [|apply Hnn]. apply G2_μ_nn; OK. }
        }
        apply RInt_le; OK.
        { apply ex_RInt_mult; [apply G2_exRInt; OK | apply Hint]. }
        { apply ex_RInt_Rmult'. apply G2_exRInt; OK. }
        { intros ??. apply Rmult_le_compat_l; [|apply Hnn]. apply G2_μ_nn; OK. }
      }
      { replace (λ k : nat, RInt (λ x : R, G2_μ k x * M) 0 1) with  (λ k : nat, RInt (λ x : R, G2_μ k x) 0 1 * M); last first.
        { funexti. rewrite RInt_Rmult'; OK. apply G2_exRInt.  }
        apply ex_seriesC_scal_r.
        rewrite /G2_μ.
        apply (ex_seriesC_RInt (fun n => exp (- (0 + n) ^ 2 / 2) * / Norm2)); OK.
        { intros ???.
          apply Rmult_le_pos; OK.
          { apply Rexp_nn. }
          apply Rlt_le.
          apply Rinv_0_lt_compat.
          apply Norm2_nn.
        }
        { apply ex_seriesC_scal_r. eapply Norm2_ex'. OK. }
        { intros ???.
          rewrite Rabs_right.
          2: { apply Rle_ge.
               rewrite Rdiv_def.
               apply Rmult_le_pos; [apply Rexp_nn|].
               apply Rlt_le.
               apply Rinv_0_lt_compat.
               apply Norm2_nn.
          }
          rewrite Rdiv_def.
          apply Rmult_le_compat; OK.
          { apply Rexp_nn. }
          { apply Rlt_le.
            apply Rinv_0_lt_compat.
            apply Norm2_nn.
          }
          apply exp_mono.
          replace (- (x + n) ^ 2 / 2) with ((-1/2) * (x + n) ^ 2) by OK.
          replace (- (0 + n) ^ 2 / 2) with ((-1/2) * (0 + n) ^ 2) by OK.
          apply Rmult_le_compat_neg_l; OK.
          apply pow_incr; OK.
          split; OK.
          rewrite Rplus_0_l.
          apply pos_INR.
        }
        { intros ?.
          apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros z Hz.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
    }
    rewrite (SeriesC_ext _ (λ k : nat, (RInt (λ x : R, G2_μ k x) 0 1) * M)); last first.
    { intros n. rewrite RInt_Rmult'; OK. apply G2_exRInt. }
    rewrite SeriesC_scal_r.
    rewrite -{2}(Rmult_1_l M).
    apply Rmult_le_compat_r; OK.
    rewrite /G2_μ.
    rewrite SeriesC_Series_nat.

    (* If I can exchange the limits here, then the inner series becomes 1, and the outter integral becomes
       the integral of 1 from 0 to 1. *)
    rewrite (FubiniIntegralSeries_Strong (fun n => exp (- (0 + n) ^ 2 / 2) / Norm2)).
    { replace (λ x : R, Series.Series (λ n' : nat, exp (- (x + n') ^ 2 / 2) / Norm2))
        with (λ x : R, scal (/ Norm2) (SeriesC (λ n' : nat, exp (- (x + n') ^ 2 / 2) ))).
      2: { funexti. rewrite /scal//=/mult//= Rmult_comm. rewrite SeriesC_Series_nat. by rewrite Series.Series_scal_r. }
      rewrite RInt_scal.
      2: { apply  ExpAddSeries_RInt. }
      right.
      Opaque pow.
      rewrite /scal//=/mult//=; OK.
      rewrite /Norm2.
      rewrite Rinv_l; OK.
      have X := Norm2_nn.
      unfold Norm2  in X.
      OK.
      Transparent pow.
    }
    { OK. }
    { intros ???.
      apply Rcomplements.Rdiv_le_0_compat.
      { apply Rexp_nn. }
      { apply Norm2_nn. }
    }
    { rewrite ex_seriesC_nat.
      replace (λ n : nat, exp (- (0 + n) ^ 2 / 2) / Norm2) with (λ n : nat, exp (- (0 + n) ^ 2 / 2) * / Norm2).
      { apply ex_seriesC_scal_r.
        apply Norm2_ex'.
        OK.
      }
      funexti.
      by rewrite Rdiv_def.
    }
    { intros ???.
      rewrite Rabs_right.
      2: {
        apply Rle_ge.
        rewrite Rdiv_def.
        apply Rmult_le_pos; first apply Rexp_nn.
        apply Rlt_le.
        apply Rinv_0_lt_compat.
        apply Norm2_nn.
      }
      do 2 rewrite Rdiv_def.
      apply Rmult_le_compat_r.
      { apply Rlt_le. apply Rinv_0_lt_compat. apply Norm2_nn. }
      apply exp_mono.
      replace (- (x + n) ^ 2 * / 2) with ((-1 / 2) * (x + n) ^ 2) by OK.
      replace (Rdiv (Ropp (pow (Rplus (IZR Z0) (INR n)) (Datatypes.S (Datatypes.S O)))) (IZR (Zpos (xO xH)))) with ((-1 / 2) * (0 + n) ^ 2) by OK.
      apply Rmult_le_compat_neg_l; OK.
      apply pow_incr; OK.
      split; OK.
      { rewrite Rplus_0_l; apply pos_INR. }
    }
    { intros n.
      apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      intros ??.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
  Qed.


  (* TODO: Once this proof is done, reduce this to piecewise continuity *)
  Lemma G2_f_ex_seriesC {F M}
    (Hnn : ∀ (x : nat) (k : R), 0 <= F x k <= M)
    (Hcont : ∀ k, PCts (F k) 0 1)
    : ex_seriesC (G2_f F).
  Proof.


    (*

    rewrite /G2_f.
    apply (ex_seriesC_le _ (fun k => M * RInt (G2_μ k) 0 1)).
   { intros n. split.
     { apply RInt_ge_0.
       { lra. }
       { apply G2_g_exRInt, Hint. }
       { intros x Hx. apply G2_g_nn; [apply Hnn | lra | apply Hint]. }
     }
   { etrans.
     { apply RInt_le.
       { lra. }
       { apply G2_g_exRInt, Hint. }
       { replace (fun x => M * G2_μ n x) with (fun x => scal M (G2_μ n x)).
         2: { apply functional_extensionality; intro; rewrite /scal/=/mult/=; reflexivity. }
         apply (ex_RInt_scal (V := R_CompleteNormedModule)).
         eapply G2_exRInt. }
       { intros x Hx.
         a dmit. }
     }
     { rewrite RInt_scal.
       2: { apply G2_exRInt. }
       rewrite /scal/=/mult/=.
       apply Req_le.
       reflexivity. }
   }
   }
  { (* Need to prove: ex_seriesC (λ k, M * RInt (G2_μ k) 0 1) *)
    apply ex_seriesC_scal_l.
    rewrite /G2_μ.
    replace (fun (x : nat) => (RInt (λ x0 : R, exp (- (x0 + x) ^ 2 / 2) / Norm2) 0 1))
       with (fun (x : nat) => (RInt (λ x0 : R, exp (- (x0 + x) ^ 2 / 2)) 0 1 * / Norm2)).
    2: {
      funexti.
      rewrite RInt_Rmult'; OK.
      apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      intros ??.
      apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      by auto_derive.
    }
    apply ex_seriesC_scal_r.
    (* I think I can upper-bound this integral by its max value, which is e^-x^2, whose series converges. *)
    a dmit.
  }
*)
  Admitted.


  Lemma G2_g_ub {F} {M : R} (Hnn : ∀ (x : nat) (k : R), 0 <= F x k <= M) {r t} (Ht : 0 <= t <= 1) (Hint : ∀ x' : nat, ex_RInt (F x') 0 1) : G2_g F r t <= M.
  Proof.
    rewrite /G2_g.
    rewrite /G2_s.
    rewrite Iverson_True; OK.
    rewrite Iverson_False; OK.
    rewrite Iverson_False; OK.
    rewrite Iverson_True; OK.
    repeat rewrite Rmult_1_l.
    repeat rewrite Rmult_0_l.
    rewrite Rplus_0_r Rplus_0_l.
    suffices H : exp (- t * (2 * r + t) / 2) * M + (1 - exp (- t * (2 * r + t) / 2)) * M <= M; last first.
    { rewrite -Rmult_plus_distr_r. OK. }
    etrans; last apply H.
    apply Rplus_le_compat.
    { apply Rmult_le_compat_l; [apply Rexp_nn|apply Hnn]. }
    { apply Rmult_le_compat_l; [|apply G2_CreditV_ub; OK].
      apply Rle_0_le_minus.
      apply Rexp_range; OK.
      rewrite Rdiv_def.
      rewrite Rmult_assoc.
      apply Rcomplements.Rmult_le_0_r; OK.
      apply Rle_mult_inv_pos; OK.
      apply Rplus_le_le_0_compat; OK.
      apply Rmult_le_pos; OK.
      apply pos_INR.
    }
  Qed.

  Lemma G2_ub {F} {M : R} (Hnn : ∀ (x : nat) (k : R), 0 <= F x k <= M) {r} (Hex : forall r, ex_RInt (λ y : R, F r y) 0 1) :  G2_f F r <= M.
  Proof.
    rewrite /G2_f.
      etrans.
      { etrans; [apply RRle_abs|].
        apply abs_RInt_le_const; OK.
        { apply G2_g_exRInt; OK. }
        intros ??.
        rewrite Rabs_pos_eq; [|apply G2_g_nn]; OK.
        { eapply G2_g_ub; OK. }
        { intros ??; apply Hnn. }
      }
      OK.
  Qed.

  Lemma G1_f_nn {F k} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_f F k.
  Proof.
    rewrite /G1_f.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [| apply G1_h_nn; auto ]).
    { apply Rexp_range.
      apply Rcomplements.Rmult_le_0_r; last lra.
      have ? : 0 <= (k * (k-1))%nat by apply pos_INR.
      lra.
    }
    { apply error_credits.Rle_0_le_minus.
      apply Rexp_range.
      have ? : 0 <= (k * (k-1))%nat by apply pos_INR.
      lra.
    }
  Qed.

  Lemma G1_f_expectation {F M} (Hnn : ∀ x, 0 <= F x <= M) : G1_CreditV F = Geo_CreditV (G1_f F) (exp (-1 / 2)) 0.
  Proof.
    have HM : 0 <= M. { specialize Hnn with 0%nat. OK.  }
    rewrite /G1_CreditV.
    (* Simplify the RHS *)
    rewrite /Geo_CreditV.
    rewrite /Geo_μ.
    setoid_rewrite Iverson_True; [|rewrite//=; lia].
    setoid_rewrite Rmult_1_l.
    setoid_rewrite Nat.sub_0_r.
    (* Split and simplify the sum *)
    rewrite /G1_f.
    setoid_rewrite Rmult_plus_distr_r.
    rewrite SeriesC_plus.
    2: {
      apply (ex_seriesC_le _ (λ x : nat, 1 * M * (exp (-1 / 2) ^ x * 1))).
      { intros n.
        split.
        { apply Rmult_le_pos; OK; apply Rmult_le_pos; OK.
          { apply Rexp_nn. }
          { apply G1_h_nn. apply Hnn. }
          { apply pow_le. apply Rexp_nn. }
          { apply Rle_0_le_minus.
            apply Rexp_range.
            OK.
          }
        }
        apply Rmult_le_compat.
        { apply Rmult_le_pos; [apply Rexp_nn | apply G1_h_nn; apply Hnn]. }
        { apply Rmult_le_pos; [apply pow_le, Rexp_nn | apply Rle_0_le_minus, Rexp_range; OK]. }
        { apply Rmult_le_compat.
          { apply Rexp_nn; OK. }
          { apply G1_h_nn; OK. apply Hnn. }
          { apply Rexp_range.
            rewrite Rdiv_def.
            apply Rcomplements.Rmult_le_0_r; OK.
            rewrite -Ropp_0.
            apply Ropp_le_contravar.
            apply pos_INR.
          }
          { apply G1_h_ub; OK. }
        }
        { apply Rmult_le_compat.
          { apply pow_le, Rexp_nn. }
          { apply Rle_0_le_minus, Rexp_range; OK. }
          { OK. }
          { have ? : (0 <= exp (-1 / 2)) by apply Rexp_nn. OK. }
        }
      }
      apply ex_seriesC_scal_l.
      apply ex_seriesC_scal_r.
      rewrite -ex_seriesC_nat.
      apply Series.ex_series_geom.
      rewrite Rabs_right; [|apply Rle_ge, Rexp_nn].
      rewrite -exp_0.
      apply exp_mono_strict.
      OK.
    }
    2: {
      apply (ex_seriesC_le _ (λ x : nat, 1 * M * (exp (-1 / 2) ^ x * 1))).
      { intros n.
        split.
        { apply Rmult_le_pos; OK; apply Rmult_le_pos; OK.
          { apply Rle_0_le_minus, Rexp_range.
            apply Rcomplements.Rmult_le_0_r; OK.
            rewrite -Ropp_0. apply Ropp_le_contravar, pos_INR.  }
          { apply G1_h_nn. apply Hnn. }
          { apply pow_le. apply Rexp_nn. }
          { apply Rle_0_le_minus. apply Rexp_range. OK. }
        }
        apply Rmult_le_compat.
        { apply Rmult_le_pos; [| apply G1_h_nn; apply Hnn].
          apply Rle_0_le_minus, Rexp_range.
          apply Rcomplements.Rmult_le_0_r; OK.
          rewrite -Ropp_0. apply Ropp_le_contravar, pos_INR.
        }
        { apply Rmult_le_pos; [apply pow_le, Rexp_nn | apply Rle_0_le_minus, Rexp_range; OK]. }
        { apply Rmult_le_compat.
          { apply Rle_0_le_minus, Rexp_range.
            apply Rcomplements.Rmult_le_0_r; OK.
            rewrite -Ropp_0. apply Ropp_le_contravar, pos_INR.   }
          { apply G1_h_nn; OK. apply Hnn. }
          { have ? : 0 <= exp (- (n * (n - 1))%nat / 2) by apply Rexp_nn. OK. }
          { apply G1_h_ub; OK. }
        }
        { apply Rmult_le_compat; OK.
          { apply pow_le, Rexp_nn. }
          { apply Rle_0_le_minus, Rexp_range; OK. }
          { have ? : (0 <= exp (-1 / 2)) by apply Rexp_nn. OK. }
        }
      }
      apply ex_seriesC_scal_l.
      apply ex_seriesC_scal_r.
      rewrite -ex_seriesC_nat.
      apply Series.ex_series_geom.
      rewrite Rabs_right; [|apply Rle_ge, Rexp_nn].
      rewrite -exp_0.
      apply exp_mono_strict.
      OK.
    }
    rewrite /G1_h.
    rewrite Iverson_True; [|intuition].
    rewrite Iverson_False; [|intuition].
    rewrite Iverson_False; [|intuition].
    rewrite Iverson_True; [|intuition].
    setoid_rewrite Rmult_1_l.
    setoid_rewrite Rmult_0_l.
    setoid_rewrite Rplus_0_l.
    setoid_rewrite Rplus_0_r.
    (* Rightmost term: Commute out the sum inside G1_CreditV *)
    rewrite /G1_CreditV.
    replace (SeriesC (λ x : nat, (1 - exp (- (x * (x - 1))%nat / 2)) * SeriesC (λ k : nat, G1_μ k * F k) * (exp (-1 / 2) ^ x * (1 - exp (-1 / 2)))))
       with (SeriesC (λ k : nat, G1_μ k * F k * SeriesC (λ x : nat,  (1 - exp (- (x * (x - 1))%nat / 2)) * (exp (-1 / 2) ^ x * (1 - exp (-1 / 2))))));
      last first.
    {
      have Hnn1 : ∀ a, 0 <= (1 - exp (- (a * (a - 1))%nat / 2)).
      { intros a.
        suffices ? : exp (- (a * (a - 1))%nat / 2) <= 1 by OK.
        rewrite -exp_0.
        apply exp_mono.
        rewrite Rdiv_def.
        apply Rcomplements.Rmult_le_0_r; OK.
        rewrite -Ropp_0.
        apply Ropp_le_contravar.
        apply pos_INR.
      }
      have Hnn2 : ∀ a, 0 <= (exp (-1 / 2) ^ a * (1 - exp (-1 / 2))).
      { intros a.
        apply Rmult_le_pos; OK.
        { apply pow_le. apply Rexp_nn. }
        suffices ? : exp (-1 / 2) <= 1 by OK.
        rewrite -exp_0.
        apply exp_mono.
        OK.
      }
      have Hbound1 : forall a, 1 - exp (- (a * (a - 1))%nat / 2) <= 1.
      { intros a.
        suffices ? : (0 <= exp (- (a * (a - 1))%nat / 2)) by OK.
        apply Rexp_nn.
      }
      replace (SeriesC (λ k : nat, G1_μ k * F k * SeriesC (λ x : nat, (1 - exp (- (x * (x - 1))%nat / 2)) * (exp (-1 / 2) ^ x * (1 - exp (-1 / 2))))))
         with (SeriesC (λ k : nat, SeriesC (λ x : nat, G1_μ k * F k * (1 - exp (- (x * (x - 1))%nat / 2)) * (exp (-1 / 2) ^ x * (1 - exp (-1 / 2)))))).
      2: {
        apply SeriesC_ext. intros ?.
        rewrite -SeriesC_scal_l.
        apply SeriesC_ext. intros ?.
        OK.
      }
      rewrite fubini_pos_seriesC'.
      { apply SeriesC_ext. intros ?.
        rewrite -SeriesC_scal_l.
        rewrite -SeriesC_scal_r.
        apply SeriesC_ext. intros ?.
        OK.
      }
      { intros ??.
        apply Rmult_le_pos; OK.
        apply Rmult_le_pos; OK.
        apply Rmult_le_pos; [|apply Hnn].
        apply G1_μ_nn.
      }
      { intros a.
        apply ex_seriesC_scal_r.
        apply (ex_seriesC_le _ (λ x : nat, G1_μ x * M * 1)).
        2 : {
          apply ex_seriesC_scal_r.
          apply ex_seriesC_scal_r.
          rewrite /G1_μ.
          replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with (λ k : nat, exp (- k ^ 2 / 2) * / Norm1) by (funexti; OK).
          apply ex_seriesC_scal_r.
          apply Norm1_ex.
        }
        intros ?.
        split.
        { apply Rmult_le_pos; OK.
          apply Rmult_le_pos; [|apply Hnn].
          apply G1_μ_nn.
        }
        apply Rmult_le_compat; OK.
        { apply Rmult_le_pos; [|apply Hnn]. apply G1_μ_nn. }
        { apply Rmult_le_compat; OK; try apply Hnn. apply G1_μ_nn. }
      }
      { replace (λ a : nat, SeriesC (λ b : nat, G1_μ b * F b * (1 - exp (- (a * (a - 1))%nat / 2)) * (exp (-1 / 2) ^ a * (1 - exp (-1 / 2)))))
           with (λ a : nat, SeriesC (λ b : nat, G1_μ b * F b) * (1 - exp (- (a * (a - 1))%nat / 2)) * (exp (-1 / 2) ^ a * (1 - exp (-1 / 2)))).
        2 : {
          funexti.
          repeat rewrite SeriesC_scal_r.
          OK.
        }
        apply (ex_seriesC_le _ (λ a : nat, M * (1 * (exp (-1 / 2) ^ a * (1 - exp (-1 / 2)))))).
        { intros ?.
          split.
          { rewrite Rmult_assoc.
            apply Rmult_le_pos.
            { apply SeriesC_ge_0'.
              intros ?.
              apply Rmult_le_pos; [|apply Hnn]. apply G1_μ_nn.
            }
          { apply Rmult_le_pos; OK. }
        }
        rewrite Rmult_assoc.
        apply Rmult_le_compat; OK.
        { apply SeriesC_ge_0'.
          intros ?.
          apply Rmult_le_pos; [|apply Hnn]. apply G1_μ_nn.
        }
        { apply Rmult_le_pos; OK. }
        { etrans; first eapply (SeriesC_le _ (fun b : nat => G1_μ b * M)).
          { intros ?.
            split.
            { apply Rmult_le_pos; [|apply Hnn]. apply G1_μ_nn. }
            apply Rmult_le_compat; OK; try apply Hnn.
            apply G1_μ_nn.
          }
          { apply ex_seriesC_scal_r.
            rewrite /G1_μ.
            replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with (λ k : nat, exp (- k ^ 2 / 2) * / Norm1) by (funexti; OK).
            apply ex_seriesC_scal_r.
            apply Norm1_ex.
          }
          { rewrite SeriesC_scal_r.
            rewrite G1_μ_pmf.
            OK.
          }
        }
        { apply Rmult_le_compat; OK. }
        }
        apply ex_seriesC_scal_l.
        apply ex_seriesC_scal_l.
        apply ex_seriesC_scal_r.
        rewrite -ex_seriesC_nat.
        apply Series.ex_series_geom.
        rewrite Rabs_right.
        { rewrite -exp_0. apply exp_mono_strict. OK. }
        { apply Rle_ge. apply Rexp_nn. }
      }
    }
    rewrite -SeriesC_plus.
    2: {
      apply (ex_seriesC_le _ (λ x : nat, 1 * M * (exp (-1 / 2) ^ x * 1))).
      { intros n.
        split.
        { apply Rmult_le_pos; OK; apply Rmult_le_pos; OK.
          { apply Rexp_nn. }
          { apply Hnn. }
          { apply pow_le. apply Rexp_nn. }
          { apply Rle_0_le_minus.
            apply Rexp_range.
            OK.
          }
        }
        apply Rmult_le_compat.
        { apply Rmult_le_pos; [apply Rexp_nn | apply Hnn; apply Hnn]. }
        { apply Rmult_le_pos; [apply pow_le, Rexp_nn | apply Rle_0_le_minus, Rexp_range; OK]. }
        { apply Rmult_le_compat.
          { apply Rexp_nn; OK. }
          { apply Hnn; OK. }
          { apply Rexp_range.
            rewrite Rdiv_def.
            apply Rcomplements.Rmult_le_0_r; OK.
            rewrite -Ropp_0.
            apply Ropp_le_contravar.
            apply pos_INR.
          }
          { apply Hnn; OK. }
        }
        { apply Rmult_le_compat.
          { apply pow_le, Rexp_nn. }
          { apply Rle_0_le_minus, Rexp_range; OK. }
          { OK. }
          { have ? : (0 <= exp (-1 / 2)) by apply Rexp_nn. OK. }
        }
      }
      apply ex_seriesC_scal_l.
      apply ex_seriesC_scal_r.
      rewrite -ex_seriesC_nat.
      apply Series.ex_series_geom.
      rewrite Rabs_right; [|apply Rle_ge, Rexp_nn].
      rewrite -exp_0.
      apply exp_mono_strict.
      OK.
    }
    2: {
      have HS : 0 <= SeriesC (λ x : nat, (1 - exp (- (x * (x - 1))%nat / 2)) * (exp (-1 / 2) ^ x * (1 - exp (-1 / 2)))).
      { apply SeriesC_ge_0'.
            intros n'.
            apply Rmult_le_pos; last apply Rmult_le_pos.
            { apply Rle_0_le_minus, Rexp_range.
              apply Rcomplements.Rmult_le_0_r; OK.
              rewrite -Ropp_0. apply Ropp_le_contravar, pos_INR.  }
            { apply pow_le, Rexp_range; OK. }
            { apply Rle_0_le_minus, Rexp_range.
              apply Rcomplements.Rmult_le_0_r; OK. }
      }


      apply (ex_seriesC_le _ (λ k : nat, G1_μ k * M * SeriesC (λ x : nat, 1 * (exp (-1 / 2) ^ x * 1)))).
      { intros n. split.
        { apply Rmult_le_pos; OK; first apply Rmult_le_pos; OK.
          { apply G1_μ_nn. }
          { apply Hnn. }
        }
        apply Rmult_le_compat; OK.
        { apply Rmult_le_pos; [ apply G1_μ_nn | apply Hnn ]. }
        { apply Rmult_le_compat; OK.
          { apply G1_μ_nn. }
          { apply Hnn. }
          { apply Hnn. }
        }
        apply SeriesC_le.
        { intros n'; split.
          { apply Rmult_le_pos.
            { apply Rle_0_le_minus, Rexp_range. apply Rcomplements.Rmult_le_0_r; OK. rewrite -Ropp_0. apply Ropp_le_contravar, pos_INR.  }
            apply Rmult_le_pos.
            { apply pow_le, Rexp_nn. }
            { apply Rle_0_le_minus, Rexp_range. OK. }
          }
          apply Rmult_le_compat; OK.
          { apply Rle_0_le_minus, Rexp_range. apply Rcomplements.Rmult_le_0_r; OK. rewrite -Ropp_0. apply Ropp_le_contravar, pos_INR.  }
          { apply Rmult_le_pos.
            { apply pow_le, Rexp_nn. }
            { apply Rle_0_le_minus, Rexp_range. OK. }
          }
          { have ? : 0 <= exp (- (n' * (n' - 1))%nat / 2) by apply Rexp_nn. OK. }
          apply Rmult_le_compat; OK.
          { apply pow_le, Rexp_nn. }
          { apply Rle_0_le_minus, Rexp_range. OK. }
          { have ? : 0 <= exp (-1 / 2) by apply Rexp_nn. OK. }
        }
        apply ex_seriesC_scal_l.
        apply ex_seriesC_scal_r.
        rewrite -ex_seriesC_nat.
        apply Series.ex_series_geom.
        rewrite Rabs_right; [|apply Rle_ge, Rexp_nn].
        rewrite -exp_0.
        apply exp_mono_strict.
        OK.
      }

      apply (ex_seriesC_le _ (λ k : nat, G1_μ k * M * (1 / (1 - exp (-1 / 2))))).
      { intros n.
        split.
        { apply Rmult_le_pos; OK; first apply Rmult_le_pos; OK.
          { apply G1_μ_nn. }
          { apply SeriesC_ge_0'. intros ?. apply Rmult_le_pos; OK. apply Rmult_le_pos; OK. apply pow_le, Rexp_nn. }
        }
        apply Rmult_le_compat; OK.
        { apply Rmult_le_pos; [ apply G1_μ_nn | OK  ]. }
        { apply SeriesC_ge_0'. intros ?. apply Rmult_le_pos; OK. apply Rmult_le_pos; OK. apply pow_le, Rexp_nn. }
        { rewrite SeriesC_scal_l Rmult_1_l.
          rewrite SeriesC_scal_r Rmult_1_r.
          right.
          rewrite SeriesC_nat.
          rewrite Series.Series_geom; OK.
          rewrite Rabs_right.
          { rewrite -exp_0. apply exp_mono_strict. OK. }
          { apply Rle_ge, Rexp_nn. }
        }
      }
      apply ex_seriesC_scal_r.
      apply ex_seriesC_scal_r.
      rewrite /G1_μ.
      replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with (λ k : nat, exp (- k ^ 2 / 2) * / Norm1) by (funexti; OK).
      apply ex_seriesC_scal_r.
      apply Norm1_ex.
    }

    f_equal. apply functional_extensionality. intro k.
    (* Cancel F *)
    do 2 rewrite (Rmult_assoc _ (F k) _) (Rmult_comm (F k) _) -(Rmult_assoc _ _ (F k)).
    rewrite -Rmult_plus_distr_r.
    f_equal.
    (* Simplify the first term *)
    rewrite -Rmult_assoc.
    rewrite exp_pow.
    rewrite -exp_plus.
    have Hcong : forall k : nat, ((- (k * (k - 1))%nat / 2 + -1 / 2 * k)) = ((-k^2)/2).
    { intros k'. destruct k' as [|k''].
      { rewrite INR_0. lra. }
      rewrite mult_INR minus_INR; last lia.
      rewrite INR_1; lra.
    }
    rewrite Hcong.
    (* Cancel the e^{-k^2/2} term*)
    rewrite /G1_μ.
    rewrite Rmult_assoc.
    rewrite -Rmult_plus_distr_l.
    replace (exp (- k ^ 2 / 2) / Norm1) with (exp (- k ^ 2 / 2) * (/ Norm1)) by lra.
    f_equal.
    (* Simplify the sum on the RHS *)
    rewrite -(Rmult_1_l (1 - exp (-1 / 2))).
    rewrite -{1}(Rinv_l Norm1); last (have ? := Norm1_nn; lra).
    rewrite Rmult_assoc.
    rewrite -Rmult_plus_distr_l.
    rewrite -{1}(Rmult_1_r (/Norm1)); f_equal.
    rewrite /Norm1.
    replace (SeriesC (λ x : nat, (1 - exp (- (x * (x - 1))%nat / 2)) * (exp (-1 / 2) ^ x * (1 * (1 - exp (-1 / 2))))))
       with (SeriesC (λ x : nat, ((1 - exp (- (x * (x - 1))%nat / 2)) * (exp (-1 / 2) ^ x) * (1 - exp (-1 / 2)))));
       last first.
    { f_equal; apply functional_extensionality; intros ?. lra. }
    rewrite SeriesC_scal_r.
    rewrite -Rmult_plus_distr_r.
    rewrite -SeriesC_plus.
    2: { apply Norm1_ex. }
    2: {
      apply (ex_seriesC_le _  (λ x : nat, 1 * exp (-1 / 2) ^ x)).
      { intros n.
        split.
        { apply Rmult_le_pos.
          { apply Rle_0_le_minus, Rexp_range. apply Rcomplements.Rmult_le_0_r; OK. rewrite -Ropp_0. apply Ropp_le_contravar, pos_INR.  }
          { apply pow_le, Rexp_nn. }
        }
        apply Rmult_le_compat; OK.
        { apply Rle_0_le_minus, Rexp_range. apply Rcomplements.Rmult_le_0_r; OK. rewrite -Ropp_0. apply Ropp_le_contravar, pos_INR.  }
        { apply pow_le, Rexp_nn. }
        { have ? : 0 <= exp (- (n * (n - 1))%nat / 2) by apply Rexp_nn. OK. }
      }
      apply ex_seriesC_scal_l.
      rewrite -ex_seriesC_nat.
      apply Series.ex_series_geom.
      rewrite Rabs_right; [|apply Rle_ge, Rexp_nn].
      rewrite -exp_0.
      apply exp_mono_strict.
      OK.
    }
    replace (λ x : nat, exp (- x ^ 2 / 2) + (1 - exp (- (x * (x - 1))%nat / 2)) * exp (-1 / 2) ^ x)
       with (λ x : nat, exp (- x ^ 2 / 2) + ( exp (-1 / 2) ^ x - exp (- x^2 / 2))); last first.
    { apply functional_extensionality; intros x.
      f_equal.
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_1_l.
      rewrite Rminus_def.
      f_equal.
      rewrite Ropp_mult_distr_l_reverse.
      f_equal.
      rewrite exp_pow.
      rewrite -exp_plus.
      f_equal.
      by rewrite Hcong.
    }
    replace (λ x : nat, exp (- x ^ 2 / 2) + (exp (-1 / 2) ^ x - exp (- x ^ 2 / 2)))
       with (λ x : nat, (exp (-1 / 2) ^ x)); last first.
    { apply functional_extensionality; intros x. lra. }
    rewrite SeriesC_nat.
    rewrite Series.Series_geom.
    { rewrite Rinv_l; OK.
      apply Rminus_eq_contra.
      rewrite -exp_0.
      intro HK.
      apply exp_inj in HK.
      OK.
    }
    rewrite Rabs_right.
    { rewrite -exp_0. apply exp_mono_strict. OK. }
    { apply Rle_ge, Rexp_nn. }
  Qed.


  Lemma HL5 {F M} (Hex : ∀ x1, ex_RInt (F x1) 0 1) (Hbound : ∀ n x, 0 <= F n x <= M) :
    ∀ k, ex_RInt (λ x1 : R, RInt (λ x0 : R, SeriesC (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1)) 0 1) 0 1.
  Proof.
    intros k.
    apply (ex_RInt_ext (λ x1 : R, G2_μ k x1 * F k x1 * RInt (λ x0 : R, SeriesC (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)))) 0 1)).
    - rewrite Rmin_left; [|lra]. rewrite Rmax_right; [|lra].
      intros x [Hx0 Hx1].
      symmetry.
      rewrite (RInt_ext _ (λ x0 : R, G2_μ k x * F k x * SeriesC (λ x1 : nat, G1_μ x1 * (1 - exp (- x0 * (2 * x1 + x0) / 2))))).
      + symmetry.
        apply RInt_Rmult.
        have HL : ∀ (n : nat) x0, 0 <= x0 <= 1 → 0 <= (1 - exp (- x0 * (2 * n + x0) / 2)) <= 1.
        { intros ???.
          suffices ? : 0 <= exp (- x0 * (2 * n + x0) / 2) <= 1 by OK.
          split.
          { apply Rexp_nn. }
          { apply Rexp_range.
            replace (- x0 * (2 * n + x0) / 2) with ((-1 / 2) * (x0 * (2 * n + x0))) by OK.
            replace 0 with ((-1/2) * 0) by OK.
            apply Rmult_le_compat_neg_l; OK.
            apply Rmult_le_pos; OK.
            apply Rplus_le_le_0_compat; OK.
            apply Rmult_le_pos; OK.
            apply pos_INR.
          }
        }
        apply (ex_RInt_SeriesC G1_μ); OK.
        { rewrite /G1_μ.
          rewrite ex_seriesC_nat.
          replace (λ k0 : nat, exp (- k0 ^ 2 / 2) / Norm1) with (λ k0 : nat, exp (- k0 ^ 2 / 2) * / Norm1) by (funexti; OK).
          apply ex_seriesC_scal_r.
          apply Norm1_ex.
        }
        { intros ???.
          split.
          { apply Rmult_le_pos; OK.
               { apply G1_μ_nn. }
               { apply HL. OK. }
          }
          rewrite -{2}(Rmult_1_r (G1_μ n)).
          apply Rmult_le_compat; OK.
          { apply G1_μ_nn. }
          { apply HL. OK. }
          { apply HL. OK. }
        }
        { intros ?.
          apply ex_RInt_mult.
          { apply ex_RInt_const.  }
          { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
            intros ??.
            apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
            by auto_derive.
          }
        }
      + intros x0 _.
        rewrite SeriesC_scal_r.
        rewrite SeriesC_scal_r.
        lra.
    - apply ex_RInt_mult.
      { apply ex_RInt_mult; [|apply Hex].
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        rewrite /G2_μ.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply ex_RInt_const. }
  Qed.


  Lemma HL3 {F M} (HPcs : ∀ x1, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= F n x <= M) :
    ex_seriesC (λ k : nat, RInt (λ x1 : R, RInt (λ x0 : R, SeriesC (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1)) 0 1) 0 1).
  Proof.
    have Hex : ∀ x1, ex_RInt (F x1) 0 1.
    { intros n. apply (@PCts_RInt _ 0 1). done. }

    (* Shuffle around inner terms *)
    suffices H1 :
      @ex_seriesC nat numbers.Nat.eq_dec nat_countable (λ k : nat, RInt (λ x1 : R, RInt (λ x0 : R,  G2_μ k x1 * F k x1 * @SeriesC nat numbers.Nat.eq_dec nat_countable (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)))) 0 1) 0 1).
    { eapply ex_seriesC_ext; [|apply H1].
      intros n. rewrite //=.
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite -SeriesC_scal_l.
      apply SeriesC_ext.
      intros ?; OK.
    }

    have HG2Le : ∀ k x, 0 <= x <= 1 → G2_μ k x <= exp (-k^2 / 2) / Norm2.
    { intros ???.
      rewrite /G2_μ.
      rewrite Rdiv_def.
      apply Rmult_le_compat_r.
      { have ? := Norm2_nn.
        rewrite -(Rmult_1_l (/ Norm2)).
        apply Rle_mult_inv_pos; OK.
      }
      apply exp_mono.
      rewrite Rdiv_def.
      apply Rmult_le_compat_r; OK.
      apply Ropp_le_contravar.
      apply pow_incr.
      have ? := (pos_INR k).
      OK.
    }

    have HFubiniEx4 : ∀ x (x0 : nat), 0 <= x <= 1 → 0 <= 1 - exp (- x * (2 * x0 + x) / 2).
    { intros ???.
      suffices ? : exp (- x * (2 * x0 + x) / 2) <= 1 by OK.
      apply Rexp_range.
      apply Rcomplements.Rmult_le_0_r; OK.
      apply Rcomplements.Rmult_le_0_r; OK.
      have ? := pos_INR x0.
      OK.
    }

    have HFubiniEx5 : ∀ n t, 0 <= t <= 1 → ex_RInt (λ x0 : R, G2_μ n t * F n t * SeriesC (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)))) 0 1.
    { intros ???.
      apply ex_RInt_Rmult.
      apply (ex_RInt_SeriesC G1_μ); OK.
      { rewrite /G1_μ.
        replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with (λ k : nat, exp (- k ^ 2 / 2) * / Norm1) by (funexti; OK).
        rewrite ex_seriesC_nat.
        apply ex_seriesC_scal_r.
        apply Norm1_ex.
      }
      { intros ???.
        split.
        { apply Rmult_le_pos; [apply G1_μ_nn|]. apply HFubiniEx4; OK. }
        { rewrite -{2}(Rmult_1_r (G1_μ n0)).
          apply Rmult_le_compat_l; OK.
          { apply G1_μ_nn. }
          suffices  ? : 0 <= exp (- x * (2 * n0 + x) / 2)  by OK.
          apply Rexp_nn.
        }
      }
      { intros ?.
        apply ex_RInt_Rmult.
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
    }

    have FubiniEx3 : ∀ n t, 0 <= t <= 1 → 0 <= RInt (λ x0 : R, G2_μ n t * F n t * SeriesC (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)))) 0 1.
    { intros ???.
      apply RInt_ge_0; OK.
      intros ??.
      apply Rmult_le_pos; [apply Rmult_le_pos|].
      { apply G2_μ_nn; OK. }
      { apply Hbound. }
      { apply SeriesC_ge_0'.
        intros ?.
        apply Rmult_le_pos.
        { apply G1_μ_nn. }
        { apply HFubiniEx4.  OK. }
      }
    }

    have HFubiniEx2 : ∀ n,  ex_RInt (λ x1 : R, RInt (λ x0 : R, G2_μ n x1 * F n x1 * SeriesC (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)))) 0 1) 0 1.
    { intros ?.
      apply Fubini_Step_ex_x.
      apply IsFubiniRR_mult; [apply IsFubiniRR_mult|].
      { apply PCts_const_x.
        apply PCts_cts.
        rewrite /Ioo//=.
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
        intros ??.
        rewrite /G2_μ.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { apply PCts_const_x. apply HPcs. }
      { apply PCts_const_y.
        apply PCts_cts.
        rewrite /Ioo//=.
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
        intros ??.
        admit.
      }
    }

    have HFubiniEx1 : ∀ n, 0 <= RInt (λ x1 : R, RInt (λ x0 : R, G2_μ n x1 * F n x1 * SeriesC (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)))) 0 1) 0 1.
    { intros ?. apply RInt_ge_0; OK.
      intros ??.
      apply FubiniEx3.
      OK.
    }

    (* Bound the outer integral above *)
    suffices H1 : (@ex_seriesC nat numbers.Nat.eq_dec nat_countable (λ k : nat, RInt (λ x0 : R, (exp (-k^2 / 2) / Norm2) * M * @SeriesC nat numbers.Nat.eq_dec nat_countable (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)))) 0 1)).
    { eapply ex_seriesC_le; [|apply H1].
      intros ?.
      split; [apply HFubiniEx1|].
      rewrite -(Rabs_right _ (Rle_ge _ _ (HFubiniEx1 n))).
      etrans; first apply abs_RInt_le_const.
      1, 2: OK.
      2: { rewrite Rminus_0_r Rmult_1_l. right. done. }
      intros ??.
      rewrite Rabs_right.
      2: { apply Rle_ge. apply FubiniEx3. OK. }
      apply RInt_le; OK.
      { apply ex_RInt_Rmult.
        apply (ex_RInt_SeriesC G1_μ); OK.
        { rewrite /G1_μ.
          replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with (λ k : nat, exp (- k ^ 2 / 2) * / Norm1) by (funexti; OK).
          rewrite ex_seriesC_nat.
          apply ex_seriesC_scal_r.
          apply Norm1_ex.
        }
        { intros ???.
          split.
          { apply Rmult_le_pos; [apply G1_μ_nn|]. apply HFubiniEx4; OK. }
          { rewrite -{2}(Rmult_1_r (G1_μ n0)).
            apply Rmult_le_compat_l; OK.
            { apply G1_μ_nn. }
            suffices  ? : 0 <= exp (- x * (2 * n0 + x) / 2)  by OK.
            apply Rexp_nn.
          }
        }
        { intros ?.
          apply ex_RInt_Rmult.
          apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      { intros ??.
        apply Rmult_le_compat_r; OK.
        { apply SeriesC_ge_0'.
          intros ?.
          apply Rmult_le_pos; [apply G1_μ_nn|].
          apply HFubiniEx4; OK.
        }
        { apply Rmult_le_compat; OK.
          { apply G2_μ_nn. OK. }
          { apply Hbound. }
          { apply Hbound. }
        }
      }
    }

    (* Move k factor out *)
    suffices H1 : @ex_seriesC nat numbers.Nat.eq_dec nat_countable (λ k : nat, exp (- k ^ 2 / 2) * / Norm2 * RInt (λ x0 : R, M * @SeriesC nat numbers.Nat.eq_dec nat_countable  (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)))) 0 1).
    { eapply ex_seriesC_ext; last eapply H1.
      intros ?. simpl.
      rewrite RInt_Rmult.
      2: {
        apply ex_RInt_Rmult.
        apply (ex_RInt_SeriesC G1_μ); OK.
        { rewrite /G1_μ.
          replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with (λ k : nat, exp (- k ^ 2 / 2) * / Norm1) by (funexti; OK).
          rewrite ex_seriesC_nat.
          apply ex_seriesC_scal_r.
          apply Norm1_ex.
        }
        { intros ???.
          split.
          { apply Rmult_le_pos; [apply G1_μ_nn|]. apply HFubiniEx4; OK. }
          { rewrite -{2}(Rmult_1_r (G1_μ n0)).
            apply Rmult_le_compat_l; OK.
            { apply G1_μ_nn. }
            suffices  ? : 0 <= exp (- x * (2 * n0 + x) / 2)  by OK.
            apply Rexp_nn.
          }
        }
        { intros ?.
          apply ex_RInt_Rmult.
          apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
      apply RInt_ext.
      intros ??; OK.
    }

    (* Now we can get rid of that integral entirely *)
    apply ex_seriesC_scal_r.
    apply ex_seriesC_scal_r.
    apply Norm1_ex.
  Admitted.

  Lemma HR1 {F M} (Hex : ∀ x1, ex_RInt (F x1) 0 1) (Hbound : ∀ n x, 0 <= F n x <= M) :
    Series.Series (λ x : nat, Series.Series (λ k : nat, RInt (λ x0 : R, RInt (λ x1 : R, (G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1)) 0 1) 0 1)) =
    Series.Series (λ x : nat, RInt (λ x0 : R, Series.Series (λ k : nat, RInt (λ x1 : R, (G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1)) 0 1)) 0 1).
  Proof.
    apply Series.Series_ext; intros n.
    apply (FubiniIntegralSeries_Strong (fun k => M * RInt (G2_μ k) 0 1)).
    - OK.
    - intros ???.
      have L1 : ex_RInt (λ x1 : R, G1_μ n * (1 - exp (- x * (2 * n + x) / 2)) * G2_μ n0 x1 * F n0 x1) 0 1.
      { apply ex_RInt_mult; OK.
      replace (λ y : R, G1_μ n * (1 - exp (- x * (2 * n + x) / 2)) * G2_μ n0 y)
         with (λ y : R, scal (G1_μ n * (1 - exp (- x * (2 * n + x) / 2))) (G2_μ n0 y)).
      2: { apply functional_extensionality; intros. rewrite /scal/=/mult/=. done. }
      apply (ex_RInt_scal (V := R_CompleteNormedModule)).
      apply G2_exRInt.
      }
      have L2 :  ∀ x0 : R, 0 < x0 < 1 → 0 <= G1_μ n * (1 - exp (- x * (2 * n + x) / 2)) * G2_μ n0 x0 * F n0 x0.
      { intros x1 Hx1.
        apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
        { apply G1_μ_nn. }
        { suffices ? :  exp (- x * (2 * n + x) / 2) <= 1 by OK.
          apply Rexp_range.
          replace (- x * (2 * n + x) / 2) with ((-1 / 2) * (x * (2 * n + x))) by OK.
          replace 0 with ((-1/2) * 0) by OK.
          apply Rmult_le_compat_neg_l; OK.
          apply Rmult_le_pos; OK.
          apply Rplus_le_le_0_compat; OK.
          apply Rmult_le_pos; OK.
          apply pos_INR.
          }
        { apply G2_μ_nn. OK. }
        { apply Hbound. }
      }
      apply RInt_ge_0; OK.
    - (* Goal 1: Series convergence - COMPLETED *)
      rewrite ex_seriesC_nat.
      apply ex_seriesC_scal_l.
      rewrite /G2_μ.
      apply (ex_seriesC_RInt (fun m => exp (- (0 + m) ^ 2 / 2) * / Norm2)).
      + OK.
      + intros x n0 Hx; apply Rmult_le_pos; [apply Rexp_nn | apply Rlt_le, Rinv_0_lt_compat, Norm2_nn].
      + apply ex_seriesC_scal_r, Norm2_ex'; lra.
      + intros x n0 Hx.
        rewrite Rabs_right.
        2: { apply Rle_ge, Rmult_le_pos; [apply Rexp_nn | apply Rlt_le, Rinv_0_lt_compat, Norm2_nn]. }
        rewrite Rdiv_def.
        apply Rmult_le_compat_r.
        { apply Rlt_le, Rinv_0_lt_compat, Norm2_nn. }
        apply exp_mono.
        replace (- (x + n0) ^ 2 / 2) with ((-1/2) * (x + n0) ^ 2) by lra.
        replace (- (0 + n0) ^ 2 / 2) with ((-1/2) * (0 + n0) ^ 2) by lra.
        apply Rmult_le_compat_neg_l; [lra|].
        apply pow_incr.
        split; [rewrite Rplus_0_l; apply pos_INR | lra].
      + intros n0.
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros z Hz.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        auto_derive; done.
    - intros x n0 ?.
      rewrite (RInt_ext _ (fun x1 => G1_μ n * (1 - exp (- x * (2 * n + x) / 2)) * (G2_μ n0 x1 * F n0 x1))).
      2: { intros; lra. }
      rewrite RInt_Rmult.
      2: { apply G2_exRInt. }
      etrans.
      + apply abs_RInt_le.
        { lra. }
        { apply ex_RInt_Rmult, ex_RInt_mult; [apply G2_exRInt | apply Hex]. }
      + apply RInt_le.
        { lra. }
        { apply (ex_RInt_ext (λ t : R, G1_μ n * (1 - exp (- x * (2 * n + x) / 2)) * (G2_μ n0 t * F n0 t))).
          { rewrite Rmin_left; OK.
            rewrite Rmax_right; OK.
            intros ??.
            rewrite Rabs_right; first done.
            apply Rle_ge.
            apply Rmult_le_pos; apply Rmult_le_pos.
            { apply G1_μ_nn. }
            { suffices ? : exp (- x * (2 * n + x) / 2) <= 1 by lra.
              rewrite -exp_0.
              apply exp_mono.
              apply Rcomplements.Rmult_le_0_r; OK.
              apply Rcomplements.Rmult_le_0_r; OK.
              apply Rplus_le_le_0_compat; OK.
              apply Rmult_le_pos; OK.
              apply pos_INR.
            }
            { apply G2_μ_nn; OK. }
            { apply Hbound. }
          }
          apply ex_RInt_mult; [apply ex_RInt_const|].
          apply ex_RInt_mult; [|apply Hex].
          apply G2_exRInt.
        }
        { apply ex_RInt_Rmult, G2_exRInt. }
        intros x0 Hx0.
        rewrite Rabs_right.
        2: {
          apply Rle_ge.
          apply Rmult_le_pos; apply Rmult_le_pos.
          { apply G1_μ_nn. }
          { suffices ? : exp (- x * (2 * n + x) / 2) <= 1 by lra.
            rewrite -exp_0.
            apply exp_mono.
            apply Rcomplements.Rmult_le_0_r; OK.
            apply Rcomplements.Rmult_le_0_r; OK.
            apply Rplus_le_le_0_compat; OK.
            apply Rmult_le_pos; OK.
            apply pos_INR.
          }
          { apply G2_μ_nn; OK. }
          { apply Hbound. }
        }
        rewrite Rmult_assoc.
        rewrite (Rmult_comm (1 - exp (- x * (2 * n + x) / 2))).
        rewrite -(Rmult_1_l (M * G2_μ n0 x0)).
        apply Rmult_le_compat; OK.
        { apply G1_μ_nn. }
        { apply Rmult_le_pos; first apply Rmult_le_pos.
          { apply G2_μ_nn; OK. }
          { apply Hbound. }
          { suffices ? : exp (- x * (2 * n + x) / 2) <= 1 by lra.
            rewrite -exp_0.
            apply exp_mono.
            apply Rcomplements.Rmult_le_0_r; OK.
            apply Rcomplements.Rmult_le_0_r; OK.
            apply Rplus_le_le_0_compat; OK.
            apply Rmult_le_pos; OK.
            apply pos_INR.
          }
        }
        { rewrite /G1_μ.
          apply Rcomplements.Rle_div_l.
          { apply Rlt_gt. apply Norm1_nn. }
          rewrite Rmult_1_l.
          rewrite /Norm1.
          apply (@SeriesC_term_le (λ k : nat, exp (- k ^ 2 / 2))).
          { intros ?. apply Rexp_nn. }
          { apply Norm1_ex. }
        }
        rewrite Rmult_assoc.
        rewrite (Rmult_comm M _).
        apply Rmult_le_compat; OK.
        { apply G2_μ_nn; OK. }
        { apply Rmult_le_pos.
          { apply Hbound. }
          { suffices ? : exp (- x * (2 * n + x) / 2) <= 1 by lra.
            rewrite -exp_0.
            apply exp_mono.
            apply Rcomplements.Rmult_le_0_r; OK.
            apply Rcomplements.Rmult_le_0_r; OK.
            apply Rplus_le_le_0_compat; OK.
            apply Rmult_le_pos; OK.
            apply pos_INR.
          }
        }
        rewrite -(Rmult_1_r (M)).
        apply Rmult_le_compat; OK.
        { apply Hbound. }
        { suffices ? : exp (- x * (2 * n + x) / 2) <= 1 by lra.
          rewrite -exp_0.
          apply exp_mono.
          apply Rcomplements.Rmult_le_0_r; OK.
          apply Rcomplements.Rmult_le_0_r; OK.
          apply Rplus_le_le_0_compat; OK.
          apply Rmult_le_pos; OK.
          apply pos_INR.
        }
        { apply Hbound. }
        suffices ? : (0 <= exp (- x * (2 * n + x) / 2)) by OK.
        apply Rexp_nn.
    - intros n0.
      apply (ex_RInt_ext (λ x : R, G1_μ n * (1 - exp (- x * (2 * n + x) / 2)) * RInt (λ x1 : R, G2_μ n0 x1 * F n0 x1) 0 1)).
      + intros x Hx.
        symmetry.
        rewrite (RInt_ext _ (λ x1 : R, G1_μ n * (1 - exp (- x * (2 * n + x) / 2)) * (G2_μ n0 x1 * F n0 x1))).
        2: { intros; lra. }
        rewrite RInt_Rmult; [reflexivity | apply ex_RInt_mult; [apply G2_exRInt | apply Hex]].
      + apply ex_RInt_mult.
        * apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros z Hz.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          auto_derive; done.
        * apply ex_RInt_const.
  Qed.

  Lemma HR2 {F M} (Hex : ∀ x1, ex_RInt (F x1) 0 1) (Hbound : ∀ n x, 0 <= F n x <= M) :
  Series.Series
    (λ k : nat,
       Series.Series
         (λ x : nat,
            RInt (λ x0 : R, RInt (λ x1 : R, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1) 0 1) 0 1)) =
  Series.Series
    (λ x : nat,
       Series.Series
         (λ k : nat,
            RInt (λ x0 : R, RInt (λ x1 : R, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1) 0 1) 0 1)).
  Proof.
    pose B : nat * nat → R := fun '(k, x) => RInt (λ x0 : R, RInt (λ x1 : R, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1) 0 1) 0 1.
    suffices H : Series.Series (λ k : nat, Series.Series (λ x : nat, B (x, k))) = Series.Series (λ x : nat, Series.Series (λ k : nat, B (x, k))).
    { rewrite /B in H.
      rewrite H.
      apply Series.Series_ext; intros ?.
      apply Series.Series_ext; intros ?.
      reflexivity.
    }
    have HL3 : ∀ (a b : nat) (x x0 : R), 0 < x < 1 → 0 < x0 < 1 → 0 <= G1_μ b * (1 - exp (- x * (2 * b + x) / 2)) * G2_μ a x0 * F a x0.
    { admit. }
    have HL2 : ∀ (a b : nat) (x : R), 0 < x < 1 → ex_RInt (λ x1 : R, G1_μ b * (1 - exp (- x * (2 * b + x) / 2)) * G2_μ a x1 * F a x1) 0 1.
    { admit. }
    have HL1 : ∀ (a b : nat), ex_RInt (λ x0 : R, RInt (λ x1 : R, G1_μ b * (1 - exp (- x0 * (2 * b + x0) / 2)) * G2_μ a x1 * F a x1) 0 1) 0 1.
    { admit. }

    have HBpos : ∀ a b : nat, 0 <= B (a, b).
    { intros a b.
      rewrite /B.
      apply RInt_ge_0; OK.
      intros ??.
      apply RInt_ge_0; OK.
    }
    apply (@fubini_pos_series B); OK.
    { intros a.
      rewrite ex_seriesC_nat.
      rewrite /B.
      (* eapply ex_seriesC_RInt. *)

      admit. }
    { admit. }
  Admitted.

  Lemma HR3 {F M x n} (Hex : ∀ x1, ex_RInt (F x1) 0 1) (Hbound : ∀ n x, 0 <= F n x <= M) :
    RInt (λ x1 : R, RInt (λ x0 : R, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ n x1 * F n x1) 0 1) 0 1 =
    RInt (λ x0 : R, RInt (λ x1 : R, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ n x1 * F n x1) 0 1) 0 1.
  Proof.
    apply Fubini_eq.
    rewrite /FubiniCondition.
    intros x0 y Hx0 Hy.
    rewrite /uncurry//=.
    (* This is Continuity2 because it is the pointwise product of Continuity1 terms.

        Actually, we want this to be the piecewise continuity thing not Continuity1. Finish that reduction first.
     *)
  Admitted.

  Lemma HR4 {F M n} (Hex : ∀ x1, ex_RInt (F x1) 0 1) (Hbound : ∀ n x, 0 <= F n x <= M) :
  RInt
    (λ x1 : R,
       Series.Series (λ x : nat, RInt (λ x0 : R, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ n x1 * F n x1) 0 1))
    0 1 =
  Series.Series
    (λ x : nat,
       RInt (λ x1 : R, RInt (λ x0 : R, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ n x1 * F n x1) 0 1) 0 1).
  Proof.
    symmetry.
    apply (FubiniIntegralSeries_Strong (fun x => G1_μ x * M * RInt (G2_μ n) 0 1)).
    - OK.
    - admit.
    - rewrite ex_seriesC_nat.
      apply ex_seriesC_scal_r, ex_seriesC_scal_r.
      rewrite /G1_μ.
      replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with (λ k : nat, exp (- k ^ 2 / 2) * / Norm1) by (funexti; lra).
      apply ex_seriesC_scal_r, Norm1_ex.
    - intros x n0 ?.
      (* The bound of G2_μ is odd. Can I get a sup for it over the interval instead of using the integral...*)
      admit.
    - intros n0.
      (* Need the ex_RInt of RInt.

        Factor out the consant terms from the inner integral, the frist integral is constant wrt the outer integral so can be factored out. Then we have the product of integrable fns.
       *)
  Admitted.

  Lemma HR5 {F M n x} (Hex : ∀ x1, ex_RInt (F x1) 0 1) (Hbound : ∀ n x, 0 <= F n x <= M) (Hx : 0 < x < 1) :
    RInt (λ x0 : R, Series.Series (λ x1 : nat, G1_μ x1 * (1 - exp (- x0 * (2 * x1 + x0) / 2)) * G2_μ n x * F n x)) 0 1 =
    Series.Series (λ x0 : nat, RInt (λ x1 : R, G1_μ x0 * (1 - exp (- x1 * (2 * x0 + x1) / 2)) * G2_μ n x * F n x) 0 1).
  Proof.
    symmetry.
    have H : ∀ n0 x0, 0 < x0 < 1 → 1 - exp (- x0 * (2 * n0 + x0) / 2) <= 1.
    { intros ???.
      suffices ? : 0 <= exp (- x0 * (2 * n0 + x0) / 2) by OK.
      apply Rexp_nn.
    }
    have H' : ∀ (n0 : nat) (x0 : R), 0 < x0 < 1 → 0 <= 1 - exp (- x0 * (2 * n0 + x0) / 2).
    { intros ???.
      suffices ? : exp (- x0 * (2 * n0 + x0) / 2) <= 1 by OK.
      apply Rexp_range.
      rewrite Rdiv_def.
      apply Rcomplements.Rmult_le_0_r; OK.
      apply Rcomplements.Rmult_le_0_r; OK.
      apply Rplus_le_le_0_compat; OK.
      apply Rmult_le_pos; OK.
      apply pos_INR.
    }
    apply (FubiniIntegralSeries_Strong (fun x0 => G1_μ x0 * G2_μ n x * M)).
    - OK.
    - intros ???.
      apply Rmult_le_pos; [|apply Hbound].
      apply Rmult_le_pos.
      2: { apply G2_μ_nn. OK. }
      apply Rmult_le_pos.
      { apply G1_μ_nn. }
      { suffices ? : exp (- x0 * (2 * n0 + x0) / 2) <= 1 by OK.
        apply Rexp_range.
        suffices ? : ((- x0) * ((2 * n0) + x0)) <= 0 by OK.
        apply Rcomplements.Rmult_le_0_r; OK.
        apply Rplus_le_le_0_compat; OK.
        apply Rmult_le_pos; OK.
        apply pos_INR.
      }
    - rewrite ex_seriesC_nat.
      apply ex_seriesC_scal_r, ex_seriesC_scal_r.
      rewrite /G1_μ.
      replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with (λ k : nat, exp (- k ^ 2 / 2) * / Norm1) by (funexti; lra).
      apply ex_seriesC_scal_r, Norm1_ex.
    - intros x0 n0 ?.
      rewrite Rabs_right.
      2: {
        apply Rle_ge.
        apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|]; OK.
        { apply G1_μ_nn.  }
        { apply G2_μ_nn.  OK. }
        { apply Hbound. }
      }
      rewrite !Rmult_assoc.
      apply Rmult_le_compat_l; [apply Rexp_nn | ].
      apply Rmult_le_compat_l; [apply Rlt_le, Rinv_0_lt_compat, Norm1_nn | ].
      rewrite (Rmult_comm (1 - exp (- x0 * (2 * n0 + x0) / 2))).
      rewrite !Rmult_assoc.
      apply Rmult_le_compat_l; [apply Rexp_nn | ].
      apply Rmult_le_compat_l; [apply Rlt_le, Rinv_0_lt_compat, Norm2_nn | ].
      rewrite -(Rmult_1_r M).
      apply Rmult_le_compat; OK; apply Hbound.
    - intros n0.
      apply (ex_RInt_ext (λ x0 : R, G1_μ n0 * (1 - exp (- x0 * (2 * n0 + x0) / 2)) * (G2_μ n x * F n x))).
      + intros; lra.
      + apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros z Hz.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        auto_derive; done.
  Qed.

  Lemma G2_f_expectation {F M} (HPcts : ∀ x1 : nat, PCts (F x1) 0 1) (Hbound : ∀ n x, 0 <= F n x <= M) :
    G2_CreditV F = G1_CreditV (G2_f F).
  Proof.
    have Hex : ∀ x1, ex_RInt (F x1) 0 1.
    { intros ?. apply (@PCts_RInt _ 0 1). done. }
    rewrite /G1_CreditV /G2_f.
    (* Split the sum and integral *)
    rewrite /G2_g.
    replace (λ k : nat, G1_μ k * RInt (λ x : R, exp (- x * (2 * k + x) / 2) * G2_s F k x true + (1 - exp (- x * (2 * k + x) / 2)) * G2_s F k x false) 0 1)
       with (λ k : nat, G1_μ k * RInt (λ x : R, exp (- x * (2 * k + x) / 2) * G2_s F k x true) 0 1 +
                      G1_μ k * RInt (λ x : R, ((1 - exp (- x * (2 * k + x) / 2)) * G2_s F k x false)) 0 1);
       last first.
    {  apply functional_extensionality; intros k.
       rewrite -Rmult_plus_distr_l.
       f_equal.
       rewrite RInt_add.
       2: {
         rewrite /G2_s.
         rewrite Iverson_True; [|intuition].
         rewrite Iverson_False; [|intuition].
         replace (λ x : R, exp (- x * (2 * k + x) / 2) * (1 * F k x + 0 * G2_CreditV F))
           with (λ x : R, exp (- x * (2 * k + x) / 2) * (F k x)); last first.
         { funexti. OK. }
         apply ex_RInt_mult.
         { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
           intros ??.
           apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
           by auto_derive.
         }
         { apply Hex. }
       }
       2: {
         rewrite /G2_s.
         rewrite Iverson_False; [|intuition].
         rewrite Iverson_True; [|intuition].
         replace (λ x : R, (1 - exp (- x * (2 * k + x) / 2)) * (0 * F k x + 1 * G2_CreditV F))
            with (λ x : R, (1 - exp (- x * (2 * k + x) / 2)) * (G2_CreditV F)); last first.
         { funexti. OK. }
         apply ex_RInt_mult.
         { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
           intros ??.
           apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
           by auto_derive.
         }
         { apply ex_RInt_const. }
        }
       done.
    }
    have HexLem1 : ex_seriesC (λ x : nat, G1_μ x * RInt (λ x0 : R, exp (- x0 * (2 * x + x0) / 2) * G2_s F x x0 true) 0 1).
    { rewrite /G2_s.
      rewrite Iverson_True; OK.
      rewrite Iverson_False; OK.
      apply (ex_seriesC_le _ (λ n : nat, G1_μ n * M)).
      2: {
        apply ex_seriesC_scal_r.
        rewrite /G1_μ.
        replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with (λ k : nat, exp (- k ^ 2 / 2) * / Norm1) by (funexti; OK).
        apply ex_seriesC_scal_r.
        apply Norm1_ex.
      }
      intros ?; split.
      { apply Rmult_le_pos; [apply G1_μ_nn|].
        apply RInt_ge_0; OK.
        { apply ex_RInt_mult.
          { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
            intros ??.
            apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
            by auto_derive.
          }
          { replace (λ y : R, 1 * F n y + 0 * G2_CreditV F) with (F n) by (funexti; OK).
            apply Hex.
          }
        }
        { intros ??. apply Rmult_le_pos; [apply Rexp_nn|]. rewrite Rmult_1_l Rmult_0_l Rplus_0_r. apply Hbound. }
      }
      { have Hex' : ex_RInt (λ x : R, exp (- x * (2 * n + x) / 2) * (1 * F n x + 0 * G2_CreditV F)) 0 1.
        { apply ex_RInt_mult.
          { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
            intros ??.
            apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
            by auto_derive.
          }
          { replace (λ y : R, 1 * F n y + 0 * G2_CreditV F) with (F n) by (funexti; OK).
            apply Hex.
          }
        }
        apply Rmult_le_compat; OK.
        { apply G1_μ_nn. }
        { apply RInt_ge_0; OK. intros ??. apply Rmult_le_pos; [apply Rexp_nn|]. rewrite Rmult_1_l Rmult_0_l Rplus_0_r. apply Hbound. }

        rewrite -(Rabs_right (RInt (λ x : R, exp (- x * (2 * n + x) / 2) * (1 * F n x + 0 * G2_CreditV F)) 0 1)).
        2: {
          apply Rle_ge.
          apply RInt_ge_0; OK. intros ??. apply Rmult_le_pos; [apply Rexp_nn|]. rewrite Rmult_1_l Rmult_0_l Rplus_0_r. apply Hbound. }
          etrans; first apply (abs_RInt_le_const _ _ _ M); OK.
          intros ??.
          rewrite Rmult_1_l Rmult_0_l Rplus_0_r.
          rewrite Rabs_right.
          2: { apply Rle_ge. apply Rmult_le_pos; [apply Rexp_nn|]. apply Hbound. }
          rewrite -(Rmult_1_l M).
          apply Rmult_le_compat; OK.
          { apply Rexp_nn. }
          { apply Hbound. }
          2: { apply Hbound. }
          rewrite -exp_0.
          apply exp_mono.
          replace (- t * (2 * n + t) / 2) with ((-1 / 2) * (t * (2 * n + t))) by OK.
          replace 0 with ((-1/2) * 0) by OK.
          apply Rmult_le_compat_neg_l; OK.
          apply Rmult_le_pos; OK.
          apply Rplus_le_le_0_compat; OK.
          apply Rmult_le_pos; OK.
          apply pos_INR.
        }
      }
    have HexLem2 : ex_seriesC (λ x : nat, G1_μ x * RInt (λ x0 : R, (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_s F x x0 false) 0 1).
    {
      rewrite /G2_s.
      rewrite Iverson_False; OK.
      rewrite Iverson_True; OK.
      apply (ex_seriesC_le _ (λ n : nat, G1_μ n * (G2_CreditV F))).
      2: {
        apply ex_seriesC_scal_r.
        rewrite /G1_μ.
        replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with (λ k : nat, exp (- k ^ 2 / 2) * / Norm1) by (funexti; OK).
        apply ex_seriesC_scal_r.
        apply Norm1_ex.
      }
      intros ?.
      have Hlem1 : ∀ x, 0 <= x <= 1 → 0 <= (1 - exp (- x * (2 * n + x) / 2)).
      { intros ??.
        suffices ? : exp (- x * (2 * n + x) / 2) <= 1 by OK.
        apply Rexp_range.
        replace (- x * (2 * n + x) / 2) with ((-1 / 2) * (x * (2 * n + x))) by OK.
        replace 0 with ((-1/2) * 0) by OK.
        apply Rmult_le_compat_neg_l; OK.
        apply Rmult_le_pos; OK.
        apply Rplus_le_le_0_compat; OK.
        apply Rmult_le_pos; OK.
        apply pos_INR.
      }
      split.
      { apply Rmult_le_pos; [apply G1_μ_nn|].
        apply RInt_ge_0; OK.
        { apply ex_RInt_mult.
          { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
            intros ??.
            apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
            by auto_derive.
          }
          { replace (λ y : R, 0 * F n y + 1 * G2_CreditV F) with (fun y : R => G2_CreditV F) by (funexti; OK).
            apply ex_RInt_const.
          }
        }
        { intros ??.
          rewrite Rmult_1_l Rmult_0_l Rplus_0_l.
          apply Rmult_le_pos; [|apply G2_CreditV_nn]; OK.
          2: { apply Hbound. }
          apply Hlem1; OK.
        }
      }
      { have Hex' : ex_RInt (λ x : R, (1 - exp (- x * (2 * n + x) / 2)) * (0 * F n x + 1 * G2_CreditV F)) 0 1.
        { apply ex_RInt_mult.
          { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
            intros ??.
            apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
            by auto_derive.
          }
          { replace (λ y : R, 0 * F n y + 1 * G2_CreditV F) with (fun y : R => G2_CreditV F) by (funexti; OK).
            apply ex_RInt_const.
          }
        }
        apply Rmult_le_compat; OK.
        { apply G1_μ_nn. }
        { apply RInt_ge_0; OK. intros ??.
          rewrite Rmult_1_l Rmult_0_l Rplus_0_l.
          apply Rmult_le_pos; [|apply G2_CreditV_nn]; OK.
          2: { apply Hbound. }
          apply Hlem1; OK.
        }

        rewrite -(Rabs_right (RInt (λ x : R, (1 - exp (- x * (2 * n + x) / 2)) * (0 * F n x + 1 * G2_CreditV F)) 0 1)).
        2: {
          apply Rle_ge.
          apply RInt_ge_0; OK. intros ??.
          rewrite Rmult_1_l Rmult_0_l Rplus_0_l.
          apply Rmult_le_pos; [|apply G2_CreditV_nn]; OK.
          2: { apply Hbound. }
          apply Hlem1; OK.
        }
        etrans; first apply (abs_RInt_le_const _ _ _ (G2_CreditV F)); OK.
        intros ??.
        rewrite Rmult_1_l Rmult_0_l Rplus_0_l.
        rewrite Rabs_right.
        2: {
          apply Rle_ge.
          apply Rmult_le_pos; [|apply G2_CreditV_nn]; OK.
          apply Hbound.
        }
        rewrite -{2}(Rmult_1_l (G2_CreditV F)).
        apply Rmult_le_compat; OK.
        { apply G2_CreditV_nn; OK. apply Hbound. }
        suffices ? : 0 <= exp (- t * (2 * n + t) / 2) by OK.
        apply Rexp_nn.
      }
    }

    have HexLem7 : ex_RInt (λ x0 : R, SeriesC (λ x1 : nat, exp (- x1 ^ 2 / 2) - exp (- (x0 + x1) ^ 2 / 2))) 0 1.
    { apply (ex_RInt_ext (λ x0 : R, SeriesC (λ x1 : nat, exp (- x1 ^ 2 / 2)) - SeriesC (fun x1 : nat => exp (- (x0 + x1) ^ 2 / 2)))).
      2 : {
        apply (ex_RInt_minus (V := R_CompleteNormedModule)).
        { apply ex_RInt_const. }
        apply ExpAddSeries_RInt.
      }
      rewrite Rmin_left; OK. rewrite Rmax_right; OK.
      intros ??.
      rewrite SeriesC_minus; OK.
      { apply Norm1_ex. }
      { apply Norm2_ex'. OK. }
    }
    have HexLem4 : ∀ k, ex_RInt (λ x : R, G1_μ k * (exp (- x * (2 * k + x) / 2) * G2_s F k x true)) 0 1.
    { intros k.
      apply ex_RInt_Rmult.
      rewrite /G2_s.
      rewrite Iverson_True; [|intuition].
      rewrite Iverson_False; [|intuition].
      apply ex_RInt_mult.
      { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      { replace (λ y : R, 1 * F k y + 0 * G2_CreditV F) with (F k) by (funexti; OK).
        apply Hex.
      }
    }
    have HexLem6 : ex_RInt (λ x0 : R, SeriesC (λ x1 : nat, G1_μ x1 * (1 - exp (- x0 * (2 * x1 + x0) / 2)))) 0 1.
    { have HL : ∀ (n : nat) x, 0 <= x <= 1 → 0 <= (1 - exp (- x * (2 * n + x) / 2)) <= 1.
      { intros ???.
        suffices ? : 0 <= exp (- x * (2 * n + x) / 2) <= 1 by OK.
        split.
        { apply Rexp_nn. }
        { apply Rexp_range.
          replace (- x * (2 * n + x) / 2) with ((-1 / 2) * (x * (2 * n + x))) by OK.
          replace 0 with ((-1/2) * 0) by OK.
          apply Rmult_le_compat_neg_l; OK.
          apply Rmult_le_pos; OK.
          apply Rplus_le_le_0_compat; OK.
          apply Rmult_le_pos; OK.
          apply pos_INR.
        }
      }
      apply (ex_RInt_SeriesC G1_μ); OK.
      { rewrite /G1_μ.
        rewrite ex_seriesC_nat.
        replace (λ k : nat, exp (- k ^ 2 / 2) / Norm1) with (λ k : nat, exp (- k ^ 2 / 2) * / Norm1) by (funexti; OK).
        apply ex_seriesC_scal_r.
        apply Norm1_ex.
      }
      { intros ???.
        split.
        {
             apply Rmult_le_pos; OK.
             { apply G1_μ_nn. }
             { apply HL. OK. }
        }
        rewrite -{2}(Rmult_1_r (G1_μ n)).
        apply Rmult_le_compat; OK.
        { apply G1_μ_nn. }
        { apply HL. OK. }
        { apply HL. OK. }
      }
      { intros ?.
        apply ex_RInt_mult.
        { apply ex_RInt_const.  }
        { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
      }
    }
    have HexLem3 : ex_seriesC (λ k : nat, RInt (λ x1 : R, RInt (λ x0 : R, SeriesC (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1)) 0 1) 0 1).
    { eapply HL3; try done. }
    have HexLem5 : ∀ k, ex_RInt (λ x1 : R, RInt (λ x0 : R, SeriesC (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1)) 0 1) 0 1.
    { eapply HL5; done. }
    rewrite SeriesC_plus; OK.

    (* Prepare second term for Foob *)
    rewrite {2}/G2_s.
    rewrite Iverson_False; [|intuition].
    rewrite Iverson_True; [|intuition].
    (* Setoid_rewrite is confused *)
    replace (λ x : nat, G1_μ x * RInt (λ x0 : R, (1 - exp (- x0 * (2 * x + x0) / 2)) * (0 * F x x0 + 1 * G2_CreditV F)) 0 1)
       with (λ x : nat, RInt (λ x0 : R, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_CreditV F) 0 1);
      last first.
    { apply functional_extensionality; intros x.
      rewrite RInt_Rmult.
      2: {
        apply ex_RInt_mult.
        { apply (ex_RInt_minus (V := R_CompleteNormedModule)).
          { apply ex_RInt_const. }
          apply ex_RInt_continuous.
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { replace (λ y : R, 0 * F x y + 1 * G2_CreditV F) with (λ _ : R, G2_CreditV F) by (funexti; OK).
          apply ex_RInt_const.
        }
      }
      f_equal.
      f_equal.
      apply functional_extensionality; intros y.
      lra.
    }
    rewrite {2}/G2_CreditV.
    replace (SeriesC (λ x : nat, RInt (λ x0 : R, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * SeriesC (λ k : nat, RInt (λ x1 : R, G2_μ k x1 * F k x1) 0 1)) 0 1))
      with (SeriesC (λ x : nat, RInt (λ x0 : R, SeriesC (λ k : nat, RInt (λ x1 : R, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1) 0 1)) 0 1));
      last first.
    { f_equal; apply functional_extensionality; intros ?.
      f_equal; apply functional_extensionality; intros ?.
      rewrite -SeriesC_scal_l.
      f_equal; apply functional_extensionality; intros ?.
      rewrite RInt_Rmult.
      2: {
        apply ex_RInt_mult.
        { apply G2_exRInt. }
        { OK. }
      }
      f_equal; apply functional_extensionality; intros ?.
      lra.
    }
    (* Go get 'em Guido *)
    replace (SeriesC (λ x : nat, RInt (λ x0 : R, SeriesC (λ k : nat, RInt (λ x1 : R, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1) 0 1)) 0 1))
       with (SeriesC (λ k : nat, RInt (λ x1 : R, RInt (λ x0 : R, SeriesC (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1)) 0 1) 0 1));
      last first.
    {
      pose B (k x : nat) (x0 x1 : R) := G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1.
      suffices Hy :
        Series.Series (λ k : nat, RInt (λ x1 : R, RInt (λ x0 : R, Series.Series (λ x : nat, B k x x0 x1)) 0 1) 0 1) =
        Series.Series (λ x : nat, RInt (λ x0 : R, Series.Series (λ k : nat, RInt (λ x1 : R, B k x x0 x1) 0 1)) 0 1).
      { replace (SeriesC (λ k : nat, RInt (λ x1 : R, RInt (λ x0 : R, SeriesC (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1)) 0 1) 0 1))
           with (Series.Series (λ k : nat, RInt (λ x1 : R, RInt (λ x0 : R, Series.Series (fun x => B k x x0 x1)) 0 1) 0 1)).
        2: {
          rewrite SeriesC_nat.
          apply Series.Series_ext.
          intros ?.
          eapply RInt_ext. intros ??.
          eapply RInt_ext. intros ??.
          rewrite SeriesC_nat.
          reflexivity.
        }
        rewrite Hy.
        rewrite SeriesC_nat.
        apply Series.Series_ext.
        intros ?.
        eapply RInt_ext. intros ??.
        rewrite -SeriesC_nat.
        apply SeriesC_ext. intros ?.
        eapply RInt_ext. intros ??.
        reflexivity.
      }

      replace (Series.Series (λ x : nat, RInt (λ x0 : R, Series.Series (λ k : nat, RInt (λ x1 : R, B k x x0 x1) 0 1)) 0 1))
         with (Series.Series (λ x : nat, Series.Series (λ k : nat, RInt (λ x0 : R, RInt (λ x1 : R, B k x x0 x1) 0 1) 0 1))).
      2: {
        eapply HR1; done.
      }

      replace (Series.Series (λ x : nat, Series.Series (λ k : nat, RInt (λ x0 : R, RInt (λ x1 : R, B k x x0 x1) 0 1) 0 1)))
         with (Series.Series (λ k : nat, Series.Series (λ x : nat, RInt (λ x0 : R, RInt (λ x1 : R, B k x x0 x1) 0 1) 0 1))).
      2: { rewrite /B. eapply HR2; done. }

      apply Series.Series_ext; intros n.

      replace (Series.Series (λ x : nat, RInt (λ x0 : R, RInt (λ x1 : R, B n x x0 x1) 0 1) 0 1))
         with (Series.Series (λ x : nat, RInt (λ x1 : R, RInt (λ x0 : R, B n x x0 x1) 0 1) 0 1)).
      2: {
        apply Series.Series_ext; intros x.
        rewrite /B.
        apply (@HR3 _ M); done.
      }

      replace (Series.Series (λ x : nat, RInt (λ x1 : R, RInt (λ x0 : R, B n x x0 x1) 0 1) 0 1))
         with (RInt (λ x1 : R, (Series.Series (λ x : nat, RInt (λ x0 : R, B n x x0 x1) 0 1))) 0 1).
      2: {
        rewrite /B.
        apply (@HR4 _ M); done.
      }

      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite /B.
      rewrite (@HR5 _ M); OK.
    }

    (* Recombine series and cancel with LHS *)

    rewrite -SeriesC_plus; OK.
    rewrite /G2_CreditV.
    f_equal; apply functional_extensionality; intros k.
    rewrite RInt_Rmult.
    2: {
      apply ex_RInt_mult.
      { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros ??.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
      rewrite /G2_s//=.
      apply (ex_RInt_plus (V := R_CompleteNormedModule)); [|apply ex_RInt_const].
      rewrite Iverson_True; OK.
      apply ex_RInt_Rmult.
      apply Hex.
    }
    rewrite RInt_add; OK.
    apply RInt_ext.
    rewrite Rmin_left; [|lra].
    rewrite Rmax_right; [|lra].
    intros x Hx.
    (* Pull out the constant terms from the series/intergral *)
    replace (RInt (λ x0 : R, SeriesC (λ x1 : nat, G1_μ x1 * (1 - exp (- x0 * (2 * x1 + x0) / 2)) * G2_μ k x * F k x)) 0 1)
       with (G2_μ k x * F k x * RInt (λ x0 : R, SeriesC (λ x1 : nat, G1_μ x1 * (1 - exp (- x0 * (2 * x1 + x0) / 2)))) 0 1);
      last first.
    { rewrite RInt_Rmult; OK.
      f_equal; apply functional_extensionality; intros ?.
      rewrite -SeriesC_scal_l.
      f_equal; apply functional_extensionality; intros ?.
      lra.
    }
    (* Cancel F *)
    rewrite /G2_s.
    rewrite Iverson_True; [|intuition].
    rewrite Iverson_False; [|intuition].
    rewrite Rmult_1_l Rmult_0_l Rplus_0_r.
    rewrite -Rmult_assoc.
    rewrite (Rmult_assoc _ (F k x)) (Rmult_comm (F k x)) -(Rmult_assoc _ _ (F k x)).
    rewrite -Rmult_plus_distr_r.
    f_equal.

    (* Don't compute the inner integral yet. Dustribute in G1_μ first and simplify. *)
    rewrite /G1_μ.
    replace (RInt (λ x0 : R, SeriesC (λ x1 : nat, exp (- x1 ^ 2 / 2) / Norm1 * (1 - exp (- x0 * (2 * x1 + x0) / 2)))) 0 1)
       with ((/ Norm1) * RInt (λ x0 : R, SeriesC (λ x1 : nat, (exp (- x1 ^ 2 / 2) - exp (- (x0 + x1)^2 / 2)))) 0 1);
      last first.
    { rewrite RInt_Rmult; OK.
      f_equal; apply functional_extensionality; intros y.
      rewrite -SeriesC_scal_l.
      f_equal; apply functional_extensionality; intros j.
      rewrite (Rdiv_def _ Norm1) (Rmult_comm _ (/ Norm1)) Rmult_assoc.
      f_equal.
      rewrite Rmult_minus_distr_l Rmult_1_r.
      f_equal.
      rewrite -exp_plus.
      f_equal.
      lra.
    }

    (* Split up the series and integral *)
    replace (RInt (λ x0 : R, SeriesC (λ x1 : nat, exp (- x1 ^ 2 / 2) - exp (- (x0 + x1) ^ 2 / 2))) 0 1)
      with (RInt (λ x0 : R, SeriesC (λ x1 : nat, exp (- x1 ^ 2 / 2)) + -1 * SeriesC (fun x1 : nat => exp (- (x0 + x1) ^ 2 / 2))) 0 1);
      last first.
    { apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite SeriesC_minus.
      2: { apply Norm1_ex. }
      2: { apply Norm2_ex'. OK. }
      lra.
    }
    rewrite -RInt_add.
    2: { apply ex_RInt_const. }
    2: { apply ex_RInt_Rmult. apply ExpAddSeries_RInt. }
    rewrite -RInt_Rmult.
    2: { apply ExpAddSeries_RInt. }

    (* Evaluate the inegrals *)
    replace (RInt (λ _ : R, SeriesC (λ x1 : nat, exp (- x1 ^ 2 / 2))) 0 1) with Norm1; last first.
    { rewrite RInt_const /scal//=/mult//= Rminus_0_r Rmult_1_l.
      rewrite /Norm1.
      f_equal.
    }
    replace (RInt (λ x0 : R, SeriesC (λ x1 : nat, exp (- (x0 + x1) ^ 2 / 2))) 0 1) with Norm2; last first.
    { by rewrite /Norm2. }

    (* Simplify *)
    rewrite /G2_μ.
    rewrite (Rdiv_def _ Norm1) (Rmult_comm _ (/ Norm1)) Rmult_assoc.
    rewrite -exp_plus.
    replace ((- k ^ 2 / 2 + - x * (2 * k + x) / 2)) with (- (x + k)^2 / 2) by lra.
    rewrite (Rmult_comm _ (exp _)).
    rewrite (Rdiv_def _ Norm2) Rmult_assoc.
    rewrite -Rmult_plus_distr_l.
    f_equal.
    apply (Rmult_eq_reg_l (Norm1 * Norm2)); last first.
    { have ? := Norm1_nn.
      have ? := Norm2_nn.
      apply Rmult_integral_contrapositive_currified; lra.
    }
    rewrite Rmult_assoc.
    rewrite Rmult_inv_r; last (have ? := Norm2_nn; lra).
    rewrite Rmult_1_r.
    rewrite Rmult_plus_distr_l.
    rewrite {1}(Rmult_comm Norm1 Norm2).
    rewrite Rmult_assoc.
    rewrite Rmult_inv_r; last (have ? := Norm1_nn; lra).
    rewrite Rmult_1_r.
    rewrite -Rmult_assoc (Rmult_assoc Norm1 Norm2).
    rewrite Rmult_inv_r; last (have ? := Norm2_nn; lra).
    rewrite Rmult_1_r.
    rewrite -Rmult_assoc.
    rewrite Rmult_inv_r; last (have ? := Norm1_nn; lra).
    lra.
  Qed.

  Lemma G2_g_RInt {F k} (Hf : ex_RInt (λ y : R, F k y) 0 1) : is_RInt (G2_g F k) 0 1 (G2_f F k).
  Proof.
    rewrite /G2_f.
    apply (RInt_correct (V := R_CompleteNormedModule)).
    apply G2_g_exRInt.
    apply Hf.
  Qed.

  Local Lemma Rexp_eq {z : R} {k : nat} : exp (- z * (2 * k + z) / 2) = exp (- z * (2 * k + z) / (2 * k + 2)) ^ (k + 1).
  Proof.
    rewrite exp_pow; f_equal.
    rewrite -Rmult_div_assoc Rmult_assoc Rmult_assoc; f_equal.
    rewrite Rdiv_def; f_equal.
    replace (2 * k + 2) with (2 * (k + 1)%nat).
    { rewrite Rinv_mult.
      rewrite Rmult_assoc.
      rewrite Rinv_l; [lra|].
      apply not_0_INR; lia.
    }
    rewrite plus_INR.
    rewrite Rmult_plus_distr_l INR_1; lra.
  Qed.

End credits.

Section program.
  Context `{!erisGS Σ}.
  Import Hierarchy.

  Definition G1 : val :=
    rec: "trial" "_" :=
      let: "k" := GeoTrial BNEHalf #0 in
      if: IterTrial BNEHalf ("k" * ("k" - #1)) then "k" else "trial" #().

  Definition G2 : val :=
    rec: "trial" "_" :=
      let: "k" := G1 #() in
      let: "x" := init #() in
      if: IterTrial (λ: "_", B "k" "x") ("k" + #1) then ("x", "k") else "trial" #().

  Theorem wp_G1 {E F M} (Hnn : ∀ r, 0 <= F r <= M) (Hex : ex_seriesC F) :
    ↯(G1_CreditV F) -∗ WP G1 #() @ E {{ vn, ∃ n : nat, ⌜vn = #n ⌝ ∗ ↯(F n) }}.
  Proof.
    iStartProof.
    iLöb as "IH".
    iIntros "Hε".
    rewrite /G1.
    wp_pures.
    wp_bind (GeoTrial BNEHalf _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hε] IH"); last first.
    { rewrite -Nat2Z.inj_0.
      wp_apply (wp_Geo _ (exp (-1 / 2)) _  _ (G1_f F)).
      { split; [apply G1_f_nn, Hnn|].
        apply G1_f_ub; OK.
      }
      {  erewrite G1_f_expectation; [|eapply Hnn]. done. }
      Unshelve.
      { apply Rexp_range; lra. }
      { iIntros (E' F' HF') "Hε".
        (* This is where it goes awry, can I remove the liftF requirement? *)
        iApply wp_BNEHalf.
        Unshelve.
        3: { exact (Rmax (F' true) (F' false)). }
        { intro b.
          split; [apply HF'|].
          destruct b.
          { apply Rmax_l. }
          { apply Rmax_r. }
        }
        { iApply (ec_eq with "Hε").
          rewrite /BNEHalf_CreditV.
          rewrite (Rmult_comm _ (F' true)) (Rmult_comm _ (F' false)).
          f_equal; f_equal; rewrite /BNEHalf_μ.
          { rewrite Iverson_True; OK. rewrite Iverson_False; OK. }
          { rewrite Iverson_False; OK. rewrite Iverson_True; OK. }
        }
      }
    }
    iIntros (v) "(#IH & [%n [-> Hε]])".
    wp_pures.
    wp_bind (IterTrial BNEHalf _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hε] IH"); last first.
    { wp_pures.
      replace (Z.mul n (Z.sub n 1)) with (Z.of_nat (Nat.mul n (Nat.sub n 1))); last first.
      { destruct n; [lia|].
        rewrite Nat2Z.inj_mul; f_equal.
        apply Nat2Z.inj_sub.
        lia.
      }
      iApply (wp_Iter BNEHalf (exp (-1 / 2)) _ True _ _ (F := G1_h F n)).
      { by intros ?; apply G1_h_nn, Hnn. }
      { iSplitL; [|done].
        iApply (ec_eq with "Hε").
        rewrite /G1_f/Iter_CreditV.
        f_equal; f_equal; rewrite exp_pow; repeat f_equal; lra.
      }
      Unshelve.
      { apply Rexp_range; lra. }
      { iIntros (E' F' HF') "(Hε & HI)".
        iFrame.
        iApply wp_BNEHalf.
        { Unshelve.
          2: { exact (Rmax (F' false) (F' true)). }
          intro b. split; OK.
          destruct b.
          { apply Rmax_r. }
          { apply Rmax_l. }
        }
        iApply (ec_eq with "Hε").
        rewrite /BNEHalf_CreditV/BNEHalf_μ.
        rewrite Iverson_True; [|intuition].
        rewrite Iverson_False; [|intuition].
        rewrite Iverson_False; [|intuition].
        rewrite Iverson_True; [|intuition].
        lra.
      }
    }
    iIntros (v) "(#IH & [%b [-> [Hε _]]])".
    destruct b.
    { wp_pures.
      iModIntro.
      iExists n.
      iSplitR; first done.
      iApply (ec_eq with "Hε").
      rewrite /G1_h.
      rewrite Iverson_True; [|intuition]; rewrite Iverson_False; [|intuition].
      by rewrite Rmult_1_l Rmult_0_l Rplus_0_r.
    }
    { wp_pure.
      iApply "IH".
      iApply (ec_eq with "Hε").
      rewrite /G1_h.
      rewrite Iverson_False; [|intuition]; rewrite Iverson_True; [|intuition].
      by rewrite Rmult_0_l Rmult_1_l Rplus_0_l.
    }
  Qed.

  Theorem wp_G2 {E F M} (Hnn : ∀ x k , 0 <= F x k <= M) (HPcts : ∀ x1 : nat, PCts (F x1) 0 1) :
    ↯(G2_CreditV F) -∗
    WP G2 #() @ E {{ vp, ∃ k : nat, ∃ r : R, ∃ l : val, lazy_real l r  ∗ ⌜vp = PairV l #k ⌝ ∗ ↯(F k r) }}.
  Proof.
    have Hint := fun n => @PCts_RInt _ 0 1 (HPcts n).
    rewrite /G2.
    iLöb as "IH".
    iIntros "Hε".
    wp_pures.
    wp_bind (G1 _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hε] IH"); last first.
    { iApply (wp_G1 (F := G2_f F) (M := M)).
      { intros ?; split; [apply G2_f_nn; OK; apply Hnn|]. apply G2_ub; OK. }
      { apply (@G2_f_ex_seriesC _ M); try done. }
      { iApply (ec_eq with "Hε").
        eapply G2_f_expectation.
        { done. }
        { apply Hnn. }
      }
    }
    iIntros (v) "(#IH & [%k [-> Hε]])".
    wp_pures.
    wp_apply wp_init; first done.
    iIntros (x) "Hx".
    iApply (wp_lazy_real_presample_adv_comp _ _ x _ (G2_f F k) (G2_g F k)); auto.
    { intros ??. apply G2_g_nn; auto. apply Hnn. }
    { apply G2_g_RInt. apply Hint. }
    iFrame.
    iIntros (z) "(% & Hε & Hx)".
    wp_pures.
    wp_bind (IterTrial _ _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hε Hx] IH"); last first.
    { rewrite /G2_g.
      replace (Z.add (Z.of_nat k) 1) with (Z.of_nat (k + 1)%nat) by lia.
      iApply (@wp_Iter _ _ _ (exp (- z * (2 * k + z) / (2*k+2))) _ (lazy_real x z) _ _ (G2_s F k z)).
      { intros ?. apply G2_s_nn; auto. apply Hnn. }
      { iFrame.
        iApply (ec_eq with "Hε").
        rewrite /Iter_CreditV.
        rewrite Rexp_eq.
        f_equal; f_equal.
      }
      Unshelve.
      { apply Rexp_range.
        rewrite Rdiv_def.
        repeat rewrite Ropp_mult_distr_l_reverse.
        rewrite -Ropp_0.
        apply Ropp_le_contravar.
        have ? : 0 <= INR k by apply pos_INR.
        apply Rmult_le_pos; first apply Rmult_le_pos; try lra.
        rewrite -(Rmult_1_l (/ _)).
        apply Rcomplements.Rdiv_le_0_compat; lra.
      }

      { iIntros (E' F' Hf') "(Hε & HI)".
        wp_pure.
        iApply (wp_B (M := F' false + F' true)).
        { intro r; split; OK.
          have ? : 0 <= F' false by apply Hf'.
          have ? : 0 <= F' true by apply Hf'.
          destruct r; OK.
        }
        rewrite /B_CreditV.
        iFrame.
        auto.
      }
    }
    iIntros (v) "(#IH & [%b [-> [Hε Hx]]])".
    destruct b.
    { wp_pures.
      iModIntro; iExists k, z, x.
      iFrame.
      iSplitR; first done.
      rewrite /G2_s.
      iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg |]. apply G2_CreditV_nn; auto. apply Hnn. }
      iApply (ec_eq with "Hε").
      rewrite Iverson_True; [lra|done].
    }
    { wp_pure.
      iApply "IH".
      rewrite /G2_s.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg |]. apply G2_CreditV_nn; auto. apply Hnn. }
      iApply (ec_eq with "Hε").
      rewrite Iverson_True; [lra|done].
    }
  Qed.

End program.
