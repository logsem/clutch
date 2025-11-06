From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import Coquelicot.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real indicators half_bern_neg_exp.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Ltac OK := auto; (try by intuition); try lia; try lra.
Ltac funext := apply functional_extensionality.
Ltac funexti := apply functional_extensionality; intros ?.

Section pmf.

  (* NB. Using nat instead of int so the SeriesC is a little bit easier to work with.
     All values bumped by 1. *)
  Definition C_μ (m : nat) : nat → R := fun n =>
    Iverson (eq 0) n * (1 / (2 * m + 2)) +
    Iverson (eq 1) n * (1 / (2 * m + 2)) +
    Iverson (eq 2) n * (m / (2 * m + 2)).

  Definition Bii_μ (k : nat) (x : R) : bool → R := fun b =>
    Iverson is_true b * (1 - (2*k+x)/(2*k+2)) + Iverson (not ∘ is_true) b * ((2*k+x)/(2*k+2)).

  Definition S_μ0 (k : nat) (x y : R) : nat → R := fun n =>
    (y^n / fact n) * ((2*k+x)/(2*k+2))^n -
    (y^(n+1) / fact (n+1)) * ((2*k+x)/(2*k+2))^(n+1).

  Definition S_μ (k : nat) (x y : R) (N : nat) : nat → R := fun n =>
    Iverson (le N) n * S_μ0 k x y (n - N).

  Definition B_μ (k : nat) (x : R) : bool → R := fun b =>
    Iverson is_true b * (exp (-x*(2*k+x)/(2*k+2))) + Iverson (not ∘ is_true) b * (1 - exp (-x*(2*k+x)/(2*k+2))).


End pmf.

Section credits.
  Import Hierarchy.

  Definition C_CreditV (F : nat → R) m :=
    (1 / (m + 2)) * F 0%nat +
    (1 / (m + 2)) * F 1%nat +
    (m / (m + 2)) * F 2%nat.

  Definition Bii_CreditV (F : bool → R) k x :=
    Bii_μ k x false * F false + Bii_μ k x true * F true.

  Definition S_CreditV (F : nat → R) k x y N : R :=
    SeriesC (fun n => S_μ k x y N n * F n).

  Definition B_CreditV (F : bool → R) (k : nat) (x : R) : R :=
    (exp (-x*(2*k+x)/(2*k+2))) * F true +
    (1 - exp (-x*(2*k+x)/(2*k+2))) * F false.

  Definition Bii_g F x : R → R := fun r =>
    Iverson (Rle x) r * F true +
    Iverson (Rge x) r * F false.

  Definition Bii_h F x : nat → R := fun n =>
    Iverson (eq 0) n * F true +
    Iverson (eq 1) n * RInt (Bii_g F x) 0 1 +
    Iverson (eq 2) n * F false.

  Definition S_hz F k x N z : bool → R := fun b =>
    Iverson is_true b * F N +
    Iverson (not ∘ is_true) b * S_CreditV F k x z (N + 1).

  Definition S_g F k x y N : R → R := fun z =>
    Iverson (Rle y) z * F N +
    Iverson (Rge y) z * (Bii_μ k x false * S_hz F k x N z false + Bii_μ k x true * S_hz F k x N z true).

  Definition B_g (F : bool → R) : nat → R := fun z =>
    Iverson Zeven z * F (true) +
    Iverson (not ∘ Zeven) z * F (false).

  Lemma C_CreditV_nn {F m} (Hnn : ∀ r, 0 <= F r) (Hm : 0 <= m) : 0 <= C_CreditV F m.
  Proof.
    rewrite /C_CreditV.
    apply Rplus_le_le_0_compat; [apply Rplus_le_le_0_compat |].
    { apply Rmult_le_pos; auto. apply Rle_mult_inv_pos; try lra. }
    { apply Rmult_le_pos; auto. apply Rle_mult_inv_pos; try lra. }
    { apply Rmult_le_pos; auto. apply Rle_mult_inv_pos; try lra. }
  Qed.

  Lemma Bii_μ_nn {k x b} (Hx : 0 <= x <= 1) : 0 <= Bii_μ k x b.
  Proof.
    rewrite /Bii_μ.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg| auto ]).
    { apply error_credits.Rle_0_le_minus.
      rewrite -Rcomplements.Rdiv_le_1.
      { apply Rplus_le_compat; [lra|lra]. }
      { apply Rplus_le_lt_0_compat; try lra.
        apply Rmult_le_pos; try lra.
        apply pos_INR. }
    }
    { apply Rle_mult_inv_pos; try lra.
      { apply Rplus_le_le_0_compat; [|lra].
        apply Rmult_le_pos; try lra.
        apply pos_INR. }
      { rewrite -(Rplus_0_l 0).
        apply Rplus_le_lt_compat; [|lra].
        apply Rmult_le_pos; try lra.
        apply pos_INR. }
    }
  Qed.

  Lemma S_μ0_nn {x k y x'} (Hx : 0 <= x <= 1) (Hy : 0 <= y <= 1) : 0 <= S_μ0 k x y x'.
  Proof.
    rewrite /S_μ0.
    apply error_credits.Rle_0_le_minus.
    apply Rmult_le_compat.
    { apply Rcomplements.Rdiv_le_0_compat.
      { apply pow_le; lra. }
      { apply INR_fact_lt_0. }
    }
    { apply pow_le.
      apply Rcomplements.Rdiv_le_0_compat.
      { apply Rplus_le_le_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
      { apply Rplus_le_lt_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
    }
    { apply Rmult_le_compat.
      { apply pow_le; lra. }
      { rewrite -(Rmult_1_l (/ _)).
        apply Rcomplements.Rdiv_le_0_compat; [lra|].
        apply INR_fact_lt_0.
      }
      { rewrite -(Rmult_1_r (y ^ x')).
        rewrite pow_add pow_1.
        apply Rmult_le_compat; try lra.
        apply pow_le; lra.
      }
      { apply Rcomplements.Rinv_le_contravar.
        { apply INR_fact_lt_0. }
        apply le_INR.
        apply fact_le.
        lia.
      }
    }
    {
      rewrite -(Rmult_1_r (_ ^ x')).
      rewrite pow_add pow_1.
      apply Rmult_le_compat; try lra.
      { apply pow_le.
        apply Rcomplements.Rdiv_le_0_compat.
        { apply Rplus_le_le_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
        { apply Rplus_le_lt_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
      }
      { apply Rcomplements.Rdiv_le_0_compat.
        { apply Rplus_le_le_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
        { apply Rplus_le_lt_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
      }
      { rewrite -Rcomplements.Rdiv_le_1.
        { apply Rplus_le_compat; [lra|lra]. }
        { apply Rplus_le_lt_0_compat; try lra.
          apply Rmult_le_pos; try lra.
          apply pos_INR. }
        }
      }
  Qed.

  Lemma S_μ_nn {x k y N x'} (Hx : 0 <= x <= 1) (Hy : 0 <= y <= 1) : 0 <= S_μ k x y N x'.
  Proof.
    rewrite /S_μ.
    apply Rmult_le_pos; first apply Iverson_nonneg.
    apply S_μ0_nn; auto.
  Qed.

  Lemma ex_RInt_S_μ0 {x n b k} : ex_RInt (λ x0 : R, S_μ0 k x x0 n) 0 b.
  Proof.
    rewrite /S_μ0.
    apply (@ex_RInt_minus R_CompleteNormedModule).
    { apply ex_RInt_Rmult'.
      replace (λ x0 : R, x0 ^ n / fact n) with (λ x0 : R, x0 ^ n * / fact n) by (funexti; OK).
      apply ex_RInt_Rmult'.
      apply ex_RInt_pow.
    }
    { apply ex_RInt_Rmult'.
      replace (λ x0 : R, x0 ^ (n + 1) / fact (n + 1)) with (λ x0 : R, x0 ^ (n + 1) * / fact (n + 1)) by (funexti; OK).
      apply ex_RInt_Rmult'.
      apply ex_RInt_pow.
    }
  Qed.

  Lemma ex_RInt_S_μ {x N n b k} : ex_RInt (λ x0 : R, S_μ k x x0 N n) 0 b.
  Proof.
    rewrite /S_μ.
    rewrite /Iverson.
    case_decide.
    { eapply ex_RInt_ext; last eapply ex_RInt_S_μ0.
      intros ??. simpl. rewrite Rmult_1_l. done.
    }
    { eapply ex_RInt_ext; last eapply (ex_RInt_const _ _ 0).
      intros ??.
      simpl.
      OK.
    }
  Qed.

  Lemma Bii_CreditV_nn {F k x} (Hnn : ∀ r, 0 <= F r) (Hx : 0 <= x <= 1) : 0 <= Bii_CreditV F k x.
  Proof.
    rewrite /Bii_CreditV.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Bii_μ_nn; auto | auto ]).
  Qed.

  Lemma S_CreditV_nn {F k x y N} (Hnn : ∀ r, 0 <= F r) (Hx : 0 <= x <= 1) (Hy : 0 <= y <= 1) : 0 <= S_CreditV F k x y N.
  Proof.
    rewrite /S_CreditV.
    apply SeriesC_ge_0'.
    intros x'.
    apply Rmult_le_pos; last auto.
    apply S_μ_nn; auto.
  Qed.

  Lemma B_CreditV_nn {F k x} (Hnn : ∀ r, 0 <= F r) (Hx : 0 <= x <= 1) : 0 <= B_CreditV F k x.
  Proof.
    rewrite /B_CreditV.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [| auto ]).
    { apply Rexp_range.
      apply Rcomplements.Rmult_le_0_r; first apply Rcomplements.Rmult_le_0_r.
      { lra. }
      { apply Rplus_le_le_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
      rewrite -(Rmult_1_l (/ _)).
      apply Rle_mult_inv_pos; [lra|].
      apply Rplus_le_lt_0_compat; [|lra].
      apply Rmult_le_pos; [lra|apply pos_INR].
    }
    { apply error_credits.Rle_0_le_minus.
      apply Rexp_range.
      apply Rcomplements.Rmult_le_0_r; first apply Rcomplements.Rmult_le_0_r.
      { lra. }
      { apply Rplus_le_le_0_compat; [|lra]. apply Rmult_le_pos; [lra|apply pos_INR]. }
      rewrite -(Rmult_1_l (/ _)).
      apply Rle_mult_inv_pos; [lra|].
      apply Rplus_le_lt_0_compat; [|lra].
      apply Rmult_le_pos; [lra|apply pos_INR].
    }
  Qed.

  Lemma Bii_g_ex_RInt {F k} (Hnn : ∀ r, 0 <= F r) : ex_RInt (Bii_g F k) 0 1.
  Proof.
    rewrite /Bii_g.
    apply ex_RInt_add.
    { apply ex_RInt_mult; first apply ex_RInt_Iverson_le.
      apply ex_RInt_const.
    }
    { apply ex_RInt_mult; first apply ex_RInt_Iverson_ge.
      apply ex_RInt_const.
    }
  Qed.

  Lemma Bii_g_nn {F k x} (Hnn : ∀ r, 0 <= F r) : 0 <= x <= 1 → 0 <= Bii_g F k x.
  Proof.
    intro H.
    rewrite /Bii_g.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg | auto ]).
  Qed.

  Lemma Bii_h_nn {F k x} (Hnn : ∀ r, 0 <= F r) : 0 <= Bii_h F k x.
  Proof.
    rewrite /Bii_h.
    apply Rplus_le_le_0_compat; first apply (Rplus_le_le_0_compat); apply Rmult_le_pos;
      try auto; try (apply Iverson_nonneg; auto).
    apply RInt_ge_0; try lra.
    { apply Bii_g_ex_RInt; auto. }
    intros ??.
    apply Bii_g_nn; auto.
    lra.
  Qed.

  Lemma Bii_g_correct {F x} (Hf : ∀ r : bool, 0 <= F r) : is_RInt (Bii_g F x) 0 1 (RInt (Bii_g F x) 0 1).
  Proof.
    apply (RInt_correct (Bii_g F x) 0 1).
    apply Bii_g_ex_RInt.
    apply Hf.
  Qed.

  Lemma Bii_f_expectation {F k x} (Hx : 0 <= x <= 1) : Bii_CreditV F k x = C_CreditV (Bii_h F x) (2 * k)%nat.
  Proof.
    rewrite /Bii_CreditV.
    rewrite /C_CreditV.
    rewrite /Bii_h.
    rewrite Iverson_True;  [rewrite Rmult_1_l|done].
    rewrite Iverson_False; [rewrite Rmult_0_l Rplus_0_r|done].
    rewrite Iverson_False; [rewrite Rmult_0_l Rplus_0_r|done].
    rewrite Iverson_False; [rewrite Rmult_0_l Rplus_0_l|simpl;lra].
    rewrite Iverson_True;  [rewrite Rmult_1_l|done].
    rewrite Iverson_False; [rewrite Rmult_0_l Rplus_0_r|simpl;lra].
    rewrite Iverson_False; [rewrite Rmult_0_l Rplus_0_l|simpl;lra].
    rewrite Iverson_False; [rewrite Rmult_0_l Rplus_0_l|simpl;lra].
    rewrite Iverson_True;  [rewrite Rmult_1_l|done].
    rewrite /Bii_g.
    (* Evaluate the inner integral *)
    rewrite -RInt_add.
    2: { apply ex_RInt_mult; first apply ex_RInt_Iverson_le. apply ex_RInt_const. }
    2: { apply ex_RInt_mult; first apply ex_RInt_Iverson_ge. apply ex_RInt_const. }
    rewrite -RInt_Rmult' -RInt_Rmult'.
    rewrite RInt_Iverson_le'''; [|done].
    rewrite RInt_Iverson_ge'''; [|done].

    (* Factor out true and false terms separately *)
    rewrite Rmult_plus_distr_l.
    rewrite -(Rmult_assoc _ (1 - x) _).
    rewrite -(Rmult_assoc _ x _).
    rewrite -Rplus_assoc.
    rewrite -(Rmult_plus_distr_r _ _ (F true)).
    rewrite Rplus_assoc.
    rewrite -(Rmult_plus_distr_r _ _ (F false)).
    rewrite Rplus_comm; f_equal.
    { f_equal.
      rewrite /Bii_μ.
      rewrite Iverson_True;  [|intuition].
      rewrite Iverson_False; [|intuition].
      rewrite Rmult_0_l Rmult_1_l Rplus_0_r.
      rewrite (Rmult_comm _ (1 - x)) -Rmult_assoc Rmult_1_r.
      rewrite -Rdiv_plus_distr.
      rewrite -{1}(Rdiv_diag (2 * k + 2)); last first.
      { intro Hk.
        rewrite -{2}(Rmult_1_r 2) in Hk.
        rewrite -Rmult_plus_distr_l in Hk.
        destruct (Rmult_integral _ _ Hk); first lra.
        have ? : 0 <= k by apply pos_INR.
        lra.
      }
      rewrite -(Rdiv_minus_distr).
      f_equal; [lra|].
      f_equal.
      rewrite mult_INR; f_equal.
    }
    { f_equal.
      rewrite /Bii_μ.
      rewrite Iverson_False; [|intuition].
      rewrite Iverson_True;  [|intuition].
      rewrite Rmult_0_l Rmult_1_l Rplus_0_l.
      rewrite (Rmult_comm _ x) -Rmult_assoc Rmult_1_r.
      rewrite -Rdiv_plus_distr.
      rewrite mult_INR.
      f_equal. rewrite Rplus_comm; f_equal.
    }
  Qed.


  Lemma S_hz_nn {F k x N z w} (Hnn : ∀ r, 0 <= F r) (H : 0 <= x <= 1) (Hy : 0 <= z <= 1) : 0 <= S_hz F k x N z w.
  Proof.
    rewrite /S_hz.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg | auto ]).
    apply S_CreditV_nn; auto.
  Qed.

  Lemma S_g_nn {F k x z N r} (Hnn : ∀ r, 0 <= F r) (H : 0 <= x <= 1) (Hy : 0 <= r <= 1) : 0 <= S_g F k x z N r.
  Proof.
    rewrite /S_g.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg | auto ]).
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Bii_μ_nn; auto | auto ]).
    { apply S_hz_nn; auto. }
    { apply S_hz_nn; auto. }
  Qed.

  Lemma S_nn_1 {F k x z N} (Hnn : ∀ r, 0 <= F r) (H : 0 <= x <= 1) (Hz : 0 <= z <= 1) :
    0 <= Bii_μ k x false * S_hz F k x N z false + Bii_μ k x true * S_hz F k x N z true.
  Proof.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Bii_μ_nn; auto | auto ]).
    { apply S_hz_nn; auto. }
    { apply S_hz_nn; auto. }
  Qed.

  Lemma ex_RInt_S_CreditV {F k x N b M} (Hb : 0 <= b <= 1) (Hx : 0 <= x <= 1) (Hf : ∀ x, 0 <= F x <= M) : ex_RInt (λ y : R, S_CreditV F k x y N) 0 b.
  Proof.
    rewrite /S_CreditV.
    rewrite -ex_RInt_dom.
    rewrite /ex_RInt.
    replace (λ x0 : R, Iverson (Ioo 0 b) x0 * SeriesC (λ n : nat, S_μ k x x0 N n * F n))
      with  (fun x0 : R => Series.Series (fun n : nat => Iverson (Ioo 0 b) x0 * (S_μ k x x0 N n * F n))); last first.
    { funexti.
      rewrite -SeriesC_scal_l.
      rewrite SeriesC_Series_nat.
      OK.
    }
    pose s : nat → R → R_CompleteNormedModule :=
      fun M x0 => sum_n (λ n : nat, Iverson (Ioo 0 b) x0 * (S_μ k x x0 N n * F n)) M.
    pose h : nat → R_CompleteNormedModule :=
      fun x1 => (RInt (λ x0 : R, sum_n (λ n : nat, Iverson (Ioo 0 b) x0 * (S_μ k x x0 N n * F n)) x1) 0 b).
    have HSLim : filterlim s eventually
      (locally (λ x0 : R, Series.Series (λ n : nat, Iverson (Ioo 0 b) x0 * (S_μ k x x0 N n * F n)))).
    { rewrite /s.
      apply (UniformConverge_Series (fun n => M * / (fact (n - N)%nat))).
      { apply (@Series.ex_series_scal_l _ R_CompleteNormedModule), ex_exp_series'. }
      intros x' n.
      rewrite Rabs_right; last first.
      { apply Rle_ge.
        rewrite /Iverson; case_decide.
        { rewrite Rmult_1_l. apply Rmult_le_pos.
          { apply S_μ_nn; OK.
            rewrite /Ioo//= in H.
            rewrite /Ioo in H.
            rewrite Rmin_left in H; OK.
            rewrite Rmax_right in H; OK.
          }
          { apply Hf. }
        }
        OK.
      }
      rewrite /Iverson.
      case_decide; last first.
      { rewrite Rmult_0_l.
        apply Rdiv_le_0_compat. { have ? := Hf 0%nat. OK. }
        apply INR_fact_lt_0. }
      rewrite /Ioo in H.
      rewrite Rmin_left in H; OK.
      rewrite Rmax_right in H; OK.
      rewrite Rmult_1_l.
      rewrite Rmult_comm.
      apply Rmult_le_compat.
      { apply Hf. }
      { apply S_μ_nn; OK. }
      { apply Hf. }
      rewrite /S_μ.
      rewrite /Iverson; case_decide; last first.
      { rewrite Rmult_0_l.
        rewrite -(Rmult_1_l (/ fact _)).
        apply Rdiv_le_0_compat; OK.
        apply INR_fact_lt_0. }
      rewrite Rmult_1_l.
      rewrite /S_μ0.
      repeat rewrite Rdiv_def.
      replace (n - N + 1)%nat with (S (n - N)) by OK.
      rewrite fact_simpl.
      rewrite mult_INR.
      rewrite Rinv_mult.
      rewrite -Rmult_assoc.
      rewrite -tech_pow_Rmult.
      rewrite -tech_pow_Rmult.
      repeat rewrite -Rmult_assoc.
      rewrite -Rmult_minus_distr_r.
      rewrite -{3}(Rmult_1_r (/fact (n - N))).
      have Lem1 : 0 <= (2 * k + x) * / (2 * k + 2) <= 1.
      { split.
        { apply Rle_mult_inv_pos.
          { apply Rplus_le_le_0_compat; OK.
            apply Rmult_le_pos; OK.
            apply pos_INR.
          }
          { apply Rplus_le_lt_0_compat; OK.
            apply Rmult_le_pos; OK.
            apply pos_INR.
          }
        }
        { have ? : 0 < (2 * k + 2). { apply Rplus_le_lt_0_compat; OK. apply Rmult_le_pos; OK. apply pos_INR. }
          apply (Rmult_le_reg_r (2 * k + 2)); OK.
          rewrite Rmult_assoc.
          rewrite Rinv_l; OK.
        }
      }
      apply Rmult_le_compat.
      { apply Rle_0_le_minus.
        rewrite (Rmult_comm x' (x' ^ (n - N))).
        repeat rewrite Rmult_assoc.
        apply Rmult_le_compat_l.
        { apply pow_le; OK. }
        rewrite -Rmult_assoc.
        rewrite (Rmult_comm _ ((/ fact (n - N) * ((2 * k + x) * / (2 * k + 2))))).
        repeat rewrite Rmult_assoc.
        rewrite -{2}(Rmult_1_r (/ fact (n - N))).
        apply Rmult_le_compat_l.
        { rewrite -(Rmult_1_l (/ _)). apply Rdiv_le_0_compat; OK. apply INR_fact_lt_0. }
        repeat rewrite -Rmult_assoc.
        rewrite Rmult_assoc.
        rewrite -(Rmult_1_l 1).
        have ? : 0 < INR (S (n - N)) by apply pos_INR_S.
        apply Rmult_le_compat; OK.
        { apply Rdiv_le_0_compat; OK.  }
        apply (Rmult_le_reg_r (INR (S (n - N)))); OK.
        rewrite Rmult_assoc.
        rewrite Rinv_l; OK.
        rewrite Rmult_comm.
        apply Rmult_le_compat; OK.
        apply (Rle_trans _ b); OK.
        apply (Rle_trans _ 1); OK.
        rewrite -INR_1.
        apply le_INR. OK.
      }
      { apply pow_le. apply Lem1. }
      { replace (x' ^ (n - N) * / fact (n - N) - x' * x' ^ (n - N) * / S (n - N) * / fact (n - N) * (2 * k + x) * / (2 * k + 2))
          with  (/ fact (n - N)  * (x' ^ (n - N) - x' * x' ^ (n - N) * / S (n - N) * (2 * k + x) * / (2 * k + 2))) by OK.
        rewrite -{2}(Rmult_1_r (/ fact (n - N))).
        apply Rmult_le_compat; OK.
        { rewrite -(Rmult_1_l (/_)). apply Rdiv_le_0_compat; OK. apply INR_fact_lt_0. }
        { apply error_credits.Rle_0_le_minus.
          rewrite (Rmult_comm  x' (x' ^ (n - N))).
          rewrite -{2}(Rmult_1_l (x' ^ (n - N))).
          repeat rewrite Rmult_assoc.
          rewrite (Rmult_comm 1 (x' ^ (n - N))).
          apply Rmult_le_compat; OK.
          { apply pow_le; OK. }
          { rewrite -Rmult_assoc.
            apply Rmult_le_pos; OK.
            apply Rdiv_le_0_compat; OK.
            apply pos_INR_S. }
          rewrite -(Rmult_1_l 1).
          apply Rmult_le_compat; OK.
          { rewrite Rmult_comm.
            apply Rdiv_le_0_compat; OK.
            apply pos_INR_S. }
          { rewrite -(Rmult_1_l 1).
            apply Rmult_le_compat; OK.
            { rewrite  -(Rmult_1_l (/ _)).
              apply Rdiv_le_0_compat; OK.
              apply pos_INR_S. }
            { rewrite -Rinv_1.
              apply Rinv_le_contravar; OK.
              rewrite -INR_1.
              apply le_INR.
              OK.
              }
            }
          }
        { etrans.
          { eapply Rminus_le_0_compat.
            repeat rewrite Rmult_assoc.
            apply Rmult_le_pos; OK.
            apply Rmult_le_pos.
            { apply pow_le; OK. }
            apply Rmult_le_pos; OK.
        { rewrite -(Rmult_1_l (/_)). apply Rdiv_le_0_compat; OK. apply pos_INR_S. } }
      { rewrite -(pow1 (n - N)). apply pow_incr; OK. } } }
    { rewrite -(pow1 (n - N)). apply pow_incr; OK. }
    }
    have HSInt : ∀ x : nat, is_RInt (s x) 0 b (h x).
    { rewrite /s/h. intro N'.
      apply (@RInt_correct R_CompleteNormedModule).
      apply ex_RInt_sum_n.
      intros n''.
      rewrite ex_RInt_dom.
      apply ex_RInt_Rmult'.
      apply ex_RInt_S_μ.
    }
    destruct (@filterlim_RInt nat R_CompleteNormedModule s 0 b eventually eventually_filter
      (λ x0 : R, Series.Series (λ n : nat, Iverson (Ioo 0 b) x0 * (S_μ k x x0 N n * F n))) h HSInt HSLim) as [IF [HIf1 HIf2]].
    exists IF. done.
  Qed.

  Lemma ex_RInt_S_hz {F k N x M b} (Hx : 0 <= x <= 1) (Hf : ∀ x, 0 <= F x <= M) : ex_RInt (λ y0 : R, S_hz F k x N y0 b) 0 1.
  Proof.
    rewrite /S_hz.
    apply ex_RInt_add; first apply ex_RInt_const.
    apply ex_RInt_mult; first apply ex_RInt_const.
    eapply ex_RInt_S_CreditV; OK.
  Qed.

  Lemma S_g_ex_RInt {F k x y M N} (Hx : 0 <= x <= 1) (Hf : ∀ x, 0 <= F x <= M) : ex_RInt (S_g F k x y N) 0 1.
  Proof.
    rewrite /S_g.
    apply ex_RInt_add.
    { apply ex_RInt_mult; first apply ex_RInt_Iverson_le. apply ex_RInt_const. }
    apply ex_RInt_mult; first apply ex_RInt_Iverson_ge.
    apply ex_RInt_add.
    { apply ex_RInt_mult; first apply ex_RInt_const. eapply ex_RInt_S_hz; OK. }
    { apply ex_RInt_mult; first apply ex_RInt_const. eapply ex_RInt_S_hz; OK. }
  Qed.

  (* TODO: Maybe I could get rid of some of the splitting if the existence side conditions are hard to prove. *)
  Lemma S_g_expectation {F k x y M N} (Hx : 0 <= x <= 1) (Hy : 0 <= y <= 1) (Hf : ∀ x, 0 <= F x <= M) : is_RInt (S_g F k x y N) 0 1 (S_CreditV F k x y N).
  Proof.
    suffices H : S_CreditV F k x y N = RInt (S_g F k x y N) 0 1.
    { rewrite H. apply (RInt_correct (V := R_CompleteNormedModule)). eapply S_g_ex_RInt; OK. }
    rewrite /S_g.
    (* Split the series; compute the first term *)
    rewrite -RInt_add.
    3: {
      apply ex_RInt_mult; first apply ex_RInt_Iverson_ge.
      apply ex_RInt_add.
      { apply ex_RInt_mult; first apply ex_RInt_const. eapply ex_RInt_S_hz; OK. }
      { apply ex_RInt_mult; first apply ex_RInt_const. eapply ex_RInt_S_hz; OK. }
    }
    2: {
      apply ex_RInt_mult; first apply ex_RInt_Iverson_le.
      apply ex_RInt_const.
    }
    rewrite -RInt_Rmult'.
    rewrite RInt_Iverson_le'''; [|done].
    replace (RInt (λ x0 : R, Iverson (Rge y) x0 * (Bii_μ k x false * S_hz F k x N x0 false + Bii_μ k x true * S_hz F k x N x0 true)) 0 1)
       with (RInt (λ x0 : R, (Bii_μ k x false * S_hz F k x N x0 false + Bii_μ k x true * S_hz F k x N x0 true)) 0 y);
      last first.
    { apply RInt_Iverson_ge''''. }
    rewrite /Bii_μ.
    rewrite Iverson_False; [|intuition].
    rewrite Iverson_True;  [|intuition].
    rewrite Iverson_True;  [|intuition].
    rewrite Iverson_False; [|intuition].
    rewrite Rmult_0_l Rmult_0_l Rmult_1_l Rmult_1_l Rplus_0_l Rplus_0_r.
    rewrite /S_hz.
    rewrite Iverson_False; [|intuition].
    rewrite Iverson_True;  [|intuition].
    rewrite Iverson_True;  [|intuition].
    rewrite Iverson_False; [|intuition].
    rewrite Rmult_0_l Rmult_1_l.
    (* Rewrite is confused by the other terms for some reason  *)
    replace (λ x0 : R, (2 * k + x) / (2 * k + 2) * (0 + 1 * S_CreditV F k x x0 (N + 1)) +
               (1 - (2 * k + x) / (2 * k + 2)) * (F N + 0 * S_CreditV F k x x0 (N + 1))) with
            (λ x0 : R, (2 * k + x) / (2 * k + 2) * (S_CreditV F k x x0 (N + 1)) +
               (1 - (2 * k + x) / (2 * k + 2)) * F N); last first.
    { apply functional_extensionality; intros ?.
      rewrite Rmult_0_l Rmult_1_l Rplus_0_l Rplus_0_r. done. }
    rewrite -RInt_add.
    3: { apply ex_RInt_mult; apply ex_RInt_const. }
    2: { apply ex_RInt_mult; first apply ex_RInt_const.
         eapply ex_RInt_S_CreditV; last done; OK.
    }
    rewrite RInt_const.
    rewrite /scal//=/mult//=.
    rewrite Rminus_0_r.
    rewrite -Rmult_assoc. rewrite -Rplus_assoc Rplus_comm -Rplus_assoc.
    (*
    replace ((1 - y) * (1 - (2 * k + x) / (2 * k + 2)) * F N + (1 - y) * F N)
       with ((1 - y) * (1 - (2 * k + x) / (2 * k + 2) + 1) * F N); last lra.
    *)
    rewrite -RInt_Rmult.
    rewrite {2}/S_CreditV.
    replace (RInt (λ x0 : R, SeriesC (λ n : nat, S_μ k x x0 (N + 1) n * F n)) 0 y)
       with (SeriesC (λ n : nat, RInt (λ x0 : R, S_μ k x x0 (N + 1) n * F n) 0 y));
      last first.
    {  (* Foob *) admit. }
    rewrite -SeriesC_scal_l.
    rewrite -Rmult_plus_distr_r.
    replace ((y * (1 - (2 * k + x) / (2 * k + 2)) + (1 - y)) * F N)
       with (SeriesC (fun n : nat => Iverson (eq N) n * ((y * (1 - (2 * k + x) / (2 * k + 2)) + (1 - y)) * F n)));
      last first.
    { rewrite (SeriesC_Iverson_singleton N); last intuition. lra. }
    rewrite -SeriesC_plus.
    3: {
      apply ex_seriesC_scal_l.
      replace (λ x0 : nat, RInt (λ x1 : R, S_μ k x x1 (N + 1) x0 * F x0) 0 y)
        with  (λ x0 : nat, 999 * F x0); last first.
      { funexti.
        symmetry.
        rewrite -RInt_Rmult'; f_equal.
        rewrite /S_μ.
        rewrite /S_μ0.
        (* Compute it *)

        admit.
      }
      (* And then it should be the exp series or somthing? bound the F term above by M...*)
      admit.

    }
    2: { apply ex_seriesC_single. }
    rewrite /S_CreditV.
    f_equal. apply functional_extensionality; intro n.
    (* Cancel F *)
    rewrite -RInt_Rmult'.
    rewrite -Rmult_assoc.
    rewrite -Rmult_assoc.
    rewrite -Rmult_plus_distr_r.
    f_equal.
    (* Do cases before unfolding S_μ0 *)
    rewrite /S_μ.
    rewrite -RInt_Rmult.
    rewrite {1}/Iverson.
    case_decide; last first.
    { rewrite Iverson_False; [|lia]. rewrite Iverson_False; [|lia]. lra. }
    rewrite Rmult_1_l.
    rewrite {1}/Iverson.
    case_decide.
    { rewrite Rmult_1_l.
      rewrite Iverson_False; [|lia].
      rewrite Rmult_0_l Rmult_0_r Rplus_0_r.
      rewrite H0.
      rewrite Nat.sub_diag.
      rewrite /S_μ0.
      rewrite pow_O.
      rewrite /fact//=.
      rewrite Rdiv_diag; [|lra].
      rewrite Rmult_1_l.
      rewrite Rmult_1_r.
      rewrite Rdiv_1_r.
      rewrite Rmult_1_r.
      lra.
    }
    rewrite Rmult_0_l Rplus_0_l.
    rewrite Iverson_True; [|lia].
    rewrite Rmult_1_l.
    rewrite /S_μ0.
    rewrite RInt_minus.
    2: {
      apply ex_RInt_Rmult'.
      eapply ex_RInt_ext; first (intros ??; symmetry; erewrite Rdiv_def; done).
      apply ex_RInt_Rmult'.
      apply ex_RInt_pow.
    }
    2: {
      apply ex_RInt_Rmult'.
      eapply ex_RInt_ext; first (intros ??; symmetry; erewrite Rdiv_def; done).
      apply ex_RInt_Rmult'.
      apply ex_RInt_pow.
    }
    rewrite /minus//=/plus/opp//= -Rminus_def.
    repeat rewrite -RInt_Rmult'.
    rewrite Rmult_minus_distr_l.
    rewrite RInt_pow.
    rewrite RInt_pow.
    repeat rewrite Rdiv_def.
    repeat (rewrite pow_i; [|lia]).
    repeat rewrite Rmult_0_l.
    repeat rewrite Rminus_0_r.
    pose X := ((2 * k + x) * / (2 * k + 2)).
    have HX : X = ((2 * k + x) * / (2 * k + 2)) by done.
    repeat rewrite -HX.
    f_equal.
    { rewrite (Rmult_comm X).
      repeat rewrite Rmult_assoc.
      rewrite -{3}(pow_1 X).
      rewrite -pow_add.
      f_equal; [f_equal; lia|].
      rewrite -Rmult_assoc.
      f_equal; [|f_equal; lia].
      rewrite -Rinv_mult.
      replace (n - (N + 1) + 1)%nat with (S (n - (N + 1)))%nat by lia.
      rewrite -mult_INR.
      rewrite -fact_simpl.
      f_equal. f_equal. f_equal. lia.
    }
    { rewrite (Rmult_comm X).
      repeat rewrite Rmult_assoc.
      rewrite -{3}(pow_1 X).
      rewrite -pow_add.
      f_equal; [f_equal; lia|].
      rewrite -Rmult_assoc.
      f_equal; [|f_equal; lia].
      rewrite -Rinv_mult.
      replace (n - (N + 1) + 1 + 1)%nat with (S (n - (N + 1) + 1))%nat by lia.
      rewrite -mult_INR.
      rewrite -fact_simpl.
      f_equal. f_equal. f_equal. lia.
    }
  Admitted.

  Lemma B_g_nn {F b} (Hnn : ∀ r, 0 <= F r) :  0 <= B_g F b.
  Proof.
    rewrite /B_g.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg | auto ]).
  Qed.

  Lemma B_g_expectation {F k x} : B_CreditV F k x = S_CreditV (B_g F) k x x 0.
  Proof.
    rewrite /B_CreditV.
    rewrite /S_CreditV.
    rewrite /B_g.
    (* Split the series *)
    rewrite /S_μ.
    rewrite /S_μ0.
    (* Apply exp t.s. to both *)
  Admitted.

End credits.

Section program.
  Context `{!erisGS Σ}.

  Definition C : val  :=
    λ: "m",
      let: "v" := rand ("m" + #1) in
      if: "v" = #0 then #0 else if: "v" = #1 then #1 else #2.

  Definition Bii : val :=
    λ: "k" "x",
      let: "f" := C (#2 * "k") in
      let: "r" := init #() in
      ("f" = #0) || (("f" = #1) && (cmp "x" "r" = #(-1))).

  Definition S : val :=
    rec: "trial" "k" "x" "y" "N" :=
      let: "z" := init #() in
      if: (cmp "y" "z" = #(-1)) || (Bii "k" "x") then "N" else "trial" "k" "x" "z" ("N" + #1%nat).

  (* The first iterate of S so that we do not need to duplicate x. All other iterates are fine. *)
  Definition S0 : val :=
    λ: "k" "x",
      let: "z" := init #() in
      if: (cmp "x" "z" = #(-1)) || (Bii "k" "x") then #0 else S "k" "x" "z" #1%nat.

  Definition B : val :=
    λ: "k" "x", (S0 "k" "x") `rem` #2 = #0.

  Theorem wp_C {E F} (m : nat) (Hnn : ∀ r, 0 <= F r) :
    ↯(C_CreditV F m) -∗ WP C #m @ E {{ vn, ∃ n : nat, ⌜vn = #n ⌝ ∗ ⌜n = 0%nat \/ n = 1%nat \/ n = 2%nat⌝∗ ↯(F n) }}.
  Proof.
    iIntros "Hε".
    rewrite /C.
    wp_pures.
    (* I hate fin >:( *)
    have HF0 : (0 < (Coq.Init.Datatypes.S (Z.to_nat (m + 1))))%nat by lia.
    have HF1 : (1 < (Coq.Init.Datatypes.S (Z.to_nat (m + 1))))%nat by lia.
    pose F0 : fin (Coq.Init.Datatypes.S  (Z.to_nat (m + 1))) := Fin.of_nat_lt HF0.
    pose F1 : fin (Coq.Init.Datatypes.S (Z.to_nat (m + 1))) := Fin.of_nat_lt HF1.
    pose C_F := fun (n : fin (Coq.Init.Datatypes.S  (Z.to_nat (m + 1)))) =>
      Iverson (eq F0) n * (1 / (m + 2) * F 0%nat) +
      Iverson (eq F1) n * (1 / (m + 2) * F 1%nat) +
      Iverson (fun n' => ¬ n' = F0 ∧ ¬ n' = F1) n * (m / (m + 2) * F 2%nat).
    wp_apply (wp_couple_rand_adv_comp _ _ _ _ C_F with "Hε").
    { intro n. rewrite /C_F.
      apply Rplus_le_le_0_compat; first apply (Rplus_le_le_0_compat); apply Rmult_le_pos;
        try auto; try (apply Iverson_nonneg; auto).
      all: apply Rmult_le_pos; auto; apply Rle_mult_inv_pos; try lra.
      { apply Rplus_le_lt_0_compat; [|lra]. apply pos_INR. }
      { apply Rplus_le_lt_0_compat; [|lra]. apply pos_INR. }
      { apply pos_INR. }
      { apply Rplus_le_lt_0_compat; [|lra]. apply pos_INR. }
    }
    { rewrite /C_CreditV.
      unfold C_F.
      rewrite SeriesC_fin_sum.
      rewrite /sum_n.
      admit. }
    iIntros (n) "Hε".
    (* Probably true, stupid fin *)
  Admitted.

  Theorem wp_Bii {E F} (k : nat) xα x (Hnn : ∀ r, 0 <= F r) (Hx : 0 <= x <= 1) :
    ↯(Bii_CreditV F k x) ∗ lazy_real xα x -∗
    WP Bii #k xα @ E {{ vb, ∃ b : bool, ⌜vb = #b ⌝ ∗ ↯(F b) ∗ lazy_real xα x }}.
  Proof.
    iIntros "(Hε & Hx)".
    rewrite /Bii.
    wp_pures.
    wp_bind (C _).
    iApply (pgl_wp_mono_frame _ with "[Hε] Hx"); last first.
    { replace (Z.mul 2 (Z.of_nat k)) with (Z.of_nat (2 * k)%nat) by lia.
      wp_apply (wp_C (F:=Bii_h F x)).
      { by intros ?; apply Bii_h_nn, Hnn. }
      { iApply (ec_eq with "Hε");  by rewrite Bii_f_expectation. }
    }
    iIntros (v) "(Hx & [%vn [-> [%Hc Hε]]])".
    destruct Hc as [->|[-> | ->]].
    { wp_pures.
      wp_apply wp_init; first done.
      iIntros (?) "?".
      wp_pures.
      iModIntro; iExists true; iFrame.
      iSplitR; first done.
      iApply (ec_eq with "Hε").
      rewrite /Bii_h//=.
      rewrite Iverson_True; [rewrite Rmult_1_l|done].
      rewrite Iverson_False; [rewrite Rmult_0_l|done].
      rewrite Iverson_False; [rewrite Rmult_0_l|done].
      lra.
    }
    { wp_pures.
      wp_apply wp_init; first done.
      iIntros (r) "Hr".
      iApply (wp_lazy_real_presample_adv_comp _ _ r _ (Bii_h F x 1) (Bii_g F x)); auto.
      { intros ??. apply Bii_g_nn; auto. }
      { rewrite /Bii_h.
        rewrite Iverson_False; [rewrite Rmult_0_l Rplus_0_l|simpl; lra].
        rewrite Iverson_True; [rewrite Rmult_1_l|done].
        rewrite Iverson_False; [rewrite Rmult_0_l Rplus_0_r|simpl; lra].
        apply Bii_g_correct.
        done.
      }
      iSplitL "Hr"; [done|].
      iSplitL "Hε"; [done|].
      iIntros (rv) "(% & Hε & Hr)".
      wp_pures.
      wp_apply (wp_cmp with "[Hr Hx]"); first iFrame.
      iIntros (cv) "(Hx & Hr & %Hc)".
      destruct Hc as [[-> Hc'] | [-> Hc']].
      { wp_pures.
        iModIntro; iExists _; iSplitR; first done.
        iFrame.
        rewrite /Bii_g.
        iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        rewrite Iverson_True; [|done].
        rewrite Rmult_1_l.
        done.
      }
      { wp_pures.
        iModIntro; iExists _; iSplitR; first done.
        iFrame.
        iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        rewrite Iverson_True; [|lra].
        by rewrite Rmult_1_l.
      }
    }
    { wp_pures.
      wp_apply wp_init; first done.
      iIntros (?) "?".
      wp_pures.
      iModIntro; iExists false; iFrame.
      iSplitR; first done.
      iApply (ec_eq with "Hε").
      rewrite /Bii_h//=.
      rewrite Iverson_False; [rewrite Rmult_0_l|lra].
      rewrite Iverson_False; [rewrite Rmult_0_l|lra].
      rewrite Iverson_True; [rewrite Rmult_1_l|done].
      lra.
    }
  Qed.

  Theorem wp_S {E F M} (k : nat) xα x (Hnn : ∀ r, 0 <= F r <= M) (Hx : 0 <= x <= 1) :
    ∀ yα y N , ↯(S_CreditV F k x y N) ∗ lazy_real xα x ∗ lazy_real yα y ∗ ⌜0 <= x <= 1 ⌝ ∗ ⌜0 <= y <= 1⌝ -∗
    WP S #k xα yα #N @ E {{ vn, ∃ n : nat, ⌜vn = #n ⌝ ∗ ↯(F n) ∗ lazy_real xα x }}.
  Proof.
    iLöb as "IH".
    iIntros (yα y N) "(Hε & Hx & Hy & % & %)".
    rewrite {2}/S.
    wp_pures.
    wp_apply wp_init; first done.
    iIntros (zα) "Hz".
    iApply (wp_lazy_real_presample_adv_comp _ _ zα _ (S_CreditV F k x y N) (S_g F k x y N)); auto.
    { intros ??. apply S_g_nn; auto. apply Hnn. }
    { eapply S_g_expectation; done. }
    iSplitL "Hz"; [done|].
    iSplitL "Hε"; [done|].
    iIntros (z) "(% & Hε & Hz)".
    wp_pures.
    wp_apply (wp_cmp with "[Hy Hz]"); first iFrame.
    iIntros (c) "(Hy & Hz & %Hcmp)".
    destruct Hcmp as [[-> Hc'] | [-> Hc']].
    { wp_pures.
      iModIntro; iExists N; iFrame; iSplitR; first done.
      rewrite /S_g.
      iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_nn_1; auto ]. apply Hnn. }
      rewrite Iverson_True; [rewrite Rmult_1_l|done].
      done.
    }
    { wp_pures.
      rewrite /S_g.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_nn_1; auto ]. apply Hnn. }
      rewrite Iverson_True; [rewrite Rmult_1_l|lra].
      wp_bind (Bii _ _).
      iApply (pgl_wp_mono_frame (□ _ ∗ _  ∗ _)%I with "[Hx Hε ] [IH Hy Hz]"); last first.
      { iSplitR; first iExact "IH". iSplitL "Hy"; first iExact "Hy". iExact "Hz". }
      { iApply (@wp_Bii _ (S_hz F k x N z)); last iFrame; last done.
        iIntros (?). apply S_hz_nn; auto. apply Hnn. }
      iIntros (bv) "((#IH & Hy & Hz) & [%b [-> [Hε Hx]]])".
      destruct b.
      { wp_pures.
        iModIntro; iExists N; iFrame; iSplitR; first done.
        rewrite /S_hz.
        iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_CreditV_nn; auto ]. apply Hnn. }
        rewrite Iverson_True; [rewrite Rmult_1_l|intuition].
        done.
      }
      { do 2 wp_pure.
        rewrite -Nat2Z.inj_add.
        iApply "IH".
        iFrame.
        rewrite /S_hz.
        iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_CreditV_nn; auto ]. apply Hnn. }
        rewrite Iverson_True; [rewrite Rmult_1_l|intuition].
        iFrame.
        iPureIntro; auto.
      }
    }
  Qed.

  Theorem wp_S0 {E F M} (k : nat) xα x (Hnn : ∀ r, 0 <= F r <= M) :
    ↯(S_CreditV F k x x 0) ∗ lazy_real xα x ∗ ⌜ 0 <= x <= 1 ⌝ -∗
    WP S0 #k xα @ E {{ vn, ∃ n : nat, ⌜vn = #n ⌝ ∗ ↯(F n) ∗ lazy_real xα x }}.
  Proof.
    iIntros "(Hε & Hx & %)".
    rewrite /S0.
    wp_pures.
    wp_apply wp_init; first done.
    iIntros (zα) "Hz".
    iApply (wp_lazy_real_presample_adv_comp _ _ zα _ (S_CreditV F k x x 0) (S_g F k x x 0)); auto.
    { intros ??. apply S_g_nn; auto. apply Hnn. }
    { eapply S_g_expectation; done. }
    iSplitL "Hz"; [done|].
    iSplitL "Hε"; [done|].
    iIntros (z) "(% & Hε & Hz)".
    wp_pures.
    wp_apply (wp_cmp with "[Hx Hz]"); first iFrame.
    iIntros (c) "(Hx & Hz & %Hcmp)".
    destruct Hcmp as [[-> Hc'] | [-> Hc']].
    { wp_pures.
      iModIntro; iExists 0%nat; iFrame; iSplitR; first done.
      rewrite /S_g.
      iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_nn_1; auto ]. apply Hnn. }
      rewrite Iverson_True; [rewrite Rmult_1_l|done].
      done.
    }
    { wp_pures.
      rewrite /S_g.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_nn_1; auto ]. apply Hnn. }
      rewrite Iverson_True; [rewrite Rmult_1_l|lra].
      wp_bind (Bii _ _).
      iApply (pgl_wp_mono_frame (_ )%I with "[Hx Hε ] Hz"); last first.
      { iApply (@wp_Bii _ (S_hz F k x _ _)); last iFrame; last done.
        iIntros (?). apply S_hz_nn; auto. apply Hnn. }
      iIntros (bv) "(Hz & [%b [-> [Hε Hx]]])".
      destruct b.
      { wp_pures.
        iModIntro; iExists 0%nat; iFrame; iSplitR; first done.
        rewrite /S_hz.
        iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_CreditV_nn; auto ]. apply Hnn. }
        rewrite Iverson_True; [rewrite Rmult_1_l|intuition].
        done.
      }
      { wp_pure.
        iApply wp_S; auto.
        iFrame.
        rewrite /S_hz.
        iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
        { apply Rmult_le_pos; [apply Iverson_nonneg | apply S_CreditV_nn; auto ]. apply Hnn. }
        rewrite Iverson_True; [rewrite Rmult_1_l|intuition].
        iFrame. by iPureIntro.
      }
    }
  Qed.

  Theorem wp_B {E F M} (k : nat) xα x (Hnn : ∀ r, 0 <= F r <= M) :
    ↯(B_CreditV F k x) ∗ lazy_real xα x ∗ ⌜0 <= x <= 1 ⌝ -∗
    WP B #k xα @ E {{ vb, ∃ b : bool, ⌜vb = #b ⌝ ∗ ↯(F b) ∗ lazy_real xα x }}.
  Proof.
    iIntros "(Hε & Hx)".
    rewrite /B.
    wp_pures.
    wp_bind (S0 _ _).
    iApply (pgl_wp_mono with "[Hx Hε] "); last first.
    { iApply (wp_S0 (F:=B_g F) (M := F true + F false)).
      { intros ?. split; first (apply B_g_nn; apply Hnn).
        rewrite /B_g.
        apply Rplus_le_compat.
        { rewrite -{2}(Rmult_1_l (F true)).
          apply Rmult_le_compat; OK.
          { apply Iverson_nonneg. }
          { apply Hnn. }
          { apply Iverson_le_1. }
        }
        { rewrite -{2}(Rmult_1_l (F false)).
          apply Rmult_le_compat; OK.
          { apply Iverson_nonneg. }
          { apply Hnn. }
          { apply Iverson_le_1. }
        }
      }
      iFrame.
      iApply (ec_eq with "Hε").
      apply B_g_expectation.
    }
    iIntros (v) "[%n [-> [Hec Hx]]]".
    iFrame.
    wp_pures.
    iModIntro.
    case_bool_decide.
    { iExists true; iSplitR; first done.
      rewrite /B_g.
      iPoseProof (ec_split _ _ with "Hec") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | auto ]. apply Hnn. }
      iApply (ec_eq with "Hε").
      rewrite Iverson_True; [by rewrite Rmult_1_l|].
      inversion H as [H'].
      apply Z.rem_mod_eq_0 in H'; [|lia].
      by apply Zeven_bool_iff; rewrite Zeven_mod H' //.
    }
    { iExists false; iSplitR; first done.
      iPoseProof (ec_split _ _ with "Hec") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | auto ]. apply Hnn. }
      iApply (ec_eq with "Hε").
      rewrite Iverson_True; [by rewrite Rmult_1_l|].
      rewrite //=.
      intro Hk; apply H. f_equal.
      apply Zeven_bool_iff in Hk.
      rewrite Zeven_mod in Hk.
      apply Zeq_bool_eq in Hk.
      apply (Z.rem_mod_eq_0 n 2 ) in Hk; [by f_equal|lia].
    }
  Qed.

End program.
