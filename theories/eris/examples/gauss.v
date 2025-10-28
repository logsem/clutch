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
  Proof. Admitted.

  Lemma Norm1_nn : 0 < Norm1.
  Proof.
    rewrite /Norm1.
    apply (Rlt_le_trans _ (SeriesC (λ k : nat, if bool_decide (1%nat = k) then exp (- 1 ^ 2 / 2) else 0))).
    { rewrite SeriesC_singleton'.
      rewrite pow1.
      admit.
    }
    { (* SeriesC_lt. *) (* why not?  *)
      admit.
    }
    (* eapply (SeriesC_filter_leq). _ (fun n => n = 0%nat)).
      { intros n. apply Rexp_range. admit. }
      { apply Norm1_ex. } *)
  Admitted.

  Lemma G1_μ_nn {x}  : 0 <= G1_μ x.
  Proof.
    rewrite /G1_μ.
    apply Rle_mult_inv_pos; [|apply Norm1_nn].
    apply Rexp_range.
    apply Rcomplements.Rmult_le_0_r; last lra.
    have ? : 0 <= x^2.  { apply pow_le. apply pos_INR. }
    lra.
  Qed.

  Lemma Norm2_nn : 0 < Norm2.
  Proof.
    rewrite /Norm2.
  Admitted.

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

  Lemma G2_exRInt {F} (Hnn : ∀ k r, 0 <= F k r) {x'} : ex_RInt (λ x : R, G2_μ x' x * F x' x) 0 1.
  Proof. Admitted.

  Lemma G2_CreditV_nn {F} (Hnn : ∀ k r, 0 <= F k r) : 0 <= G2_CreditV F.
  Proof.
    rewrite /G2_CreditV.
    apply SeriesC_ge_0'; intros x'.
    apply RInt_ge_0; try lra.
    { apply G2_exRInt; auto. }
    intros x Hx.
    apply Rmult_le_pos; [|auto].
    apply G2_μ_nn; auto.
    lra.
  Qed.

  Lemma G1_h_nn {F k b} (Hnn : ∀ r, 0 <= F r) : 0 <= G1_h F k b.
  Proof.
    rewrite /G1_h.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg| auto ]).
    apply G1_CreditV_nn; auto.
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

  Lemma G1_f_expectation {F} : G1_CreditV F = Geo_CreditV (G1_f F) (exp (-1 / 2)) 0.
  Proof.
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
    2, 3: admit.
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
    { (* Foob, then funext, then SeriesC_scal_l etc. *) admit. }
    rewrite -SeriesC_plus.
    2, 3: admit.
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
    2, 3: admit.
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

    (* Conclude by geometric series formula *)
  Admitted.

  Lemma G2_s_nn {F k x b} (Hnn : ∀ a b , 0 <= F a b) : 0 <= G2_s F k x b.
  Proof.
    rewrite /G2_s.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg| auto ]).
    apply G2_CreditV_nn; auto.
  Qed.

  Lemma G2_g_nn {F k x} (Hnn : ∀ a b , 0 <= F a b) (Hx : 0 <= x <= 1) : 0 <= G2_g F k x.
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

  Lemma G2_g_exRInt {F k} : ex_RInt (G2_g F k) 0 1.
  Proof. Admitted.

  Lemma G2_f_nn {F k} (Hnn : ∀ a b , 0 <= F a b) : 0 <= G2_f F k.
  Proof.
    rewrite /G2_f.
    apply RInt_ge_0; try lra.
    { apply G2_g_exRInt; auto. }
    intros x Hx.
    apply G2_g_nn; auto. lra.
  Qed.

  Lemma G2_f_expectation {F} : G2_CreditV F = G1_CreditV (G2_f F).
  Proof.
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
       2, 3: admit.
       done.
    }
    rewrite SeriesC_plus.
    2, 3: admit.
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
      f_equal; apply functional_extensionality; intros ?.
      lra.
    }
    (* Go get 'em Guido *)
    replace (SeriesC (λ x : nat, RInt (λ x0 : R, SeriesC (λ k : nat, RInt (λ x1 : R, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1) 0 1)) 0 1))
       with (SeriesC (λ k : nat, RInt (λ x1 : R, RInt (λ x0 : R, SeriesC (λ x : nat, G1_μ x * (1 - exp (- x0 * (2 * x + x0) / 2)) * G2_μ k x1 * F k x1)) 0 1) 0 1));
      last first.
    { admit. }
    (* Recombine series and cancel with LHS *)
    rewrite -SeriesC_plus.
    2, 3: admit.
    rewrite /G2_CreditV.
    f_equal; apply functional_extensionality; intros k.
    rewrite RInt_Rmult.
    rewrite RInt_add.
    2, 3: admit.
    apply RInt_ext.
    rewrite Rmin_left; [|lra].
    rewrite Rmax_right; [|lra].
    intros x Hx.
    (* Pull out the constant terms from the series/intergral *)
    replace (RInt (λ x0 : R, SeriesC (λ x1 : nat, G1_μ x1 * (1 - exp (- x0 * (2 * x1 + x0) / 2)) * G2_μ k x * F k x)) 0 1)
       with (G2_μ k x * F k x * RInt (λ x0 : R, SeriesC (λ x1 : nat, G1_μ x1 * (1 - exp (- x0 * (2 * x1 + x0) / 2)))) 0 1);
      last first.
    { rewrite RInt_Rmult.
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
    { rewrite RInt_Rmult.
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
    replace (λ x0 : R, SeriesC (λ x1 : nat, exp (- x1 ^ 2 / 2) - exp (- (x0 + x1) ^ 2 / 2)))
      with (λ x0 : R, SeriesC (λ x1 : nat, exp (- x1 ^ 2 / 2)) + -1 * SeriesC (fun x1 : nat => exp (- (x0 + x1) ^ 2 / 2)));
      last first.
    { f_equal; apply functional_extensionality; intros y.
      rewrite SeriesC_minus.
      2, 3: admit.
      lra.
    }
    rewrite -RInt_add.
    2, 3: admit.
    rewrite -RInt_Rmult.

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
  Admitted.

  Lemma G2_g_RInt {F k} : is_RInt (G2_g F k) 0 1 (G2_f F k).
  Proof. Admitted.

  (*
  (* TODO: Solve and move me *)
  Lemma Rexp_half_bound : 0 <= exp (-1 / 2) <= 1.
  Proof. Admitted.

  Local Lemma Rexp_ineq {z : R} {k : nat} : 0 <= exp (- z * (2 * k + z) / (2 * k + 2)) <= 1.
  Proof. Admitted.
   *)

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

  Definition G1 : val :=
    rec: "trial" "_" :=
      let: "k" := GeoTrial BNEHalf #0 in
      if: IterTrial BNEHalf ("k" * ("k" - #1)) then "k" else "trial" #().

  Definition G2 : val :=
    rec: "trial" "_" :=
      let: "k" := G1 #() in
      let: "x" := init #() in
      if: IterTrial (λ: "_", B "k" "x") ("k" + #1) then ("x", "k") else "trial" #().

  Theorem wp_G1 {E F} (Hnn : ∀ r, 0 <= F r) :
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
      { by intros ?; apply G1_f_nn, Hnn. }
      { by rewrite G1_f_expectation. }
      Unshelve.
      { apply Rexp_range; lra. }
      { iIntros (E' F' HF') "Hε".
        iApply wp_BNEHalf; [done|].
        iApply (ec_eq with "Hε").
        rewrite /BNEHalf_CreditV/BNEHalf_μ.
        rewrite Iverson_True; [|intuition].
        rewrite Iverson_False; [|intuition].
        rewrite Iverson_False; [|intuition].
        rewrite Iverson_True; [|intuition].
        lra.
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
        iApply wp_BNEHalf; [done|].
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

  Theorem wp_G2 {E F} (Hnn : ∀ x k , 0 <= F x k ) :
    ↯(G2_CreditV F) -∗
    WP G2 #() @ E {{ vp, ∃ k : nat, ∃ r : R, ∃ l : val, lazy_real l r  ∗ ⌜vp = PairV l #k ⌝ ∗ ↯(F k r) }}.
  Proof.
    rewrite /G2.
    iLöb as "IH".
    iIntros "Hε".
    wp_pures.
    wp_bind (G1 _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hε] IH"); last first.
    { iApply (wp_G1 (F := G2_f F)).
      { intros ?; apply G2_f_nn; auto. }
      iApply (ec_eq with "Hε").
      apply G2_f_expectation.
    }
    iIntros (v) "(#IH & [%k [-> Hε]])".
    wp_pures.
    wp_apply wp_init; first done.
    iIntros (x) "Hx".
    iApply (wp_lazy_real_presample_adv_comp _ _ x _ (G2_f F k) (G2_g F k)); auto.
    { intros ??. apply G2_g_nn; auto. }
    { apply G2_g_RInt. }
    iFrame.
    iIntros (z) "(% & Hε & Hx)".
    wp_pures.
    wp_bind (IterTrial _ _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hε Hx] IH"); last first.
    { rewrite /G2_g.
      replace (Z.add (Z.of_nat k) 1) with (Z.of_nat (k + 1)%nat) by lia.
      iApply (@wp_Iter _ _ _ (exp (- z * (2 * k + z) / (2*k+2))) _ (lazy_real x z) _ _ (G2_s F k z)).
      { intros ?. apply G2_s_nn. auto. }
      { iFrame.
        iApply (ec_eq with "Hε").
        rewrite /Iter_CreditV.
        rewrite Rexp_eq.
        f_equal; f_equal.
      }
      Unshelve.
      { apply Rexp_range.
        apply Rcomplements.Rmult_le_0_r.
        { apply Rcomplements.Rmult_le_0_r; [lra|].
          apply Rplus_le_le_0_compat.
          { apply Rmult_le_pos; [lra|]. apply pos_INR. }
          { lra. }
        }
        rewrite -(Rmult_1_l (/ _)).
        apply Rle_mult_inv_pos; [lra|].
        rewrite -(Rplus_0_l 0).
        apply Rplus_le_lt_compat; [|lra].
        apply Rmult_le_pos; [lra|].
        apply pos_INR.
      }
      { iIntros (E' F' Hf') "(Hε & HI)".
        wp_pure.
        iApply wp_B; first done.
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
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply G2_CreditV_nn, Hnn ]. }
      iApply (ec_eq with "Hε").
      rewrite Iverson_True; [lra|done].
    }
    { wp_pure.
      iApply "IH".
      rewrite /G2_s.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply G2_CreditV_nn, Hnn ]. }
      iApply (ec_eq with "Hε").
      rewrite Iverson_True; [lra|done].
    }
  Qed.

End program.
