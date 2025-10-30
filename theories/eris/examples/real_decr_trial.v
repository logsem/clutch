From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real indicators.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.

  (* The PMF for lazyDecrR starting with N=0 *)
  Definition RealDecrTrial_μ0 (x : R) (n : nat) : R :=
    ((x ^ n) / fact n) - ((x ^ (n + 1)) / fact (n + 1)).

  (* The PMF for the trial starting at 0, over the integers *)
  Definition RealDecrTrial_μZ (x : R) (z : Z) : R :=
    Iverson (Z.le 0%Z) z * RealDecrTrial_μ0 x (Z.to_nat z).

  (* The PMF for lazyDecrR starting with N=i *)
  Definition RealDecrTrial_μ (x : R) (i n : nat) : R :=
    Iverson (uncurry le) (i, n) * RealDecrTrial_μ0 x (n - i).

  Theorem RealDecrTrial_μ_not_supp {x i n} (H : lt n i) : RealDecrTrial_μ x i n = 0.
  Proof. rewrite /RealDecrTrial_μ Iverson_False //=; [lra|lia]. Qed.

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

  Definition RealDecrTrial_CreditV0 (F : Z → R) (x : R) : R :=
    SeriesC (fun z : Z => RealDecrTrial_μZ x z * F z).

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

  Lemma RealDecrTrial_CreditV_ex_RInt {F N M} 
    (Hbound : forall n, 0 <= F n <= M) : ex_RInt (RealDecrTrial_CreditV F (N + 1)) 0 1.
  Proof.
    rewrite /RealDecrTrial_CreditV.
    (*
    apply (DominatedCvgTheorem_ex (fun _ => 1 * M)); [|apply ex_RInt_const].
    rewrite Rmin_left; [|lra].
    rewrite Rmax_right; [|lra].
    intros n x H.
    split.
    { apply Rmult_le_pos; [|apply Hbound]. apply RealDecrTrial_μnn; lra. }
    apply Rmult_le_compat.
    { apply RealDecrTrial_μnn; lra. }
    { apply Hbound. }
    { apply RealDecrTrial_μ_le_1; lra. }
    { apply Hbound. }
    *)
  Admitted.

  (* Telescoping series *)
  Lemma RealDecrTrial_μ0_ex_seriesC {x} (Hx : 0 <= x <= 1) : ex_seriesC (λ n : nat, RealDecrTrial_μ0 x n).
  Proof. Admitted.

  Lemma RealDecrTrial_μ0_ex_seriesC' {x} (Hx : 0 <= x <= 1) : ex_seriesC (λ n : nat, RealDecrTrial_μ0 x (n + 1)).
  Proof. Admitted.



  Lemma g_ex_RInt {F N rx M} (Hbound : forall n, 0 <= F n <= M) : ex_RInt (g F N rx) 0 1.
  Proof.
    rewrite /g.
    apply ex_RInt_add.
    { apply ex_RInt_mult; [apply ex_RInt_Iverson_le_uncurry|].
      eapply RealDecrTrial_CreditV_ex_RInt.
      intro n.
      apply Hbound.
    }
    { apply ex_RInt_mult; [apply ex_RInt_Iverson_ge_uncurry|].
      apply ex_RInt_const.
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

  Theorem g_expectation {F N rx M} (Hrx : 0 <= rx <= 1) (Hex : ex_seriesC F)
    (Hbound : forall n, 0 <= F n <= M) : is_RInt (g F N rx) 0 1 (RealDecrTrial_CreditV F N rx).
  Proof.
    suffices H : RInt (g F N rx) 0 1 = RealDecrTrial_CreditV F N rx.
    { rewrite -H. eapply (RInt_correct (V := R_CompleteNormedModule)), g_ex_RInt.
      { apply Hbound. }
    }
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
    { (* Deploy the Foob *) admit. }
    rewrite (@RInt_Iverson_ge rx (fun x => F N) Hrx).
    rewrite RInt_const/scal//=/mult//=.
    replace ((1 - rx) * F N) with (SeriesC (fun n => Iverson (fun y => y = N) n * ((1 - rx) * F n))); last first.
    { rewrite (SeriesC_Iverson_singleton (F := fun z => (1 - rx) * F z) N); [lra|intuition]. }
    rewrite -SeriesC_plus.
    3: {
      apply (ex_seriesC_le _ F); [|apply Hex].
      intro n.
      split.
      { apply Rmult_le_pos; [apply Iverson_nonneg|].
        apply Rmult_le_pos; [lra|].
        apply Hbound.
      }
      { rewrite -Rmult_assoc.
        rewrite -{2}(Rmult_1_l (F n)).
        apply Rmult_le_compat_r; [apply Hbound|].
        rewrite -(Rmult_1_l 1).
        apply Rmult_le_compat.
        { apply Iverson_nonneg. }
        { lra. }
        { apply Iverson_le_1. }
        { lra. }
      }
    }
    2: {
      apply (ex_seriesC_le _ F); [|apply Hex].
      intro n.
      split.
      { apply RInt_ge_0; [lra | |].
        { apply ex_RInt_mult; [|apply ex_RInt_const].
          apply ex_RInt_mult; [apply ex_RInt_Iverson_le_uncurry|].
          apply RealDecrTrial_μ_ex_RInt.
        }
        { intros x Hx.
          apply Rmult_le_pos; [|apply Hbound].
          apply Rmult_le_pos; [apply Iverson_nonneg|].
          rewrite /RealDecrTrial_μ.
          apply Rmult_le_pos; [apply Iverson_nonneg|].
          apply RealDecrTrial_μ0nn.
          lra.
        }
      }
      { rewrite -RInt_Rmult'.
        rewrite -{2}(Rmult_1_l (F n)).
        apply Rmult_le_compat_r; [apply Hbound|].
        etransitivity; first eapply Rle_abs.
        etransitivity; first eapply (abs_RInt_le_const _ _ _ (1 * 1)).
        { lra. }
        { apply ex_RInt_mult.
          { apply ex_RInt_Iverson_le_uncurry. }
          { apply RealDecrTrial_μ_ex_RInt. }
        }
        { intros t Ht.
          rewrite Rabs_mult.
          apply Rmult_le_compat.
          { apply Rabs_pos. }
          { apply Rabs_pos. }
          { rewrite Rabs_right; [|apply Rle_ge, Iverson_nonneg].
            apply Iverson_le_1. }
          { rewrite Rabs_right; [|apply Rle_ge].
            { apply RealDecrTrial_μ_le_1; lra. }
            { apply RealDecrTrial_μnn; lra. }
          }
        }
        { lra. }
      }
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

  Lemma wp_lazyDecrR_gen {M} (F : nat → R) (Hnn : ∀ n, 0 <= F n <= M) E (Hex : ex_seriesC F) :
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
