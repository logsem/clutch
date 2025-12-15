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

End pmf.


Section credits.
  Import Hierarchy.

  Definition NegExp_CreditV (F : nat → R → R) (L : nat) : R :=
    SeriesC (fun (k : nat) => RInt (fun x => NegExp_ρ L k x * F k x) 0 1).

  Lemma NegExp_CreditV_nn {F L} : 0 <= NegExp_CreditV F L.
  Proof. Admitted.

  Local Definition hx (F : nat → R → R) (x : R) (L : nat) : nat → R :=
    fun z => Iverson Zeven z * F L x + Iverson (not ∘ Zeven) z * NegExp_CreditV F (L + 1).

  Local Definition g (F : nat → R -> R) (L : nat) : R -> R := fun x =>
    RealDecrTrial_CreditV (hx F x L) 0 x.

  Local Lemma g_nonneg {F : nat → R -> R} {L : nat} : ∀ r : R, 0 <= r <= 1 → 0 <= g F L r.
  Proof. Admitted.


  Local Lemma g_ex_RInt {F : nat → R → R} {L} : ex_RInt (g F L) 0 1.
  Proof. Admitted.

  Local Definition B (F : nat → R → R) (L : nat) (x : R) (n : nat) (k : nat) (x0 : R) :=
      RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_ρ (L + 1) k x0 * F k x0.

  Local Lemma QuadExchange1 {F L} :
    (RInt (λ x : R, SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1))) 0 1) =
    (SeriesC (λ n : nat, RInt (λ x : R, SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1)) 0 1)).
  Proof. Admitted.

  Local Lemma QuadExchange2 {F L} :
    (SeriesC (λ n : nat, RInt (λ x : R, SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1)) 0 1)) =
    (SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x : R, RInt (λ x0 : R, B F L x n k x0) 0 1) 0 1))).
  Proof. Admitted.

  Local Lemma QuadExchange3 {F L} :
    (SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x : R, RInt (λ x0 : R, B F L x n k x0) 0 1) 0 1))) =
    (SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1))).
  Proof. Admitted.

  Local Lemma QuadExchange4 {F L} :
    (SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1))) =
    (SeriesC (λ k : nat, SeriesC (λ n : nat, RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1))).
  Proof. Admitted.

  Local Lemma QuadExchange5 {F L} :
    (SeriesC (λ k : nat, SeriesC (λ n : nat, RInt (λ x0 : R, RInt (λ x : R, B F L x n k x0) 0 1) 0 1))) =
    (SeriesC (λ k : nat, RInt (λ x0 : R, SeriesC (λ n : nat, RInt (λ x : R, B F L x n k x0) 0 1)) 0 1)).
  Proof. Admitted.

  Local Lemma g_expectation {F : nat → R → R} {L} : is_RInt (g F L) 0 1 (NegExp_CreditV F L).
  Proof.
    (* have Hex : ∀ (a b : R), ex_RInt F a b.
    { intros ??. apply PCts_RInt. by apply IPCts_PCts. } *)
    suffices H : RInt (g F L) 0 1 = NegExp_CreditV F L.
    { rewrite -H. apply (RInt_correct (V := R_CompleteNormedModule)). apply (g_ex_RInt); OK. }

    (* Unfold everything that involves F *)
    rewrite /g.
    rewrite /hx.
    rewrite /RealDecrTrial_CreditV.
    rewrite /NegExp_CreditV.

    (* Step 1: Split the series *)
    replace
      (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * (Iverson Zeven n * F L x + Iverson (not ∘ Zeven) n * SeriesC (λ k : nat, RInt (λ x0 : R, NegExp_ρ (L + 1) k x0 * F k x0) 0 1))))
        with
      (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson Zeven n * F L x) +
                SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_ρ (L + 1) k x0 * F k x0) 0 1))); last first.
    { funexti.
      rewrite -SeriesC_plus.
      2: { admit. }
      2: { admit. }
      apply SeriesC_ext.
      intros n.
      rewrite Rmult_plus_distr_l.
      f_equal; OK.
      rewrite -SeriesC_scal_l.
      rewrite -SeriesC_scal_l.
      apply SeriesC_ext; intros ?.
      rewrite RInt_Rmult.
      2: { admit. }
      rewrite RInt_Rmult.
      2: { admit. }
      apply RInt_ext; intros ??. OK.
    }
    rewrite RInt_plus.
    2: { admit. }
    2: { admit. }
    rewrite /plus//=.

    (* Step 2: Quadruple limit exchange *)
    replace (RInt (λ x : R, SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_ρ (L + 1) k x0 * F k x0) 0 1))) 0 1)
       with (RInt (λ x : R, SeriesC (λ n : nat, SeriesC (λ k : nat, RInt (λ x0 : R, B F L x n k x0) 0 1))) 0 1); last first.
    { repeat f_equal. }

    rewrite QuadExchange1.
    rewrite QuadExchange2.
    rewrite QuadExchange3.
    rewrite QuadExchange4.
    rewrite QuadExchange5.

    (* Step 3: Exchange on the RHS *)
    replace (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson Zeven n * F L x)) 0 1)
       with (SeriesC (λ n : nat, RInt (λ x : R, RealDecrTrial_μ x 0 n * Iverson Zeven n * F L x) 0 1)); last first.
    { admit. }

    (* Step 4: Combine the outer two series *)
    rewrite -SeriesC_plus.
    2: { admit. }
    2: { admit. }

    (* Step 5: Combine the outer two integrals *)
    replace (λ x : nat,
       RInt (λ x0 : R, RealDecrTrial_μ x0 0 x * Iverson Zeven x * F L x0) 0 1 +
       RInt (λ x0 : R, @SeriesC nat numbers.Nat.eq_dec nat_countable (λ n : nat, RInt (λ x1 : R, B F L x1 n x x0) 0 1)) 0 1) with
      (λ x : nat,
       RInt (λ x0 : R, RealDecrTrial_μ x0 0 x * Iverson Zeven x * F L x0 + SeriesC (λ n : nat, RInt (λ x1 : R, B F L x1 n x x0) 0 1)) 0 1); last first.
    { funexti.
      rewrite (RInt_plus (V := R_CompleteNormedModule)); OK.
      { admit. }
      { admit. }
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
      2: { admit. }
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
        2: { admit. }
        rewrite //=.
        rewrite Rminus_def.
        f_equal.
        rewrite Rdiv_def.
        rewrite pow1.
        lra.
      }
      rewrite SeriesC_nat_shift_rev.
      2: { admit. }
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
      2: admit.
      2: admit.
      apply SeriesC_ext.
      intros ?.
      rewrite RInt_plus.
      2: admit.
      2: admit.
      done.
    }

    (* Split series on RHS *)
    replace (SeriesC (λ k : nat, RInt (λ x : R, Iverson (le L) k * exp (- (x + (k - L)%nat)) * F k x) 0 1))
       with (SeriesC (λ k : nat, RInt (λ x : R, Iverson (le (L + 1)) k * exp (- (x + (k - L)%nat)) * F k x) 0 1) +
             SeriesC (λ k : nat, RInt (λ x : R, Iverson (eq L) k * exp (- (x + (k - L)%nat)) * F k x) 0 1)).
    2: {
      rewrite -SeriesC_plus.
      2: admit.
      2: admit.
      apply SeriesC_ext.
      intros ?.
      replace (RInt (λ x : R, Iverson (le (L + 1)) n * exp (- (x + (n - L)%nat)) * F n x) 0 1 + RInt (λ x : R, Iverson (eq L) n * exp (- (x + (n - L)%nat)) * F n x) 0 1)
        with  (plus (RInt (λ x : R, Iverson (le (L + 1)) n * exp (- (x + (n - L)%nat)) * F n x) 0 1) (RInt (λ x : R, Iverson (eq L) n * exp (- (x + (n - L)%nat)) * F n x) 0 1)).
      2: { by rewrite //=. }
      rewrite -(RInt_plus (V := R_CompleteNormedModule)).
      2: admit.
      2: admit.
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
    replace (SeriesC (λ x : nat, RInt (λ x0 : R, RealDecrTrial_μ0 x0 x * Iverson Zeven x * F L x0) 0 1))
       with (RInt (λ x0 : R, SeriesC (λ x : nat, RealDecrTrial_μ0 x0 x * Iverson Zeven x * F L x0)) 0 1).
    2: { admit. }
    replace (SeriesC (λ k : nat, RInt (λ x : R, Iverson (eq L) k * exp (- (x + (k - L)%nat)) * F k x) 0 1))
       with (RInt (λ x : R, SeriesC (λ k : nat, Iverson (eq L) k * (exp (- (x + (k - L)%nat)) * F k x))) 0 1).
    2: { admit. }
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
  Admitted.

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

  Lemma wp_NegExp_gen E (F : nat → R → R) {M} (Hnn : ∀ a b, 0 <= F a b <= M) (*  E (HPcts : IPCts F) *) :
    ⊢ ∀ L, ↯ (NegExp_CreditV F L) -∗
           WP NegExp #L @ E
      {{ p, ∃ (vz : Z) (vr : R) (ℓ : val), ⌜p = PairV #vz ℓ⌝ ∗ lazy_real ℓ vr ∗ ↯(F (Z.to_nat vz) vr)}}.
  Proof.
    (* have Hex : ∀ a b, ex_RInt F a b.
    { intros ??. apply PCts_RInt. by apply IPCts_PCts. } *)
    iLöb as "IH".
    iIntros (L) "Hε".
    rewrite {2}/NegExp.
    wp_pure.
    wp_apply wp_init; first done.
    iIntros (x) "Hx".
    iApply (wp_lazy_real_presample_adv_comp _ _ x _ (NegExp_CreditV F L) (g F L)); auto.
    { intros ??. apply g_nonneg; eauto. }
    { eapply g_expectation. } (* eapply g_expectation; first apply Hnn.  OK. *)

    iFrame.
    iIntros (xr) "(%Hrange & Hε & Hx)".
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
          { apply Hnn.  }
          { eapply NegExp_CreditV_nn. }
        }
        { apply Rplus_le_compat.
          { rewrite -{2}(Rmult_1_l (F L xr)).
            apply Rmult_le_compat_r; [|apply Iverson_le_1].
            apply Hnn.
          }
          { rewrite -{2}(Rmult_1_l (NegExp_CreditV F (L + 1))).
            apply Rmult_le_compat_r; [|apply Iverson_le_1].
            apply NegExp_CreditV_nn.
          }
        }
      }
    }
    iIntros (v) "(#IH & [%l (%Hv & Hε & Hx)])"; rewrite Hv.
    wp_pures.
    case_bool_decide.
    { have Heven : Zeven l.
      { inversion H as [H'].
        apply Z.rem_mod_eq_0 in H'; [|lia].
        by apply Zeven_bool_iff; rewrite Zeven_mod H' //. }
      wp_pures.
      iModIntro.
      iExists L, xr, x.
      iFrame.
      iSplitR; first done.
      unfold hx.
      iPoseProof (ec_split _ _ with "Hε") as "(Hε & _)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ].  }
      { apply Rmult_le_pos; [apply Iverson_nonneg |]. apply NegExp_CreditV_nn. }
      rewrite Iverson_True; last done.
      by rewrite Rmult_1_l Nat2Z.id.
    }
    { do 2 wp_pure.
      rewrite {1}/NegExp.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | eapply NegExp_CreditV_nn; OK ]. }
      rewrite Iverson_True; last first.
      { intro Hk; apply H. f_equal.
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

End program.






(*

  Lemma NegExp_ρ0_nn {k x} : 0 <= NegExp_ρ0 k x.
  Proof.
    rewrite /NegExp_ρ0.
    apply Rmult_le_pos; first apply Iverson_nonneg.
    apply Rexp_nn.
  Qed.

  Lemma NegExp_ρ_nn {x L} : 0 <= NegExp_ρ x L.
  Proof.
    rewrite /NegExp_ρ.
    apply Rmult_le_pos; first apply Iverson_nonneg.
    apply NegExp_ρ0_nn.
  Qed.









  Theorem NegExp_ρ0_ex_RInt {F : R → R} {a b} (Hex : ∀ b : R, ex_RInt F a b) :
    ex_RInt NegExp_ρ0 a b.
  Proof.
    rewrite /NegExp_ρ0.
    apply ex_RInt_mult.
    { apply ex_RInt_Iverson_le. }
    apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
    intros ??.
    eapply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
    auto_derive. OK.
  Qed.

  Theorem NegExp_ρ_ex_RInt {L a b} :
    ex_RInt (NegExp_ρ L) a b.
  Proof.
    rewrite /NegExp_ρ0.
    apply ex_RInt_mult.
    { apply ex_RInt_const. }
    rewrite /NegExp_ρ0.
    apply ex_RInt_mult.
    { replace (λ y : R, Iverson (Rle 0) (y - L))
         with (λ y : R, scal 1 (Iverson (Rle 0) (1 * y + - L))); last first.
      { funexti. rewrite /scal//=/mult//= Rmult_1_l. f_equal; OK. }
      apply (ex_RInt_comp_lin (Iverson (Rle 0)) 1 (-L) a b).
      apply ex_RInt_Iverson_le. }
    apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
    intros ??.
    eapply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
    auto_derive. OK.
  Qed.

  Lemma NegExp_μ_IPcts {L} : IPCts (NegExp_ρ L).
  Proof.
    rewrite /NegExp_ρ.
    apply IPCts_mult.
    { apply IPCts_cts. intros ?. apply Continuity.continuous_const. }
    rewrite /NegExp_ρ0.
    apply IPCts_mult.
    2: {
      apply IPCts_cts.
      intros ?.
      eapply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
      auto_derive. OK.
    }
    (* Decompose this indicator function into
                 ______
            ____/            (step function, continuous, as the right tails)

        +       \            (correction for the diagonal part)


        Then the diagonal step just has to be proven continuous
    *)

    (*
    exists (fun _ => 1).
    exists (List.cons ((fun _ => -1), 0, INR L) (List.cons ((fun _ => 1), INR L, INR L) List.nil)).
    split; [|split].
    { intros.
      rewrite /fsum//=.
      rewrite {1}/Iverson//=.
      case_decide.
      { have HH : L <= x by OK.
        rewrite {2}/Iverson//=.
        case_decide.
        { rewrite Iverson_True; OK.
          rewrite /Icc in H0.
          rewrite Rmin_left in H0; OK.
          rewrite Rmax_right in H0; OK.
          rewrite /Icc//=; OK.
          rewrite Rmin_left.
          2: { apply pos_INR. }
          rewrite Rmax_right.
          2: { apply pos_INR. }
          split; OK.
          etrans; [|eapply HH].
          apply pos_INR.
        }
        { rewrite Iverson_False; OK.
          revert H0.
          rewrite /Icc.
          rewrite Rmin_left; OK.
          rewrite Rmax_right; OK.
          rewrite Rmin_left.
          2: { apply pos_INR. }
          rewrite Rmax_right.
          2: { apply pos_INR. }
          intros H1 H2; OK.
        }
      }
      { have HH : x < L by OK.
        rewrite Iverson_True; OK.
        2: {
          rewrite /Icc.
          rewrite Rmin_left.
          2: { apply pos_INR. }
          rewrite Rmax_right.
          2: { apply pos_INR. }
          split.

    *)
  Admitted.

  Lemma NegExp_μ_ex_RInt_gen {a N} : ex_RInt_gen (NegExp_ρ N) (at_point a) (Rbar_locally Rbar.p_infty).
  Proof.
    rewrite /NegExp_ρ.
    (* Compare to a version without the indicator *)
  Admitted.

  Lemma NegExp_CreditV_nn {F : R -> R} {M} (Hnn : ∀ r, 0 <= F r <= M) {L : nat} (H : IPCts F) :
    0 <= NegExp_CreditV F (L + 1).
  Proof.
    rewrite /NegExp_CreditV.
    apply RInt_gen_pos_strong.
    { intros ?. apply Rmult_le_pos; first apply Hnn. apply NegExp_ρ_nn. }
    { intros b. apply ex_RInt_mult; [ | apply NegExp_ρ_ex_RInt]. apply PCts_RInt.
      by apply IPCts_PCts.
    }
    { intros b Hb.
      apply RInt_ge_0; try done.
      { apply ex_RInt_mult; [ | apply NegExp_ρ_ex_RInt].
        apply PCts_RInt.
        by apply IPCts_PCts. }
      { intros ??.  apply Rmult_le_pos; first apply Hnn. apply NegExp_ρ_nn. }
    }
    eapply NegExp_prod_bounded_left_IPCts; try done.
    { apply NegExp_μ_IPcts. }
    { intros ?. apply NegExp_ρ_nn. }
    { apply NegExp_μ_ex_RInt_gen. }
  Qed.


  Lemma hx_nonneg {F M xr L} (Hnn : ∀ r, 0 <= F r <= M) (Hb : IPCts F) : ∀ n : nat, 0 <= hx F xr L n.
  Proof.
    rewrite /hx.
    intros ?.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg|]).
    { apply Hnn. }
    { eapply NegExp_CreditV_nn; auto. }
  Qed.

  Lemma g_nonneg {F M L r} (Hnn : ∀ r, 0 <= F r <= M) (Hr : 0 <= r <= 1) (Hb : IPCts F) : 0 <= g F L r.
  Proof.
    rewrite /g.
    apply CreditV_nonneg; auto.
    intros ?.
    eapply hx_nonneg; auto.
  Qed.

  Local Lemma g_ex_RInt {F L M} (Hbound : ∀ x, 0 <= F x <= M) (Hb : IPCts F) : ex_RInt (g F L) 0 1.
  Proof.
    rewrite -ex_RInt_dom /ex_RInt /g /RealDecrTrial_CreditV.
    replace (λ x : R, Iverson (Ioo 0 1) x * SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * hx F x L n))
       with (λ x : R, Series.Series (λ n : nat, Iverson (Ioo 0 1) x * (RealDecrTrial_μ x 0 n * hx F x L n))); last first.
    { apply functional_extensionality; intros ?.
      rewrite -SeriesC_scal_l SeriesC_Series_nat. done. }
    pose s : nat → R → R_CompleteNormedModule :=
      fun M x => sum_n (λ n : nat, Iverson (Ioo 0 1) x * (RealDecrTrial_μ x 0 n * hx F x L n)) M.
    pose h : nat → R_CompleteNormedModule :=
      fun x => (RInt (λ x0 : R, sum_n (λ n : nat, Iverson (Ioo 0 1) x0 * (RealDecrTrial_μ x0 0 n * hx F x0 L n)) x) 0 1).
    have HSLim : filterlim s eventually
      (locally (λ x : R, Series.Series (λ n : nat, Iverson (Ioo 0 1) x * (RealDecrTrial_μ x 0 n * hx F x L n)))).
    { rewrite /s.
      apply (UniformConverge_Series (fun n => (M + NegExp_CreditV F (L + 1)) * / (fact (n - 0)%nat))).
      { intros ??.
        rewrite /Iverson//=. case_decide; OK.
        rewrite Rmult_1_l.
        rewrite /Ioo//= in H.
        rewrite Rmin_left in H; OK.
        rewrite Rmax_right in H; OK.
        apply Rmult_le_pos.
        { apply RealDecrTrial_μnn; OK. }
        { eapply hx_nonneg; OK. }
      }
      { replace (λ n : nat, (M + NegExp_CreditV F (L + 1)) * / fact (n - 0)) with (λ n : nat, / fact n * (M + NegExp_CreditV F (L + 1))); last first.
        { funexti. rewrite Rmult_comm. repeat f_equal. OK. }
        apply Series.ex_series_scal_r.
        apply ex_exp_series.
      }
      intros x n.
      rewrite Rabs_right; last first.
      { apply Rle_ge. rewrite /Iverson; case_decide.
        { rewrite Rmult_1_l. apply Rmult_le_pos; [apply RealDecrTrial_μnn|].
          { rewrite /Ioo in H. rewrite Rmin_left in H; OK. rewrite Rmax_right in H; OK. }
          rewrite /hx. apply Rplus_le_le_0_compat; apply Rmult_le_pos;
            [apply Iverson_nonneg | apply Hbound | apply Iverson_nonneg | ].
          eapply NegExp_CreditV_nn; OK. }
        OK. }
      rewrite /Iverson. case_decide; last first.
      { rewrite Rmult_0_l.
        apply Rle_mult_inv_pos; last apply INR_fact_lt_0.
        have ? := Hbound 0.
        apply Rplus_le_le_0_compat; OK.
        eapply NegExp_CreditV_nn; OK.
      }
      rewrite /Ioo in H. rewrite Rmin_left in H; OK. rewrite Rmax_right in H; OK.
      rewrite Rmult_1_l Rmult_comm.
      have Hhx : hx F x L n <= M + NegExp_CreditV F (L + 1).
      { rewrite /hx.
        apply Rplus_le_compat.
        { rewrite -(Rmult_1_l M).
          apply Rmult_le_compat; OK.
          { apply Iverson_nonneg. }
          { apply Hbound. }
          { apply Iverson_le_1. }
          { apply Hbound. }
        }
        { rewrite -{2}(Rmult_1_l (NegExp_CreditV F (L + 1))).
          apply Rmult_le_compat; OK.
          { apply Iverson_nonneg. }
          { eapply NegExp_CreditV_nn; done. }
          { rewrite /Iverson//=. case_decide; OK. }
        }
      }
      apply Rmult_le_compat.
      { eapply hx_nonneg; OK. }
      { apply RealDecrTrial_μnn. OK. }
      { OK. }
      rewrite /RealDecrTrial_μ /Iverson. case_decide; last first.
      { rewrite Rmult_0_l. left. apply Rinv_0_lt_compat. apply INR_fact_lt_0. }
      rewrite Rmult_1_l /RealDecrTrial_μ0. repeat rewrite Rdiv_def.
      replace (n - 0 + 1)%nat with (S (n - 0)) by OK.
      rewrite fact_simpl mult_INR Rinv_mult -Rmult_assoc -Rmult_minus_distr_r.
      rewrite -{2}(Rmult_1_l (/ fact (n - 0))).
      apply Rmult_le_compat.
      { apply Rle_0_le_minus. rewrite -(Rmult_1_l (x ^ (n - 0))) Rmult_comm.
        apply Rmult_le_compat; [| apply pow_le; OK | | ].
        { rewrite -(Rmult_1_l (/ _)). apply Rle_mult_inv_pos; OK. apply pos_INR_S. }
        { rewrite -Rinv_1. apply Rinv_le_contravar; OK. rewrite -INR_1. apply le_INR. OK. }
        rewrite -(Rmult_1_l (x ^ (n - 0))) -tech_pow_Rmult.
        apply Rmult_le_compat_r; OK. apply pow_le; OK. }
      { rewrite -(Rmult_1_l (/ _)). apply Rle_mult_inv_pos; OK. apply INR_fact_lt_0. }
      { have ? : 0 <= x ^ S (n - 0) * / S (n - 0).
        { apply Rle_mult_inv_pos; OK. { apply pow_le; OK. } apply pos_INR_S. }
        suffices ? : x ^ (n - 0) <= 1 by OK.
        rewrite -(pow1 (n - 0)). apply pow_incr; OK. }
      apply Rinv_le_contravar; OK. apply INR_fact_lt_0.
    }
    have HSInt : ∀ N : nat, is_RInt (s N) 0 1 (h N).
    { rewrite /s /h. intro N'.
      apply (@RInt_correct R_CompleteNormedModule).
      apply ex_RInt_sum_n. intros n.
      rewrite ex_RInt_dom.
      apply ex_RInt_mult.
      { apply RealDecrTrial_μ_ex_RInt. }
      { rewrite /hx.
        apply (ex_RInt_plus (V := R_CompleteNormedModule)).
        2: { apply ex_RInt_const. }
        apply (ex_RInt_mult).
        { apply ex_RInt_const. }
        replace (λ y : R, F (y + L)) with  (λ y : R, scal 1 (F (1 * y + L))).
        2: { funexti. rewrite /scal//=/mult//= Rmult_1_l; f_equal; OK. }
        apply (ex_RInt_comp_lin F 1 L 0 1).
        repeat rewrite Rmult_1_l.
        apply PCts_RInt.
        apply IPCts_PCts.
        apply Hb.
      }
    }
    destruct (@filterlim_RInt nat R_CompleteNormedModule s 0 1 eventually eventually_filter
      (λ x : R, Series.Series (λ n : nat, Iverson (Ioo 0 1) x * (RealDecrTrial_μ x 0 n * hx F x L n)))
      h HSInt HSLim) as [IF [HIf1 HIf2]].
    by exists IF.
  Qed.

  Local Theorem g_expectation {F L M}
    (Hf : ∀ x, 0 <= F x <= M)
    (HCts : IPCts F) :
    is_RInt (g F L) 0 1 (NegExp_CreditV F L).
  Proof.
    have Hex : ∀ (a b : R), ex_RInt F a b.
    { intros ??. apply PCts_RInt. by apply IPCts_PCts. }
    suffices H : RInt (g F L) 0 1 = NegExp_CreditV F L.
    { rewrite -H. apply (RInt_correct (V := R_CompleteNormedModule)), (g_ex_RInt (M := M)); OK. }
    rewrite /g.
    rewrite /RealDecrTrial_CreditV.
    rewrite /hx.
    (* Separate the sum *)
    replace  (RInt (λ x, SeriesC (λ n, RealDecrTrial_μ x 0 n * (Iverson Zeven n * F (x + L) + Iverson (not ∘ Zeven) n * NegExp_CreditV F (L + 1)))) 0 1)
      with  ((RInt (λ x, SeriesC (λ n, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_CreditV F (L + 1))) 0 1 +
             (RInt (λ x, SeriesC (λ n, RealDecrTrial_μ x 0 n * Iverson Zeven n * F (x + L))) 0 1)));
      last first.
    { rewrite RInt_add.
      3: {
        eapply (ex_RInt_SeriesC (λ n : nat, 1^n/(fact n) * M)); OK.
        { rewrite ex_seriesC_nat.
          apply ex_seriesC_scal_r.
          apply Hpow_ex.
        }
        { intros ???.
          have HL : 0 <= 1 ^ n / fact n * M.
          { apply Rmult_le_pos; OK.
            2: { specialize Hf with 0; OK. }
            apply Rcomplements.Rdiv_le_0_compat.
            { apply pow_le; OK. }
            { apply INR_fact_lt_0. }
          }
          split.
          { apply Rmult_le_pos; [|apply Hf].
            apply Rmult_le_pos; [apply RealDecrTrial_μnn; lra|].
            apply Iverson_nonneg.
          }
          rewrite /Iverson//=.
          case_decide; OK.
          rewrite Rmult_1_r.
          rewrite /RealDecrTrial_μ.
          rewrite /Iverson.
          case_decide; OK.
          rewrite Rmult_1_l.
          apply Rmult_le_compat; OK.
          { apply RealDecrTrial_μ0nn; OK. }
          1,3: apply Hf.
          rewrite /RealDecrTrial_μ0.
          have ? : 0 <= x ^ (n - 0 + 1) / fact (n - 0 + 1).
          { apply Rcomplements.Rdiv_le_0_compat.
            { apply pow_le; OK. }
            { apply INR_fact_lt_0. }
          }
          suffices ? : x ^ (n - 0) / fact (n - 0) <= 1 ^ n / fact n by OK.
          rewrite Nat.sub_0_r.
          rewrite Rdiv_def.
          apply Rmult_le_compat; OK.
          { apply pow_le; OK. }
          { apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0. }
          { apply pow_incr; OK. }
        }
        { intros n.
          apply ex_RInt_mult.
          2: { by apply ex_RInt_shift. }
          apply ex_RInt_mult.
          { apply RealDecrTrial_μ_ex_RInt; OK. }
          { apply ex_RInt_const. }
        }
      }
      2: {
        eapply (ex_RInt_SeriesC (λ n : nat, 1^n/(fact n) * (NegExp_CreditV F (L + 1)))); OK.
        { rewrite ex_seriesC_nat.
          apply ex_seriesC_scal_r.
          apply Hpow_ex.
        }
        { intros ???.
          have HL : 0 <= 1 ^ n / fact n * M.
          { apply Rmult_le_pos; OK.
            2: { specialize Hf with 0; OK. }
            apply Rcomplements.Rdiv_le_0_compat.
            { apply pow_le; OK. }
            { apply INR_fact_lt_0. }
          }
          split.
          { apply Rmult_le_pos.
            2: { eapply NegExp_CreditV_nn; OK. }
            apply Rmult_le_pos; [apply RealDecrTrial_μnn; lra|].
            apply Iverson_nonneg.
          }
          rewrite /Iverson//=.
          case_decide; OK.
          2: {
            rewrite Rmult_0_r.
            rewrite Rmult_0_l.
            apply Rmult_le_pos.
            { apply Rcomplements.Rdiv_le_0_compat.
              { apply pow_le; OK. }
              { apply INR_fact_lt_0. }
            }
            eapply NegExp_CreditV_nn; OK.
          }

          rewrite Rmult_1_r.
          rewrite /RealDecrTrial_μ.
          rewrite /Iverson.
          case_decide; OK.
          2: {
            rewrite Rmult_0_l.
            rewrite Rmult_0_l.
            apply Rmult_le_pos.
            { apply Rcomplements.Rdiv_le_0_compat.
              { apply pow_le; OK. }
              { apply INR_fact_lt_0. }
            }
            eapply NegExp_CreditV_nn; OK.
          }
          rewrite Rmult_1_l.
          apply Rmult_le_compat; OK.
          { apply RealDecrTrial_μ0nn; OK. }
          1: { eapply NegExp_CreditV_nn; OK. }
          rewrite /RealDecrTrial_μ0.
          have ? : 0 <= x ^ (n - 0 + 1) / fact (n - 0 + 1).
          { apply Rcomplements.Rdiv_le_0_compat.
            { apply pow_le; OK. }
            { apply INR_fact_lt_0. }
          }
          suffices ? : x ^ (n - 0) / fact (n - 0) <= 1 ^ n / fact n by OK.
          rewrite Nat.sub_0_r.
          rewrite Rdiv_def.
          apply Rmult_le_compat; OK.
          { apply pow_le; OK. }
          { apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0. }
          { apply pow_incr; OK. }
        }
        { intros n.
          apply ex_RInt_mult.
          2: { apply ex_RInt_const. }
          apply ex_RInt_mult.
          2: { apply ex_RInt_const. }
          apply RealDecrTrial_μ_ex_RInt; OK.
        }
      }
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite -SeriesC_plus.
      3: {
        rewrite /RealDecrTrial_μ.
        eapply (ex_seriesC_le _ (λ n : nat, RealDecrTrial_μ0 x (n + 0) * M)).
        2: { apply ex_seriesC_scal_r. apply (RealDecrTrial_μ0_ex_seriesC (x := x) (M := 0)). OK. }
        intros n.
        split.
        { apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
          { apply Iverson_nonneg. }
          { apply RealDecrTrial_μ0nn. OK. }
          { apply Iverson_nonneg. }
          { apply Hf. }
        }
        { apply Rmult_le_compat.
          2: { apply Hf; OK. }
          3: { apply Hf; OK. }
          1: { apply Rmult_le_pos; [apply Rmult_le_pos|].
               { apply Iverson_nonneg. }
               { apply RealDecrTrial_μ0nn. OK. }
               { apply Iverson_nonneg. }
          }
          rewrite -(Rmult_1_r (RealDecrTrial_μ0 x (n + 0))).
          apply Rmult_le_compat.
          { apply Rmult_le_pos.
            { apply Iverson_nonneg. }
            { apply RealDecrTrial_μ0nn. OK. }
          }
          { apply Iverson_nonneg. }
          2: {  apply Iverson_le_1. }
          rewrite -(Rmult_1_l (RealDecrTrial_μ0 x (n + 0))).
          apply Rmult_le_compat.
          { apply Iverson_nonneg. }
          { apply RealDecrTrial_μ0nn. OK. }
          {  apply Iverson_le_1. }
          right.
          f_equal; OK.
        }
      }
      2: {
        rewrite /RealDecrTrial_μ.
        eapply (ex_seriesC_le _ (λ n : nat, RealDecrTrial_μ0 x (n + 0) * (NegExp_CreditV F (L + 1)))).
        2: { apply ex_seriesC_scal_r. apply (RealDecrTrial_μ0_ex_seriesC (x := x) (M := 0)). OK. }
        intros n.
        split.
        { apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos|]|].
          { apply Iverson_nonneg. }
          { apply RealDecrTrial_μ0nn. OK. }
          { apply Iverson_nonneg. }
          { eapply NegExp_CreditV_nn; last OK. intros ?. eapply Hf. }
        }
        { apply Rmult_le_compat.
          2: { eapply NegExp_CreditV_nn; last OK. intros ?. apply Hf. }
          3: { done. }
          1: { apply Rmult_le_pos; [apply Rmult_le_pos|].
               { apply Iverson_nonneg. }
               { apply RealDecrTrial_μ0nn. OK. }
               { apply Iverson_nonneg. }
          }
          rewrite -(Rmult_1_r (RealDecrTrial_μ0 x (n + 0))).
          apply Rmult_le_compat.
          { apply Rmult_le_pos.
            { apply Iverson_nonneg. }
            { apply RealDecrTrial_μ0nn. OK. }
          }
          { apply Iverson_nonneg. }
          2: {  apply Iverson_le_1. }
          rewrite -(Rmult_1_l (RealDecrTrial_μ0 x (n + 0))).
          apply Rmult_le_compat.
          { apply Iverson_nonneg. }
          { apply RealDecrTrial_μ0nn. OK. }
          {  apply Iverson_le_1. }
          right.
          f_equal; OK.
        }
      }
      f_equal; apply functional_extensionality; intro n.
      lra.
    }
    (* Apply Fubini to the odd term *)
    rewrite {1}/NegExp_CreditV.
    replace (RInt (λ x : R, SeriesC (λ n : nat,
            RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n *
            RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0) (at_point 0) (Rbar_locally Rbar.p_infty))) 0 1)
      with  (RInt_gen (λ x0 : R, (F x0 * NegExp_ρ (L + 1) x0) * (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n)) 0 1)) (at_point 0) (Rbar_locally Rbar.p_infty));
      last first.
    { pose B (x : R) (n : nat) (x0 : R) := ((RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * F x0 * NegExp_ρ (L + 1) x0)).
      replace (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n)) 0 1)  (at_point 0) (Rbar_locally Rbar.p_infty))
         with (RInt_gen (λ x0 : R, RInt (λ x : R, SeriesC (λ n : nat, B x n x0)) 0 1)  (at_point 0) (Rbar_locally Rbar.p_infty)).
      2: {
        f_equal.
        funexti.
        rewrite RInt_Rmult.
        2: {
          eapply (ex_RInt_SeriesC (λ n : nat, 1^n/(fact n))); OK.
          { rewrite ex_seriesC_nat.
            apply Hpow_ex.
          }
          { intros ???.
            have HL : 0 <= 1 ^ n / fact n.
            { apply Rcomplements.Rdiv_le_0_compat.
              { apply pow_le; OK. }
              { apply INR_fact_lt_0. }
            }
            split.
            {
              apply Rmult_le_pos; [apply RealDecrTrial_μnn; lra|].
              apply Iverson_nonneg.
            }
            rewrite /Iverson//=.
            case_decide; OK.
            rewrite Rmult_1_r.
            rewrite /RealDecrTrial_μ.
            rewrite /Iverson.
            case_decide; OK.
            rewrite Rmult_1_l.
            rewrite /RealDecrTrial_μ0.
            have ? : 0 <= x0 ^ (n - 0 + 1) / fact (n - 0 + 1).
            { apply Rcomplements.Rdiv_le_0_compat.
              { apply pow_le; OK. }
              { apply INR_fact_lt_0. }
            }
            suffices ? : x0 ^ (n - 0) / fact (n - 0) <= 1 ^ n / fact n by OK.
            rewrite Nat.sub_0_r.
            rewrite Rdiv_def.
            apply Rmult_le_compat; OK.
            { apply pow_le; OK. }
            { apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0. }
            { apply pow_incr; OK. }
          }
          { intros n.
            apply ex_RInt_mult.
            2: { apply ex_RInt_const. }
            apply RealDecrTrial_μ_ex_RInt; OK.
          }
        }
        apply RInt_ext.
        intros ??.
        rewrite -SeriesC_scal_l.
        apply SeriesC_ext.
        intros ?.
        rewrite /B.
        OK.
      }
      replace (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0) (at_point 0) (Rbar_locally Rbar.p_infty))) 0 1)
         with (RInt (λ x : R, SeriesC (λ n : nat, RInt_gen (λ x0 : R, B x n x0) (at_point 0) (Rbar_locally Rbar.p_infty))) 0 1).
      2: {
        apply RInt_ext.
        intros ??.
        apply SeriesC_ext.
        intros ?.
        rewrite /B//=.
        rewrite  RInt_gen_Ici_scal.
        { f_equal; funexti; OK. }
        eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, M * NegExp_ρ (L + 1) x)).
        { apply IPCts_scal_mult, NegExp_μ_IPcts. }
        { apply IPCts_mult; first done. apply NegExp_μ_IPcts. }
        { intros ?.
          split.
          { apply Rmult_le_pos; [apply Hf|]. apply NegExp_ρ_nn. }
          { apply Rmult_le_compat.
            { apply Hf. }
            { apply NegExp_ρ_nn. }
            { apply Hf. }
            { lra. }
          }
        }
        apply ex_RInt_gen_Ici_scal.
        apply NegExp_μ_ex_RInt_gen.
      }
      replace (RInt_gen (λ x0 : R, RInt (λ x : R, SeriesC (λ n : nat, B x n x0)) 0 1) (at_point 0) (Rbar_locally Rbar.p_infty))
         with (RInt (λ x : R, RInt_gen (λ x0 : R,SeriesC (λ n : nat, B x n x0)) (at_point 0) (Rbar_locally Rbar.p_infty)) 0 1).
      2: {
        (* Fubini *)
        symmetry.
        apply FubiniImproper_eq_x.
        { rewrite /IFubiniCondition_x.
          rewrite Rmin_left; OK.
          rewrite Rmax_right; OK.
          intros ???.
          (* (@UniformLimitTheorem2 (fun n x y => B x n y)) *)
          (* Okay wait, this could be a problem.
             Try to simplify Fubini, or more likely, come up with IPCts version of the Fubini's theorem. *)
          admit. }
        { apply (UniformConverge_RInt_weak _ (fun x0 => F x0 * NegExp_ρ (L + 1) x0) _ 0 1).
          { intros ??.
            split.
            { rewrite /Iverson//=. case_decide; OK.
              rewrite Rmult_1_l.
              apply SeriesC_ge_0'.
              intros ?.
              rewrite /B.
              apply Rmult_le_pos; [|apply NegExp_ρ_nn].
              apply Rmult_le_pos; [|apply Hf].
              apply Rmult_le_pos; [|apply Iverson_nonneg].
              apply RealDecrTrial_μnn.
              rewrite /Ioo in H; OK.
              rewrite Rmin_left in H; OK.
              rewrite Rmax_right in H; OK.
            }
            rewrite /Iverson//=.
            case_decide.
            2: { rewrite Rmult_0_l.
              apply Rmult_le_pos; [|apply NegExp_ρ_nn].
              apply Hf.
            }
            rewrite Rmult_1_l.
            rewrite /B.
            replace ((λ n : nat, RealDecrTrial_μ y 0 n * Iverson (not ∘ Zeven) n * F x * NegExp_ρ (L + 1) x))
               with (λ n : nat, RealDecrTrial_μ y 0 n * Iverson (not ∘ Zeven) n * (F x * NegExp_ρ (L + 1) x)).
            2: { funexti; OK. }
            rewrite SeriesC_scal_r.
            rewrite -{2}(Rmult_1_l (F x * NegExp_ρ (L + 1) x)).
            apply Rmult_le_compat; OK.
            2: {
              apply Rmult_le_pos; [|apply NegExp_ρ_nn].
              apply Hf.
            }
            { apply SeriesC_ge_0'.
              intros ?.
              apply Rmult_le_pos; [|apply Iverson_nonneg].
              apply RealDecrTrial_μnn.
              rewrite /Ioo in H; OK.
              rewrite Rmin_left in H; OK.
              rewrite Rmax_right in H; OK.
            }
            { rewrite /RealDecrTrial_μ.
              replace (λ x0 : nat, Iverson (uncurry le) (0%nat, x0) * RealDecrTrial_μ0 y (x0 - 0) * Iverson (not ∘ Zeven) x0)
                  with (λ x0 : nat, Iverson (not ∘ Zeven) x0 * RealDecrTrial_μ0 y x0).
              2: {
                funexti.
                symmetry.
                rewrite Iverson_True; OK.
                { rewrite Rmult_1_l Rmult_comm. repeat f_equal. OK. }
                rewrite /uncurry//=.
                OK.
              }
              rewrite /RealDecrTrial_μ0.
              have HSeries := (@ExpSeriesOdd y).
              (* can upper bound this by (exp 1 - 1) or whatever instead of 1 *)
              admit.
            }
          }
          { apply IPCts_mult; OK. apply NegExp_μ_IPcts. }
          { (* Not sure. IPCts version of Uniform limit theorem? *)
            admit. }
          { eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, M * NegExp_ρ (L + 1) x)).
            { apply IPCts_scal_mult, NegExp_μ_IPcts. }
            { apply IPCts_mult; first done. apply NegExp_μ_IPcts. }
            { intros ?.
              split.
              { apply Rmult_le_pos; [apply Hf|]. apply NegExp_ρ_nn. }
              { apply Rmult_le_compat.
                { apply Hf. }
                { apply NegExp_ρ_nn. }
                { apply Hf. }
                { lra. }
              }
            }
            apply ex_RInt_gen_Ici_scal.
            apply NegExp_μ_ex_RInt_gen.
          }
          { intros ???. rewrite Iverson_False; OK. rewrite /Ioo//=; OK. }
          { intros ???. rewrite Iverson_False; OK. rewrite /Ioo//=; OK. }
        }
      }
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.

      (** New Fubini *)
      eapply @FubiniImproper_Series.
      all: admit.
    }
    replace (RInt_gen (λ x0 : R, (F x0 * NegExp_ρ (L + 1) x0) * (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n)) 0 1)) (at_point 0) (Rbar_locally Rbar.p_infty))
       with (RInt_gen (λ x0 : R, (F x0 * NegExp_ρ (L + 1) x0) * (RInt (λ x : R, 1 - exp (-x)) 0 1)) (at_point 0) (Rbar_locally Rbar.p_infty));
      last first.
    { f_equal; apply functional_extensionality; intro x0.
      f_equal.
      f_equal; apply functional_extensionality; intro x.
      rewrite /RealDecrTrial_μ.
      rewrite /RealDecrTrial_μ0.
      replace (λ n : nat, Iverson (uncurry le) (0%nat, n) * (x ^ (n - 0) / fact (n - 0) - x ^ (n - 0 + 1) / fact (n - 0 + 1)) * Iverson (not ∘ Zeven) n)
         with (λ n : nat, Iverson (not ∘ Zeven) n * (x ^ n / fact n - x ^ (n + 1) / fact (n + 1))); last first.
      { funexti.
        symmetry. rewrite Iverson_True; [|rewrite //=; OK].
        rewrite Rmult_comm.
        f_equal; OK.
        rewrite Rmult_1_l.
        f_equal; OK.
        { f_equal; f_equal; OK. f_equal; OK. }
        { f_equal; f_equal; OK. f_equal; OK. }
      }
      replace (SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * (x ^ n / fact n - x ^ (n + 1) / fact (n + 1))))
         with ((-1) * SeriesC (λ n : nat, Iverson (not ∘ Zeven) n * ((-x) ^ n / fact n + (-x) ^ (n + 1) / fact (n + 1)))); last first.
      { rewrite -SeriesC_scal_l.
        apply SeriesC_ext.
        intros n.
        rewrite /Iverson.
        case_decide; OK.
        rewrite Rmult_plus_distr_l.
        repeat rewrite Rmult_1_l.
        rewrite Rmult_plus_distr_l.
        rewrite Rminus_def.
        repeat rewrite Rdiv_def.
        f_equal.
        { rewrite -Rmult_assoc; f_equal; OK. rewrite not_even_pow_neg; OK. }
        { repeat rewrite -Rmult_assoc.
          rewrite Ropp_mult_distr_l; f_equal.
          rewrite even_pow_neg; OK.
          replace (Z.of_nat (n + 1)%nat) with (Z.succ (Z.of_nat n)) by OK.
          apply Zeven_Sn.
          destruct (Zeven_odd_dec n); OK.
        }
      }
      rewrite ExpSeriesOdd.
      OK.
    }
    (* Compute the integral *)
    replace (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * RInt (λ x : R, 1 - exp (- x)) 0 1) (at_point 0) (Rbar_locally Rbar.p_infty))
       with (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (at_point 0) (Rbar_locally Rbar.p_infty));
      last first.
    { f_equal; apply functional_extensionality; intro x0.
      f_equal.
      have H : (Derive.Derive (fun x : R => x + exp (- x))) = (λ x : R, 1 - exp (- x)).
      { funexti.
        rewrite Derive.Derive_plus; [|by auto_derive| by auto_derive].
        rewrite Rminus_def.
        f_equal.
        { apply Derive.Derive_id. }
        { apply Derive_exp_neg. }
      }
      rewrite -H.
      rewrite RInt_Derive.
      { rewrite Rplus_0_l Ropp_0 exp_0.  replace (Ropp 1) with (-1) by OK. OK. }
      { intros ??. auto_derive. OK. (* Wait why does this work*) }
      { intros ??.
        rewrite H.
        apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
        by auto_derive.
      }
    }
    (* Separate out the gen integrals.
       Use RInt_gen_Chasles, though it's timing out my proof process right now *)
    replace (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (at_point 0) (Rbar_locally Rbar.p_infty))
      with ((RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (at_point 0) (at_point (L + 1))) +
             (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (at_point (L + 1)) (Rbar_locally Rbar.p_infty)));
      last first.
    { rewrite -(@RInt_gen_Chasles R_CompleteNormedModule (at_point 0) (Rbar_locally Rbar.p_infty) _ _ (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (L + 1) _ _).
      { OK. }
      { apply ex_RInt_gen_at_point.
        eapply ex_RInt_Rmult'.
        eapply ex_RInt_mult.
        { eapply Hex. }
        apply NegExp_ρ_ex_RInt.
      }
      { replace (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1))
           with (λ x0 : R, exp (-1) * (F x0 * NegExp_ρ (L + 1) x0)) by (funexti; OK).
        apply ex_RInt_gen_Ici_scal.
        eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, M * NegExp_ρ (L + 1) x)).
        { apply IPCts_scal_mult, NegExp_μ_IPcts. }
        { apply IPCts_mult; first done. apply NegExp_μ_IPcts. }
        { intros ?.
          split.
          { apply Rmult_le_pos; [apply Hf|]. apply NegExp_ρ_nn. }
          { apply Rmult_le_compat.
            { apply Hf. }
            { apply NegExp_ρ_nn. }
            { apply Hf. }
            { lra. }
          }
        }
        apply ex_RInt_gen_Ici_scal.
        apply NegExp_μ_ex_RInt_gen.
      }
    }
    rewrite RInt_gen_at_point.
    2: {
      eapply ex_RInt_Rmult'.
      eapply ex_RInt_mult.
      { eapply Hex. }
      apply NegExp_ρ_ex_RInt.
    }
    replace (RInt (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) 0 (L + 1))
       with (RInt (λ x0 : R, 0) 0 (L + 1)); last first.
    { apply RInt_ext; intros x [Hx1 Hx2].
      rewrite /NegExp_ρ/NegExp_ρ0.
      rewrite (@Iverson_False _ (Rle 0)); [lra|].
      intro Hk.
      rewrite -Rcomplements.Rminus_le_0 in Hk.
      have ? : (L + 1 <= x).
      { etransitivity; last apply Hk. by rewrite plus_INR. }
      rewrite Rmax_right in Hx2; last first.
      { apply Rplus_le_le_0_compat; [apply pos_INR |lra]. }
      lra.
    }
    rewrite RInt_const /scal//=/mult//= Rmult_0_r Rplus_0_l.
    rewrite /NegExp_CreditV.
    replace (RInt_gen (λ x : R, F x * NegExp_ρ L x) (at_point 0) (Rbar_locally Rbar.p_infty))
      with (RInt_gen (λ x : R, F x * NegExp_ρ L x) (at_point 0) (at_point (INR L)) +
            RInt_gen (λ x : R, F x * NegExp_ρ L x) (at_point (INR L)) (at_point (L + 1)) +
            RInt_gen (λ x : R, F x * NegExp_ρ L x) (at_point (L + 1)) (Rbar_locally Rbar.p_infty));
      last first.
    { rewrite -(@RInt_gen_Chasles R_CompleteNormedModule (at_point 0) (Rbar_locally Rbar.p_infty) _ _  (λ x : R, F x * NegExp_ρ L x) (L + 1) _ _).
      { rewrite /plus//=.
        rewrite RInt_gen_at_point.
        2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
        rewrite RInt_gen_at_point.
        2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
        rewrite RInt_gen_at_point.
        2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
        rewrite -(RInt_Chasles (λ x : R, F x * NegExp_ρ L x) 0 L (L + 1)).
        2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
        2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
        OK.
      }
      { apply ex_RInt_gen_at_point.
        apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
      { (** Integrable + Bounded argument (Should be done somewhere) *)
        eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, M * NegExp_ρ L x)).
        { apply IPCts_scal_mult, NegExp_μ_IPcts. }
        { apply IPCts_mult; first done. apply NegExp_μ_IPcts. }
        { intros ?.
          split.
          { apply Rmult_le_pos; [apply Hf|]. apply NegExp_ρ_nn. }
          { apply Rmult_le_compat.
            { apply Hf. }
            { apply NegExp_ρ_nn. }
            { apply Hf. }
            { lra. }
          }
        }
        apply ex_RInt_gen_Ici_scal.
        apply NegExp_μ_ex_RInt_gen.
      }
    }
    rewrite RInt_gen_at_point.
    2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
    rewrite RInt_gen_at_point.
    2: { apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. } }
    replace (RInt (λ x : R, F x * NegExp_ρ L x) 0 L) with (RInt (λ x : R, 0) 0 L); last first.
    { apply RInt_ext; intros x [Hx1 Hx2].
      rewrite /NegExp_ρ/NegExp_ρ0.
      rewrite (@Iverson_False _ (Rle 0)); [lra|].
      intro Hk.
      rewrite -Rcomplements.Rminus_le_0 in Hk.
      have ? : (L <= x).
      { etransitivity; last apply Hk. done. }
      rewrite Rmax_right in Hx2; last apply pos_INR.
      lra.
    }
    rewrite RInt_const /scal//=/mult//= Rmult_0_r Rplus_0_l.
    rewrite Rplus_comm.
    f_equal.
    { (* Change of variables *)
      replace (RInt (λ x : R, F x * NegExp_ρ L x) L (L + 1)) with (RInt (λ x : R, F (x + L) * NegExp_ρ L (x + L)) 0 1); last first.
      { replace (RInt (λ x : R, F x * NegExp_ρ L x) L (L + 1)) with (RInt (λ x : R, F x * NegExp_ρ L x) (1 * 0 + L) (1 * 1 + L)); last first.
        { f_equal; OK. }
        rewrite -(RInt_comp_lin (λ x : R, F x * NegExp_ρ L x) 1 L 0 1).
        2: {
          rewrite Rmult_0_r Rplus_0_l.
          rewrite Rmult_1_l Rplus_comm.
          apply ex_RInt_mult. { apply Hex. } { apply NegExp_ρ_ex_RInt. }
        }
        f_equal. apply functional_extensionality. intros ?. rewrite /scal//=/mult//= Rmult_1_l.
        f_equal; f_equal; OK.
      }
      apply RInt_ext; intros x [Hx1 Hx2].
      (* Factor out F *)
      rewrite SeriesC_scal_r Rmult_comm; f_equal.
      (* Simplify *)
      rewrite /NegExp_ρ.
      rewrite Iverson_True; last lia.
      rewrite Rmult_1_l.
      rewrite /NegExp_ρ0.
      rewrite Rplus_minus_r.
      rewrite Iverson_True; last (rewrite Rmin_left in Hx1; lra).
      rewrite Rmult_1_l.
      (* Exponential series *)
      rewrite /RealDecrTrial_μ.
      rewrite /RealDecrTrial_μ0.
      replace  (λ x0 : nat, Iverson (uncurry le) (0%nat, x0) * (x ^ (x0 - 0) / fact (x0 - 0) - x ^ (x0 - 0 + 1) / fact (x0 - 0 + 1)) * Iverson Zeven x0) with (λ x0 : nat, (x ^ (x0) / fact (x0) - x ^ (x0 + 1) / fact (x0 + 1)) * Iverson Zeven x0); last first.
      { funexti.
        symmetry. rewrite Iverson_True; [|rewrite //=; OK].
        rewrite Rmult_1_l.
        f_equal; OK.
        f_equal; OK.
        { f_equal; f_equal; OK. f_equal; OK. }
        { f_equal; f_equal; OK. f_equal; OK. }
      }
      replace (SeriesC (λ x0 : nat, (x ^ x0 / fact x0 - x ^ (x0 + 1) / fact (x0 + 1)) * Iverson Zeven x0)) with
              (SeriesC (λ x0 : nat, Iverson Zeven x0 * ((-x) ^ x0 / fact x0 + (-x) ^ (x0 + 1) / fact (x0 + 1)))); last first.
      { apply SeriesC_ext.
        intros n.
        rewrite /Iverson.
        case_decide; OK.
        repeat rewrite Rmult_1_l.
        repeat rewrite Rmult_1_r.
        rewrite Rminus_def.
        repeat rewrite Rdiv_def.
        f_equal.
        { f_equal; OK. rewrite even_pow_neg; OK. }
        { repeat rewrite -Rmult_assoc.
          rewrite Ropp_mult_distr_l; f_equal.
          rewrite not_even_pow_neg; OK.
          replace (Z.of_nat (n + 1)%nat) with (Z.succ (Z.of_nat n)) by OK.
          intro Hk.
          apply Zodd_Sn in H.
          apply Zodd_not_Zeven in H.
          apply Zeven_not_Zodd in Hk.
          destruct (Zeven_odd_dec (Z.succ n)); OK.
        }
      }
      rewrite ExpSeriesEven.
      OK.
    }
    {
      apply RInt_gen_ext_eq_Ici.
      2: {  (** Integrable + Bounded argument (Should be done somewhere) *)
        replace (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1))
           with (λ x0 : R, exp (-1) * (F x0 * NegExp_ρ (L + 1) x0)) by (funexti; OK).
        apply ex_RInt_gen_Ici_scal.
        eapply (@ex_RInt_gen_Ici_compare_IPCts _ (λ x : R, M * NegExp_ρ (L + 1) x)).
        { apply IPCts_scal_mult, NegExp_μ_IPcts. }
        { apply IPCts_mult; first done. apply NegExp_μ_IPcts. }
        { intros ?.
          split.
          { apply Rmult_le_pos; [apply Hf|]. apply NegExp_ρ_nn. }
          { apply Rmult_le_compat.
            { apply Hf. }
            { apply NegExp_ρ_nn. }
            { apply Hf. }
            { lra. }
          }
        }
        apply ex_RInt_gen_Ici_scal.
        apply NegExp_μ_ex_RInt_gen.
      }
      intros x Hx.
      rewrite Rmult_assoc. f_equal.
      rewrite /NegExp_ρ.
      rewrite Iverson_True; last lia.
      rewrite Rmult_1_l.
      rewrite Iverson_True; last lia.
      rewrite Rmult_1_l.
      rewrite /NegExp_ρ0.
      (* Can't simply get the inequalities for the bounds by cases
         on the iverson function here; the terms are not equal on the [L, L+1] interval. *)
      rewrite Iverson_True; last first.
      { (* Need the bounds here *)
        apply error_credits.Rle_0_le_minus.
        etrans; last eapply Hx.
        rewrite plus_INR INR_1. OK. }
      rewrite Rmult_1_l.
      rewrite Iverson_True; last first.
      { apply error_credits.Rle_0_le_minus.
        etrans; last eapply Hx.
        OK. }
      rewrite Rmult_1_l.
      rewrite -exp_plus; f_equal.
      rewrite plus_INR INR_1.
      lra.
    }
  Admitted.

End credits.


*)
