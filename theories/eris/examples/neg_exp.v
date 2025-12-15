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
