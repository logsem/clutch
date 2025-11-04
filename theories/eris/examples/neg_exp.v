From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive RInt_gen.
From clutch.eris Require Import infinite_tape.
From clutch.eris.examples Require Import lazy_real max_lazy_real indicators real_decr_trial.
Set Default Proof Using "Type*".
#[local] Open Scope R.

Section pmf.

  Local Definition NegExp_ρ0 (x : R) : R :=
    Iverson (Rle 0%R) x * exp (-x)%R.

  Theorem NegExp_ρ0_not_supp {x} (H : Rlt x 0%R) : NegExp_ρ0 x = 0.
  Proof. rewrite /NegExp_ρ0 Iverson_False //=; [lra|lra]. Qed.

  Theorem NegExp_ρ0_supp {x} (H : Rlt 0%R x) : NegExp_ρ0 x = exp (-x)%R.
  Proof. rewrite /NegExp_ρ0 Iverson_True //=; [lra|lra]. Qed.

  Local Definition NegExp_ρ (L : nat) (x : R) : R :=
    Iverson (le 0) L * NegExp_ρ0 (x - INR L).

  Theorem NegExp_ρ_not_supp {x L} (H : lt L 0) : NegExp_ρ L x = 0.
  Proof. rewrite /NegExp_ρ Iverson_False //=; [lra|lia]. Qed.

  Theorem NegExp_ρ_supp {x L} (H : le 0 L) : NegExp_ρ L x = NegExp_ρ0 (x - INR L).
  Proof. rewrite /NegExp_ρ Iverson_True //=; lra. Qed.

End pmf.

Section credits.
  Import Hierarchy.

  Definition NegExp_CreditV (F : R → R) (L : nat) : R :=
    RInt_gen (fun x : R => F x * NegExp_ρ L x) (at_point 0%R) (Rbar_locally Rbar.p_infty).

  Lemma NegExp_CreditV_nn {F : R -> R} (Hnn : ∀ r, 0 <= F r) (L : nat) : 0 <= NegExp_CreditV F (L + 1).
  Proof.
    rewrite /NegExp_CreditV.
  Admitted.

  Local Definition hx (F : R → R) (x : R) (L : nat) : nat → R := fun z =>
    Iverson Zeven z * F (x + INR L) +
    Iverson (not ∘ Zeven) z * NegExp_CreditV F (L + 1).

  Local Definition g (F : R -> R) (L : nat) : R -> R := fun x =>
    RealDecrTrial_CreditV (hx F x L) 0 x.

  Lemma hx_nonneg {F xr L} (Hnn : ∀ r, 0 <= F r) : ∀ n : nat, 0 <= hx F xr L n.
  Proof.
    rewrite /hx.
    intros ?.
    apply Rplus_le_le_0_compat; (apply Rmult_le_pos; [apply Iverson_nonneg|]).
    { auto. }
    { apply NegExp_CreditV_nn; auto. }
  Qed.

  Lemma g_nonneg {F L r} (Hnn : ∀ r, 0 <= F r) (Hr : 0 <= r <= 1) : 0 <= g F L r.
  Proof.
    rewrite /g.
    apply CreditV_nonneg; auto.
    intros ?.
    apply hx_nonneg; auto.
  Qed.

  Local Lemma g_ex_RInt {F L} : ex_RInt (g F L) 0 1.
  Proof. Admitted.

  (*
  Lemma hx_ex_seriesC {F xr L} : ex_seriesC (hx F xr L).
  Proof.
    rewrite /hx.
    (* BA by sum, then needs Fubini for RInt_gen *)
  Admitted.
*)


  Local Theorem g_expectation {F L} : is_RInt (g F L) 0 1 (NegExp_CreditV F L).
  Proof.
    suffices H : RInt (g F L) 0 1 = NegExp_CreditV F L.
    { rewrite -H. apply (RInt_correct (V := R_CompleteNormedModule)), g_ex_RInt. }
    rewrite /g.
    rewrite /RealDecrTrial_CreditV.
    rewrite /hx.
    (* Separate the sum *)
    replace  (RInt (λ x, SeriesC (λ n, RealDecrTrial_μ x 0 n * (Iverson Zeven n * F (x + L) + Iverson (not ∘ Zeven) n * NegExp_CreditV F (L + 1)))) 0 1)
      with  ((RInt (λ x, SeriesC (λ n, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n * NegExp_CreditV F (L + 1))) 0 1 +
             (RInt (λ x, SeriesC (λ n, RealDecrTrial_μ x 0 n * Iverson Zeven n * F (x + L))) 0 1)));
      last first.
    { rewrite RInt_add.
      3: admit.
      2: admit.
      f_equal; apply functional_extensionality; intro x.
      rewrite -SeriesC_plus.
      3: admit.
      2: admit.
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
    { (* Deploy the foob *) admit. }
    replace (RInt_gen (λ x0 : R, (F x0 * NegExp_ρ (L + 1) x0) * (RInt (λ x : R, SeriesC (λ n : nat, RealDecrTrial_μ x 0 n * Iverson (not ∘ Zeven) n)) 0 1)) (at_point 0) (Rbar_locally Rbar.p_infty))
       with (RInt_gen (λ x0 : R, (F x0 * NegExp_ρ (L + 1) x0) * (RInt (λ x : R, 1 - exp (-x)) 0 1)) (at_point 0) (Rbar_locally Rbar.p_infty));
      last first.
    { f_equal; apply functional_extensionality; intro x0.
      f_equal.
      f_equal; apply functional_extensionality; intro x.
      (* Compute the exponential series *) admit. }
    (* Compute the integral *)
    replace (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * RInt (λ x : R, 1 - exp (- x)) 0 1) (at_point 0) (Rbar_locally Rbar.p_infty))
       with (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (at_point 0) (Rbar_locally Rbar.p_infty));
      last first.
    { f_equal; apply functional_extensionality; intro x0.
      f_equal.
      admit.
    }
    (* Separate out the gen integrals.
       Use RInt_gen_Chasles, though it's timing out my proof process right now *)
    replace (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (at_point 0) (Rbar_locally Rbar.p_infty))
      with ((RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (at_point 0) (at_point (L + 1))) +
             (RInt_gen (λ x0 : R, F x0 * NegExp_ρ (L + 1) x0 * exp (-1)) (at_point (L + 1)) (Rbar_locally Rbar.p_infty)));
      last first.
    { admit. }
    rewrite RInt_gen_at_point.
    2: admit.
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
    { admit. }
    rewrite RInt_gen_at_point.
    2: admit.
    rewrite RInt_gen_at_point.
    2: admit.
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
      { admit. }
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
      admit. }
    {
      apply RInt_gen_ext_eq. (* TODO: Need a version of this which includes the
                                      bounds--both integrals are on [L+1, ∞) *)
      2: admit.
      intro x.
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
        admit. }
      rewrite Rmult_1_l.
      rewrite Iverson_True; last first.
      { (* Need the bounds here *)
        admit. }
      rewrite Rmult_1_l.
      rewrite -exp_plus; f_equal.
      rewrite plus_INR INR_1.
      lra.
    }
  Admitted.

End credits.


Section program.
  Context `{!erisGS Σ}.

  (* Tail-recursive Negative Exponential sampling*)
  Definition NegExp : val :=
    rec: "trial" "L" :=
      let: "x" := init #() in
      let: "y" := lazyDecrR #Nat.zero "x" in
      if: ("y" `rem` #2%Z = #0%Z) then
        ("L", "x")
      else
        "trial" ("L" + #1%Z).

  Lemma wp_NegExp_gen {M} (F : R → R) (Hnn : ∀ n, 0 <= F n <= M) E :
    ⊢ ∀ L, ↯ (NegExp_CreditV F L) -∗
           WP NegExp #L @ E
      {{ p, ∃ (vz : Z) (vr : R) (ℓ : val), ⌜p = PairV #vz ℓ⌝ ∗ lazy_real ℓ vr ∗ ↯(F (vr + IZR vz))}}.
  Proof.
    iLöb as "IH".
    iIntros (L) "Hε".
    rewrite {2}/NegExp.
    wp_pure.
    wp_apply wp_init; first done.
    iIntros (x) "Hx".
    iApply (wp_lazy_real_presample_adv_comp _ _ x _ (NegExp_CreditV F L) (g F L)); auto.
    { intros ??; apply g_nonneg; auto. apply Hnn. }
    { by apply g_expectation. }
    iFrame.
    iIntros (xr) "(%Hrange & Hε & Hx)".
    do 2 wp_pure.
    wp_bind (lazyDecrR _ _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hx Hε] IH"); last first.
    { iApply (wp_lazyDecrR_gen (hx F xr L) _ E $! _ x xr).
      by rewrite /g; iFrame.
      Unshelve.
      1: { exact ((F (xr + L)) + (NegExp_CreditV F (L + 1))). }
      1: {
        rewrite /hx.
        intro n.
        split.
        { apply Rplus_le_le_0_compat; apply Rmult_le_pos; try apply Iverson_nonneg.
          { apply Hnn.  }
          { apply NegExp_CreditV_nn. intro r. apply Hnn. }
        }
        { apply Rplus_le_compat.
          { rewrite -{2}(Rmult_1_l (F (xr + L))).
            apply Rmult_le_compat_r; [|apply Iverson_le_1].
            apply Hnn.
          }
          { rewrite -{2}(Rmult_1_l (NegExp_CreditV F (L + 1))).
            apply Rmult_le_compat_r; [|apply Iverson_le_1].
            apply NegExp_CreditV_nn. intro r. apply Hnn.
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
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply NegExp_CreditV_nn, Hnn ]. }
      rewrite Iverson_True; last done.
      by rewrite Rmult_1_l INR_IZR_INZ.
    }
    { do 2 wp_pure.
      rewrite {1}/NegExp.
      iPoseProof (ec_split _ _ with "Hε") as "(_ & Hε)".
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply Hnn ]. }
      { apply Rmult_le_pos; [apply Iverson_nonneg | apply NegExp_CreditV_nn, Hnn ]. }
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
