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
  Proof. Admitted.

  Local Definition hx (F : R → R) (x : R) (L : nat) : nat → R := fun z =>
    Iverson Zeven z * F (x + INR L) +
    Iverson (not ∘ Zeven) z * NegExp_CreditV F (L + 1).

  Local Definition g (F : R -> R) (L : nat) : R -> R := fun x =>
    RealDecrTrial_CreditV (hx F x L) 0 x.

  Lemma g_nonneg {F L r} (Hnn : ∀ r, 0 <= F r) : 0 <= g F L r.
  Proof. Admitted.

  Lemma hx_nonneg {F xr L} (Hnn : ∀ r, 0 <= F r) : ∀ n : nat, 0 <= hx F xr L n.
  Proof. Admitted.

  Theorem g_expectation {F L} : is_RInt (g F L) 0 1 (NegExp_CreditV F L).
  Proof. Admitted.

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

  Lemma wp_NegExp_gen (F : R → R) (Hnn : ∀ n, 0 <= F n) E :
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
    { by intros ??; apply g_nonneg, Hnn. }
    { by apply g_expectation. }
    iFrame.
    iIntros (xr) "(Hε & Hx)".
    do 2 wp_pure.
    wp_bind (lazyDecrR _ _).
    iApply (pgl_wp_mono_frame (□ _) with "[Hx Hε] IH"); last first.
    { iApply (wp_lazyDecrR_gen (hx F xr L) _ E $! _ x xr). by rewrite /g; iFrame.
      Unshelve. intros ?. by apply hx_nonneg, Hnn. }
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
