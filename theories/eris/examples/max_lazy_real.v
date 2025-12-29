From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive.
From clutch.eris Require Import infinite_tape lazy_real.
From clutch.eris.examples Require Import lazy_real half_bern_neg_exp math.
Set Default Proof Using "Type*".
#[local] Open Scope R.


Section max_lazy_real.
Import Hierarchy.
Context `{!erisGS Σ}.

Definition MLR : val :=
  λ: "_",
    let: "vx" := init #() in
    let: "vy" := init #() in
    if: cmp "vx" "vy" = #(-1)%Z then "vy" else "vx".

Definition MLR_CreditV (F : R → R) : R := RInt (fun x => F x * 2 * x) 0 1.

Definition MLR_ε2 (F : R → R) (x : R) : R → R  := fun y => F(Rmax x y).

Definition MLR_ε1 (F : R → R) : R → R  := fun x => RInt (MLR_ε2 F x) 0 1.

Lemma MLR_ex_RInt {F M} (Hnn : ∀ r, 0 <= F r <= M) (Hcts : PCts F 0 1) :
  ∀ x : R, 0 <= x <= 1 → ex_RInt (MLR_ε2 F x) 0 1.
Proof.
  intros ??.
  rewrite /MLR_ε2//=.
  apply (@ex_RInt_Chasles_0 R_CompleteNormedModule _ _ x); [lra| |].
  { apply (ex_RInt_ext (λ y : R, F x)).
    { rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      f_equal.
      rewrite Rmax_left; lra.
    }
    { apply ex_RInt_const. }
  }
  { apply (ex_RInt_ext (λ y : R, F y)).
    { rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      f_equal.
      rewrite Rmax_right; lra.
    }
    { apply (@ex_RInt_Chasles_2 R_CompleteNormedModule _ 0); try lra.
      apply PCts_RInt.
      apply Hcts.
    }
  }
Qed.

Lemma MLR_ε1nn {F M} (Hnn : ∀ r, 0 <= F r <= M) (Hcts : PCts F 0 1) : ∀ r : R, 0 <= r <= 1 → 0 <= MLR_ε1 F r.
Proof.
  intros ??.
  rewrite /MLR_ε1.
  apply RInt_ge_0; try lra.
  2: { intros ??. rewrite /MLR_ε2. apply Hnn. }
  by eapply MLR_ex_RInt.
Qed.


Lemma MLR_ε2_nn {F M x} (Hnn : ∀ r, 0 <= F r <= M) (Hcts : PCts F 0 1) (Hx : 0 <= x <= 1) :
  ∀ r : R, 0 <= r <= 1 → 0 <= MLR_ε2 F x r.
Proof.
  intros ??.
  rewrite /MLR_ε2.
  apply Hnn.
Qed.

Lemma MLR_ε2_ev {F M x} (Hnn : ∀ r, 0 <= F r <= M) (Hcts : PCts F 0 1) (Hx : 0 <= x <= 1) :
  is_RInt (MLR_ε2 F x) 0 1 (MLR_ε1 F x).
Proof.
  rewrite /MLR_ε1/MLR_ε2//=.
  eapply (@RInt_correct R_CompleteNormedModule).
  by eapply MLR_ex_RInt.
Qed.

(* Below:
 A stronger variant of Fubini's theorem: the integrand is permitted to be
  discontinuous along a line in 2D. This variant is neccessary for the
  maximum of two uniforms example.

  This is true because the set of discontinuities, namely a line, has measure zero.
  It does not reduce to our prior axiomatiziation in general. *)

Section max_lazy_real_ax.
  Import Hierarchy.

  Axiom Max_Fubini_ex_x : ∀ {f a b}, PCts f a b →
    ex_RInt (fun x => RInt (fun y => f (Rmax x y)) a b) a b.

  Axiom Max_Fubini_ex_x' : ∀ {f}, PCts f 0 1 →
    ex_RInt (λ x : R, RInt (λ y : R, f y) x 1) 0 1.

  Axiom Fubini_Max : ∀ {f}, PCts f 0 1 →
    RInt (λ x : R, RInt (λ y : R, Iverson (Icc x 1) y * f (Rmax x y)) 0 1) 0 1 =
    RInt (λ y : R, RInt (λ x : R, Iverson (Icc x 1) y * f (Rmax x y)) 0 1) 0 1.

  (*
  Axiom Max_Fubini : ∀ {f}, PCts f 0 1 →
    RInt (λ x : R, RInt (λ y : R, F y) x 1) 0 1 =
    RInt (λ x : R, RInt (λ y : R, F y) x 1) 0 1 =
  *)

End max_lazy_real_ax.

Lemma MLR_ε1_ev {F M} (Hnn : ∀ r, 0 <= F r <= M) (Hcts : PCts F 0 1) : is_RInt (MLR_ε1 F) 0 1 (MLR_CreditV F).
Proof.
  rewrite /MLR_ε1/MLR_ε2//=.
  suffices : RInt (λ x : R, RInt (λ y : R, F (Rmax x y)) 0 1) 0 1 = (MLR_CreditV F).
  { intros HH.
    eapply is_RInt_ext.
    2 : {
      rewrite -HH.
      eapply (@RInt_correct R_CompleteNormedModule).
      apply Max_Fubini_ex_x; try lra.
      apply Hcts.
    }
    auto.
  }
  rewrite /MLR_CreditV//=.
  replace (RInt (λ x : R, RInt (λ y : R, F (Rmax x y)) 0 1) 0 1)
     with (RInt (λ x : R, RInt (λ y : R, Iverson (Icc 0 x) y * F (Rmax x y)) 0 1) 0 1 +
           RInt (λ x : R, RInt (λ y : R, Iverson (Icc x 1) y * F (Rmax x y)) 0 1) 0 1).
  2: {
    replace (RInt (λ x : R, RInt (λ y : R, Iverson (Icc 0 x) y * F (Rmax x y)) 0 1) 0 1)
       with (RInt (λ x : R, RInt (λ y : R, F (Rmax x y)) 0 x) 0 1).
    2: admit.
    replace (RInt (λ x : R, RInt (λ y : R, Iverson (Icc x 1) y * F (Rmax x y)) 0 1) 0 1)
       with (RInt (λ x : R, RInt (λ y : R, F (Rmax x y)) x 1) 0 1).
    2: admit.

    rewrite RInt_add; first last.
    { eapply (ex_RInt_ext (λ x : R, RInt (λ y : R, F y) x 1)).
      { rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros ??.
        apply RInt_ext.
        rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros ??.
        f_equal.
        rewrite Rmax_right; lra.
      }
      by apply Max_Fubini_ex_x'.
    }
    { eapply (ex_RInt_ext (λ x : R, RInt (λ y : R, F x) 0 x)).
      { rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros ??.
        apply RInt_ext.
        rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros ??.
        f_equal.
        rewrite Rmax_left; lra.
      }
      replace (λ x : R, RInt (λ _ : R, F x) 0 x)
         with (fun x => x * F x).
      2: {
        funexti.
        rewrite RInt_const.
        rewrite /scal//=.
        rewrite /mult//=.
        lra.
      }
      apply PCts_RInt.
      apply PCts_mult; try done.
      apply PCts_cts.
      intros ??.
      apply Continuity.continuous_id.
    }
    apply RInt_ext.
    rewrite Rmin_left; try lra.
    rewrite Rmax_right; try lra.
    intros ??.
    replace (RInt (λ y : R, F (Rmax x y)) 0 x + RInt (λ y : R, F (Rmax x y)) x 1)
       with (plus (RInt (λ y : R, F (Rmax x y)) 0 x) (RInt (λ y : R, F (Rmax x y)) x 1)) by f_equal.
    rewrite RInt_Chasles; first last.
    { eapply (ex_RInt_ext (λ y : R, F y)).
      { rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros ??.
        f_equal.
        rewrite Rmax_right; lra.
      }
      { apply (@ex_RInt_Chasles_2 R_CompleteNormedModule _ 0); try lra.
        by apply PCts_RInt.
      }
    }
    { eapply (ex_RInt_ext (λ y : R, F x)).
      { rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros ??.
        f_equal.
        rewrite Rmax_left; lra.
      }
      { apply ex_RInt_const. }
    }
    done.
  }

  replace (RInt (λ x : R, RInt (λ y : R, F (Rmax x y)) 0 x) 0 1)
     with (RInt (λ x : R, RInt (λ y : R, F x) 0 x) 0 1).
  2: {
    apply RInt_ext.
    rewrite Rmin_left; try lra.
    rewrite Rmax_right; try lra.
    intros ??.
    rewrite (RInt_ext _ (λ y : R, F x)) .
    { done. }
    rewrite Rmin_left; try lra.
    rewrite Rmax_right; try lra.
    intros ??.
    f_equal.
    rewrite Rmax_left; try lra.
  }
  replace (RInt (λ x : R, RInt (λ y : R, F (Rmax x y)) x 1) 0 1)
     with (RInt (λ x : R, RInt (λ y : R, F y) x 1) 0 1).
  2: {
    apply RInt_ext.
    rewrite Rmin_left; try lra.
    rewrite Rmax_right; try lra.
    intros ??.
    rewrite (RInt_ext _ (λ y : R, F y)) .
    { done. }
    rewrite Rmin_left; try lra.
    rewrite Rmax_right; try lra.
    intros ??.
    f_equal.
    rewrite Rmax_right; try lra.
  }
  replace (λ x : R, RInt (λ _ : R, F x) 0 x)
     with (fun x => x * F x).
  2: {
    funexti.
    rewrite RInt_const.
    rewrite /scal//=.
    rewrite /mult//=.
    lra.
  }
  rewrite Fubini_Max; try done.
  (* Meh *)
Admitted.

Theorem wp_G1 {E F M} (Hnn : ∀ r, 0 <= F r <= M) (Hcts : PCts F 0 1) :
  ↯(MLR_CreditV F) -∗ WP MLR #() @ E {{ vr, ∃ r : R, lazy_real vr r ∗ ↯(F r) }}.
Proof.
  iIntros "Herr".
  rewrite /MLR.
  wp_pures.
  wp_apply wp_init; first done.
  iIntros (v1) "Hv1".
  iApply (@wp_lazy_real_presample_adv_comp _ _ E _ v1 _ (MLR_CreditV F) (MLR_ε1 F) with "[Herr Hv1]"); eauto.
  { by eapply MLR_ε1nn. }
  { by eapply MLR_ε1_ev. }
  iFrame.
  iIntros (x) "[%[Herr Hx]]".
  wp_pures.
  wp_apply wp_init; first done.
  iIntros (v2) "Hv2".
  iApply (@wp_lazy_real_presample_adv_comp _ _ E _ v2 _ (MLR_ε1 F x) (MLR_ε2 F x) with "[Herr Hx Hv2]"); eauto.
  { by eapply MLR_ε2_nn. }
  { by eapply MLR_ε2_ev. }
  iFrame.
  iIntros (y) "[%[Herr Hy]]".
  wp_pures.
  wp_bind (cmp _ _).
  wp_apply (wp_cmp with "[Hx Hy]"); iFrame.
  iIntros (z) "[Hx[Hy %]]".
  destruct H1 as [[-> ?]|[-> ?]].
  { wp_pures.
    iModIntro.
    iExists y.
    iFrame.
    iApply (ec_eq with "Herr").
    rewrite /MLR_ε2; f_equal.
    rewrite Rmax_right; lra.
  }
  { wp_pures.
    iModIntro.
    iExists x.
    iFrame.
    iApply (ec_eq with "Herr").
    rewrite /MLR_ε2; f_equal.
    rewrite Rmax_left; lra.
  }
Qed.

End max_lazy_real.


(*
Section max_lazy_real.
Import Hierarchy.

Context `{!erisGS Σ}.

Definition IndicatorLe (x y : R) : R := if decide (x <= y)%R then 1 else 0.

Lemma IndicatorLe_le (x y : R) : (x <= y)%R → IndicatorLe x y = 1.
Proof. rewrite /IndicatorLe; case_decide; [done | nra]. Qed.

Lemma IndicatorLe_gt (x y : R) : (y < x)%R → IndicatorLe x y = 0.
Proof. rewrite /IndicatorLe; case_decide; [nra | done]. Qed.

Lemma ex_RInt_IndicatorLe y a b (Hab : a <= b) : ex_RInt (λ y0 : R, IndicatorLe y0 y) a b.
Proof.
  rewrite /IndicatorLe//=.
  case (decide (a <= y <= b)).
  { intros [Hy1 Hy2].
    apply (ex_RInt_Chasles_0 _ a y b); first nra.
    { apply (ex_RInt_ext (fun _ => 1)); last apply ex_RInt_const.
      rewrite Rmin_left; last nra.
      rewrite Rmax_right; last nra.
      intros x [Hx1 Hx2].
      case_decide; nra.
    }
    { apply (ex_RInt_ext (fun _ => 0)); last apply ex_RInt_const.
      rewrite Rmin_left; last nra.
      rewrite Rmax_right; last nra.
      intros x [Hx1 Hx2].
      case_decide; nra.
    }
  }
  { intro H; apply Classical_Prop.not_and_or in H.
    destruct H.
    { apply (ex_RInt_ext (fun _ => 0)); last apply ex_RInt_const.
      rewrite Rmin_left; last nra.
      rewrite Rmax_right; last nra.
      intros x [Hx1 Hx2].
      case_decide; nra.
    }
    { apply (ex_RInt_ext (fun _ => 1)); last apply ex_RInt_const.
      rewrite Rmin_left; last nra.
      rewrite Rmax_right; last nra.
      intros x [Hx1 Hx2].
      case_decide; nra.
    }
  }
Qed.

Lemma is_RInt_of_RInt F a b (ε : R) : ex_RInt F a b → RInt F a b = ε → is_RInt F a b ε.
Proof. intros Hex H; rewrite -H; apply RInt_correct; done. Qed.

Lemma RInt_of_is_RInt F a b (ε : R) : is_RInt F a b ε → RInt F a b = ε.
Proof.
  intro H.
  rewrite /RInt.
  apply iota_unique; last exact H.
  intros y Hy.
  rewrite -(is_RInt_unique F a b ε H).
  rewrite -(is_RInt_unique F a b y Hy).
  done.
Qed.

Lemma IndicatorLe_mul_func_Rmax (F : R -> R) (x y : R) :
  IndicatorLe x y * F (Rmax x y) = IndicatorLe x y * F y.
Proof.
  rewrite /IndicatorLe.
  case_decide.
  { rewrite Rmax_right; nra. }
  { rewrite Rmax_left; nra. }
Qed.



Lemma RInt_RInt_split_indicator (F : R -> R -> R) (HF : IsFubiniRR F 0 1 0 1) :
  RInt (fun y => RInt (fun x => F x y) 0 1) 0 1 =
  RInt (fun y => RInt (fun x => IndicatorLe x y * F x y) 0 1) 0 1 +
  RInt (fun y => RInt (fun x => IndicatorLe y x * F x y) 0 1) 0 1.
Proof.
  have Hplus := RInt_plus
    (λ y : R, RInt (λ x : R, IndicatorLe x y * F x y) 0 1)
    (λ y : R, RInt (λ x : R, IndicatorLe y x * F x y) 0 1)
    0 1.
  rewrite /plus//= in Hplus; rewrite -Hplus; last first.
  all: clear Hplus.
  { apply Fubini_Step_ex_x.
    (* Integral is integrable *) admit. }
  { (* Integral is integrable *) admit. }
  apply RInt_ext.
  rewrite Rmin_left; last nra.
  rewrite Rmax_right; last nra.
  intros x [Hx1 Hx2].
  (* Use Chasales to avoid the middle point *)
  rewrite -(RInt_Chasles (λ x0 : R, F x0 x) 0 x 1); first last.
  { (* integrability *) admit. }
  { (* integrability *) admit. }
  rewrite /plus//=.
  f_equal.
  { rewrite -(RInt_Chasles (λ x0 : R, IndicatorLe x0 x * F x0 x) 0 x 1) /plus//=; first last.
    { (* integrability *) admit. }
    { (* integrability *) admit. }
    replace (RInt (λ x0 : R, IndicatorLe x0 x * F x0 x) x 1) with (RInt (fun _ => 0) x 1); last first.
    { apply RInt_ext.
      rewrite Rmin_left; last nra.
      rewrite Rmax_right; last nra.
      intros y [Hy1 Hy2].
      rewrite IndicatorLe_gt; nra.
    }
    rewrite RInt_const /scal //= /mult //= Rmult_0_r Rplus_0_r.
    apply RInt_ext.
    rewrite Rmin_left; last nra.
    rewrite Rmax_right; last nra.
    intros y [Hy1 Hy2].
    rewrite IndicatorLe_le; nra.
  }
  { rewrite -(RInt_Chasles (λ x0 : R, IndicatorLe x x0 * F x0 x) 0 x 1) /plus//=; first last.
    { (* integrability *) admit. }
    { (* integrability *) admit. }
    replace (RInt (λ x0 : R, IndicatorLe x x0 * F x0 x) 0 x) with (RInt (fun _ => 0) 0 x); last first.
    { apply RInt_ext.
      rewrite Rmin_left; last nra.
      rewrite Rmax_right; last nra.
      intros y [Hy1 Hy2].
      rewrite IndicatorLe_gt; nra.
    }
    rewrite RInt_const /scal //= /mult //= Rmult_0_r Rplus_0_l.
    apply RInt_ext.
    rewrite Rmin_left; last nra.
    rewrite Rmax_right; last nra.
    intros y [Hy1 Hy2].
    rewrite IndicatorLe_le; nra.
  }
Admitted.

Lemma IndicatorLe_to_bounds (F : R -> R)  :
  RInt (λ y, RInt (λ x, IndicatorLe x y * F y) 0 1) 0 1 =
  RInt (fun y => RInt (fun x => F y) 0 y) 0 1.
Proof.
  apply RInt_ext.
  intros y [Hy1 Hy2].
  rewrite Rmin_left in Hy1; last nra.
  rewrite Rmax_right in Hy2; last nra.
  rewrite -(RInt_Chasles (λ x : R, IndicatorLe x y * F y) 0 y 1) /plus//=; first last.
  { apply ex_RInt_mult.
    { apply ex_RInt_IndicatorLe; nra. }
    { apply (ex_RInt_Chasles_2 (λ _ : R, F y) 0 y 1); first nra.
      apply ex_RInt_const. }
  }
  { apply ex_RInt_mult.
    { apply ex_RInt_IndicatorLe; nra. }
    { apply (ex_RInt_Chasles_1 (λ _ : R, F y) 0 y 1); first nra.
      apply ex_RInt_const. }
  }
  replace (RInt (λ x : R, IndicatorLe x y * F y) y 1) with (RInt (fun _ => 0) y 1); last first.
  { apply RInt_ext.
    intros x [Hx1 Hx2].
    rewrite Rmin_left in Hx1; last nra.
    rewrite Rmax_right in Hx2; last nra.
    rewrite IndicatorLe_gt; nra.
  }
  rewrite RInt_const /scal //= /mult //= Rmult_0_r Rplus_0_r.
  apply RInt_ext.
  intros x [Hx1 Hx2].
  rewrite Rmin_left in Hx1; last nra.
  rewrite Rmax_right in Hx2; last nra.
  rewrite IndicatorLe_le; nra.
Qed.




(* The triangle integral argument *)
(* NOTE: If we have to add more restrictions on F, I think that's fine.
   I believe the characterization argument in the continuous case rests the probabilites
   of each basis set (for the Borel sigma algebra: the open balls). Their indicator
   functions, which are what we would use for F, are piecewise smooth. *)
Lemma max_presample_RInt ε (F : R → R) (HF : ex_RInt F 0 1)
    (Hint : is_RInt (λ x : R, 2 * x * F x) 0 1 ε) :
    is_RInt (λ y : R, RInt (λ x : R, F (Rmax y x)) 0 1) 0 1 ε.
Proof.
  apply is_RInt_of_RInt.
  {

    (* Integral is integrable. Not sure if this is neccesary? *)  admit. }
  replace (RInt (λ y, RInt (λ x, F (Rmax y x)) 0 1) 0 1) with
          (RInt (λ y, RInt (λ x, F (Rmax x y)) 0 1) 0 1); last first.
  { do 2 (f_equal; apply functional_extensionality; intros ?). by rewrite Rmax_comm. }
  (*
  rewrite RInt_RInt_split_indicator.
  rewrite Rplus_comm weak_Fubini_bounded_integrable; first rewrite Rplus_comm; last first.
  { (* Fubini integrability hypothesis *) admit. }
  { (* Fubini boundedness *) admit. }
  replace
    (RInt (λ y, RInt (λ x, IndicatorLe x y * F (Rmax y x)) 0 1) 0 1) with
    (RInt (λ y, RInt (λ x, IndicatorLe x y * F (Rmax x y)) 0 1) 0 1); last first.
  { do 2 (f_equal; apply functional_extensionality; intros ?). by rewrite Rmax_comm. }
  rewrite Rplus_diag.
  replace
    (RInt (λ y, RInt (λ x, IndicatorLe x y * F (Rmax x y)) 0 1) 0 1) with
    (RInt (λ y, RInt (λ x, IndicatorLe x y * F y) 0 1) 0 1); last first.
  { do 2 (f_equal; apply functional_extensionality; intros ?).
    by rewrite IndicatorLe_mul_func_Rmax. }
  rewrite IndicatorLe_to_bounds.
  replace (RInt (λ y, RInt (λ _ : R, F y) 0 y) 0 1) with (RInt (λ y, y * F y) 0 1); last first.
  { f_equal; apply functional_extensionality; intros y.
    by rewrite RInt_const /scal //= /mult //= Rminus_0_r. }
  apply RInt_of_is_RInt in Hint; rewrite -Hint.
  have Hex : ex_RInt (λ y : R, y * F y) 0 1.
  { apply ex_RInt_mult; [apply ex_RInt_id | apply HF]. }
  have Hscal := RInt_scal (λ y : R, y * F y) 0 1 2 Hex.
  rewrite /scal //= /mult //= in Hscal.
  rewrite -Hscal.
  f_equal; apply functional_extensionality; intros ?; nra.
  *)
Admitted.

Lemma comp_max_integrability (r1 : R) (F : R → R) (H : ex_RInt F 0 1) (Hr1 : (0 <= r1 <= 1)%R) :
  ex_RInt (F ∘ Rmax r1) 0 1.
Proof.
  (* Integrability comes from piecewise continuity *)
  eapply ex_RInt_Chasles_0; first eapply Hr1.
  { apply (ex_RInt_ext (fun _ => F r1)); last by apply ex_RInt_const.
    intros x Hx; rewrite /compose//=. f_equal.
    rewrite Rmax_left; first done.
    destruct Hr1 as [A B].
    destruct Hx as [C D].
    rewrite Rmax_right in D; nra.
  }
  { apply (ex_RInt_ext F); last exact (ex_RInt_Chasles_2 F 0 r1 1 Hr1 H).
    intros x Hx; rewrite /compose//=. f_equal.
    rewrite Rmax_right; first done.
    destruct Hr1 as [A B].
    destruct Hx as [C D].
    rewrite Rmin_left in C; nra.
  }
Qed.

(* TODO: Can I reduce away the integrability of F? *)
Lemma wp_lazy_real_presample_max_adv_comp E e v1 v2 Φ (ε : R) (F : R -> R) (HF : ex_RInt F 0 1) :
  to_val e = None →
  (forall r, 0 <= r <= 1 → (0 <= F r)%R) ->
  is_RInt (fun x => 2 * x * F x)%R 0 1 ε →
  lazy_real_uninit v1 ∗
  lazy_real_uninit v2 ∗
  ↯ ε ∗
  (∀ r1 r2 : R, ↯ (F (Rmax r1 r2)%R) ∗ lazy_real v1 r1 ∗ lazy_real v2 r2 -∗ WP e @ E {{ Φ }})
    ⊢ WP e @ E {{ Φ }}.
Proof.
  (* First: do the proof but without the integration lemma to get the right form. *)
  iIntros (Hv Hr Hint) "(Hv1 & Hv2 & Hε & Hwp)".
  iDestruct "Hv1" as (l1 α1) "(-> & Hchunk1 & Htape1)".
  iDestruct "Hv2" as (l2 α2) "(-> & Hchunk2 & Htape2)".
  set ε1 : R → R := fun r => (RInt (F ∘ (Rmax r)) 0 1).
  set ε2 : R → R → R := fun x y => F (Rmax x y).
  wp_apply (wp_presample_unif_adv_comp _ _ α1 _ ε ε1 with "[-]"); first done.
  { intros x Hx.
    apply RInt_ge_0; first nra.
    { apply comp_max_integrability; done. }
    intros y Hy.
    apply Hr; constructor.
    { apply <- Rmax_Rle; nra. }
    { apply Rmax_lub; nra. }
  }
  { apply max_presample_RInt; done. }
  iFrame "∗".
  iIntros (r1) "(Hε & (% & Hα1 & %))".
  wp_apply (wp_presample_unif_adv_comp _ _ α2 _ (ε1 r1) (ε2 r1) with "[-]"); first done.
  { intros x Hx.
    apply Hr; constructor.
    { apply <- Rmax_Rle; nra. }
    { apply Rmax_lub; last nra.
      rewrite -H.
      have Hrange := seq_bin_to_R_range f.
      nra.
    }
  }
  { apply (RInt_correct (ε2 r1) 0 1).
    (* Integrability side condition *)
    unfold ε2.
    replace (λ y : R, F (Rmax r1 y)) with (F ∘ (Rmax r1)); last done.
    apply comp_max_integrability; first done.
    have Hrange := seq_bin_to_R_range f.
    nra. }
  iFrame.
  iIntros (r2) "(Hε & (% & Hα2 & %))".
  iApply ("Hwp" $! r1 r2); iSplitL "Hε"; first iFrame.
  iSplitL "Hchunk1 Hα1"; iFrame; iExists _; iPureIntro; split_and!; eauto.
Qed.

End max_lazy_real.
*)
