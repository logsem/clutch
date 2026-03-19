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
    2: {
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite -(RInt_Chasles _ 0 x 1).
      3: {
        apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
        intros ??.
        rewrite Iverson_False; OK.
        rewrite /Icc//=; OK.
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
      }
      2: {
        apply (ex_RInt_ext (fun y => F x)).
        2: { apply ex_RInt_const. }
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
        intros ??.
        rewrite Iverson_True; OK.
        { rewrite Rmax_left; OK. }
        rewrite /Icc//=; OK.
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
      }
      rewrite /plus//=.
      replace (RInt (λ y : R, Iverson (Icc 0 x) y * F (Rmax x y)) x 1) with 0.
      2: {
        rewrite (RInt_ext _ (fun _ => 0)).
        { rewrite RInt_const. rewrite /scal//=/mult//=; OK. }
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
        intros ??.
        rewrite Iverson_False/Icc//=; OK.
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
      }
      rewrite Rplus_0_r.
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite Iverson_True/Icc//=; OK.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
    }
    replace (RInt (λ x : R, RInt (λ y : R, Iverson (Icc x 1) y * F (Rmax x y)) 0 1) 0 1)
       with (RInt (λ x : R, RInt (λ y : R, F (Rmax x y)) x 1) 0 1).
    2: {
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite -(RInt_Chasles _ 0 x 1).
      2: {
        apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
        intros ??.
        rewrite Iverson_False; OK.
        rewrite /Icc//=; OK.
        rewrite Rmin_left; OK.
      }
      2: {
        apply (ex_RInt_ext (fun y => F y)).
        2: {
          apply (ex_RInt_Chasles_2 (V := R_CompleteNormedModule) _ 0 x 1); OK.
          apply PCts_RInt.
          done.
        }
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
        intros ??.
        rewrite Iverson_True; OK.
        { rewrite Rmax_right; OK. }
        rewrite /Icc//=; OK.
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
      }

      rewrite /plus//=.
      replace (RInt (λ y : R, Iverson (Icc x 1) y * F (Rmax x y)) 0 x) with 0.
      { rewrite Rplus_0_l.
        apply RInt_ext.
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
        intros ??.
        rewrite Iverson_True/Icc//=; OK.
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
      }
      rewrite (RInt_ext _ (fun y => 0)).
      { rewrite RInt_const. rewrite /scal//=/mult//=; OK. }
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite Iverson_False/Icc//=; OK.
      rewrite Rmin_left; OK.
    }

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
  replace (RInt (λ y : R, RInt (λ x : R, Iverson (Icc x 1) y * F (Rmax x y)) 0 1) 0 1)
     with (RInt (λ x : R, RInt (λ y : R, Iverson (Icc 0 x) y * F (Rmax x y)) 0 1) 0 1).
  2: {
    apply RInt_ext.
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    intros ??.
    apply RInt_ext.
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    intros ??.
    f_equal.
    2: { f_equal. by rewrite Rmax_comm. }
    rewrite /Iverson/Icc//=.
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    case_decide; case_decide; OK.
  }
  rewrite Rplus_diag.
  rewrite RInt_Rmult.
  2: {
    apply (ex_RInt_ext (λ x : R, RInt (λ y : R, F x) 0 x)).
    2: {
      replace (λ x : R, RInt (λ _ : R, F x) 0 x) with (λ x : R, x * F x).
      { apply ex_RInt_mult.
        { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
          intros ??.
          apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
          by auto_derive.
        }
        { apply PCts_RInt; OK. }
      }
      funexti.
      rewrite RInt_const.
      rewrite /scal//=/mult//=; OK.
    }
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    intros ??.
    rewrite -(RInt_Chasles _ 0 x 1).
    3: {
      apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite Iverson_False; OK.
      rewrite /Icc//=; OK.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
    }
    2: {
      apply (ex_RInt_ext (fun y => F x)).
      2: { apply ex_RInt_const. }
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite Iverson_True; OK.
      { rewrite Rmax_left; OK. }
      rewrite /Icc//=; OK.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
    }
    rewrite /plus//=.
    replace (RInt (λ y : R, Iverson (Icc 0 x) y * F (Rmax x y)) x 1) with 0.
    { rewrite Rplus_0_r.
      apply RInt_ext.
      rewrite Rmin_left; OK.
      rewrite Rmax_right; OK.
      intros ??.
      rewrite Iverson_True; OK.
      { rewrite Rmax_left; OK. }
      { rewrite /Icc//=; OK.
        rewrite Rmin_left; OK.
        rewrite Rmax_right; OK.
      }
    }
    rewrite (RInt_ext _ (fun _ : R => 0)).
    { rewrite RInt_const. rewrite /scal//=/mult//=; OK. }
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    intros ??.
    rewrite Iverson_False; OK.
    rewrite /Icc//=; OK.
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
  }
  apply RInt_ext.
  rewrite Rmin_left; OK.
  rewrite Rmax_right; OK.
  intros ??.
  rewrite (Rmult_comm _ 2).
  rewrite Rmult_assoc.
  f_equal.
  rewrite -(RInt_Chasles _ 0 x 1).
  3: {
    apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    intros ??.
    rewrite Iverson_False; OK.
    rewrite /Icc//=; OK.
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
  }
  2: {
    apply (ex_RInt_ext (fun y => F x)).
    2: { apply ex_RInt_const. }
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    intros ??.
    rewrite Iverson_True; OK.
    { rewrite Rmax_left; OK. }
    rewrite /Icc//=; OK.
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
  }
  rewrite /plus//=.
  replace (RInt (λ y : R, Iverson (Icc 0 x) y * F (Rmax x y)) 0 x) with (F x * x).
  2: {
    rewrite (RInt_ext _ (fun _ => F x)).
    {  rewrite RInt_const. rewrite /scal//=/mult//=; OK. }
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
    intros ??.
    rewrite Rmax_left; OK.
    rewrite Iverson_True; OK.
    rewrite /Icc//=.
    rewrite Rmin_left; OK.
    rewrite Rmax_right; OK.
  }
  rewrite (RInt_ext _ (fun _ => 0)).
  {  rewrite RInt_const. rewrite /scal//=/mult//=; OK. }
  rewrite Rmin_left; OK.
  rewrite Rmax_right; OK.
  intros ??.
  rewrite Iverson_False; OK.
  rewrite /Icc//=.
  rewrite Rmin_left; OK.
  rewrite Rmax_right; OK.
Qed.


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
