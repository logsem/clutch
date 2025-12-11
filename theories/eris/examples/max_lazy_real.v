From clutch.eris Require Export eris error_rules receipt_rules.
From clutch.eris Require Import presample_many.
From Coquelicot Require SF_seq Hierarchy.
From Coquelicot Require Import RInt RInt_analysis AutoDerive.
From clutch.eris Require Import infinite_tape lazy_real.
From clutch.eris.examples Require Import lazy_real indicators half_bern_neg_exp.
Set Default Proof Using "Type*".
#[local] Open Scope R.

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
