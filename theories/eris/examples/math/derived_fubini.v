From clutch.eris.examples.math Require Import prelude axioms iverson sets continuity2 piecewise improper limit_exchanges.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** Existence of iterated integral *)
Theorem Fubini_ex_y : ∀ {f xa xb ya yb}, FubiniCondition f xa xb ya yb →
  ex_RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.
Proof.
  intros ??????.
  apply Fubini_ex_x.
  rewrite /FubiniCondition in H.
  rewrite /FubiniCondition.
  intros ????.
  apply Continuity2_swap.
  apply H; done.
Qed.

(** FubiniCondition implies Integrability along horizontal lines *)
Theorem FubiniCondition_ex_RInt_x {f xa xb ya yb} :
  FubiniCondition f xa xb ya yb →
  ∀ y, Rmin ya yb <= y <= Rmax ya yb → ex_RInt (fun x => f x y) xa xb.
Proof.
  rewrite /FubiniCondition.
  intros ???.
  apply ex_RInt_continuous.
  intros ??.
  specialize H with z y.
  have W := (H H1 H0).
  apply (Continuity2_continuous_fst W).
Qed.

(** FubiniCondition implies Integrability along vertical lines *)
Theorem FubiniCondition_ex_RInt_y {f xa xb ya yb} :
  FubiniCondition f xa xb ya yb →
  ∀ x, Rmin xa xb <= x <= Rmax xa xb → ex_RInt (fun y => f x y) ya yb.
Proof.
  rewrite /FubiniCondition.
  intros ???.
  apply ex_RInt_continuous.
  intros ??.
  specialize H with x z.
  have W := (H H0 H1).
  apply (Continuity2_continuous_snd W).
Qed.


(** Fubini's theorem for piecewise continuous functions *)

(* Slice of 2D continuous function is integrable in x *)
Lemma ex_RInt_continuous_slice_x (f : R → R → R) y xa xb ya yb :
  Icc ya yb y →
  (∀ x, Icc xa xb x → Continuity2 (uncurry f) x y) →
  ex_RInt (fun x => f x y) xa xb.
Proof.
  intros ??.
  apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
  intros z Hz.
  apply (@Continuity2_continuous_fst (uncurry f) z y).
  apply H0.
  rewrite /Ioo//=.
Qed.


Lemma ex_RInt_continuous_slice_y (f : R → R → R) x xa xb ya yb :
  Icc xa xb x →
  (∀ y, Icc ya yb y → Continuity2 (uncurry f) x y) →
  ex_RInt (fun y => f x y) ya yb.
Proof.
  intros ??.
  apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
  intros z Hz.
  apply (@Continuity2_continuous_snd (uncurry f) x z).
  apply H0.
  rewrite /Ioo//=.
Qed.

(* Integrability of Iverson-masked continuous function in y *)
Lemma ex_RInt_Iverson_continuous_y (f : R → R → R) xa' xb' ya' yb' x ya yb :
  Icc xa' xb' x →
  (∀ y, Icc ya' yb' y → Continuity2 (uncurry f) x y) →
  ex_RInt (fun y => Iverson (Icc ya' yb') y * f x y) ya yb.
Proof.
  intros Hx Hcont.
  (* Reduce to the case where the bounds are in order *)
  suffices HH : ex_RInt (λ y : R, Iverson (Icc ya' yb') y * f x y) (Rmin ya yb) (Rmax ya yb).
  { destruct (Rle_lt_dec ya yb).
    { rewrite Rmin_left in HH; try lra.
      rewrite Rmax_right in HH; try lra.
      apply HH. }
    { rewrite Rmin_right in HH; try lra.
      rewrite Rmax_left in HH; try lra.
      apply ex_RInt_swap.
      apply HH. }
  }
  have LraLem1 : Rmin ya yb <= Rmax ya yb := Rminmax _ _.
  have LraLem2 : Rmin ya' yb' <= Rmax ya' yb' := Rminmax _ _.

  (* Trivial: Upper bound of indicator is le lower bound of integral *)
  destruct (Rle_lt_dec (Rmax ya' yb') (Rmin ya yb)).
  { apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
    rewrite Rmin_left; try lra.
    rewrite Rmax_right; try lra.
    intros ??.
    rewrite /Icc//=.
    rewrite Iverson_False; try lra.
  }

  (* Trivial: Lower bound of indicator is le upper bound of integral *)
  destruct (Rle_lt_dec (Rmin ya' yb') (Rmax ya yb)).
  2: {
    apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
    rewrite Rmin_left; try lra.
    rewrite Rmax_right; try lra.
    intros ??.
    rewrite /Icc//=.
    rewrite Iverson_False; try lra.
  }

  (* Case on the lower bound of the indicator being in range.*)
  destruct (Rle_lt_dec (Rmin ya' yb') (Rmin ya yb));
  destruct (Rle_lt_dec (Rmax ya' yb') (Rmax ya yb)).
  { (* Case: ---____ *)
    apply (ex_RInt_Chasles_0 _ _ (Rmax ya' yb') _).
    { split; lra. }
    { apply (ex_RInt_ext (fun y => f x y)).
      { rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros ??.
        rewrite Iverson_True; try lra.
        rewrite /Icc//=. lra.
      }
      { apply (ex_RInt_continuous_slice_y _ _ _ _ _ _ Hx).
        rewrite /Icc.
        rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros ??.
        apply Hcont.
        rewrite /Icc.
        lra.
      }
    }
    { apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
      rewrite Rmin_left; try lra.
      rewrite (Rmax_right (Rmax ya' yb') (Rmax ya yb)); try lra.
      intros ??.
      rewrite Iverson_False; try lra.
      rewrite /Icc//=. lra.
    }
  }
  { (* Case: ------- *)
    apply (ex_RInt_ext (fun y => f x y)).
    {
      rewrite Rmin_left; try lra.
      rewrite (Rmax_right); try lra.
      intros ??.
      rewrite Iverson_True; try lra.
      rewrite /Icc//=. lra.
    }
    { apply (ex_RInt_continuous_slice_y _ _ _ _ _ _ Hx).
      rewrite /Icc.
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      apply Hcont.
      rewrite /Icc.
      lra.
    }
  }

  { (* Case : __----__*)
    apply (ex_RInt_Chasles_0 _ _ (Rmin ya' yb') _).
    { split; try lra. }
    { apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      rewrite Iverson_False; try lra.
      rewrite /Icc//=. lra.
    }
    apply (ex_RInt_Chasles_0 _ _ (Rmax ya' yb') _).
    { split; try lra.  }
    { apply (ex_RInt_ext (fun y => f x y)).
      { rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros ??.
        rewrite Iverson_True; try lra.
        rewrite /Icc//=. lra.
      }
      apply (ex_RInt_continuous_slice_y _ _ _ _ _ _ Hx).
      rewrite /Icc.
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      apply Hcont.
      rewrite /Icc.
      lra.
    }
    { apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
      rewrite Rmin_left; try lra.
      rewrite (Rmax_right (Rmax ya' yb') (Rmax ya yb)); try lra.
      intros ??.
      rewrite Iverson_False; try lra.
      rewrite /Icc//=. lra.
    }
  }
  { (* Case: ____---- *)
    apply (ex_RInt_Chasles_0 _ _ (Rmin ya' yb') _).
    { split; lra. }
    { apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      rewrite Iverson_False; try lra.
      rewrite /Icc//=. lra.
    }
    { apply (ex_RInt_ext (fun y => f x y)).
      { rewrite Rmin_left; try lra.
        rewrite (Rmax_right) ; try lra.
        intros ??.
        rewrite Iverson_True; try lra.
        rewrite /Icc//=.
        split; try lra.
      }
      apply (ex_RInt_continuous_slice_y _ _ _ _ _ _ Hx).
      rewrite /Icc.
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      apply Hcont.
      rewrite /Icc.
      lra.
    }
  }
Qed.


(* Integrability of Iverson-masked continuous function in y *)
(* Reduce to the continuous_y case instead of duplicating that horrifying proof *)
Lemma ex_RInt_Iverson_continuous_x (f : R → R → R) xa' xb' ya' yb' y xa xb :
  Icc ya' yb' y →
  (∀ x, Icc xa' xb' x → Continuity2 (uncurry f) x y) →
  ex_RInt (fun x => Iverson (Icc xa' xb') x * f x y) xa xb.
Proof.
  intros ??.
  apply (@ex_RInt_Iverson_continuous_y (fun x' y' => f y' x') _ _ _ _ _ _ _ H).
  intros z Hz.
  apply Continuity2_swap.
  exact (H0 z Hz).
Qed.

(* Integrability of a single rectangle function in y for fixed x *)
Lemma RectFun_RR_ex_RInt_y (rect : (R → R → R) * R * R * R * R) x ya yb :
  RectFun_continuity rect →
  ex_RInt (fun y => RectFun_RR rect x y) ya yb.
Proof.
  intros Hcont.
  destruct rect as [[[[f xa'] xb'] ya'] yb'].
  unfold RectFun_RR.
  (* Cases on if x is in the first interval *)
  destruct (decide (Icc xa' xb' x)) as [Hx | Hx].
  2: { apply (@ex_RInt_ext _ (fun y => 0)).
    { intros y _. rewrite (Iverson_False Hx). lra. }
    apply ex_RInt_const.
  }
  { apply (@ex_RInt_ext _ (fun y => Iverson (Icc ya' yb') y * f x y)).
    { intros y _. rewrite (Iverson_True Hx). lra. }
    eapply @ex_RInt_Iverson_continuous_y.
    { exact Hx. }
    { intros y Hy. apply Hcont; done. }
  }
Qed.

(* Integrability of a single rectangle function in x for fixed y *)
Lemma RectFun_RR_ex_RInt_x (rect : (R → R → R) * R * R * R * R) y xa xb :
  RectFun_continuity rect →
  ex_RInt (fun x => RectFun_RR rect x y) xa xb.
Proof.
  intros Hcont.
  destruct rect as [[[[f xa'] xb'] ya'] yb'].
  unfold RectFun_RR.
  destruct (decide (Icc ya' yb' y)) as [Hy | Hy].
  { apply (@ex_RInt_ext _ (fun x => Iverson (Icc xa' xb') x * f x y)).
    { intros x _. rewrite (Iverson_True Hy). lra. }
    eapply ex_RInt_Iverson_continuous_x.
    { exact Hy. }
    { intros x Hx. apply Hcont; done. }
  }
  { apply (@ex_RInt_ext _ (fun x => 0)).
    { intros x _. rewrite (Iverson_False Hy). lra. }
    apply ex_RInt_const.
  }
Qed.

(* Integrability of fsum2 in y for fixed x *)
Lemma fsum2_RectFun_ex_RInt_y (L : list ((R → R → R) * R * R * R * R)) x ya yb :
  Forall RectFun_continuity L →
  ex_RInt (fun y => fsum2 (RectFun_RR <$> L) x y) ya yb.
Proof.
  induction L.
  { simpl. intros ?. apply ex_RInt_const. }
  intros H.
  apply (@ex_RInt_ext _ (λ y : R, RectFun_RR a x y + fsum2 (RectFun_RR <$> L) x y)).
  { intros ??. rewrite /fmap//=. }
  apply (ex_RInt_plus (V := R_CompleteNormedModule)).
  { apply RectFun_RR_ex_RInt_y. by eapply Forall_inv. }
  { apply IHL. by eapply Forall_inv_tail. }
Qed.

(* Integrability of fsum2 in x for fixed y *)
Lemma fsum2_RectFun_ex_RInt_x (L : list ((R → R → R) * R * R * R * R)) y xa xb :
  Forall RectFun_continuity L →
  ex_RInt (fun x => fsum2 (RectFun_RR <$> L) x y) xa xb.
Proof.
  induction L.
  { simpl. intros ?. apply ex_RInt_const. }
  intros H.
  apply (@ex_RInt_ext _ (λ x : R, RectFun_RR a x y + fsum2 (RectFun_RR <$> L) x y)).
  { intros ??. rewrite /fmap//=. }
  apply (ex_RInt_plus (V := R_CompleteNormedModule)).
  { apply RectFun_RR_ex_RInt_x. by eapply Forall_inv. }
  { apply IHL. by eapply Forall_inv_tail. }
Qed.

(* Key lemma: integrability for a single rectangle function *)
Lemma RectFun_RR_ex_RInt_iterated_x (rect : (R → R → R) * R * R * R * R) xa xb ya yb :
  RectFun_continuity rect →
  ex_RInt (fun x => RInt (fun y => RectFun_RR rect x y) ya yb) xa xb.
Proof.
  destruct rect as [[[[f xa'] xb'] ya'] yb'].
  rewrite /RectFun_continuity//=.
  intros H.
  suffices HH : ex_RInt (λ x : R, RInt (λ y : R, Iverson (Icc xa' xb') x * Iverson (Icc ya' yb') y * f x y) ya yb) (Rmin xa xb) (Rmax xa xb).
  { destruct (Rle_lt_dec xa xb).
    { rewrite Rmin_left in HH; try lra.
      rewrite Rmax_right in HH; try lra.
      apply HH. }
    { rewrite Rmin_right in HH; try lra.
      rewrite Rmax_left in HH; try lra.
      apply ex_RInt_swap.
      apply HH. }
  }





  (* Start by cases on x *)




  (* Also just a big case proof I think (ugh!) *)
Admitted.

Lemma RectFun_RR_ex_RInt_iterated_y (rect : (R → R → R) * R * R * R * R) xa xb ya yb :
  RectFun_continuity rect →
  ex_RInt (fun y => RInt (fun x => RectFun_RR rect x y) xa xb) ya yb.
Proof.
Admitted.

(* Key lemma: Fubini for a single rectangle function *)
Lemma RectFun_RR_Fubini (rect : (R → R → R) * R * R * R * R) xa xb ya yb :
  RectFun_continuity rect →
  RInt (fun x => RInt (fun y => RectFun_RR rect x y) ya yb) xa xb =
  RInt (fun y => RInt (fun x => RectFun_RR rect x y) xa xb) ya yb.
Proof.
Admitted.

(* Helper lemma: integrability for lists of rectangle functions *)
Lemma fsum2_RectFun_ex_x (L : list ((R → R → R) * R * R * R * R)) xa xb ya yb :
  Forall RectFun_continuity L →
  ex_RInt (fun x => RInt (fun y => fsum2 (RectFun_RR <$> L) x y) ya yb) xa xb.
Proof.
  intros HL.
  induction L as [| rect L IH]; simpl.
  { apply ex_RInt_const. }
  apply (@ex_RInt_ext _ (fun x => RInt (fun y => RectFun_RR rect x y) ya yb + RInt (fun y => fsum2 (RectFun_RR <$> L) x y) ya yb)).
  { intros x _. rewrite RInt_plus.
    { reflexivity. }
    { apply RectFun_RR_ex_RInt_y. apply Forall_inv in HL. exact HL. }
    { apply fsum2_RectFun_ex_RInt_y.  apply Forall_inv_tail in HL. exact HL. } }
  apply (ex_RInt_plus (V := R_CompleteNormedModule)).
  { apply RectFun_RR_ex_RInt_iterated_x. apply Forall_inv in HL. exact HL. }
  { apply IH. apply Forall_inv_tail in HL. exact HL. }
Qed.

(* Helper lemma: integrability for lists in y-direction *)
Lemma fsum2_RectFun_ex_y (L : list ((R → R → R) * R * R * R * R)) xa xb ya yb :
  Forall RectFun_continuity L →
  ex_RInt (fun y => RInt (fun x => fsum2 (RectFun_RR <$> L) x y) xa xb) ya yb.
Proof.
  intros HL.
  induction L as [| rect L IH]; simpl.
  { apply ex_RInt_const. }
  apply (@ex_RInt_ext _ (fun y => RInt (fun x => RectFun_RR rect x y) xa xb + RInt (fun x => fsum2 (RectFun_RR <$> L) x y) xa xb)).
  { intros y _. rewrite RInt_plus.
    { reflexivity. }
    { apply RectFun_RR_ex_RInt_x. apply Forall_inv in HL. exact HL. }
    { apply fsum2_RectFun_ex_RInt_x. apply Forall_inv_tail in HL. exact HL. } }
  apply (ex_RInt_plus (V := R_CompleteNormedModule)).
  { apply RectFun_RR_ex_RInt_iterated_y. apply Forall_inv in HL. exact HL. }
  { apply IH. apply Forall_inv_tail in HL. exact HL. }
Qed.

Lemma Fubini_Step_ex_x {f xa xb ya yb} : PCts2 f xa xb ya yb →
  ex_RInt (fun x => RInt (fun y => f x y) ya yb) xa xb.
Proof.
  intros [L H].
  apply (@ex_RInt_ext _ (fun x => RInt (fun y => fsum2 (RectFun_RR <$> L) x y) ya yb)).
  { intros x Hx. apply RInt_ext. intros y Hy.
    destruct (H x y) as [Heq _]. symmetry. apply Heq.
    { rewrite /Icc; lra. }
    { rewrite /Icc; lra. }
  }
  destruct (H xa ya) as [_ HL].
  apply fsum2_RectFun_ex_x. exact HL.
Qed.

Lemma Fubini_Step_ex_y {f xa xb ya yb} : PCts2 f xa xb ya yb →
  ex_RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.
Proof.
  intros [L H].
  apply (@ex_RInt_ext _ (fun y => RInt (fun x => fsum2 (RectFun_RR <$> L) x y) xa xb)).
  { intros y Hy. apply RInt_ext. intros x Hx.
    destruct (H x y) as [Heq _]. symmetry. apply Heq; rewrite /Icc; lra. }
  destruct (H xa ya) as [_ HL].
  apply fsum2_RectFun_ex_y. exact HL.
Qed.


Lemma fsum2_Fubini (L : list ((R → R → R) * R * R * R * R)) xa xb ya yb :
  Forall RectFun_continuity L →
  RInt (fun x => RInt (fun y => fsum2 (RectFun_RR <$> L) x y) ya yb) xa xb =
  RInt (fun y => RInt (fun x => fsum2 (RectFun_RR <$> L) x y) xa xb) ya yb.
Proof.
  intros HL.
  induction L as [| rect L IH].
  - simpl. rewrite /fsum2. simpl. rewrite !RInt_const. rewrite /scal /= /mult /=. lra.
  - simpl. rewrite /fmap. simpl.
    rewrite (RInt_ext (fun x => RInt (fun y => RectFun_RR rect x y + fsum2 (RectFun_RR <$> L) x y) ya yb) (fun x => RInt (fun y => RectFun_RR rect x y) ya yb + RInt (fun y => fsum2 (RectFun_RR <$> L) x y) ya yb) xa xb).
    2: { intros x Hx. rewrite RInt_plus. { reflexivity. } { apply RectFun_RR_ex_RInt_y. apply Forall_inv in HL. exact HL. } { apply fsum2_RectFun_ex_RInt_y. apply Forall_inv_tail in HL. exact HL. } }
    rewrite (RInt_ext (fun y => RInt (fun x => RectFun_RR rect x y + fsum2 (RectFun_RR <$> L) x y) xa xb) (fun y => RInt (fun x => RectFun_RR rect x y) xa xb + RInt (fun x => fsum2 (RectFun_RR <$> L) x y) xa xb) ya yb).
    2: { intros y Hy. rewrite RInt_plus. { reflexivity. } { apply RectFun_RR_ex_RInt_x. apply Forall_inv in HL. exact HL. } { apply fsum2_RectFun_ex_RInt_x. apply Forall_inv_tail in HL. exact HL. } }
    rewrite (RInt_plus (V := R_CompleteNormedModule) (fun x => RInt (fun y => RectFun_RR rect x y) ya yb) (fun x => RInt (fun y => fsum2 (RectFun_RR <$> L) x y) ya yb) xa xb).
    2: { apply RectFun_RR_ex_RInt_iterated_x. apply Forall_inv in HL. exact HL. }
    2: { apply fsum2_RectFun_ex_x. apply Forall_inv_tail in HL. exact HL. }
    rewrite (RInt_plus (V := R_CompleteNormedModule) (fun y => RInt (fun x => RectFun_RR rect x y) xa xb) (fun y => RInt (fun x => fsum2 (RectFun_RR <$> L) x y) xa xb) ya yb).
    2: { apply RectFun_RR_ex_RInt_iterated_y. apply Forall_inv in HL. exact HL. }
    2: { apply fsum2_RectFun_ex_y. apply Forall_inv_tail in HL. exact HL. }
    rewrite /plus /=. f_equal.
    + apply RectFun_RR_Fubini. apply Forall_inv in HL. exact HL.
    + apply IH. apply Forall_inv_tail in HL. exact HL.
Qed.

Lemma Fubini_Step_eq : ∀ {f xa xb ya yb}, PCts2 f xa xb ya yb →
  RInt (fun x => RInt (fun y => f x y) ya yb) xa xb = RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.
Proof.
  intros f xa xb ya yb [L H].
  rewrite (RInt_ext (fun x => RInt (fun y => f x y) ya yb) (fun x => RInt (fun y => fsum2 (RectFun_RR <$> L) x y) ya yb) xa xb).
  2: { intros x Hx. apply RInt_ext. intros y Hy. destruct (H x y) as [Heq _]. apply Heq; rewrite /Icc; lra. }
  rewrite (RInt_ext (fun y => RInt (fun x => f x y) xa xb) (fun y => RInt (fun x => fsum2 (RectFun_RR <$> L) x y) xa xb) ya yb).
  2: { intros y Hy. apply RInt_ext. intros x Hx. destruct (H x y) as [Heq _]. apply Heq; rewrite /Icc; lra. }
  apply fsum2_Fubini.
  destruct (H xa ya) as [_ HL]. exact HL.
Qed.


(*

(** Fubini's theorem holds for improper integrals of continuous functions *)

Definition IFubiniCondition_x (f : R → R → R) (ya yb : R) :=
  ∀ x y, Rmin ya yb <= y <= Rmax ya yb →
  Continuity2 (uncurry f) x y.

Definition IFubiniCondition_y (f : R → R → R) (xa xb : R) :=
  ∀ x y, Rmin xa xb <= x <= Rmax xa xb →
  Continuity2 (uncurry f) x y.

Lemma IFubini_Fubini_x {f xa xb ya yb} : IFubiniCondition_x f ya yb → FubiniCondition f xa xb ya yb.
Proof. intros H ????. apply H; lra. Qed.

Lemma IFubini_x_Ioo {f xa xb ya yb} :
  IFubiniCondition_x f ya yb <-> FubiniCondition (fun x y => Iverson (Ioo ya yb) y *  f x y) xa xb ya yb.
Proof.
  (* The indicator is constant 1 on a neighbourhood of (x, y) *)
A dmitted.

Lemma IFubini_y_Ioo {f xa xb ya yb} :
  IFubiniCondition_y f xa xb <-> FubiniCondition (fun x y => Iverson (Ioo xa xb) x * f x y) xa xb ya yb.
Proof.
  (* The indicator is constant 1 on a neighbourhood of (x, y) *)
A dmitted.

Lemma IFubini_Fubini_y {f xa xb ya yb} : IFubiniCondition_y f xa xb → FubiniCondition f xa xb ya yb.
Proof. intros H ????. apply H; lra. Qed.

Theorem FubiniImproper_ex_x {f xa ya yb} (H : IFubiniCondition_x f ya yb)
  (Hunif :
    filterlim (λ xb y : R, RInt (λ x : R, Iverson (Ioo ya yb) y * f x y) xa xb) (Rbar_locally Rbar.p_infty)
          (locally (λ y : R, RInt_gen (λ x : R, Iverson (Ioo ya yb) y * f x y) (at_point xa) (Rbar_locally Rbar.p_infty)))) :
  ex_RInt_gen (fun x => RInt (fun y => f x y) ya yb) (at_point xa) (Rbar_locally Rbar.p_infty).
Proof.
  (* Reduce to indicator version using extensionality *)
  apply (ex_RInt_gen_ext_eq_Ici (f := λ x, RInt (λ y, Iverson (Ioo ya yb) y * f x y) ya yb)).
  { intros x Hx. apply RInt_ext. intros y Hy.
    rewrite /Iverson. case_decide; [lra | exfalso; rewrite /Ioo//= in H0; lra]. }

  (* Prove existence using uniform convergence *)
  unfold ex_RInt_gen.
  exists (RInt (λ y : R, RInt_gen (λ x : R, Iverson (Ioo ya yb) y * f x y) (at_point xa) (Rbar_locally Rbar.p_infty)) ya yb).

  (* Use is_RInt_gen_filterlim *)
  apply is_RInt_gen_filterlim.
  { intros xb. apply Fubini_ex_x. apply IFubini_x_Ioo. apply H. }

  (* Rewrite LHS using Fubini for finite integrals *)
  replace (λ b : R, RInt (λ x : R, RInt (λ y : R, Iverson (Ioo ya yb) y * f x y) ya yb) xa b)
     with (λ b : R, RInt (λ y : R, RInt (λ x : R, Iverson (Ioo ya yb) y * f x y) xa b) ya yb).
  2: { apply functional_extensionality. intros xb. rewrite -Fubini_eq; try lra.
       apply IFubini_x_Ioo. apply H. }

  (* Apply Exchange2 to get limit interchange *)
  apply (@Exchange2 (λ xb y : R, RInt (λ x : R, Iverson (Ioo ya yb) y * f x y) xa xb) ya yb
                    (λ y : R, RInt_gen (λ x : R, Iverson (Ioo ya yb) y * f x y) (at_point xa) (Rbar_locally Rbar.p_infty))).
  { intros xb. apply Fubini_ex_y. apply IFubini_x_Ioo. apply H. }
  apply Hunif.
Qed.

(* Helper lemma: extract pointwise convergence from uniform convergence *)
Lemma filterlim_locally_eval {A : Type} {F : R → A → R} {G : A → R} {a : A} :
  filterlim F (Rbar_locally Rbar.p_infty) (locally G) →
  filterlim (λ r, F r a) (Rbar_locally Rbar.p_infty) (locally (G a)).
Proof.
  intro H. intros P HP.
  destruct HP as [eps Heps].
  unfold filtermap.
  apply (H (fun g => P (g a))).
  exists eps. intros g Hg.
  apply Heps.
  unfold fct_ball in Hg.
  apply Hg.
Qed.

(* Helper lemma: uniform limits of integrable functions are integrable *)
Lemma ex_RInt_filterlim_uniform {a b : R} {F : R → R → R} {G : R → R} :
  (∀ r, ex_RInt (F r) a b) →
  filterlim F (Rbar_locally Rbar.p_infty) (locally G) →
  ex_RInt G a b.
Proof.
  intros Hex Hunif.
  have HL := Exchange2 Hex Hunif.
  unfold ex_RInt.
  exists (RInt G a b).
  have H (r : R) : is_RInt (F r) a b (RInt (F r) a b)
    by apply (RInt_correct (V := R_CompleteNormedModule)), Hex.
  destruct (filterlim_RInt F a b (Rbar_locally Rbar.p_infty)
    (Rbar_locally_filter Rbar.p_infty) _ _ H Hunif) as [I [HLI HF]].
  have Heq : I = RInt G a b by apply filterlim_locally_unique with (1 := HLI) (2 := HL); apply Rbar_locally_filter.
  rewrite -Heq. exact HF.
Qed.

Theorem FubiniImproper_ex_y {f xa ya yb} (H : IFubiniCondition_x f ya yb)
  (Hunif : filterlim (λ xb y : R, RInt (λ x : R, Iverson (Ioo ya yb) y * f x y) xa xb) (Rbar_locally Rbar.p_infty)
                     (locally (λ y : R, RInt_gen (λ x : R, Iverson (Ioo ya yb) y * f x y) (at_point xa) (Rbar_locally Rbar.p_infty)))) :
  ex_RInt (fun y => (RInt_gen (fun x => f x y) (at_point xa) (Rbar_locally Rbar.p_infty))) ya yb.
Proof.
  (* Reduce to indicator version using extensionality *)
  apply (@ex_RInt_ext _ (λ y : R, RInt_gen (λ x : R, Iverson (Ioo ya yb) y * f x y) (at_point xa) (Rbar_locally Rbar.p_infty))).
  - intros y Hy.
    (* For y in (ya, yb), the indicator is 1 on [xa, ∞) *)
    apply RInt_gen_ext_eq_Ici.
    { intros x Hx. rewrite /Iverson. case_decide; [lra | exfalso; rewrite /Ioo//= in H0; lra]. }
    (* Existence follows from pointwise application of Hunif *)
    unfold ex_RInt_gen.
    exists (RInt_gen (λ x : R, Iverson (Ioo ya yb) y * f x y) (at_point xa) (Rbar_locally Rbar.p_infty)).
    apply is_RInt_gen_filterlim.
    { intros xb. apply (@FubiniCondition_ex_RInt_x (λ x y0, Iverson (Ioo ya yb) y0 * f x y0) xa xb ya yb).
      { apply IFubini_x_Ioo. done. }
      { lra. } }
    (* Extract pointwise convergence from uniform: apply Hunif at fixed y *)
    apply (filterlim_locally_eval (F := λ xb y0, RInt (λ x, Iverson (Ioo ya yb) y0 * f x y0) xa xb)
                                   (G := λ y0, RInt_gen (λ x, Iverson (Ioo ya yb) y0 * f x y0) (at_point xa) (Rbar_locally Rbar.p_infty))
                                   (a := y)).
    apply Hunif.
  - (* Show the indicator version is integrable using uniform convergence *)
    apply (ex_RInt_filterlim_uniform (F := λ xb y, RInt (λ x, Iverson (Ioo ya yb) y * f x y) xa xb)).
    { intros r. apply Fubini_ex_y. apply IFubini_x_Ioo. done. }
    apply Hunif.
Qed.

Theorem FubiniImproper_eq_x {f xa ya yb} (H : IFubiniCondition_x f ya yb)
  (Hcauchy :  filterlim (λ xb y : R, RInt (λ x : R, Iverson (Ioo ya yb) y * f x y) xa xb) (Rbar_locally Rbar.p_infty)
                (locally (λ y : R, RInt_gen (λ x : R, Iverson (Ioo ya yb) y * f x y) (at_point xa) (Rbar_locally Rbar.p_infty)))) :
  RInt_gen (fun x => RInt (fun y => f x y) ya yb) (at_point xa) (Rbar_locally Rbar.p_infty) =
  RInt (fun y => (RInt_gen (fun x => f x y) (at_point xa) (Rbar_locally Rbar.p_infty))) ya yb.
Proof.

  suffices Hred :
    RInt_gen (fun x => RInt (fun y => Iverson (Ioo ya yb) y * f x y) ya yb) (at_point xa) (Rbar_locally Rbar.p_infty) =
    RInt (fun y => (RInt_gen (fun x => Iverson (Ioo ya yb) y * f x y) (at_point xa) (Rbar_locally Rbar.p_infty))) ya yb.
  {
    have -> : (λ x : R, RInt (λ y : R, f x y) ya yb) = (λ x : R, RInt (λ y : R, Iverson (Ioo ya yb) y * f x y) ya yb).
    { apply functional_extensionality. intros x. apply RInt_ext. intros y Hy.
      rewrite /Iverson. case_decide; [lra | exfalso; rewrite /Ioo//= in H0; lra]. }
    rewrite (RInt_ext (λ y : R, RInt_gen (λ x : R, f x y) (at_point xa) (Rbar_locally Rbar.p_infty))
                       (λ y : R, RInt_gen (λ x : R, Iverson (Ioo ya yb) y * f x y) (at_point xa) (Rbar_locally Rbar.p_infty))
                       ya yb).
    2: { intros y Hy. f_equal. apply functional_extensionality. intros x.
         rewrite /Iverson. case_decide; [lra | exfalso; rewrite /Ioo//= in H0; lra]. }
    apply Hred.
  }

  (* Reuce this by changing f to be f times an indictor *)
  rewrite filterlim_RInt_gen.
  2: {
    intros xb.
    apply Fubini_ex_x.
    apply IFubini_x_Ioo.
    apply H.
  }
  replace (RInt (λ y : R, RInt_gen (λ x : R, Iverson (Ioo ya yb) y * f x y) (at_point xa) (Rbar_locally Rbar.p_infty)) ya yb)
     with (RInt (λ y : R, iota (λ IF : R, filterlim (λ b : R, RInt (λ x : R, Iverson (Ioo ya yb) y * f x y) xa b) (Rbar_locally Rbar.p_infty) (locally IF))) ya yb).
  2: {
    apply RInt_ext.
    intros y Hy.
    symmetry; apply filterlim_RInt_gen.
    intros xb.
    eapply (@FubiniCondition_ex_RInt_x (λ x y, Iverson (Ioo ya yb) y * f x y) xa xb ya yb).
    2: lra.
    apply IFubini_x_Ioo.
    apply H.
  }
  apply @iota_filterlim_locally.
  { apply Proper_StrongProper. apply Rbar_locally_filter. }
  (* Apply Definite/Definite Fubini *)
  replace (λ xb : R, RInt (λ x : R, RInt (λ y : R, Iverson (Ioo ya yb) y * f x y) ya yb) xa xb)
    with  (λ xb : R, RInt (λ y : R, RInt (λ x : R, Iverson (Ioo ya yb) y * f x y) xa xb) ya yb).
  2: { apply functional_extensionality. intros xb. rewrite -Fubini_eq; try lra.
    apply IFubini_x_Ioo.
    apply H.
  }
  apply (@Exchange2 (λ xb y : R, RInt (λ x : R, Iverson (Ioo ya yb) y * f x y) xa xb) ya yb
    (λ y : R, iota (λ IF : R, filterlim (λ b : R, RInt (λ x : R, Iverson (Ioo ya yb) y * f x y) xa b) (Rbar_locally Rbar.p_infty) (locally IF)))).
  { intros xb. apply Fubini_ex_y.
    apply IFubini_x_Ioo.
    apply H.
  }

  replace (λ y : R, iota (λ IF : R, filterlim (λ b : R, RInt (λ x : R, Iverson (Ioo ya yb) y * f x y) xa b) (Rbar_locally Rbar.p_infty) (locally IF)))
     with (λ y : R, RInt_gen (λ x : R, Iverson (Ioo ya yb) y * f x y) (at_point xa) (Rbar_locally Rbar.p_infty)).
  { apply Hcauchy. }

  apply functional_extensionality. intros y.
  apply filterlim_RInt_gen.
  intros xb.
  apply (@IFubini_x_Ioo _ xa xb) in H.
  rewrite /Iverson.
  case_decide.
  2: {
    replace (λ x : R, 0 * f x y) with (λ x : R, 0) by (apply functional_extensionality; intros ?; lra).
    apply ex_RInt_const.
  }
  1: {
    replace (λ x : R, 1 * f x y) with (λ x : R, f x y) by (apply functional_extensionality; intros ?; lra).
    eapply (@FubiniCondition_ex_RInt_x _ _ _ ya yb).
    2: {  rewrite /Ioo//= in H0. lra. }
    rewrite -IFubini_x_Ioo in H.
    by apply IFubini_Fubini_x.
  }
Qed.

Theorem FubiniImproper_Series {f UB L}
  (HexU : Series.ex_series UB)
  (Hub : forall x n, Rabs (f n x) <= UB n)
  (Hex : ∀ n, ex_RInt_gen (f n) (at_point L) (Rbar_locally Rbar.p_infty)) :
  RInt_gen (λ x : R, SeriesC (λ n : nat, f n x)) (at_point L) (Rbar_locally Rbar.p_infty) =
  SeriesC (λ n : nat, RInt_gen (λ x : R, f n x) (at_point L) (Rbar_locally Rbar.p_infty)).
Proof.
  (* Step 2: Establish that for each n, the finite integral exists *)
  have Hex_n : ∀ n b, ex_RInt (f n) L b.
  { intros n b.
    (* We need continuity or local integrability assumptions.
       Ex_RInt_gen alone doesn't guarantee ex_RInt on finite intervals without regularity. *)
    a dmit. }

  (* Step 1: Establish that for each b, the finite integral of the series exists *)
  have Hex_finite : ∀ b, ex_RInt (λ x, SeriesC (λ n, f n x)) L b.
  { a dmit. }

  (* Step 3: Exchange finite integral and series at each cutoff b
     RInt (λ x, SeriesC (λ n, f n x)) L b = SeriesC (λ n, RInt (f n) L b) *)
  have Hfubini_finite : ∀ b, L < b →
    RInt (λ x, SeriesC (λ n, f n x)) L b = SeriesC (λ n, RInt (f n) L b).
  { intros b Hb. a dmit. }

  (* Step 4: The series of improper integrals converges *)
  have Hex_series_improper : ex_seriesC (λ n, RInt_gen (f n) (at_point L) (Rbar_locally Rbar.p_infty)).
  { have HexU' : ex_seriesC UB. { rewrite -ex_seriesC_nat. apply HexU. }
    (* Need to show: |RInt_gen (f n) ...| <= C * UB(n) for some constant C.
       This requires bounding the integral by the L^infinity norm times the measure. *)
    a dmit. }

  (* Step 5: The improper integral of the series exists *)
  have Hex_improper_series : ex_RInt_gen (λ x, SeriesC (λ n, f n x)) (at_point L) (Rbar_locally Rbar.p_infty).
  { (* This follows from monotone/dominated convergence: the partial sums converge
       pointwise and are bounded by SeriesC UB. *)
    a dmit. }

  (* Step 7: Compute LHS using filterlim_RInt_gen *)
  have HLHS : RInt_gen (λ x, SeriesC (λ n, f n x)) (at_point L) (Rbar_locally Rbar.p_infty) =
              iota (λ I, filterlim (λ b, RInt (λ x, SeriesC (λ n, f n x)) L b) (Rbar_locally Rbar.p_infty) (locally I)).
  { apply filterlim_RInt_gen. apply Hex_finite. }

  (* Step 8: Rewrite finite integrals using Hfubini_finite *)
  have HLHS' : RInt_gen (λ x, SeriesC (λ n, f n x)) (at_point L) (Rbar_locally Rbar.p_infty) =
               iota (λ I, filterlim (λ b, SeriesC (λ n, RInt (f n) L b)) (Rbar_locally Rbar.p_infty) (locally I)).
  { a dmit. }

  (* Step 6: Key limit exchange - lim[b→∞] SeriesC (λ n, RInt (f n) L b) = SeriesC (λ n, lim[b→∞] RInt (f n) L b)
     This uses uniform convergence from the M-test *)
  have Hlimit_exchange :
    filterlim (λ b, SeriesC (λ n, RInt (f n) L b)) (Rbar_locally Rbar.p_infty)
              (locally (SeriesC (λ n, RInt_gen (f n) (at_point L) (Rbar_locally Rbar.p_infty)))).
  { have Hlim_n : ∀ n, filterlim (λ b, RInt (f n) L b) (Rbar_locally Rbar.p_infty)
                                  (locally (RInt_gen (f n) (at_point L) (Rbar_locally Rbar.p_infty))).
    { intros n. apply filterlim_is_RInt_gen. { apply Hex_n. } apply RInt_gen_correct. apply Hex. }
    (* Need to exchange lim with SeriesC using dominated convergence.
       The series tail must vanish uniformly in b. *)
    a dmit. }

  (* Step 9: Use Hlimit_exchange to identify the iota as RHS *)
  rewrite HLHS'.
  apply (@iota_filterlim_locally _ _ _ (Rbar_locally Rbar.p_infty) _ _ (SeriesC (λ n : nat, RInt_gen (λ x : R, f n x) (at_point L) (Rbar_locally Rbar.p_infty)))).
  apply Hlimit_exchange.
A dmitted.
*)
