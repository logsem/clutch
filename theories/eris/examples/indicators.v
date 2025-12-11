From clutch.eris.examples.math Require Import prelude iverson integrals exp axioms continuity2 sets series limit_exchanges improper.
From clutch.eris Require Import infinite_tape.

Set Default Proof Using "Type*".
#[local] Open Scope R.

Section Lib.
Import Hierarchy.

End Lib.

Section FubiniAx.

  Import Hierarchy.

  (* Current best condition for Fubini's theorem between definite integrals:
     Continuity on a rectangle.
     In fact, this implies boundedness, but we will not use this. *)
  Definition FubiniCondition (f : R → R → R_CompleteNormedModule) (xa xb ya yb : R) : Prop := forall x y,
    Rmin xa xb <= x <= Rmax xa xb →
    Rmin ya yb <= y <= Rmax ya yb →
    Continuity2 (uncurry f) x y.

  (* FubiniCondition implies integrability along any vertical line *)
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

  (* FubiniCondition implies integrability along any horizontal line *)
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

  Axiom Fubini_ex_x : ∀ {f xa xb ya yb}, FubiniCondition f xa xb ya yb →
    ex_RInt (fun x => RInt (fun y => f x y) ya yb) xa xb.

  Axiom Fubini_ex_y : ∀ {f xa xb ya yb}, FubiniCondition f xa xb ya yb →
    ex_RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.

  Axiom Fubini_eq : ∀ {f xa xb ya yb}, FubiniCondition f xa xb ya yb →
    RInt (fun x => RInt (fun y => f x y) ya yb) xa xb =  RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.

End FubiniAx.

Section max_lazy_real_ax.
  Import Hierarchy.
  (** Axiomatize Fubini's theorem for functions of the form
        F (max (x, y))
      Given that F is 2D-continuous on a rectange.

      This is true because the set of discontinuities, namely {(x,x)|x ∈ [0,1]},
      has measure zero. However, it does not reduce to our other axiomatization.
   *)

  Definition MaxFubiniCondition (f : R → R_CompleteNormedModule) (a b : R) : Prop :=
    forall x, Rmin a b <= x <= Rmax a b → Continuity.continuous f x.

  Axiom Max_Fubini_ex_x : ∀ {f a b}, MaxFubiniCondition f a b →
    ex_RInt (fun x => RInt (fun y => f (Rmax x y)) a b) a b.

  Axiom Max_Fubini_ex_y : ∀ {f a b}, MaxFubiniCondition f a b →
    ex_RInt (fun y => RInt (fun x => f (Rmax x y)) a b) a b.

  Axiom Max_Fubini_eq : ∀ {f a b}, MaxFubiniCondition f a b →
     RInt (fun x => RInt (fun y => f (Rmax x y)) a b) a b =  RInt (fun y => RInt (fun x => f (Rmax x y)) a b ) a b.

End max_lazy_real_ax.


(* Now, reduce Piecewise continuous functions to  *)

Section PiecewiseCts.
  Import Hierarchy.

  (* A function on a rectangle *)
  Definition IntervalFun_R : ((R → R) * R * R) → (R → R) :=
    fun '(f, xa, xb) x => Iverson (Ioo xa xb) x * f x.

  Definition IntervalFun_continuity : ((R → R) * R * R) → Prop :=
    fun '(f, xa, xb) => ∀ x, Ioo xa xb x → Continuity.continuous f x.

  Definition fsum {T : Type} (L : list (T → R)) : T → R := fun t => foldr (fun f s => f t + s) 0 L.

  (* Generalized: f is a finite sum of rectangle functions *)
  Definition PCts (f : R → R) (xa xb : R) : Prop :=
    ∃ L, (∀ x, Ioo xa xb x → f = fsum (IntervalFun_R <$> L)) ∧ Forall IntervalFun_continuity L.

  Lemma IntervalFun_RInt {f xa xb} {a b} :
    IntervalFun_continuity (f, xa, xb) →
    ex_RInt (IntervalFun_R (f, xa, xb)) a b.
  Proof.
  Admitted.

  Lemma PCts_RInt {f xa xb} (HP : PCts f xa xb) {a b} :
    ex_RInt f a b.
  Proof.
  Admitted.

  Lemma PCts_cts {f xa xb} : (∀ x, Ioo xa xb x → Continuity.continuous f x) → PCts f xa xb.
  Proof. Admitted.

  Lemma PCts_plus {f g xa xb} : PCts f xa xb → PCts g xa xb → PCts (fun x => f x + g x) xa xb.
  Proof. Admitted.

  Lemma PCts_mult {f g xa xb} : PCts f xa xb → PCts g xa xb → PCts (fun x => f x + g x) xa xb.
  Proof. Admitted.

End PiecewiseCts.

Section UniformLimitTheorem.
  Import Hierarchy.

  (* Wrapper around the Coquelicot french definitions + some basic reductions *)
  Theorem UniformLimitTheorem {f : nat → R → R} {a b x : R} :
    Icc a b x →
    (* Oh oops I need each to be continuous too *)
    (∀ (n : nat) (x' : R), Rmin a b < x' < Rmax a b → (Continuity.continuous (f n) x')) →
    (* Uniform convergence (TODO: Just on the interval [a,b], right? ) *)
    filterlim (fun (M : nat) (x : R) => sum_n (fun n => f n x) M) eventually (locally (λ x : R, Series.Series (fun n => f n x))) →
    (* The limit is continuous *)
    Continuity.continuous (fun x' => (Series.Series (fun n => f n x'))) x.
  Proof.
    intros HB Hcvg.
    (*
    Search Seq_fct.CVU_dom .
  Check Seq_fct.Dini.
  Check Seq_fct.CVN_CVU_r.
*)


    (*
  Search CVN_r.
  Search CVU.
  Check CVU_continuity.
  Search Seq_fct.CVS_dom.
  *)
  Admitted.


End UniformLimitTheorem.

Section FubiniStep.
  Import Hierarchy.

  Lemma Continuity2_swap (f : R * R → R) (x y : R) :
    Continuity2 (fun '(x', y') => f (y', x')) y x → Continuity2 f x y.
  Proof.
    intros H P Hp.
    have H' := H P Hp.
    revert H'.
    rewrite /filtermap//=/locally//=.
    intros [e He].
    exists e.
    intros [zx zy] Hz.
    apply (He (zy, zx)).
    revert Hz.
    rewrite /ball//=/prod_ball//=.
    intuition.
  Qed.

  Lemma Continuity2_const {F : R * R → R} (v x y : R) :
    (∀ z, F z = v) →
    Continuity2 F x y.
  Proof. Admitted.

  (* Continuity.continuity_2d_pt_filterlim ???? *)
  Definition IsFubiniCoreRR (f : R → R → R) : Prop :=
    ∀ x y, Continuity2 (uncurry f) x y.

  Definition IsFubiniCoreSR (f : nat → R → R) : Prop :=
    forall n x, Continuity.continuous (f n) x.


  Definition fsum2 {T U : Type} (L : list (T → U → R)) : T → U → R :=
    fun t u => foldr (fun f s => f t u + s) 0 L.

  (* A function on a rectangle *)
  Definition RectFun_RR : ((R → R → R) * R * R * R * R) → (R → R → R) :=
    fun '(f, xa, xb, ya, yb) x y => Iverson (Ioo xa xb) x * Iverson (Ioo ya yb) y * f x y.

  Definition RectFun_continuity : ((R → R → R) * R * R * R * R) → Prop :=
    fun '(f, xa, xb, ya, yb) => ∀ x y, Icc xa xb x → Icc ya yb y → Continuity2 (uncurry f) x y.

  (* Generalized: f is a finite sum of rectangle functions on the rectangle [xa xb] [ya yb] *)
  Definition IsFubiniRR (f : R → R → R) (xa xb ya yb : R) : Prop :=
    ∃ L,
      ∀ x y, (Ioo xa xb x → Ioo ya yb y → f x y = fsum2 (RectFun_RR <$> L) x y) ∧
      Forall RectFun_continuity L.

  Lemma IsFubiniRR_continuous {f : R → R → R} {xa xb ya yb} :
    (∀ x y, Continuity2 (uncurry f) x y) →
    IsFubiniRR f xa xb ya yb.
  Proof. Admitted.

  Lemma fsum2_app {T U : Type} (L1 L2 : list (T → U → R)) (t : T) (u : U) :
    fsum2 (L1 ++ L2) t u = fsum2 L1 t u + fsum2 L2 t u.
  Proof.
    unfold fsum2.
    induction L1 as [| f L1 IH].
    { simpl. lra. }
    { simpl. rewrite IH. lra. }
  Qed.

  Lemma IsFubiniRR_plus {f g : R → R → R} {xa xb ya yb} :
    IsFubiniRR f xa xb ya yb → IsFubiniRR g xa xb ya yb → IsFubiniRR (fun (x y : R) => f x y + g x y) xa xb ya yb.
  Proof.
    intros [Lf Hf] [Lg Hg].
    unfold IsFubiniRR.
    exists (Lf ++ Lg).
    intros x y.
    split.
    {
      intros Hx Hy.
      destruct (Hf x y) as [Hfeq _].
      destruct (Hg x y) as [Hgeq _].
      rewrite (Hfeq Hx Hy).
      rewrite (Hgeq Hx Hy).
      rewrite fmap_app.
      rewrite fsum2_app.
      reflexivity.
    }
    {
      apply Forall_app.
      split.
      { destruct (Hf xa ya) as [_ HLf]. exact HLf. }
      { destruct (Hg xa ya) as [_ HLg]. exact HLg. }
    }
  Qed.

  Lemma IsFubiniRR_mult {f g : R → R → R} {xa xb ya yb} :
    IsFubiniRR f xa xb ya yb → IsFubiniRR g xa xb ya yb → IsFubiniRR (fun (x y : R) => f x y * g x y) xa xb ya yb.
  Proof.
  Admitted.

  (* Slice of 2D continuous function is integrable in y *)
  Lemma ex_RInt_continuous_slice_y (f : R → R → R)x xa xb ya yb :
    Ioo xa xb x →
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

  (* Slice of 2D continuous function is integrable in x *)
  Lemma ex_RInt_continuous_slice_x (f : R → R → R) y xa xb ya yb :
    Ioo ya yb y →
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


  (* Integrability of Iverson-masked continuous function in y *)
  Lemma ex_RInt_Iverson_continuous_y (f : R → R → R) xa' xb' ya' yb' x ya yb :
    Ioo xa' xb' x →
    (∀ y, Icc ya' yb' y → Continuity2 (uncurry f) x y) →
    ex_RInt (fun y => Iverson (Ioo ya' yb') y * f x y) ya yb.
  Proof.
    intros Hx Hcont.
    (* Reduce to the case where the bounds are in order *)
    suffices HH : ex_RInt (λ y : R, Iverson (Ioo ya' yb') y * f x y) (Rmin ya yb) (Rmax ya yb).
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
      rewrite /Ioo//=.
      rewrite Iverson_False; try lra.
    }

    (* Trivial: Lower bound of indicator is le upper bound of integral *)
    destruct (Rle_lt_dec (Rmin ya' yb') (Rmax ya yb)).
    2: {
      apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      rewrite /Ioo//=.
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
          rewrite /Ioo//=. lra.
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
        rewrite /Ioo//=. lra.
      }
    }
    { (* Case: ------- *)
      apply (ex_RInt_ext (fun y => f x y)).
      {
        rewrite Rmin_left; try lra.
        rewrite (Rmax_right); try lra.
        intros ??.
        rewrite Iverson_True; try lra.
        rewrite /Ioo//=. lra.
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
        rewrite /Ioo//=. lra.
      }
      apply (ex_RInt_Chasles_0 _ _ (Rmax ya' yb') _).
      { split; try lra.  }
      { apply (ex_RInt_ext (fun y => f x y)).
        { rewrite Rmin_left; try lra.
          rewrite Rmax_right; try lra.
          intros ??.
          rewrite Iverson_True; try lra.
          rewrite /Ioo//=.
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
        rewrite /Ioo//=. lra.
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
        rewrite /Ioo//=. lra.
      }
      { apply (ex_RInt_ext (fun y => f x y)).
        { rewrite Rmin_left; try lra.
          rewrite (Rmax_right) ; try lra.
          intros ??.
          rewrite Iverson_True; try lra.
          rewrite /Ioo//=.
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
    Ioo ya' yb' y →
    (∀ x, Icc xa' xb' x → Continuity2 (uncurry f) x y) →
    ex_RInt (fun x => Iverson (Ioo xa' xb') x * f x y) xa xb.
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
    destruct (decide (Ioo xa' xb' x)) as [Hx | Hx].
    2: { apply (@ex_RInt_ext _ (fun y => 0)).
      { intros y _. rewrite (Iverson_False Hx). lra. }
      apply ex_RInt_const.
    }
    { apply (@ex_RInt_ext _ (fun y => Iverson (Ioo ya' yb') y * f x y)).
      { intros y _. rewrite (Iverson_True Hx). lra. }
      eapply ex_RInt_Iverson_continuous_y.
      { exact Hx. }
      { intros y Hy.
        apply Hcont.
        { exact (Ioo_Icc Hx). }
        { exact Hy. }
      }
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
    destruct (decide (Ioo ya' yb' y)) as [Hy | Hy].
    { apply (@ex_RInt_ext _ (fun x => Iverson (Ioo xa' xb') x * f x y)).
      { intros x _. rewrite (Iverson_True Hy). lra. }
      eapply ex_RInt_Iverson_continuous_x.
      { exact Hy. }
      { intros x Hx. apply Hcont; [exact Hx|exact (Ioo_Icc Hy)]. }
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
    (* Also just a big case proof I think (ugh!) *)
  Admitted.

  Lemma RectFun_RR_ex_RInt_iterated_y (rect : (R → R → R) * R * R * R * R) xa xb ya yb :
    RectFun_continuity rect →
    ex_RInt (fun y => RInt (fun x => RectFun_RR rect x y) xa xb) ya yb.
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

  Lemma Fubini_Step_ex_x {f xa xb ya yb} : IsFubiniRR f xa xb ya yb →
    ex_RInt (fun x => RInt (fun y => f x y) ya yb) xa xb.
  Proof.
    intros [L H].
    apply (@ex_RInt_ext _ (fun x => RInt (fun y => fsum2 (RectFun_RR <$> L) x y) ya yb)).
    { intros x Hx. apply RInt_ext. intros y Hy.
      destruct (H x y) as [Heq _]. symmetry. apply Heq. { exact Hx. } { exact Hy. } }
    destruct (H xa ya) as [_ HL].
    apply fsum2_RectFun_ex_x. exact HL.
  Qed.

  Lemma Fubini_Step_ex_y {f xa xb ya yb} : IsFubiniRR f xa xb ya yb →
    ex_RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.
  Proof.
    intros [L H].
    apply (@ex_RInt_ext _ (fun y => RInt (fun x => fsum2 (RectFun_RR <$> L) x y) xa xb)).
    { intros y Hy. apply RInt_ext. intros x Hx.
      destruct (H x y) as [Heq _]. symmetry. apply Heq. { exact Hx. } { exact Hy. } }
    destruct (H xa ya) as [_ HL].
    apply fsum2_RectFun_ex_y. exact HL.
  Qed.

  Lemma Fubini_Step_eq : ∀ {f xa xb ya yb}, IsFubiniRR f xa xb ya yb →
    RInt (fun x => RInt (fun y => f x y) ya yb) xa xb = RInt (fun y => RInt (fun x => f x y) xa xb) ya yb.
  Proof.
  Admitted.

  Lemma PCts_const_x {f xa xb ya yb} : PCts f xa xb → IsFubiniRR (fun x _ => f x) xa xb ya yb.
  Proof.
  Admitted.

  Lemma PCts_const_y {f xa xb ya yb} : PCts f ya yb → IsFubiniRR (fun _ y => f y) xa xb ya yb.
  Proof.
  Admitted.

End FubiniStep.



(* Reduction: This implies Fubini's theorem holds for improper integrals? *)


Section FubiniImproper.
  Import Hierarchy.

  (*

  (* E *)


  (* FubiniImproper_ex *)
  Theorem FubiniImproper_ex_x {f xa ya yb} (H : ∀ xb, FubiniCondition f xa xb ya yb) (HInt : True) :
    ex_RInt_gen (fun x => RInt (fun y => f x y) ya yb) (at_point xa) (Rbar_locally Rbar.p_infty).
  Proof.
    unfold ex_RInt_gen.
    suffices Hlim : ∃ l, filterlim (λ b : R, RInt (λ x : R, RInt (λ y : R, f x y) ya yb) xa b) (Rbar_locally Rbar.p_infty) (locally l).
    { destruct Hlim as [l Hl]; exists l.
      apply is_RInt_gen_filterlim; [|exact Hl].
      intros b.
      apply Fubini_ex_x.
      apply H.
    }
    (* Side condition, the integrals needs to be finite? Is there a general theorem I can prove here? *)
    a dmit.
  A dmitted.

  Theorem FubiniImproper_ex_y {f xa ya yb} (H : ∀ xb, FubiniCondition f xa xb ya yb) (HInt : True) :
    ex_RInt (fun y => (RInt_gen (fun x => f x y) (at_point xa) (Rbar_locally Rbar.p_infty))) ya yb.
  Proof.
    unfold ex_RInt.
    suffices Hlim : ∃ l, is_RInt (λ y : R, iota (λ IF : R, filterlim (λ b : R, RInt (λ x : R, f x y) xa b) (Rbar_locally Rbar.p_infty) (locally IF))) ya yb l.
    { destruct Hlim as [l Hl]; exists l.
      eapply is_RInt_ext; [|exact Hl].
      intros y Hy.
      symmetry; apply filterlim_RInt_gen.
      intros xb.
      apply (@FubiniCondition_ex_RInt_x f xa xb ya yb (H xb) y).
      lra.
    }

    (*
    Search RInt_gen iota.
    Check (iota (is_RInt_gen F (at_point M) (Rbar_locally Rbar.p_infty))).
    Search RInt_gen.
    Check filterlim.
    *)
  A dmitted.

  Theorem FubiniImproper_eq {f xa ya yb} (H : ∀ xb, FubiniCondition f xa xb ya yb)
    (HInt : True) :
    RInt_gen (fun x => RInt (fun y => f x y) ya yb) (at_point xa) (Rbar_locally Rbar.p_infty) =
    RInt (fun y => (RInt_gen (fun x => f x y) (at_point xa) (Rbar_locally Rbar.p_infty))) ya yb.
  Proof.
    rewrite filterlim_RInt_gen.
    2: {
      intros xb.
      apply Fubini_ex_x.
      apply H.
    }
    replace (RInt (λ y : R, RInt_gen (λ x : R, f x y) (at_point xa) (Rbar_locally Rbar.p_infty)) ya yb)
       with (RInt (λ y : R, iota (λ IF : R, filterlim (λ b : R, RInt (λ x : R, f x y) xa b) (Rbar_locally Rbar.p_infty) (locally IF))) ya yb).
    2: {
      apply RInt_ext.
      intros y Hy.
      symmetry; apply filterlim_RInt_gen.
      intros xb.
      apply (@FubiniCondition_ex_RInt_x f xa xb ya yb (H xb) y).
      lra.
    }
    apply @iota_filterlim_locally.
    { apply Proper_StrongProper. apply Rbar_locally_filter. }
    (* Apply Definite/Definite Fubini *)
    replace (λ xb : R, RInt (λ x : R, RInt (λ y : R, f x y) ya yb) xa xb)
      with  (λ xb : R, RInt (λ y : R, RInt (λ x : R, f x y) xa xb) ya yb).
    2: { apply functional_extensionality. intros xb. rewrite -Fubini_eq; done. }
    apply (@Exchange2 (λ xb y : R, RInt (λ x : R, f x y) xa xb) ya yb
      (λ y : R, iota (λ IF : R, filterlim (λ b : R, RInt (λ x : R, f x y) xa b) (Rbar_locally Rbar.p_infty) (locally IF)))).
    { intros xb. apply Fubini_ex_y. apply H.  }

    replace (λ y : R, iota (λ IF : R, filterlim (λ b : R, RInt (λ x : R, f x y) xa b) (Rbar_locally Rbar.p_infty) (locally IF)))
       with (λ y : R, RInt_gen (λ x : R, f x y) (at_point xa) (Rbar_locally Rbar.p_infty)).
    2: { apply functional_extensionality. intros y. apply filterlim_RInt_gen.
         intros xb. apply (@FubiniCondition_ex_RInt_x f xa xb ya yb (H xb) y).
         (* We can improve FubiniCondition to FubiniConditionU that applies on the entire x/y plane,
            and requires that the function be zero outside of the rectangle.  *)
         a dmit.
    }

    (* I think we can prove this with something like the Cauchy Critereon

      A family of functions indexed by a real number r converges as the r → ∞
      if for evey epsilon, there exists R such that the for every R' > R,
      the sup of f on [R, R'] is bounded above by epsilon *)

  A dmitted.
  *)

End FubiniImproper.


