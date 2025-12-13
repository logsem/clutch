From clutch.eris.examples.math Require Import prelude continuity2 iverson sets.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** Piecewise continuous 1D functions *)

(* A function on a rectangle *)
Definition IntervalFun_R : ((R → R) * R * R) → (R → R) :=
  fun '(f, xa, xb) x => Iverson (Icc xa xb) x * f x.

Definition IntervalFun_continuity : ((R → R) * R * R) → Prop :=
  fun '(f, xa, xb) => ∀ x, Icc xa xb x → Continuity.continuous f x.

Definition fsum {T : Type} (L : list (T → R)) : T → R := fun t => foldr (fun f s => f t + s) 0 L.

(* Generalized: f is a finite sum of rectangle functions *)
Definition PCts (f : R → R) (xa xb : R) : Prop :=
  ∃ L, (∀ x, Icc xa xb x → f x = fsum (IntervalFun_R <$> L) x) ∧ Forall IntervalFun_continuity L.

Lemma IntervalFun_RInt {f xa xb} {a b} :
  IntervalFun_continuity (f, xa, xb) →
  ex_RInt (IntervalFun_R (f, xa, xb)) a b.
Proof.
  rewrite //=.
  intros H.

  (* Reduce to the case where the bounds are in order *)
  suffices HH : ex_RInt (λ x : R, Iverson (Icc xa xb) x * f x) (Rmin a b) (Rmax a b).
  { destruct (Rle_lt_dec a b).
    { rewrite Rmin_left in HH; try lra.
      rewrite Rmax_right in HH; try lra.
      apply HH. }
    { rewrite Rmin_right in HH; try lra.
      rewrite Rmax_left in HH; try lra.
      apply ex_RInt_swap.
      apply HH. }
  }

  have LraLem1 : Rmin a b <= Rmax a b := Rminmax _ _.
  have LraLem2 : Rmin xa xb <= Rmax xa xb := Rminmax _ _.

  (* Trivial: Upper bound of indicator is le lower bound of integral *)
  destruct (Rle_lt_dec (Rmax xa xb) (Rmin a b)).
  { apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
    rewrite Rmin_left; try lra.
    rewrite Rmax_right; try lra.
    intros ??.
    rewrite /Icc//=.
    rewrite Iverson_False; try lra.
  }

  (* Trivial: Lower bound of indicator is le upper bound of integral *)
  destruct (Rle_lt_dec (Rmin xa xb) (Rmax a b)).
  2: {
    apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
    rewrite Rmin_left; try lra.
    rewrite Rmax_right; try lra.
    intros ??.
    rewrite /Icc//=.
    rewrite Iverson_False; try lra.
  }

  (* Case on the lower bound of the indicator being in range.*)
  destruct (Rle_lt_dec (Rmin xa xb) (Rmin a b));
  destruct (Rle_lt_dec (Rmax xa xb) (Rmax a b)).
  { (* Case: ---____ *)
    apply (ex_RInt_Chasles_0 _ _ (Rmax xa xb) _).
    { split; lra. }
    { apply (ex_RInt_ext f).
      { rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros ??.
        rewrite Iverson_True; try lra.
        rewrite /Icc//=. lra.
      }
      {
        apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros ??.
        apply H.
        rewrite /Icc.
        lra.
      }
    }
    { apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
      rewrite Rmin_left; try lra.
      rewrite (Rmax_right (Rmax xa xb) (Rmax a b)); try lra.
      intros ??.
      rewrite Iverson_False; try lra.
      rewrite /Icc//=. lra.
    }
  }
  { (* Case: ------- *)
    apply (ex_RInt_ext f).
    {
      rewrite Rmin_left; try lra.
      rewrite (Rmax_right); try lra.
      intros ??.
      rewrite Iverson_True; try lra.
      rewrite /Icc//=. lra.
    }
    {
     apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
     rewrite Rmin_left; try lra.
     rewrite Rmax_right; try lra.
     intros ??.
     apply H.
     rewrite /Icc.
     lra.
    }
  }

  { (* Case : __----__*)
    apply (ex_RInt_Chasles_0 _ _ (Rmin xa xb) _).
    { split; try lra. }
    { apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      rewrite Iverson_False; try lra.
      rewrite /Icc//=. lra.
    }
    apply (ex_RInt_Chasles_0 _ _ (Rmax xa xb) _).
    { split; try lra.  }
    { apply (ex_RInt_ext f).
      { rewrite Rmin_left; try lra.
        rewrite Rmax_right; try lra.
        intros ??.
        rewrite Iverson_True; try lra.
        rewrite /Icc//=.
        lra.
      }

      apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      apply H.
      rewrite /Icc.
      lra.
    }
    { apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
      rewrite Rmin_left; try lra.
      rewrite (Rmax_right (Rmax xa xb) (Rmax a b)); try lra.
      intros ??.
      rewrite Iverson_False; try lra.
      rewrite /Icc//=. lra.
    }
  }
  { (* Case: ____---- *)
    apply (ex_RInt_Chasles_0 _ _ (Rmin xa xb) _).
    { split; lra. }
    { apply (ex_RInt_ext (fun y => 0)); [|apply ex_RInt_const].
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      rewrite Iverson_False; try lra.
      rewrite /Icc//=. lra.
    }
    { apply (ex_RInt_ext f).
      { rewrite Rmin_left; try lra.
        rewrite (Rmax_right) ; try lra.
        intros ??.
        rewrite Iverson_True; try lra.
        rewrite /Icc//=.
        split; try lra.
      }

      apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      rewrite Rmin_left; try lra.
      rewrite Rmax_right; try lra.
      intros ??.
      apply H.
      rewrite /Icc.
      lra.
    }
  }
Qed.

Lemma fsum_app {T : Type} (L1 L2 : list (T → R)) (t : T) :
  fsum (L1 ++ L2) t = fsum L1 t + fsum L2 t.
Proof.
  induction L1 as [|f L1 IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma PCts_RInt {f xa xb} (HP : PCts f xa xb) :
  ex_RInt f xa xb.
Proof.
  destruct HP as [L [HL1 HL2]].
  apply (ex_RInt_ext (fsum (IntervalFun_R <$> L))).
  { intros ??. rewrite HL1; try done. rewrite /Icc//=. lra.  }
  clear HL1.
  induction L.
  { rewrite /fsum//=. apply ex_RInt_const. }
  replace (a :: L) with ([a] ++ L); last by simpl.
  rewrite fmap_app.
  replace (fsum ((IntervalFun_R <$> [a]) ++ (IntervalFun_R <$> L)))
     with (fun x => fsum ((IntervalFun_R <$> [a])) x + fsum (IntervalFun_R <$> L) x); last first.
  { apply functional_extensionality. intros x. by rewrite fsum_app. }
  apply (ex_RInt_plus (V := R_CompleteNormedModule)).
  { rewrite /fsum//=.
    replace (λ t : R, IntervalFun_R a t + 0) with (IntervalFun_R a); last first.
    { apply functional_extensionality; intros ?; lra. }
    destruct a as [[f' a'] b'].
    apply (@IntervalFun_RInt f' a' b' xa xb).
    apply Forall_inv in HL2.
    done.
  }
  { apply IHL. eapply Forall_inv_tail; done. }
Qed.

Lemma PCts_cts {f xa xb} : (∀ x, Icc xa xb x → Continuity.continuous f x) → PCts f xa xb.
Proof.
  exists [(f, xa, xb)].
  split.
  { rewrite /fsum//=.
    intros ??.
    rewrite Iverson_True; try done.
    lra.
  }
  rewrite Forall_singleton //=.
Qed.

Lemma PCts_plus {f g xa xb} : PCts f xa xb → PCts g xa xb → PCts (fun x => f x + g x) xa xb.
Proof. Admitted.

Lemma PCts_mult {f g xa xb} : PCts f xa xb → PCts g xa xb → PCts (fun x => f x + g x) xa xb.
Proof. Admitted.

(** Piecewise continuity over the enture real line *)

(* I'm writing infintie piecewise continuity as being a continuous function +
   finitely many interval functions.

    Doing it this way means we can reuse some super annoying intervalfun lemmas. *)
Definition IPCts (f : R → R) : Prop :=
  ∃ f0 L,
    (∀ x, f x = f0 x + fsum (IntervalFun_R <$> L) x) ∧
    Forall IntervalFun_continuity L ∧
    (∀ x, Continuity.continuous f0 x).

Lemma IPCts_PCts (f : R → R) : IPCts f → ∀ a b, PCts f a b.
Proof.
  intros [f0 [L[?[??]]]] ??.
  (*  Need to add f0 to each rectangle, but otherwise it's easy.
  exists L; split; try done.
  intros ??. rewrite H //=.
  *)
Admitted.

Lemma IPCts_RInt {f xa xb} (HP : IPCts f ) : ex_RInt f xa xb.
Proof. by apply PCts_RInt, IPCts_PCts. Qed.

Lemma IPCts_cts {f} : (∀ x, Continuity.continuous f x) → IPCts f.
Proof.
  (** TODO: The definition is actually not right, since we need the intervals to possibly be infinite.
      Easy fix though.  *)



Admitted.

Lemma IPCts_plus {f g} : IPCts f → IPCts g → IPCts (fun x => f x + g x).
Proof. Admitted.

Lemma IPCts_mult {f g} : IPCts f → IPCts g → IPCts (fun x => f x * g x).
Proof. Admitted.

Lemma IPCts_scal_mult {c : R} {G : R → R} :
  IPCts G → IPCts (fun x => c * G x).
Proof. Admitted.

(** Piecewise continuous 2D functions *)

Definition fsum2 {T U : Type} (L : list (T → U → R)) : T → U → R :=
  fun t u => foldr (fun f s => f t u + s) 0 L.

Definition RectFun_RR : ((R → R → R) * R * R * R * R) → (R → R → R) :=
  fun '(f, xa, xb, ya, yb) x y => Iverson (Ioo xa xb) x * Iverson (Ioo ya yb) y * f x y.

Definition RectFun_continuity : ((R → R → R) * R * R * R * R) → Prop :=
  fun '(f, xa, xb, ya, yb) => ∀ x y, Icc xa xb x → Icc ya yb y → Continuity2 (uncurry f) x y.

(* f is a finite sum of rectangle functions on the rectangle [xa xb] [ya yb] *)
Definition PCts2 (f : R → R → R) (xa xb ya yb : R) : Prop :=
  ∃ L,
    ∀ x y, (Ioo xa xb x → Ioo ya yb y → f x y = fsum2 (RectFun_RR <$> L) x y) ∧
    Forall RectFun_continuity L.

Lemma PCts2_continuous {f : R → R → R} {xa xb ya yb} :
  (∀ x y, Continuity2 (uncurry f) x y) →
  PCts2 f xa xb ya yb.
Proof. Admitted.

Lemma fsum2_app {T U : Type} (L1 L2 : list (T → U → R)) (t : T) (u : U) :
  fsum2 (L1 ++ L2) t u = fsum2 L1 t u + fsum2 L2 t u.
Proof.
  unfold fsum2.
  induction L1 as [| f L1 IH].
  { simpl. lra. }
  { simpl. rewrite IH. lra. }
Qed.

Lemma PCts2_plus {f g : R → R → R} {xa xb ya yb} :
  PCts2 f xa xb ya yb → PCts2 g xa xb ya yb → PCts2 (fun (x y : R) => f x y + g x y) xa xb ya yb.
Proof.
  intros [Lf Hf] [Lg Hg].
  unfold PCts2.
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

Lemma PCts2_mult {f g : R → R → R} {xa xb ya yb} :
  PCts2 f xa xb ya yb → PCts2 g xa xb ya yb → PCts2 (fun (x y : R) => f x y * g x y) xa xb ya yb.
Proof.
Admitted.

Lemma PCts_const_x {f xa xb ya yb} : PCts f xa xb → PCts2 (fun x _ => f x) xa xb ya yb.
Proof.
Admitted.

Lemma PCts_const_y {f xa xb ya yb} : PCts f ya yb → PCts2 (fun _ y => f y) xa xb ya yb.
Proof.
Admitted.
