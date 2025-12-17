From clutch.eris.examples.math Require Import prelude continuity2 iverson sets.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** Piecewise continuous 1D functions *)

(** A function on an interval *)
Definition IntervalFun_R : ((R → R) * R * R) → (R → R) :=
  fun '(f, xa, xb) x => Iverson (Icc xa xb) x * f x.

(** An IntervalFun is continuous on its interval *)
Definition IntervalFun_continuity : ((R → R) * R * R) → Prop :=
  fun '(f, xa, xb) => ∀ x, Icc xa xb x → Continuity.continuous f x.

(** Finite sum of functions *)
Definition fsum {T : Type} (L : list (T → R)) : T → R := fun t => foldr (fun f s => f t + s) 0 L.

(** 1D piecewise compactly-supported continuity: The function is a sum of continuous IntervalFuns *)
Definition PCts (f : R → R) (xa xb : R) : Prop :=
  ∃ L, (∀ x, Icc xa xb x → f x = fsum (IntervalFun_R <$> L) x) ∧ Forall IntervalFun_continuity L.

(** IntervalFun integrablility *)
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

(** Finite function sums distribute over list appending *)
Lemma fsum_app {T : Type} (L1 L2 : list (T → R)) (t : T) :
  fsum (L1 ++ L2) t = fsum L1 t + fsum L2 t.
Proof.
  induction L1 as [|f L1 IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

(** Right scale a finite function sum *)
Lemma fsum_scal_r {T : Type} (L : list (T → R)) (h : T → R) (t : T) :
  fsum L t * h t = fsum (map (fun f => fun x => f x * h x) L) t.
Proof.
  induction L as [|f L' IH].
  { rewrite //=. lra. }
  rewrite /fsum//=.
  rewrite Rmult_plus_distr_r.
  f_equal. apply IH.
Qed.

(** Left scale a finite function sum *)
Lemma fsum_scal_l {T : Type} (L : list (T → R)) (h : T → R) (t : T) :
  h t * fsum L t = fsum (map (fun f => fun x => h x * f x) L) t.
Proof.
  induction L as [|f L' IH].
  { rewrite //=. lra. }
  rewrite /fsum//=.
  rewrite Rmult_plus_distr_l.
  f_equal. apply IH.
Qed.


Definition PCts' (f : R → R) (xa xb : R) : Prop :=
  ∃ L, (∀ x, Icc xa xb x → f x = fsum (IntervalFun_R <$> L) x) ∧ Forall IntervalFun_continuity L /\
       (∀ x, ¬ Icc xa xb x → fsum (IntervalFun_R <$> L) x = 0)
.

Lemma PCts_PCts' f xa xb :
  PCts f xa xb -> PCts' f xa xb.
Proof.
  intros [L [H1 H2]].
  exists ((λ '(f, xa', xb'), (f, Rmax (Rmin xa xb) (Rmin xa' xb'), Rmin (Rmax xa xb) (Rmax xa' xb')))<$>
       (filter (λ '(f, xa', xb'),  Rmin xa' xb' <= Rmax xa xb /\  Rmin xa xb <= Rmax xa' xb' ) L)).
  repeat split.
  - clear H2.
    intros.
    rewrite H1; last done.
    clear -H.
    induction L as [|hd L' IHL]; first done.
    simpl.
    rewrite filter_cons/=.
    destruct hd as [[]]. simpl.
    case_match.
    + simpl.
      rewrite IHL. f_equal.
      unfold Iverson, Icc, Rmin, Rmax in *. repeat case_match; lra.
    + rewrite Iverson_False; first (rewrite IHL; lra).
      unfold Iverson, Icc, Rmin, Rmax in *. repeat case_match; lra.
  - clear H1.
    revert H2.
    induction L as [|hd tl IHL]; first (intros; by apply Forall_nil).
    rewrite Forall_cons.
    intros [H1 H2].
    destruct hd as [[]].
    rewrite filter_cons.
    case_match; last naive_solver.
    simpl.
    rewrite Forall_cons. split; last naive_solver.
    unfold IntervalFun_continuity.
    intros.
    apply H1.
    clear H1.
    simpl in *. 
    unfold Icc, Rmin, Rmax in *.
    repeat case_match; lra.
  - clear.
    induction L as [|hd tl IHL]; first (simpl; by intros).
    intros.
    rewrite filter_cons.
    destruct hd as [[]].
    case_match; last naive_solver.
    simpl.
    rewrite IHL; last done.
    rewrite Iverson_False; first lra.
    unfold Icc, Rmin, Rmax in *.
    repeat case_match; lra.
Qed.   
  
Lemma PCts_split f xa xb xc: Rmin xa xc<=xb<=Rmax xa xc -> PCts f xa xb -> PCts f xb xc -> PCts f xa xc.
Proof.
  intros H [l1 [H1[H2 H3]]]%PCts_PCts' [l2 [H4[H5 H6]]]%PCts_PCts'.
  exists ((λ _, - f xb, xb, xb)::l1++l2).
  split.
  - rewrite /Icc.
    rewrite /Rmin/Rmax.
    intros.
    rewrite fmap_cons fmap_app.
    simpl.
    rewrite fsum_app.
    rewrite /Icc.
    rewrite /Iverson.
    unfold Rmin, Rmax in *.
    repeat case_match; try lra.
    + rewrite -H1; last (rewrite /Icc/Rmax/Rmin; repeat case_match; lra).
      rewrite -H4; last (rewrite /Icc/Rmax/Rmin; repeat case_match; lra).
      replace x with xb; lra.
    + destruct (decide (x<=xb)).
      * rewrite -H1; last (rewrite /Icc/Rmax/Rmin; repeat case_match; lra).
        rewrite H6; first lra.
        unfold Icc, Rmin, Rmax. repeat case_match; lra.
      * rewrite -H4; last (rewrite /Icc/Rmax/Rmin; repeat case_match; lra).
        rewrite H3; first lra.
        unfold Icc, Rmin, Rmax. repeat case_match; lra.
    + rewrite -H1; last (rewrite /Icc/Rmax/Rmin; repeat case_match; lra).
      rewrite -H4; last (rewrite /Icc/Rmax/Rmin; repeat case_match; lra).
      replace x with xb; lra.
    + destruct (decide (x<=xb)).
      * rewrite -H4; last (rewrite /Icc/Rmax/Rmin; repeat case_match; lra).
        rewrite H3; first lra.
        unfold Icc, Rmin, Rmax. repeat case_match; lra.
      * rewrite -H1; last (rewrite /Icc/Rmax/Rmin; repeat case_match; lra).
        rewrite H6; first lra.
        unfold Icc, Rmin, Rmax. repeat case_match; lra.
  - apply Forall_cons.
    split.
    + intros ??. apply Continuity.continuous_const.
    + by apply Forall_app.
Qed. 

Lemma PCts_subset f xa xa' xb xb': Rmin xa xb<=xa'<=Rmax xa xb ->
                                   Rmin xa xb<=xb'<=Rmax xa xb ->
                                   PCts f xa xb -> PCts f xa' xb'.
Proof.
  intros H1 H2 [x [K1 K2]].
  exists x.
  split; last done.
  intros.
  apply K1.
  unfold Icc, Rmin, Rmax in *.
  repeat case_match; lra.
Qed.

Lemma PCts_shift f f' xa xb xa' xb' r:
  xa' = xa + r -> xb' = xb + r ->
  (∀ x, Icc xa xb x-> f x = f' (x+r)) ->
  PCts f xa xb -> 
  PCts f' xa' xb'.
Proof.
  intros -> -> H1 [l[K1 K2]].
  exists ((λ '(g, y, z), (λ x, g(x-r), y+r, z+r))<$>l).
  assert (∀ x, Icc (xa+r) (xb+r) x-> f (x-r) = f' (x)) as H1'.
  { intros.
    rewrite H1; first (f_equal; lra).
    unfold Icc, Rmax, Rmin in *. repeat case_match; lra.
  }
  split.
  - intros.
    rewrite -H1'; last done.
    rewrite K1; last first.
    { unfold Icc, Rmax, Rmin in *. repeat case_match; lra. }
    clear.
    induction l as [|hd tl IHL]; first done.
    simpl. rewrite IHL.
    f_equal.
    repeat case_match. subst.
    unfold IntervalFun_R, Iverson, Icc, Rmin, Rmax.
    repeat case_match; lra.
  - clear -K2.
    revert K2.
    induction l as [|hd tl IHL]; first done.
    rewrite !Forall_cons.
    intros [].
    split; last naive_solver.
    destruct hd as [[]].
    intros x ?.
    unshelve epose proof H (x-r) _.
    { unfold Icc, Rmin, Rmax in *. repeat case_match; lra. }
    apply Continuity.continuous_comp; last done.
    apply: Derive.ex_derive_continuous.
    by auto_derive.
Qed. 

Lemma PCts_unit_implies_all (F:nat -> R -> R) r:
  (∀ k, PCts (F k) 0 1) ->
  PCts (λ y0 : R, F (Z.to_nat (Int_part y0)) (frac_part y0)) (0) r.
Proof.
Admitted.
  
(** Integrability of 1D compactly-supported piecewise continuous functions, on any interval *)
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

(** Continuous functions are piecewise continous *)
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

(** Piecewise continuity of addition *)
Lemma PCts_plus {f g xa xb} : PCts f xa xb → PCts g xa xb → PCts (fun x => f x + g x) xa xb.
Proof.
  intros [Lf [Hfeq HfC]] [Lg [Hgeq HgC]].
  exists (Lf ++ Lg).
  split.
  { intros x Hx. rewrite Hfeq; try done. rewrite Hgeq; try done. rewrite fmap_app. rewrite fsum_app. done. }
  apply Forall_app_2; done.
Qed.

(** IntervalFun continuity of multiplication *)
Lemma IntervalFun_continuity_mult {f g xa xb ya yb} :
  IntervalFun_continuity (f, xa, xb) →
  IntervalFun_continuity (g, ya, yb) →
  IntervalFun_continuity ((fun x => f x * g x), (Rmax xa ya), (Rmin xb yb)).
Proof.
  rewrite /IntervalFun_continuity//=.
  intros Hf Hg x Hx.
  apply (@Continuity.continuous_mult R_CompleteNormedModule).
  - apply Hf.
    revert Hx.
    rewrite /Icc//=.
    intros [??]. split.
    { etrans; [|apply H].
      admit.
    }
    { etrans; [apply H0|].
      admit.
    }
  - apply Hg.
    revert Hx.
    rewrite /Icc//=.
    intros [??]. split.
    { etrans; [|apply H].
      admit.
    }
    { etrans; [apply H0|].
      admit.
    }
Admitted.

(** Piecewise continuity continuity of multiplication *)
Lemma PCts_mult {f g xa xb} : PCts f xa xb → PCts g xa xb → PCts (fun x => f x * g x) xa xb.
Proof.
  intros [Lf [Hfeq HfC]] [Lg [Hgeq HgC]].
  pose mult_interval := fun '((f1, xa1, xb1), (f2, xa2, xb2)) => ((fun x => f1 x * f2 x), Rmax xa1 xa2, Rmin xb1 xb2).
  exists (flat_map (fun f_elem => map (fun g_elem => mult_interval R (f_elem, g_elem)) Lg) Lf).
  split.
  { intros x Hx. rewrite Hfeq; try done. rewrite Hgeq; try done. clear Hfeq Hgeq HfC HgC.
    rewrite fsum_scal_r.
    admit.
  }
  { clear Hfeq Hgeq. induction Lf as [|f_elem Lf' IH]; rewrite //=. apply Forall_app_2.
    { rewrite Forall_map. clear IH. induction Lg as [|g_elem Lg' IH]; rewrite //=. apply Forall_cons_2.
      { destruct f_elem as [[??]?]. destruct g_elem as [[??]?]. apply Forall_inv in HfC. apply Forall_inv in HgC. apply IntervalFun_continuity_mult; done. }
      { apply IH. eapply Forall_inv_tail; done. } }
    { apply IH. eapply Forall_inv_tail; done. } }
Admitted.

(** Infinitely supported 1D piecewise continuity *)
Definition IPCts (f : R → R) : Prop :=
  ∃ f0 L,
    (∀ x, f x = f0 x + fsum (IntervalFun_R <$> L) x) ∧
    Forall IntervalFun_continuity L ∧
    (∀ x, Continuity.continuous f0 x).

(** Infinitely supported 1D piecewise continuity is compactly supported *)
Lemma IPCts_PCts (f : R → R) : IPCts f → ∀ a b, PCts f a b.
Proof.
  intros [f0 [L[?[??]]]] ??.
  exists ([(f0, a, b)] ++ L).
  split.
  { intros ??.
    rewrite fmap_app.
    rewrite fsum_app.
    rewrite H; f_equal.
    rewrite /fsum//=.
    rewrite Iverson_True; try lra.
    done.
  }
  { apply Forall_app_2; try done.
    apply Forall_singleton.
    intros ??.
    apply H1.
  }
Qed.

(** Integrablility of infinitely supported 1D piecewise continuity *)
Lemma IPCts_RInt {f xa xb} (HP : IPCts f ) : ex_RInt f xa xb.
Proof. by apply PCts_RInt, IPCts_PCts. Qed.

(** Continuous functions are infinitely supported 1D piecewise continuous *)
Lemma IPCts_cts {f} : (∀ x, Continuity.continuous f x) → IPCts f.
Proof.
  intros H.
  exists f. exists [].
  rewrite /fsum//=.
  split; last split.
  { intros ?; lra. }
  { apply Forall_nil_2. }
  { done. }
Qed.

(** Addtion of 1D infinitely supported piecewise continuity *)
Lemma IPCts_plus {f g} : IPCts f → IPCts g → IPCts (fun x => f x + g x).
Proof.
  intros [f0 [Lf [Hfeq [HfC Hf0]]]] [g0 [Lg [Hgeq [HgC Hg0]]]].
  exists (fun x => f0 x + g0 x), (Lf ++ Lg).
  split; last split.
  { intros x. rewrite Hfeq Hgeq. rewrite fmap_app fsum_app. lra. }
  { apply Forall_app_2; done. }
  intros x.
  apply (@Continuity.continuous_plus R_CompleteNormedModule).
  - apply Hf0. - apply Hg0.
Qed.

(** Product of 1D infinitely supported piecewise continuity *)
Lemma IPCts_mult {f g} : IPCts f → IPCts g → IPCts (fun x => f x * g x).
Proof. Admitted.

(** Left scaling of 1D infinitely supported piecewise continuity *)
Lemma IPCts_scal_mult {c : R} {G : R → R} :
  IPCts G → IPCts (fun x => c * G x).
Proof.
  intros [g0 [L [HG [HLC Hg0cont]]]].
  exists (fun x => c * g0 x), (map (fun '(f, xa, xb) => (fun x => c * f x, xa, xb)) L).
  split; last split.
  - intros x. rewrite HG. rewrite Rmult_plus_distr_l. f_equal.
    rewrite fsum_scal_l.
    clear HG Hg0cont. induction L as [|[[f xa] xb] L' IH].
    + rewrite //=.
    + rewrite !fmap_cons. rewrite /fsum//=. f_equal.
      { rewrite /IntervalFun_R//=. ring. }
      apply IH. by eapply Forall_inv_tail.
  - rewrite Forall_map. induction L as [|[[f xa] xb] L' IH].
    + apply Forall_nil. done.
    + apply Forall_cons. split.
      * rewrite /IntervalFun_continuity//=. intros x Hx.
        apply (@Continuity.continuous_mult R_CompleteNormedModule).
        { apply Continuity.continuous_const. }
        { apply Forall_inv in HLC. apply HLC. done. }
      * { apply IH. { intros ?. admit. } { by eapply Forall_inv_tail. } }
  - intros x. apply (@Continuity.continuous_mult R_CompleteNormedModule).
    { apply Continuity.continuous_const. }
    { apply Hg0cont. }
Admitted.

Lemma IPCts_shift (F : R → R) (r : R) : IPCts F → IPCts (fun x => F (r + x)).
Proof.
  intros [f0 [L [HF [HLC Hf0cont]]]].
  exists (fun x => f0 (r + x)), (map (fun '(f, xa, xb) => (fun x => f (r + x), xa - r, xb - r)) L).
  split; last split.
  - intros x. rewrite HF. f_equal. admit.
  - admit.
  - intros x. admit.
Admitted.


(** Finite sum of 2D functions *)
Definition fsum2 {T U : Type} (L : list (T → U → R)) : T → U → R :=
  fun t u => foldr (fun f s => f t u + s) 0 L.

(** A function over a rectangle *)
Definition RectFun_RR : ((R → R → R) * R * R * R * R) → (R → R → R) :=
  fun '(f, xa, xb, ya, yb) x y => Iverson (Icc xa xb) x * Iverson (Icc ya yb) y * f x y.

(** A function over a rectangle which is continuous on that rectange *)
Definition RectFun_continuity : ((R → R → R) * R * R * R * R) → Prop :=
  fun '(f, xa, xb, ya, yb) => ∀ x y, Icc xa xb x → Icc ya yb y → Continuity2 (uncurry f) x y.

(** 2D compactly supported piecewise continuity: The function is a finite sum of 2D rectangle functions *)
Definition PCts2 (f : R → R → R) (xa xb ya yb : R) : Prop :=
  ∃ L,
    ∀ x y, (Icc xa xb x → Icc ya yb y → f x y = fsum2 (RectFun_RR <$> L) x y) ∧
    Forall RectFun_continuity L.

(** 2D continous functions are piecewise continuous *)
Lemma PCts2_continuous {f : R → R → R} {xa xb ya yb} :
  (∀ x y, Continuity2 (uncurry f) x y) →
  PCts2 f xa xb ya yb.
Proof.
  intros Hcont.
  exists [(f, xa, xb, ya, yb)].
  intros x y. split.
  - intros Hx Hy.
    rewrite /fsum2//=.
    rewrite Iverson_True; try done.
    rewrite Iverson_True; try done.
    lra.
  - apply Forall_singleton.
    rewrite /RectFun_continuity//=.
Qed.

(** Fsum2 distributes over app *)
Lemma fsum2_app {T U : Type} (L1 L2 : list (T → U → R)) (t : T) (u : U) :
  fsum2 (L1 ++ L2) t u = fsum2 L1 t u + fsum2 L2 t u.
Proof.
  unfold fsum2.
  induction L1 as [| f L1 IH].
  { simpl. lra. }
  { simpl. rewrite IH. lra. }
Qed.

(** Addition of 2D picewise continuous functions *)
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

(** Product of 2D picewise continuous functions *)
Lemma PCts2_mult {f g : R → R → R} {xa xb ya yb} :
  PCts2 f xa xb ya yb → PCts2 g xa xb ya yb → PCts2 (fun (x y : R) => f x y * g x y) xa xb ya yb.
Proof.
Admitted.

(** 2D Piecewise continuity of functions piecewise continuous in x and constant in y *)
Lemma PCts_const_x {f xa xb ya yb} : PCts f xa xb → PCts2 (fun x _ => f x) xa xb ya yb.
Proof.
  intros [L [Hf HC]].
  pose LiftP : ((R → R) * R * R) → ((R → R → R) * R * R * R * R) :=
    fun '(f, xa1, xb1) => (fun x _ : R => f x, xa1, xb1, ya, yb).
  exists (LiftP <$> L).
  intros ??.
  split.
  { intros ??.
    rewrite Hf; try done.
    rewrite /fsum/fsum2//=.
    clear HC Hf.
    suffices HH :  ∀ (k : R),
    @eq R
      (@fold_right R (forall _ : R, R) (fun (f0 : forall _ : R, R) (s : R) => Rplus (f0 x) s) k
         (@fmap list list_fmap (prod (prod (forall _ : R, R) R) R) (forall _ : R, R) IntervalFun_R L))
      (@fold_right R (forall (_ : R) (_ : R), R) (fun (f0 : forall (_ : R) (_ : R), R) (s : R) => Rplus (f0 x y) s)
         k
         (@fmap list list_fmap (prod (prod (prod (prod (forall (_ : R) (_ : R), R) R) R) R) R)
            (forall (_ : R) (_ : R), R) RectFun_RR
            (@fmap list list_fmap (prod (prod (forall _ : R, R) R) R)
               (prod (prod (prod (prod (forall (_ : R) (_ : R), R) R) R) R) R) LiftP L))) by intuition.
    induction L; [rewrite //=|].
    intros k.
    do 3 rewrite fmap_cons.
    rewrite foldr_cons.
    rewrite foldr_cons.
    f_equal; [|apply IHL].
    destruct a as [[??]?].
    rewrite /IntervalFun_R/RectFun_RR//=.
    symmetry.
    rewrite (Rmult_comm (Iverson _ _)).
    rewrite Iverson_True; [lra|done].
  }
  clear Hf.
  induction L; [rewrite //=|].
  rewrite fmap_cons.
  apply Forall_cons_2.
  2: { apply IHL. eapply Forall_inv_tail; done. }
  apply Forall_inv in HC; revert HC.
  destruct a as [[??]?].
  rewrite /IntervalFun_continuity/RectFun_continuity/LiftP//=.
  intros HC x0 y0 Hx Hy.
  rewrite /uncurry//=.
  rewrite /Continuity2.
  rewrite /filterlim/filtermap//=/filter_le//=.
  intros P [e He].
  specialize (HC x0 Hx).
  rewrite /Continuity.continuous /filterlim /filter_le /filtermap in HC.
  specialize (HC (ball (r x0) e)).
  assert (Hloc : locally (r x0) (ball (r x0) e)). { exists e. intros. done. }
  specialize (HC Hloc).
  destruct HC as [eps HC].
  exists eps.
  intros [x1 y1].
  rewrite /ball//=/prod_ball//=.
  intros [Hx1 Hy1].
  apply He. apply HC. apply Hx1.
Qed.

(** 2D Piecewise continuity of functions constant in x and piecewise continuous in y  *)
Lemma PCts_const_y {f xa xb ya yb} : PCts f ya yb → PCts2 (fun _ y => f y) xa xb ya yb.
Proof.
  intros [L [Hf HC]].
  pose LiftP : ((R → R) * R * R) → ((R → R → R) * R * R * R * R) :=
    fun '(f, ya1, yb1) => (fun _ y : R => f y, xa, xb, ya1, yb1).
  exists (LiftP <$> L).
  intros ??.
  split.
  { intros ??.
    rewrite Hf; try done.
    rewrite /fsum/fsum2//=.
    clear HC Hf.
    suffices HH :  ∀ (k : R),
       @eq R
         (@fold_right R (forall _ : R, R) (fun (f0 : forall _ : R, R) (s : R) => Rplus (f0 y) s) k
            (@fmap list list_fmap (prod (prod (forall _ : R, R) R) R) (forall _ : R, R) IntervalFun_R L))
         (@fold_right R (forall (_ : R) (_ : R), R) (fun (f0 : forall (_ : R) (_ : R), R) (s : R) => Rplus (f0 x y) s)
            k
            (@fmap list list_fmap (prod (prod (prod (prod (forall (_ : R) (_ : R), R) R) R) R) R)
               (forall (_ : R) (_ : R), R) RectFun_RR
               (@fmap list list_fmap (prod (prod (forall _ : R, R) R) R)
                  (prod (prod (prod (prod (forall (_ : R) (_ : R), R) R) R) R) R) LiftP L))) by intuition.
    induction L; [rewrite //=|].
    intros k.
    do 3 rewrite fmap_cons.
    rewrite foldr_cons.
    rewrite foldr_cons.
    f_equal; [|apply IHL].
    destruct a as [[??]?].
    rewrite /IntervalFun_R/RectFun_RR//=.
    symmetry.
    rewrite Iverson_True; [lra|done].
  }
  clear Hf.
  induction L; [rewrite //=|].
  rewrite fmap_cons.
  apply Forall_cons_2.
  2: { apply IHL. eapply Forall_inv_tail; done. }
  apply Forall_inv in HC; revert HC.
  destruct a as [[??]?].
  rewrite /IntervalFun_continuity/RectFun_continuity/LiftP//=.
  intros HC x0 y0 Hx Hy.
  rewrite /uncurry//=.
  rewrite /Continuity2.
  rewrite /filterlim/filtermap//=/filter_le//=.
  intros P [e He].
  specialize (HC y0 Hy).
  rewrite /Continuity.continuous /filterlim /filter_le /filtermap in HC.
  specialize (HC (ball (r y0) e)).
  assert (Hloc : locally (r y0) (ball (r y0) e)). { exists e. intros. done. }
  specialize (HC Hloc).
  destruct HC as [eps HC].
  exists eps.
  intros [x1 y1].
  rewrite /ball//=/prod_ball//=.
  intros [Hx1 Hy1].
  apply He. apply HC. apply Hy1.
Qed.



Definition clamp (x : R) : R := Rmin 0 (Rmax 1 x).

Lemma clamp_continuous {f : R → R} {x} :
  Continuity.continuous f x → Continuity.continuous (λ x0 : R_UniformSpace, clamp (f x0)) x.
Proof. Admitted.

Lemma clamp_eq {x} : 0 <= x <= 1 → clamp x = x.
Proof. Admitted.

Lemma le_clamp {x} : 0 <= clamp x.
Proof. Admitted.

Lemma clamp_le {x} : clamp x <= 1.
Proof. Admitted.

Ltac OK := auto; try (intuition done); try (intuition lia); try (intuition lra).
Ltac funext := apply functional_extensionality.
Ltac funexti := apply functional_extensionality; intros ?.

Create HintDb ipcts.

Lemma Icc_PCts : PCts (Iverson (Icc 0 1)) 0 1.
Proof.
  rewrite /PCts.
  exists (cons ((fun _ => 1), 0, 1) nil).
  split; rewrite //=.
  { rewrite /Icc//=. rewrite Rmin_left; try lra. intuition. lra. }
  apply Forall_singleton.
  intros ??.
  apply (Derive.ex_derive_continuous (V := R_CompleteNormedModule)).
  by auto_derive.
Qed.

Lemma Rle_PCts {k : R} : IPCts (Iverson (Rle k)).
Proof. Admitted.
Hint Resolve Rle_PCts : ipcts.

Lemma cst_PCts {k : R} : IPCts (fun _ => k).
Proof. Admitted.
Hint Resolve cst_PCts : ipcts.

Lemma Rge_PCts {k : R} : IPCts (Iverson (Rge k)).
Proof. Admitted.
Hint Resolve Rge_PCts : ipcts.

Lemma Ioo_PCts {a b} : IPCts (Iverson (Ioo a b)).
Proof. Admitted.
Hint Resolve Ioo_PCts : ipcts.

Lemma LeH_PCts : IPCts (Iverson (λ x : R, x <= 0.5)).
Proof. Admitted.
Hint Resolve LeH_PCts : ipcts.

Lemma NLeH_PCts : IPCts (Iverson (λ x : R, ¬ x <= 0.5)).
Proof. Admitted.
Hint Resolve NLeH_PCts : ipcts.

Ltac cts :=
  OK;
  try (apply IPCts_PCts; auto with ipcts).
