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
  
Lemma PCts_point f xa :
  PCts f xa xa.
Proof.
  exists ([(λ _, f xa , xa, xa)]).
  simpl.
  split.
  - intros.
    rewrite Iverson_True; last done.
    unfold Icc, Rmin, Rmax in *.
    case_match; try lra.
    rewrite Rmult_1_l Rplus_0_r.
    f_equal. lra.
  - rewrite Forall_singleton.
    intros ? ? .
    apply Continuity.continuous_const.
Qed. 
  
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

Lemma fsum_cons {T : Type} hd (L : list (T → R)) (t : T) :
  fsum (hd :: L) t = hd t + fsum L t.
Proof.
  done.
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

Definition PCts'' (f : R → R) (xa xb : R) : Prop :=
  ∃ L, (∀ x, Ioo xa xb x → f x = fsum (IntervalFun_R <$> L) x) ∧ Forall IntervalFun_continuity L.

Lemma PCts''_PCts f xa xb:
  PCts'' f xa xb -> PCts f xa xb.
Proof.
  destruct (decide (xa = xb)); first (subst; intros; apply PCts_point).
  intros [L[H1 H2]].
  exists ((λ _, f xa - fsum (IntervalFun_R <$> L) xa, xa, xa)::(λ _, f xb - fsum (IntervalFun_R <$> L) xb, xb, xb)::L).
  split.
  - simpl.
    intros x ?.
    rewrite /fmap.
    unfold Iverson, Icc, Ioo, Rmin, Rmax in *; repeat case_match; try lra;
                                    try replace x with xa by lra; try replace x with xb by lra; try lra; rewrite H1; rewrite /fmap; lra.
  - repeat rewrite Forall_cons; repeat split; last done.
    + intros ??. apply Continuity.continuous_const.
    + intros ??. apply Continuity.continuous_const.
Qed.

Lemma PCts_ext f f' xa xb:
  (∀ x, Ioo xa xb x-> f x = f' x) ->
  PCts f xa xb ->
  PCts f' xa xb.
Proof.
  intros H [L [H1 H2]].
  apply PCts''_PCts.
  exists L.
  split; last done.
  intros. rewrite -H; last done.
  apply H1. by apply Ioo_Icc.
Qed. 

Lemma PCts_shift f f' xa xb xa' xb' r:
  xa' = xa + r -> xb' = xb + r ->
  (∀ x, Ioo xa xb x-> f x = f' (x+r)) ->
  PCts f xa xb -> 
  PCts f' xa' xb'.
Proof.
  intros -> -> H1 [l[K1 K2]].
  apply PCts''_PCts.
  exists ((λ '(g, y, z), (λ x, g(x-r), y+r, z+r))<$>l).
  assert (∀ x, Ioo (xa+r) (xb+r) x-> f (x-r) = f' (x)) as H1'.
  { intros.
    rewrite H1; first (f_equal; lra).
    unfold Ioo, Rmax, Rmin in *. repeat case_match; lra.
  }
  split.
  - intros.
    rewrite -H1'; last done.
    rewrite K1; last first.
    { unfold Ioo, Icc, Rmax, Rmin in *. repeat case_match; lra. }
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

Lemma PCts_unit_implies_all_nat (F:nat -> R -> R) (n:nat):
  (∀ k, PCts (F k) 0 1) ->
  PCts (λ y0 : R, F (Z.to_nat (Int_part y0)) (frac_part y0)) (0) n.
Proof.
  intros ?.
  induction n as [|n' IHn].
  - replace (INR 0) with 0 by done.
    apply PCts_point.
  - rewrite S_INR.
    eapply PCts_split; [|done|].
    + pose proof pos_INR n'. unfold Rmin, Rmax; case_match; lra.
    + eapply (PCts_shift (F n') _ 0 1  _ _ (INR n')); try lra; last done.
      intros.
      rewrite /frac_part.
      f_equal.
      * erewrite <-(Int_part_spec _ (Z.of_nat n')); first lia.
        rewrite -INR_IZR_INZ.
        unfold Ioo, Rmin, Rmax in *. case_match; lra.
      * erewrite <-(Int_part_spec _ (Z.of_nat n')).
        -- rewrite -INR_IZR_INZ. lra.
        -- rewrite -INR_IZR_INZ.
           unfold Ioo, Rmin, Rmax in *. case_match; lra.
Qed. 

Lemma PCts_unit_implies_all (F:nat -> R -> R) r:
  (0<=r) ->
  (∀ k, PCts (F k) 0 1) ->
  PCts (λ y0 : R, F (Z.to_nat (Int_part y0)) (frac_part y0)) (0) r.
Proof.
  intros.
  pose proof archimed r.
  assert (PCts (λ y0 : R, F (Z.to_nat (Int_part y0)) (frac_part y0)) 0 (IZR (up r))).
  - rewrite -(Z2Nat.id (up r)). 
    + rewrite -INR_IZR_INZ.
      by apply PCts_unit_implies_all_nat.
    + apply le_IZR.
      lra.
  - eapply PCts_subset; last done; unfold Rmin, Rmax; repeat case_match; lra.
Qed. 
(*   - (* r is negative *) *)
(*     assert (PCts (λ y0 : R, F (Z.to_nat (Int_part y0)) (frac_part y0)) 0 (IZR (up r - 1))) as H'. *)
(*     + replace (up r - 1)%Z with (- (1-up r))%Z by lia. *)
(*       rewrite opp_IZR. *)
(*       rewrite -(Z2Nat.id ((1-up r))). *)
(*       * rewrite -INR_IZR_INZ. *)
(*         by apply PCts_unit_implies_all2. *)
(*       * apply le_IZR. rewrite minus_IZR. lra. *)
(*     + rewrite minus_IZR in H'. eapply PCts_subset; last done; *)
(*       unfold Rmin, Rmax; repeat case_match; lra. *)
(* Qed. *)

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
  Rmin xa xb <= Rmax ya yb ->
  Rmin ya yb <= Rmax xa xb ->
  IntervalFun_continuity (f, xa, xb) →
  IntervalFun_continuity (g, ya, yb) →
  IntervalFun_continuity ((fun x => f x * g x), Rmax (Rmin xa xb) (Rmin ya yb), Rmin (Rmax xa xb) (Rmax ya yb)).
Proof.
  rewrite /IntervalFun_continuity//=.
  intros H1 H2 Hf Hg x Hx.
  apply (@Continuity.continuous_mult R_CompleteNormedModule).
  - unfold Icc, Rmin, Rmax in *. apply Hf.
    repeat case_match; lra.
  - unfold Icc, Rmin, Rmax in *. apply Hg.
    repeat case_match; lra.
Qed.

(** Piecewise continuity continuity of multiplication *)
Lemma PCts_mult {f g xa xb} : PCts f xa xb → PCts g xa xb → PCts (fun x => f x * g x) xa xb.
Proof.
  intros [Lf [Hfeq HfC]] [Lg [Hgeq HgC]].
  pose (mult_interval := fun '((f1, xa1, xb1), (f2, xa2, xb2)) =>
                          if bool_decide (Rmin xa1 xb1 <= Rmax xa2 xb2 /\ Rmin xa2 xb2 <= Rmax xa1 xb1)
                          then ((fun (x:R) => f1 x * f2 x), Rmax (Rmin xa1 xb1) (Rmin xa2 xb2), Rmin (Rmax xa1 xb1) (Rmax xa2 xb2)) else (λ x, 0, 0 ,0)).
  exists (flat_map (fun f_elem => map (fun g_elem => mult_interval (f_elem, g_elem)) Lg) Lf).
  split.
  { intros x Hx. rewrite Hfeq; try done. rewrite Hgeq; try done. clear Hfeq Hgeq HfC HgC.
    revert Lf.
    induction Lg as [|hd ? IHg].
    { intros Lf. induction Lf; simpl; first lra.
      rewrite -IHLf. simpl. lra. }
    intros Lf. induction Lf as [|hd' ? IHf]; first (simpl; lra). 
    rewrite {1}/flat_map.
    rewrite -/(flat_map _ _).
    rewrite fmap_app.
    rewrite fsum_app.
    rewrite -IHf.
    etrans.
    - rewrite !fmap_cons.
      rewrite /fsum.
      rewrite !foldr_cons.
      rewrite -!/(fsum _ _).
      rewrite Rmult_plus_distr_r.
      by rewrite !Rmult_plus_distr_l.
    - etrans; last first.
      + rewrite map_cons fmap_cons {1}/fsum foldr_cons -/(fsum _ _).
        by rewrite fmap_cons {3}/fsum foldr_cons -/(fsum _ _).
      + assert (IntervalFun_R hd' x * IntervalFun_R hd x + IntervalFun_R hd' x * fsum (IntervalFun_R <$> Lg) x =
  IntervalFun_R (mult_interval (hd', hd)) x +
    fsum (IntervalFun_R <$> map (λ g_elem : (R → R) * R * R, mult_interval (hd', g_elem)) Lg) x); last lra.
        f_equal.
        * rewrite /mult_interval.
          do 4 case_match; subst.
          unfold IntervalFun_R, Iverson, Icc, Rmin, Rmax.
          case_bool_decide; repeat (lra||case_match).
        * clear -Hx.
          induction Lg as [|hd ? IHL]; first (simpl; lra).
          rewrite fmap_cons.
          rewrite /fsum foldr_cons.
          rewrite -/(fsum _ _).
          rewrite map_cons fmap_cons.
          rewrite foldr_cons.
          rewrite -/(fsum _ _).
          rewrite -IHL.
          assert (IntervalFun_R hd' x * (IntervalFun_R hd x) =
                  IntervalFun_R (mult_interval (hd', hd)) x ); last lra.
          rewrite /mult_interval.
          do 4 case_match; subst.
          unfold IntervalFun_R, Iverson, Icc, Rmin, Rmax.
          case_bool_decide; repeat (lra||case_match).
  }
  { clear Hfeq Hgeq. induction Lf as [|f_elem Lf' IH]; rewrite //=. apply Forall_app_2.
    { rewrite Forall_map. clear IH. induction Lg as [|g_elem Lg' IH]; rewrite //=. apply Forall_cons_2.
      { destruct f_elem as [[??]?]. destruct g_elem as [[??]?]. apply Forall_inv in HfC. apply Forall_inv in HgC. case_bool_decide; first apply IntervalFun_continuity_mult; try (done||lra).
        intros ??. apply Continuity.continuous_const.
      }
      { apply IH. eapply Forall_inv_tail; done. } }
    { apply IH. eapply Forall_inv_tail; done. } }
Qed.

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
Proof.
  intros [f1[L1[H1[H2 H3]]]][f2[L2[H4[H5 H6]]]].
  pose (mult_interval := fun '((f1, xa1, xb1), (f2, xa2, xb2)) =>
                          if bool_decide (Rmin xa1 xb1 <= Rmax xa2 xb2 /\ Rmin xa2 xb2 <= Rmax xa1 xb1)
                          then ((fun (x:R) => f1 x * f2 x), Rmax (Rmin xa1 xb1) (Rmin xa2 xb2), Rmin (Rmax xa1 xb1) (Rmax xa2 xb2)) else (λ x, 0, 0 ,0)).
  exists (λ x, f1 x * f2 x).
  exists ((flat_map (fun f_elem => map (fun g_elem => mult_interval (f_elem, g_elem)) L2) L1) ++
    ((λ '(f', a', b'), (λ x', f1 x' * f' x',a',b'))<$>L2) ++
    ((λ '(f', a', b'), (λ x', f' x' * f2 x' ,a',b'))<$>L1))
  .
  repeat split; last first.
  { intros.
    by apply: Continuity.continuous_mult.
  }
  { apply Forall_app; split; last (apply Forall_app; split).
    - clear -H2 H5.
      rewrite Forall_flat_map.
      setoid_rewrite Forall_map.
      generalize dependent L2.
      induction L1 as [|? ? IHL1]; first (intros; by apply Forall_nil).
      intros ? H5.
      rewrite Forall_cons.
      split; last first.
      + apply IHL1; last done.
        by eapply Forall_inv_tail.
      + rewrite Forall_cons in H2.
        destruct H2 as [H2 ?]. clear -H5 H2.
        revert H5.
        induction L2; first (intros; by apply Forall_nil).
        rewrite Forall_cons.
        intros [H' ?].
        rewrite Forall_cons.
        split; last naive_solver.
        rewrite /mult_interval.
        do 4 case_match; subst.
        case_bool_decide.
        * intros ??.
          unfold IntervalFun_continuity in *.
          apply: Continuity.continuous_mult.
          -- apply H2. unfold Icc, Rmax, Rmin in *. repeat case_match; lra.
          -- apply H'. unfold Icc, Rmax, Rmin in *. repeat case_match; lra.
        * intros ??. apply Continuity.continuous_const.
    - clear -H5 H3.
      revert H5.
      induction L2; first (intros; by apply Forall_nil).
      rewrite Forall_cons.
      intros [K1 K2].
      rewrite fmap_cons Forall_cons; split; last naive_solver.
      do 2 case_match; subst.
      intros ??.
      apply: Continuity.continuous_mult; naive_solver.
    - clear -H2 H6.
      revert H2.
      induction L1; first (intros; by apply Forall_nil).
      rewrite Forall_cons.
      intros [K1 K2].
      rewrite fmap_cons Forall_cons; split; last naive_solver.
      do 2 case_match; subst.
      intros ??.
      apply: Continuity.continuous_mult; naive_solver.
  }
  clear -H1 H4.
  intros x.
  rewrite H1 H4.
  clear H1 H4.
  revert L2.
  induction L1 as [|a L1 IHL1].
  { intros L2.
    rewrite app_nil_r.
    simpl.
    induction L2.
    - simpl. lra.
    - do 3 rewrite fmap_cons.
      do 2 rewrite fsum_cons.
      assert (f1 x * IntervalFun_R a x = IntervalFun_R (let '(f', a', b') := a in (λ x' : R, f1 x' * f' x', a', b')) x); last lra.
      do 2 case_match; subst.
      unfold IntervalFun_R, Iverson, Icc, Rmin, Rmax.
      repeat case_match; lra.
  }
  intros L2.
  rewrite fmap_cons fsum_cons.
  trans ((f1 x + fsum (IntervalFun_R <$> L1) x) * (f2 x + fsum (IntervalFun_R <$> L2) x) +
           IntervalFun_R a x * (f2 x + fsum (IntervalFun_R <$> L2) x)); first lra.
  rewrite IHL1.
  clear IHL1.
  rewrite Rplus_assoc.
  f_equal.
  rewrite /flat_map-/(flat_map _).
  rewrite fmap_cons.
  rewrite !fmap_app !fsum_app fmap_cons fsum_cons.
  assert (
  IntervalFun_R a x * (f2 x + fsum (IntervalFun_R <$> L2) x) =
  fsum (IntervalFun_R <$> map (λ g_elem : (R → R) * R * R, mult_interval (a, g_elem)) L2) x +
  ((IntervalFun_R (let '(f', a', b') := a in (λ x' : R, f' x' * f2 x', a', b')) x ))
    ); last lra.
  destruct a as [[r0 r1 ]r].
  induction L2 as [|a L2 IHL2]; first (simpl; lra).
  rewrite fmap_cons.
  rewrite fmap_cons.
  rewrite -/(map _ _).
  rewrite !fsum_cons.
  assert (IntervalFun_R (r0, r1, r) x *(IntervalFun_R a x) = IntervalFun_R (mult_interval (r0, r1, r, a)) x); last lra.
  clear.
  unfold mult_interval.
  destruct a as [[s0 s1] s].
  unfold IntervalFun_R, Iverson, Icc, Rmin, Rmax.
  case_bool_decide; repeat case_match; lra.
Qed. 
  
  
  

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
  - rewrite Forall_map. clear HG. induction L as [|[[f xa] xb] L' IH].
    + apply Forall_nil. done.
    + apply Forall_cons. split.
      * rewrite /IntervalFun_continuity//=. intros x Hx.
        apply (@Continuity.continuous_mult R_CompleteNormedModule).
        { apply Continuity.continuous_const. }
        { apply Forall_inv in HLC. apply HLC. done. }
      * { apply IH. { by eapply Forall_inv_tail. } }
  - intros x. apply (@Continuity.continuous_mult R_CompleteNormedModule).
    { apply Continuity.continuous_const. }
    { apply Hg0cont. }
Qed. 

Lemma IPCts_shift (F : R → R) (r : R) : IPCts F → IPCts (fun x => F (r + x)).
Proof.
  intros [f0 [L [HF [HLC Hf0cont]]]].
  exists (fun x => f0 (r + x)), (map (fun '(f, xa, xb) => (fun x => f (r + x), xa - r, xb - r)) L).
  split; last split.
  - intros x. rewrite HF. f_equal.
    clear.
    induction L as [|? ? IHL]; first done.
    simpl. rewrite IHL.
    f_equal.
    do 2 case_match. subst.
    rewrite /IntervalFun_R.
    unfold Icc, Iverson, Rmin, Rmax. repeat case_match; lra.
  - clear -HLC.
    induction L as [|? ? IHL]; first done.
    apply Forall_cons.
    split; last (apply IHL; by eapply Forall_inv_tail).
    repeat case_match; subst.
    unfold IntervalFun_continuity in *.
    apply Forall_cons in HLC as [H1 H2].
    intros. 
    apply Continuity.continuous_comp; last apply H1.
    + apply: Derive.ex_derive_continuous.
      by auto_derive.
    + unfold Icc, Rmin, Rmax in *. repeat case_match; lra.
  - intros x. 
    apply Continuity.continuous_comp; last done.
    apply: Derive.ex_derive_continuous.
    by auto_derive.
Qed. 

Lemma IPCts_Iio L:
  IPCts (Iverson (Iio L)).
Proof.
Admitted.

Lemma IPCts_Ioi L:
  IPCts (Iverson (Ioi L)).
Proof.
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
    (∀ x y, (Icc xa xb x → Icc ya yb y → f x y = fsum2 (RectFun_RR <$> L) x y)) ∧
    Forall RectFun_continuity L.

(** 2D continous functions are piecewise continuous *)
Lemma PCts2_continuous {f : R → R → R} {xa xb ya yb} :
  (∀ x y, Continuity2 (uncurry f) x y) →
  PCts2 f xa xb ya yb.
Proof.
  intros Hcont.
  exists [(f, xa, xb, ya, yb)].
  split.
  - intros x y Hx Hy.
    rewrite /fsum2//=.
    rewrite Iverson_True; try done.
    rewrite Iverson_True; try done.
    lra.
  - apply Forall_singleton.
    rewrite /RectFun_continuity//=.
Qed.


Lemma fsum2_cons {T U : Type} hd (L : list (T → U → R)) (t : T) (u : U) :
  fsum2 (hd ::  L) t u = hd t u  + fsum2 L t u.
Proof.
  done. 
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
  intros [Lf [Hf]] [Lg [Hg]].
  unfold PCts2.
  exists (Lf ++ Lg).
  split.
  {
    intros x y Hx Hy.
    pose proof (Hf x y) as Hfeq.
    pose proof (Hg x y) as Hgeq.
    rewrite (Hfeq Hx Hy).
    rewrite (Hgeq Hx Hy).
    rewrite fmap_app.
    rewrite fsum2_app.
    reflexivity.
  }
  {
    apply Forall_app.
    split; naive_solver.
  }
Qed.

(** Rect continuity of multiplication *)
Lemma RectFun_continuity_mult {f g xa1 xb1 ya1 yb1 xa2 xb2 ya2 yb2} :
  Rmin xa1 xb1 <= Rmax xa2 xb2 ->
  Rmin xa2 xb2 <= Rmax xa1 xb1 ->
  Rmin ya1 yb1 <= Rmax ya2 yb2 ->
  Rmin ya2 yb2 <= Rmax ya1 yb1 ->
  RectFun_continuity (f, xa1, xb1, ya1, yb1) →
  RectFun_continuity (g, xa2, xb2, ya2, yb2) →
  RectFun_continuity ((fun x y=> f x y * g x y ), Rmax (Rmin xa1 xb1) (Rmin xa2 xb2), Rmin (Rmax xa1 xb1) (Rmax xa2 xb2), Rmax (Rmin ya1 yb1) (Rmin ya2 yb2), Rmin (Rmax ya1 yb1) (Rmax ya2 yb2)).
Proof.
  rewrite /RectFun_continuity.
  intros H1 H2 H3 H4 Hf Hg.
  intros x y K1 K2.
  unshelve epose proof Hf x y _ _ as Hf'.
  { clear H3 H4 K2. unfold Icc, Rmin, Rmax in *. repeat case_match; lra. }
  { clear H1 H2 K1. unfold Icc, Rmin, Rmax in *. repeat case_match; lra. }
  unshelve epose proof Hg x y _ _ as Hg'.
  { clear H3 H4 K2. unfold Icc, Rmin, Rmax in *. repeat case_match; lra. }
  { clear H1 H2 K1. unfold Icc, Rmin, Rmax in *. repeat case_match; lra. }
  eapply Continuity2_mult; [apply Hf'| apply Hg'|].
  intros []. simpl. lra.
Qed. 

(** Product of 2D picewise continuous functions *)
Lemma PCts2_mult {f g : R → R → R} {xa xb ya yb} :
  PCts2 f xa xb ya yb → PCts2 g xa xb ya yb → PCts2 (fun (x y : R) => f x y * g x y) xa xb ya yb.
Proof.
  intros [Lf [H1 H2]][Lg [H3 H4]].
  pose (mult_interval := fun '((f1, xa1, xb1, ya1, yb1), (f2, xa2, xb2, ya2, yb2)) =>
                           if bool_decide (Rmin xa1 xb1 <= Rmax xa2 xb2 /\ Rmin xa2 xb2 <= Rmax xa1 xb1 /\
                                           Rmin ya1 yb1 <= Rmax ya2 yb2 /\ Rmin ya2 yb2 <= Rmax ya1 yb1
                                )
                           then ((fun (x y:R) => f1 x y* f2 x y), Rmax (Rmin xa1 xb1) (Rmin xa2 xb2), Rmin (Rmax xa1 xb1) (Rmax xa2 xb2), Rmax (Rmin ya1 yb1) (Rmin ya2 yb2), Rmin (Rmax ya1 yb1) (Rmax ya2 yb2)) else (λ x y, 0, 0 ,0,0,0)).
  exists (flat_map (fun f_elem => map (fun g_elem => mult_interval (f_elem, g_elem)) Lg) Lf).
  split.
  - intros x y.
    intros.
    rewrite H1; try done.
    rewrite H3; try done.
    clear.
    revert Lg.
    induction Lf as [|a ? IHLf]; first (simpl; intros; lra).
    intros Lg.
    rewrite fmap_cons.
    rewrite /flat_map-/(flat_map _ _).
    rewrite fmap_app fsum2_app.
    rewrite fsum2_cons.
    rewrite -IHLf.
    assert (RectFun_RR a x y * fsum2 (RectFun_RR <$> Lg) x y =
  fsum2 (RectFun_RR <$> map (λ g_elem : (R → R → R) * R * R * R * R, mult_interval (a, g_elem)) Lg) x
    y); last lra.
    clear.
    induction Lg as [|a' ? IHLg]; first (simpl; lra).
    rewrite fmap_cons map_cons fmap_cons !fsum2_cons.
    rewrite -IHLg.
    assert ( RectFun_RR a x y * (RectFun_RR a' x y) =
             RectFun_RR (mult_interval (a, a')) x y ); last lra.
    unfold RectFun_RR.
    do 4 case_match; subst.
    do 4 case_match; subst.
    clear.
    unfold mult_interval.
    case_bool_decide as H; last (trans 0; last lra;
                            unfold Iverson, Icc; repeat case_match; lra).
    symmetry.
    rewrite {1}/Iverson.
    case_match; last first.
    { trans 0; first lra.
      rewrite {1 3}/Iverson.
      case_match; last lra.
      case_match; last lra.
      exfalso.
      unfold Icc, Rmin, Rmax in *.
      repeat (lra||case_match).
    }
    rewrite {1}/Iverson.
    case_match; last first.
    { trans 0; first lra.
      rewrite {2 4}/Iverson.
      case_match; last lra.
      case_match; last lra.
      exfalso.
      unfold Icc, Rmin, Rmax in *.
      repeat (lra||case_match).
    }
    rename select (Icc _ _ x) into K1.
    rename select (Icc _ _ y) into K2.
    clear -K1 K2 H.
    rewrite /(Rmin (Rmax _ _)) in K1.
    rewrite /(Rmin (Rmax _ _)) in K2.
    rewrite /(Rmax (Rmin _ _)) in K1.
    rewrite /(Rmax (Rmin _ _)) in K2.
    rewrite !Iverson_True; first lra.
    + unfold Icc in *.
      clear K1.
      unfold Rmin, Rmax in *.
      repeat case_match; lra.
    + unfold Icc in *.
      clear K2.
      unfold Rmin, Rmax in *.
      repeat case_match; lra.
    + unfold Icc in *.
      clear K1.
      unfold Rmin, Rmax in *.
      repeat case_match; lra.
    + unfold Icc in *.
      clear K2.
      unfold Rmin, Rmax in *.
      repeat case_match; lra.
  - clear H1 H3.
    revert Lg H4.
    induction Lf as [|a ? IHLf]; first (intros; by apply Forall_nil).
    intros Lg.
    intros.
    rewrite /flat_map -/(flat_map _).
    apply Forall_app. 
    apply Forall_cons in H2.
    split; last naive_solver.
    induction Lg as [|b ? IHLg]; first by apply Forall_nil.
    rewrite map_cons.
    rewrite Forall_cons in H4.
    apply Forall_cons; split; last naive_solver.
    rewrite /mult_interval.
    do 8 case_match; subst.
    case_bool_decide.
    + apply RectFun_continuity_mult; try lra; naive_solver.
    + intros ????.
      eapply (Continuity2_const 0).
      by intros [].
Qed. 

(** 2D Piecewise continuity of functions piecewise continuous in x and constant in y *)
Lemma PCts_const_x {f xa xb ya yb} : PCts f xa xb → PCts2 (fun x _ => f x) xa xb ya yb.
Proof.
  intros [L [Hf HC]].
  pose LiftP : ((R → R) * R * R) → ((R → R → R) * R * R * R * R) :=
    fun '(f, xa1, xb1) => (fun x _ : R => f x, xa1, xb1, ya, yb).
  exists (LiftP <$> L).
  split.
  { intros ????.
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
  split.
  { intros ????.
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



Definition clamp (x : R) : R := Rmax 0 (Rmin 1 x).

Lemma clamp_continuous {f : R → R} {x} :
  Continuity.continuous f x → Continuity.continuous (λ x0 : R_UniformSpace, clamp (f x0)) x.
Proof.
  intros. 
  apply Continuity.continuous_comp; first done.
  intros ? [x' H1].
  exists x'.
  rewrite /clamp.
  intros ? H2.
  apply H1.
  rewrite /ball/=/AbsRing_ball/abs/= in H2 *.
  eapply Rle_lt_trans; last exact.
  rewrite /minus/=/plus/=/opp/=/clamp/Rmin/Rmax/Rabs.
  repeat case_match; lra.
Qed.

Lemma clamp_eq {x} : 0 <= x <= 1 → clamp x = x.
Proof.
  intros ?. rewrite /clamp.
  rewrite Rmin_right; try lra.
  rewrite Rmax_right; try lra.
Qed.

Lemma le_clamp {x} : 0 <= clamp x.
Proof. rewrite /clamp. apply Rmax_l. Qed.

Lemma clamp_le {x} : clamp x <= 1.
Proof.
  rewrite /clamp.
  apply Rmax_lub; try lra.
  apply Rmin_l.
Qed.

Ltac OK := auto; try (intuition done); try (intuition lia); try (intuition lra).
Ltac funext := apply functional_extensionality.
Ltac funexti := apply functional_extensionality; intros ?.

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

Definition rect_swap (rect : (R → R → R) * R * R * R * R) : (R → R → R) * R * R * R * R :=
  let '(f, xa, xb, ya, yb) := rect in
  (fun x y => f y x, ya, yb, xa, xb).

Lemma rect_swap_cts {rect} : RectFun_continuity rect → RectFun_continuity (rect_swap rect).
Proof.
  destruct rect as [[[[??]?]?]?].
  rewrite /RectFun_continuity//=.
  intros ?????.
  rewrite //=.
  apply Continuity2_swap.
  by apply H.
Qed.
