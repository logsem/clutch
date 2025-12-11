From clutch.eris.examples.math Require Import prelude axioms series iverson sets integrals.
From clutch.eris Require Import infinite_tape.
Import Hierarchy.
Set Default Proof Using "Type*".
#[local] Open Scope R.

(** [∑] Weierstrass M test for uniform convergence
Rudin, Principles of Mathematical Analysis, 7.10 *)
Lemma UniformConverge_Series {F : R → nat → R} (UB : nat → R) :
  (∀ x n, 0 <= F x n) →
  (Series.ex_series UB) →
  (forall x n, Rabs (F x n) <= UB n) →
  filterlim (fun (M : nat) (x : R) => sum_n (F x) M) eventually (locally (λ x : R, Series.Series (F x))).
Proof.
  intros H3 H1 H2.
  rewrite filterlim_locally /eventually//=.
  intro eps.
  have H1' := H1.
  destruct H1 as [l Hl].
  have HS : Series.Series UB = l.
  { apply Series.is_series_unique. apply Hl.  }
  unfold Series.is_series in Hl.
  rewrite filterlim_locally /eventually//= in Hl.
  specialize (Hl eps).
  destruct Hl as [N HN].
  exists N.
  intros n Hn.
  rewrite /ball/=/fct_ball.
  intros t.
  specialize (HN n Hn).
  rewrite /ball/=/AbsRing_ball//=.
  rewrite /ball/=/AbsRing_ball//= in HN.
  rewrite -HS in HN.
  eapply Rle_lt_trans; [|apply HN].
  clear HN eps.
  do 2 rewrite (abs_minus (sum_n _ _) ).
  rewrite -TailSeries_eq.
  2: {
    rewrite ex_seriesC_nat.
    apply (ex_seriesC_le _ UB).
    { intros ?. split; [done|].
      etrans; [apply Rle_abs|].
      apply H2.
    }
    rewrite -ex_seriesC_nat.
    done.
  }
  rewrite -TailSeries_eq.
  2: { done. }
  (* LHS term: use triangle inequality to avoid nonnegatiity hypothesis. *)
  rewrite /TailSeries.
  etrans; first eapply Series.Series_Rabs.
  { rewrite ex_seriesC_nat.
    apply (@ex_SeriesC_nat_shiftN_r' (fun n' => Rabs (F t n')) (S n)).
    eapply ex_seriesC_le.
    2: { rewrite -ex_seriesC_nat. apply H1'. }
    intros.
    split; [apply Rabs_pos|].
    apply H2.
  }
  (* RHS term: It's a series of nonnegative values. *)
  rewrite /abs//=.
  rewrite Rabs_right.
  2: {
    apply Rle_ge.
    rewrite -SeriesC_nat.
    apply SeriesC_ge_0'.
    intros ?.
    rewrite /compose//=.
    etrans; [|eapply (H2 0%R)].
    apply Rabs_pos.
  }
  do 2 rewrite -SeriesC_nat.
  apply SeriesC_le.
  2: {
    rewrite /compose//=.
    apply (@ex_SeriesC_nat_shiftN_r' UB (S n)).
    rewrite -ex_seriesC_nat.
    apply H1'.
  }
  intros n'.
  split; [apply Rabs_pos|].
  by apply H2.
Qed.

(** [∑∫] Limit exchange for a the integral of a uniformly convergent sequence of functions *)
Lemma Exchange1 {f : nat → R → R_CompleteNormedModule} {a b : R} {F : R → R}
  (Hex : ∀ n, ex_RInt (f n) a b) (Hunif : filterlim f eventually (locally F)) :
  filterlim (λ n : nat, RInt (f n) a b) eventually (locally (RInt F a b)).
Proof.
  have H (n : nat) : is_RInt (f n) a b (RInt (f n) a b).
  { apply (RInt_correct (V := R_CompleteNormedModule)), Hex. }
  destruct (filterlim_RInt f a b eventually eventually_filter _ _ H Hunif) as [I [HL HF]].
  rewrite (is_RInt_unique F a b I HF).
  done.
Qed.

(** [∫∫{∞}] Limit exchange for a the integral of a uniformly convergent family of functions (R-indexed) *)
Lemma Exchange2 {f : R → R → R_CompleteNormedModule} {a b : R} {F : R → R}
  (Hex : ∀ r, ex_RInt (f r) a b) (Hunif : filterlim f (Rbar_locally Rbar.p_infty) (locally F)) :
  filterlim (λ r : R, RInt (f r) a b) (Rbar_locally Rbar.p_infty) (locally (RInt F a b)).
Proof.
  have H (r : R) : is_RInt (f r) a b (RInt (f r) a b).
  { apply (RInt_correct (V := R_CompleteNormedModule)), Hex. }
  destruct (filterlim_RInt f a b (Rbar_locally Rbar.p_infty) (Rbar_locally_filter Rbar.p_infty) _ _ H Hunif)
      as [I [HL HF]].
  rewrite (is_RInt_unique F a b I HF).
  done.
Qed.

(** [∑f∑f] Fubini's theorem for finite sums *)
Lemma FubiniFinite {a b M} {f : nat → R → R} (Hex : ∀ n, ex_RInt (f n) a b) :
  RInt (λ x : R, sum_n (λ n : nat, f n x) M) a b = sum_n (λ n : nat, RInt (λ x : R, f n x) a b) M.
Proof.
  induction M.
   { replace (λ x : R, sum_n (λ n : nat, f n x) 0) with (λ x : R, f 0%nat x); last first.
     { apply functional_extensionality; intros ?.
       by rewrite sum_O.
     }
     rewrite sum_O.
     done.
   }
   { replace (λ x : R, sum_n (λ n : nat, f n x) (S M)) with
       (λ x : R, sum_n (λ n : nat, f n x) M + f (S M) x); last first.
     { apply functional_extensionality; intros ?.
       rewrite sum_Sn.
       rewrite /plus//=/zero//=.
     }
     rewrite RInt_plus.
     3: { apply Hex. }
     2: { by apply ex_RInt_sum_n.  }
      rewrite sum_Sn.
     by rewrite IHM.
   }
Qed.

(** Compatibility lemma for convergent sequences of extended reals *)
Lemma SequeneceLemma1 {r : R} {rb : Rbar.Rbar} (s : nat → R) :
  filterlim s eventually (locally r) →
  filterlim s eventually (Rbar_locally rb) →
  rb = Rbar.Finite r.
Proof.
  intro Hreal.
  intro Hrbar.
  assert (H1 : Lim_seq.is_lim_seq s (Rbar.Finite r)).
  { unfold Lim_seq.is_lim_seq. assumption. }
  assert (H2 : Lim_seq.is_lim_seq s rb).
  { unfold Lim_seq.is_lim_seq. assumption. }
  apply Lim_seq.is_lim_seq_unique in H1; apply Lim_seq.is_lim_seq_unique in H2.
  by rewrite H2 in H1.
Qed.

(** Compatibility lemma for convergent sequences of extended reals *)
Lemma seq_lift {s : nat → R} {L : R} :
  filterlim s eventually (locally L) →
  filterlim s eventually (Rbar_locally (Rbar.Finite L)).
Proof.
intros H.
unfold filterlim in *.
exact H.
Qed.

(** Compatibility lemma for convergent sequences of extended reals *)
Lemma Filterlim_Series1 {s : nat → R} (Hex : Lim_seq.ex_lim_seq s) :
  filterlim s eventually (Rbar_locally (Lim_seq.Lim_seq s)).
Proof. apply (Lim_seq.Lim_seq_correct s Hex). Qed.

(** Relate a Series to its limit of partial sums, when the limit of partial sums exists. *)
Lemma Filterlim_Series {s : nat → R} {L : R} :
  Lim_seq.ex_lim_seq (sum_n s) →
  filterlim (λ M : nat, sum_n (λ n : nat, s n) M) eventually (locally L) →
  Series.Series s = L.
Proof.
  intros Hex H.
  unfold Series.Series.
  have H1 := @Filterlim_Series1 (sum_n s) Hex.
  rewrite (SequeneceLemma1 _ H H1).
  done.
Qed.

(** [∑∫] Fubini's theorem for integrals series that converge uniformly by the M test *)
Lemma FubiniIntegralSeries {f : nat → R → R_CompleteNormedModule} {a b : R} (UB : nat → R)
  (Hnn : ∀ (x : R) (n : nat), 0 <= f n x)
  (HexU : Series.ex_series UB) (Hub : forall x n, Rabs (f n x) <= UB n) (Hex : ∀ n, ex_RInt (f n) a b) :
  Series.Series (fun n => RInt (λ x : R, f n x) a b) = RInt (λ x : R, Series.Series (λ n' : nat, f n' x)) a b.
Proof.
  have H : ∀ n : nat, ex_RInt (λ x : R, sum_n (λ n' : nat, f n' x) n) a b.
  { intros n. apply ex_RInt_sum_n. apply Hex. }
  have HU : filterlim (λ (M : nat) (x : R), sum_n (λ n' : nat, f n' x) M) eventually
              (locally (λ x : R, Series.Series (λ n' : nat, f n' x))).
  { apply (UniformConverge_Series UB); done. }
  have HLimit := @Exchange1 (fun M x => sum_n (fun n' => f n' x) M) a b (fun x => Series.Series (fun n' => f n' x)) H HU.
  (* Exchange the RInt and the sum_n *)
  have H1 : (λ n : nat, RInt (λ x : R, sum_n (λ n' : nat, f n' x) n) a b) =
            (λ n : nat, sum_n (λ n' : nat, RInt (λ x : R, f n' x) a b) n).
  { apply functional_extensionality; intros ?. rewrite FubiniFinite; done. }
  rewrite H1 in HLimit. clear H1.
  rewrite (Filterlim_Series _ HLimit); [done|].
  have Hex' : Series.ex_series (λ n' : nat, RInt (λ x : R, f n' x) a b).
  { apply (Series.ex_series_le _ (fun n => Rabs (b - a) * UB n)).
    2: { by apply @Series.ex_series_scal_l. }
    intros n.
    rewrite /norm//=/abs//=.
    destruct (ClassicalEpsilon.excluded_middle_informative (a <= b)).
    { etrans; first eapply (abs_RInt_le_const _ _ _ (UB n)).
      { done. }
      { by apply Hex. }
      { intros ??. apply Hub. }
      { rewrite Rabs_right; try lra. }
    }
    have HP : b <= a by lra.
    rewrite -opp_RInt_swap.
    2: { apply ex_RInt_swap, Hex. }
    rewrite /opp//=.
    rewrite Rabs_Ropp.
    { etrans; first eapply (abs_RInt_le_const _ _ _ (UB n)).
      { done. }
      { apply ex_RInt_swap, Hex. }
      { intros ??. apply Hub. }
      { replace (b - a) with (- (a - b)) by lra.
        rewrite Rabs_Ropp.
        rewrite Rabs_right; try lra. }
    }
  }
  destruct Hex' as [L HEL].
  unfold Series.is_series in HEL.
  unfold Lim_seq.ex_lim_seq.
  exists (Rbar.Finite L).
  unfold Lim_seq.is_lim_seq.
  by apply seq_lift.
Qed.


(** [∑∫] Fubini's theorem for integrals and series which do not converge uniformly outisde
 of the interval of integration. *)
Lemma FubiniIntegralSeries_Strong {f : nat → R → R_CompleteNormedModule} {a b : R} (UB : nat → R) (Hab : a < b)
  (Hnn : ∀ (x : R) (n : nat), a < x < b → 0 <= f n x)
  (HexU : Series.ex_series UB) (Hub : forall x n, a < x < b → Rabs (f n x) <= UB n) (Hex : ∀ n, ex_RInt (f n) a b) :
  Series.Series (fun n => RInt (λ x : R, f n x) a b) = RInt (λ x : R, Series.Series (λ n' : nat, f n' x)) a b.
Proof.
  replace (Series.Series (λ n : nat, RInt (λ x : R, f n x) a b))
     with (Series.Series (λ n : nat, RInt (λ x : R, Iverson (Ioo a b) x * f n x) a b)).
  2: {
    apply Series.Series_ext.
    intros n.
    rewrite (RInt_ext _ (f n)); try done.
    intros x.
    rewrite /Ioo.
    rewrite Rmin_left; try lra.
    rewrite Rmax_right; try lra.
    intros H.
    rewrite /Iverson. case_decide; try lra.
  }
  replace (RInt (λ x : R, Series.Series (λ n' : nat, f n' x)) a b)
     with (RInt (λ x : R, Series.Series (λ n' : nat, Iverson (Ioo a b) x * f n' x)) a b).
  2: {
    apply RInt_ext.
    intros x.
    rewrite /Ioo.
    rewrite Rmin_left; try lra.
    rewrite Rmax_right; try lra.
    intro H.
    apply Series.Series_ext.
    intros n.
    rewrite /Iverson//=.
    case_decide; try lra.
  }
  apply (FubiniIntegralSeries UB).
  { intros ??.
    rewrite /Iverson//=.
    case_decide; try lra.
    rewrite Rmult_1_l.
    apply Hnn.
    rewrite /Ioo//= in H.
    rewrite Rmin_left in H; try lra.
    rewrite Rmax_right in H; try lra.
  }
  { done. }
  { intros ??.
    rewrite /Iverson.
    case_decide.
    { rewrite Rmult_1_l.
      apply Hub.
      rewrite /Ioo//= in H.
      rewrite Rmin_left in H; try lra.
      rewrite Rmax_right in H; try lra.
    }
    { rewrite Rmult_0_l Rabs_R0.
      etrans; [|apply (Hub ((a+b)/2) n)].
      { apply Rabs_pos. }
      { lra. }
    }
  }
  { intro n.
    apply ex_RInt_mult; [|done].
    apply  (ex_RInt_ext (fun (_ : R) => 1)); [|apply ex_RInt_const].
    intros x.
    rewrite Rmin_left; try lra.
    rewrite Rmax_right; try lra.
    intros Hx.
    rewrite /Iverson.
    case_decide; try lra.
    rewrite /Ioo in H.
    rewrite Rmin_left in H; try lra.
    rewrite Rmax_right in H; try lra.
  }
Qed.

Lemma FubiniIntegralSeriesC_Strong {f : nat → R → R_CompleteNormedModule} {a b : R} (UB : nat → R) (Hab : a < b)
  (Hnn : ∀ (x : R) (n : nat), a < x < b → 0 <= f n x)
  (HexU : ex_seriesC UB) (Hub : forall x n, a < x < b → Rabs (f n x) <= UB n) (Hex : ∀ n, ex_RInt (f n) a b) :
  SeriesC (fun n => RInt (λ x : R, f n x) a b) = RInt (λ x : R, SeriesC (λ n' : nat, f n' x)) a b.
Proof.
  rewrite SeriesC_nat.
  rewrite (FubiniIntegralSeries_Strong UB); try done.
  2: { by apply ex_seriesC_nat. }
  apply RInt_ext.
  intros ??.
  rewrite SeriesC_nat.
  done.
Qed.

(** [∑∫] Existence of a series of integrals using uniform convergence. *)
Lemma ex_seriesC_RInt {f : nat → R → R_CompleteNormedModule} {a b : R} (UB : nat → R)
  (Hab  : a <= b)
  (Hnn : ∀ x n, a < x < b → 0 <= f n x)
  (HexU : ex_seriesC UB)
  (Hub : forall x n, a <= x <= b → Rabs (f n x) <= UB n)
  (Hex : ∀ n, ex_RInt (f n) a b) :
  ex_seriesC (fun n => RInt (λ x : R, f n x) a b).
Proof.
  apply (ex_seriesC_le _ (fun n => (b - a) * UB n)); first (intros ?; split).
  2: {
    replace (RInt (λ x : R, f n x) a b) with (Rabs (RInt (λ x : R, f n x) a b)).
    2: {
      rewrite Rabs_right; first done.
      apply Rle_ge.
      apply RInt_ge_0.
      { done. }
      { apply Hex. }
      { intros ??. apply Hnn.  done. }
    }
    { etrans; first eapply (abs_RInt_le_const _ _ _ (UB n)).
      { done.  }
      { apply Hex. }
      { intros ??. apply Hub. lra. }
      { right. f_equal. }
    }
  }
  { apply RInt_ge_0.
    { done. }
    { apply Hex. }
    { intros ??. apply Hnn.  done. }
  }
  apply ex_seriesC_scal_l.
  apply HexU.
Qed.

(** [∑∫] Integrability of a series using uniform convergence. *)
Lemma ex_RInt_SeriesC {f : nat → R → R_CompleteNormedModule} {a b : R} (UB : nat → R) (Hab : a < b)
  (HexU : Series.ex_series UB)
  (Hub : forall x n, a < x < b → 0 <= (f n x) <= UB n)
  (Hex : ∀ n, ex_RInt (f n) a b) :
  ex_RInt (λ x : R, SeriesC (λ n' : nat, f n' x)) a b.
Proof.
  (* Internalize the domain as indicator function. *)
  suffices H : ex_RInt (λ x : R, @SeriesC nat numbers.Nat.eq_dec nat_countable (λ n' : nat, Iverson (Ioo a b) x  * f n' x)) a b.
  { eapply ex_RInt_ext; [|apply H].
    intros x.
    intros Hx.
    apply SeriesC_ext; intros n.
    rewrite Iverson_True; try lra.
    rewrite /Ioo.
    lra.
  }
  have H : ∀ n : nat, ex_RInt (λ x : R, sum_n (λ n' : nat, Iverson (Ioo a b) x * f n' x) n) a b.
  { intros n; apply ex_RInt_sum_n.
    intros ?.
    apply ex_RInt_mult; [|apply Hex].
    apply (ex_RInt_ext (fun _ => 1)); [|apply ex_RInt_const].
    intros ??.
    rewrite Iverson_True; try lra.
    rewrite /Ioo.
    lra.
  }
  have HU : filterlim (λ (M : nat) (x : R), sum_n (λ n' : nat, Iverson (Ioo a b) x *  f n' x) M) eventually
              (locally (λ x : R, Series.Series (λ n' : nat, Iverson (Ioo a b) x * f n' x))).
  { apply (UniformConverge_Series UB); try done.
    { intros ??.
      rewrite /Iverson//=. case_decide; try lra.
      rewrite Rmult_1_l.
      apply Hub.
      rewrite /Ioo in H0.
      rewrite Rmin_left in H0; try lra.
      rewrite Rmax_right in H0; try lra.
    }
    { intros ??.
      rewrite /Iverson//=. case_decide; try lra.
      2: { rewrite Rmult_0_l Rabs_R0.
           specialize Hub with ((a+b)/2) n.
           etrans; eapply Hub; lra.
      }
      rewrite Rmult_1_l.
      rewrite /Ioo in H0.
      rewrite Rmin_left in H0; try lra.
      rewrite Rmax_right in H0; try lra.
      rewrite Rabs_right.
      { apply Hub. lra. }
      apply Rle_ge.
      apply Hub. lra.
    }
  }
  apply ex_RInt_ext with (f := (λ x : R, Series.Series (λ n' : nat, Iverson (Ioo a b) x * f n' x))).
  { intros x Hx. rewrite -SeriesC_nat. done. }
  have Hrec (n : nat) : is_RInt (fun x => sum_n (fun n' => Iverson (Ioo a b) x * f n' x) n) a b
                                 (RInt (fun x => sum_n (fun n' => Iverson (Ioo a b) x * f n' x) n) a b).
  { apply @RInt_correct. apply H. }
  destruct (filterlim_RInt (fun M x => sum_n (fun n' => Iverson (Ioo a b) x * f n' x) M) a b
                           eventually eventually_filter _ _ Hrec HU) as [I [HL HF]].
  exists I.
  apply HF.
Qed.
