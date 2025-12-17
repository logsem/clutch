From clutch.eris.examples.math Require Import prelude axioms series iverson sets integrals improper continuity2 piecewise.
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


(** The Uniform Limit Theorem *)


(* Wrapper around the Coquelicot french definitions + some basic reductions *)
Theorem UniformLimitTheorem {f : nat → R → R} {a b x : R} :
  Icc a b x →
  (* Oh oops I need each to be continuous too *)
  (∀ (n : nat) (x' : R), Rmin a b <= x' <= Rmax a b → (Continuity.continuous (f n) x')) →
  (* Uniform convergence (TODO: Just on the interval [a,b], right? ) *)
  filterlim (fun (M : nat) (x : R) => sum_n (fun n => f n x) M) eventually (locally (λ x : R, Series.Series (fun n => f n x))) →
  (* The limit is continuous *)
  Continuity.continuous (fun x' => (Series.Series (fun n => f n x'))) x.
Proof.
  intros HB Hcts Hunif.
  (* Classic ε/3 argument *)
  rewrite /Continuity.continuous.
  apply filterlim_locally.
  intro eps.
  (* Set up ε/3 *)
  have Heps3_pos : 0 < eps / 3.
  { apply Rdiv_lt_0_compat; [apply cond_pos | lra]. }
  pose (eps3 := mkposreal (eps / 3) Heps3_pos).
  (* Extract N from uniform convergence *)
  have Hunif_eps : eventually (λ M : nat, ∀ x0 : R, ball (Series.Series (λ n : nat, f n x0)) eps3 (sum_n (λ n : nat, f n x0) M)).
  { rewrite filterlim_locally in Hunif.
    rewrite /ball /= /fct_ball in Hunif.
    apply Hunif. }
  rewrite /eventually /= in Hunif_eps.
  destruct Hunif_eps as [N HN].
  (* The finite sum is continuous (finite sum of continuous functions) *)
  have Hcts_sum : Continuity.continuous (λ x' : R, sum_n (λ n : nat, f n x') N) x.
  { rewrite /Icc in HB.
    clear HN.
    induction N.
    { replace (λ x' : R, sum_n (λ n : nat, f n x') 0) with (λ x' : R, f 0%nat x').
      2: { apply functional_extensionality. intros ?. by rewrite sum_O. }
      { apply Hcts. done. }
    }
    { replace (λ x' : R, sum_n (λ n : nat, f n x') (S N)) with (λ x' : R, sum_n (λ n : nat, f n x') N + f (S N) x').
      2: { apply functional_extensionality. intros ?. rewrite sum_Sn /plus//=. }
      apply (Continuity.continuous_plus (V := R_CompleteNormedModule)).
      { apply IHN. }
      { apply Hcts. done. }
    }
  }
  (* Get delta from continuity of finite sum *)
  rewrite /Continuity.continuous filterlim_locally in Hcts_sum.
  specialize (Hcts_sum eps3).
  rewrite /locally in Hcts_sum.
  destruct Hcts_sum as [delta Hdelta].
  (* Show the limit is continuous at x with this delta *)
  exists delta.
  intros y Hy.
  rewrite /ball /= /AbsRing_ball /abs /= /minus /plus /opp /=.
  (* Decompose into three parts for ε/3 argument *)
  replace (Series.Series (λ n : nat, f n y) + - Series.Series (λ n : nat, f n x))
     with ((Series.Series (λ n : nat, f n y) - sum_n (λ n : nat, f n y) N) +
           (sum_n (λ n : nat, f n y) N - sum_n (λ n : nat, f n x) N) +
           (sum_n (λ n : nat, f n x) N - Series.Series (λ n : nat, f n x))) by lra.
  (* Prove each part is < ε/3 *)
  have H1 : Rabs (Series.Series (λ n : nat, f n y) - sum_n (λ n : nat, f n y) N) < eps / 3.
  { have HNy := HN N ltac:(lia) y.
    rewrite /ball /= /AbsRing_ball /= in HNy.
    rewrite /abs /= /minus /plus /opp /= in HNy.
    replace (Series.Series (λ n0 : nat, f n0 y) - sum_n (λ n0 : nat, f n0 y) N)
       with (-(sum_n (λ n0 : nat, f n0 y) N - Series.Series (λ n0 : nat, f n0 y))) by lra.
    rewrite Rabs_Ropp.
    apply HNy. }
  have H2 : Rabs (sum_n (λ n : nat, f n y) N - sum_n (λ n : nat, f n x) N) < eps / 3.
  { specialize (Hdelta y Hy).
    rewrite /ball /= /AbsRing_ball /= in Hdelta.
    rewrite /abs /= /minus /plus /opp /= in Hdelta.
    apply Hdelta. }
  have H3 : Rabs (sum_n (λ n : nat, f n x) N - Series.Series (λ n : nat, f n x)) < eps / 3.
  { have HNx := HN N ltac:(lia) x.
    rewrite /ball /= /AbsRing_ball /= in HNx.
    rewrite /abs /= /minus /plus /opp /= in HNx.
    apply HNx. }
  (* Combine using triangle inequality *)
  pose (term1 := Series.Series (λ n : nat, f n y) - sum_n (λ n : nat, f n y) N).
  pose (term2 := sum_n (λ n : nat, f n y) N - sum_n (λ n : nat, f n x) N).
  pose (term3 := sum_n (λ n : nat, f n x) N - Series.Series (λ n : nat, f n x)).
  replace (Series.Series (λ n : nat, f n y) - sum_n (λ n : nat, f n y) N +
     (sum_n (λ n : nat, f n y) N - sum_n (λ n : nat, f n x) N) +
     (sum_n (λ n : nat, f n x) N - Series.Series (λ n : nat, f n x))) with (term1 + term2 + term3) by (rewrite /term1 /term2 /term3; lra).
  have Hbound : Rabs (term1 + term2 + term3) <= Rabs term1 + Rabs term2 + Rabs term3.
  { have H_step1 := Rabs_triang term1 (term2 + term3).
    replace (term1 + term2 + term3) with (term1 + (term2 + term3)) by lra.
    eapply Rle_trans; [apply H_step1|].
    have H_step2 := Rabs_triang term2 term3.
    lra. }
  eapply Rle_lt_trans; [apply Hbound|].
  fold term1 in H1.
  fold term2 in H2.
  fold term3 in H3.
  lra.
Qed.


(** 2D Uniform Limit Theorem *)
(*
Theorem UniformLimitTheorem2 {f : nat → R → R → R} {xa xb ya yb x y : R} :
  xa <= xb →
  ya <= yb →
  Icc xa xb x →
  Icc ya yb x →
  (∀ (n : nat) (x' y' : R),
     Icc xa xb x' →
     Icc ya yb y' →
     Continuity2 (uncurry (λ x0 y0, f n x0 y0)) x' y') →
  filterlim (fun (M : nat) (x y : R) => sum_n (fun n => f n x y) M) eventually
    (locally (λ x y : R, SeriesC (fun n => f n x y))) →
  Continuity2 (uncurry (λ x0 y0 : R, SeriesC (λ n : nat, f n x0 x0))) x y.
Proof. A dmitted.
*)


(** Uniform convergence of improper integrals *)

(** Helper: Tail of a converging improper integral goes to zero
    Proof strategy: Use filterlim_is_RInt_gen and RInt_gen_correct *)
Lemma RInt_gen_tail_converges (g : R → R) (xa : R)
  (Hex_fin : ∀ b, ex_RInt g xa b)
  (Hg_ex : ex_RInt_gen g (at_point xa) (Rbar_locally Rbar.p_infty)) :
  ∀ eps : posreal, ∃ M : R, ∀ xb : R, M < xb →
    Rabs (RInt_gen g (at_point xa) (Rbar_locally Rbar.p_infty) - RInt g xa xb) < eps.
Proof.
  intro eps.
  unfold ex_RInt_gen in Hg_ex.
  destruct Hg_ex as [lg Hg_ex].
  have Hg_lim : filterlim (λ b : R, RInt g xa b) (Rbar_locally Rbar.p_infty) (locally lg).
  { apply filterlim_is_RInt_gen; [apply Hex_fin | apply Hg_ex]. }
  have Heq : RInt_gen g (at_point xa) (Rbar_locally Rbar.p_infty) = lg.
  { apply is_RInt_gen_unique. apply Hg_ex. }
  rewrite Heq.
  rewrite filterlim_locally //= in Hg_lim.
  destruct (Hg_lim eps) as [M HM].
  exists M.
  intros xb Hxb.
  specialize (HM xb Hxb).
  rewrite /ball/=/AbsRing_ball/= in HM.
  by rewrite Rabs_minus_sym.
Qed.

(** If a full integral exists and finite piece exists, then the tail exists. *)
Lemma ex_RInt_gen_Chasles_exists {f : R → R} {xa xb : R}
  (Hfull : ex_RInt_gen f (at_point xa) (Rbar_locally Rbar.p_infty))
  (Hfin : ex_RInt_gen f (at_point xa) (at_point xb)) :
  ex_RInt_gen f (at_point xb) (Rbar_locally Rbar.p_infty).
Proof.
  destruct Hfull as [L1 H1].
  destruct Hfin as [L2 H2].
  exists (plus (opp L2) L1).
  eapply (is_RInt_gen_Chasles f xa (opp L2) L1).
  2: { done. }
  rewrite is_RInt_gen_at_point.
  rewrite is_RInt_gen_at_point in H2.
  apply is_RInt_swap; done.
Qed.


(*
(** Absolute value of improper integral is bounded by integral of absolute value bound.
    If |f(x,y)| ≤ g(x) for all x ≥ M, and g ≥ 0, then |∫[M,∞) f(·,y)| ≤ ∫[M,∞) g. *)
Lemma RInt_gen_abs_bound {f g : R → R} (M : R)
  (Hbound : ∀ x, 0 <= f x <= g x)
  (Hf_ex : ex_RInt_gen f (at_point M) (Rbar_locally Rbar.p_infty))
  (Hg_ex : ex_RInt_gen g (at_point M) (Rbar_locally Rbar.p_infty))
  (Hg_ex' : ∀ b, ex_RInt g M b) :
  Rabs (RInt_gen f (at_point M) (Rbar_locally Rbar.p_infty)) <= Rabs (RInt_gen g (at_point M) (Rbar_locally Rbar.p_infty)).
Proof.
  destruct Hf_ex as [lf Hf_is].
  destruct Hg_ex as [lg Hg_is].
  have -> : RInt_gen f (at_point M) (Rbar_locally Rbar.p_infty) = lf.
  { apply is_RInt_gen_unique. exact Hf_is. }
  have -> : RInt_gen g (at_point M) (Rbar_locally Rbar.p_infty) = lg.
  { apply is_RInt_gen_unique. exact Hg_is. }
  have Hnorm : norm lf <= lg.
  { eapply (@RInt_gen_norm R_CompleteNormedModule (at_point M) (Rbar_locally Rbar.p_infty)
          _ _ _ _ lf lg _ _ Hf_is Hg_is).
    Unshelve.
    { apply (Filter_prod _ _ _ (fun x => x = M) (fun y => M <= y)).
      { rewrite /at_point//=. }
      { rewrite /Rbar_locally//=. exists M. intros ??; lra. }
      { intros ????. simpl. lra. }
    }
    { apply (Filter_prod _ _ _ (fun x => x = M) (fun y => M <= y)).
      { rewrite /at_point//=. }
      { rewrite /Rbar_locally//=. exists M. intros ??; lra. }
      rewrite /norm//=/abs//=.
      intros ??->??[??].
      rewrite Rabs_right; try lra.
      { apply Hbound. }
      { apply Rle_ge, Hbound. }
    }
  }
  rewrite /norm/=/abs/= in Hnorm.
  have Hlg_pos : 0 <= lg.
  { have H := (RInt_gen_pos_strong (F := g) (M := M)).
    rewrite -[lg](is_RInt_gen_unique _ _ Hg_is).
    apply H.
    - intros x. specialize Hbound with x. etrans; apply Hbound.
    - intros b. apply Hg_ex'.
    - intros b Hb.
      apply RInt_ge_0; try lra.
      { apply Hg_ex'. }
      intros ??.
      specialize Hbound with x. etrans; apply Hbound.
    - exists lg. exact Hg_is.
  }
  etrans; first eapply Hnorm.
  right.
  rewrite Rabs_right; lra.
Qed.

(** Helper: Tail integral is bounded by tail of dominating function *)
Lemma RInt_tail_bound (f : R → R → R) (g : R → R) (xa xb : R) (y : R)
  (Hbound : ∀ x, 0 <= f x y <= g x)
  (Hfy_ex : ex_RInt_gen (fun x => f x y) (at_point xa) (Rbar_locally Rbar.p_infty))
  (Hg_ex : ex_RInt_gen g (at_point xa) (Rbar_locally Rbar.p_infty))
  (Hf_fin : ex_RInt (fun x => f x y) xa xb)
  (Hg_fin : ∀ b, ex_RInt g xa b)
  (Hg_fin' : ∀ b : R, ex_RInt g xb b) :
  Rabs (RInt_gen (fun x => f x y) (at_point xa) (Rbar_locally Rbar.p_infty) - RInt (fun x => f x y) xa xb)
  <= Rabs (RInt_gen g (at_point xa) (Rbar_locally Rbar.p_infty) - RInt g xa xb).
Proof.
  have HFilter1 : ∀ (xa : R), ProperFilter' (at_point xa).
  { intros ?. apply Proper_StrongProper. apply at_point_filter. }
  have HFilter2 : ProperFilter' (Rbar_locally Rbar.p_infty).
  { apply Proper_StrongProper. apply Rbar_locally_filter. }
  (* Establish existence of tail integrals *)
  have Hfy_tail : ex_RInt_gen (fun x => f x y) (at_point xb) (Rbar_locally Rbar.p_infty).
  { have Hexf : ex_RInt_gen (fun x => f x y) (at_point xa) (at_point xb).
    { apply (proj2 (@ex_RInt_gen_at_point R_CompleteNormedModule (fun x => f x y) xa xb)). exact Hf_fin. }
    apply (@ex_RInt_gen_Chasles_exists (fun x => f x y) xa xb Hfy_ex Hexf). }
  have Hg_tail : ex_RInt_gen g (at_point xb) (Rbar_locally Rbar.p_infty).
  { have Hexg : ex_RInt_gen g (at_point xa) (at_point xb).
    { apply (proj2 (@ex_RInt_gen_at_point R_CompleteNormedModule g xa xb)).
      apply Hg_fin. }
    apply (@ex_RInt_gen_Chasles_exists g xa xb Hg_ex Hexg). }
  (* Apply Chasles to decompose: ∫[xa,∞) = ∫[xa,xb] + ∫[xb,∞) *)
  have Hchasles_f : RInt_gen (fun x => f x y) (at_point xa) (Rbar_locally Rbar.p_infty) - RInt (fun x => f x y) xa xb
                  = RInt_gen (fun x => f x y) (at_point xb) (Rbar_locally Rbar.p_infty).
  { have Hexf : ex_RInt_gen (fun x => f x y) (at_point xa) (at_point xb).
    { apply (proj2 (@ex_RInt_gen_at_point R_CompleteNormedModule (fun x => f x y) xa xb)). exact Hf_fin. }
    have HC := @RInt_gen_Chasles R_CompleteNormedModule (at_point xa) (Rbar_locally Rbar.p_infty)
      (HFilter1 _) HFilter2 (fun x => f x y) xb Hexf Hfy_tail.
    rewrite RInt_gen_at_point in HC.
    2: { done. }
    rewrite /plus//= in HC.
    lra. }
  have Hchasles_g : RInt_gen g (at_point xa) (Rbar_locally Rbar.p_infty) - RInt g xa xb
                  = RInt_gen g (at_point xb) (Rbar_locally Rbar.p_infty).
  { have Hexg : ex_RInt_gen g (at_point xa) (at_point xb).
    { apply (proj2 (@ex_RInt_gen_at_point R_CompleteNormedModule g xa xb)).
      apply Hg_fin. }
    have HC := @RInt_gen_Chasles R_CompleteNormedModule (at_point xa) (Rbar_locally Rbar.p_infty)
      (HFilter1 _) HFilter2 g xb Hexg Hg_tail.
    rewrite RInt_gen_at_point in HC.
    2: { apply Hg_fin. }
    rewrite /plus//= in HC.
    lra. }
  rewrite Hchasles_f Hchasles_g.
  apply (@RInt_gen_abs_bound); try done.
Qed.

(** Uniform convergence of improper integrals via dominated convergence.
    Analogous to UniformConverge_Series (Weierstrass M-test) for series. *)
Lemma UniformConverge_RInt_weak (f : R → R → R) (g : R → R) (xa ya yb : R)
  (Hbound  : ∀ x y, 0 <= f x y <= g x)
  (Hg_cont : IPCts g)
  (Hf_cont : forall y, IPCts (fun x => f x y))
  (Hg_ex : ex_RInt_gen g (at_point xa) (Rbar_locally Rbar.p_infty))
  (Hf_lo : forall x y, y < Rmin ya yb -> f x y = 0)
  (Hf_hi : forall x y, Rmax ya yb < y -> f x y = 0) :
  filterlim (λ xb y, RInt (λ x, f x y) xa xb)
            (Rbar_locally Rbar.p_infty)
            (locally (λ y, RInt_gen (λ x, f x y) (at_point xa) (Rbar_locally Rbar.p_infty))).
Proof.
  rewrite filterlim_locally /Rbar_locally //=.
  intro eps.
  have Hex_g_fin' : ∀ a b, ex_RInt g a b.
  { intros ??. by eapply IPCts_RInt. }
  have Hex_g_fin : ∀ b, ex_RInt g xa b.
  { intro b. apply Hex_g_fin'. }
  have Htail := RInt_gen_tail_converges g xa Hex_g_fin Hg_ex eps.
  destruct Htail as [M0 HM0].
  (* Ensure M >= xa by taking maximum *)
  pose (M := Rmax M0 xa).
  exists M.
  intros xb Hxb.
  have HM : Rabs (RInt_gen g (at_point xa) (Rbar_locally Rbar.p_infty) - RInt g xa xb) < eps.
  { apply HM0. unfold M in Hxb. generalize (Rmax_l M0 xa). lra. }
  rewrite /ball/=/fct_ball.
  intro y.
  destruct (Rle_dec (Rmin ya yb) y) as [Hy_min | Hy_min].
  2: {
    rewrite (RInt_ext _ (fun _ : R => 0)).
    2: { intros ??. apply Hf_lo. lra. }
    replace (λ x : R, f x y) with (λ x : R, 0).
    2: { apply functional_extensionality. intros ?. symmetry. apply Hf_lo. lra. }
    rewrite RInt_gen_0.
    rewrite RInt_const.
    rewrite /scal//=/mult//= Rmult_0_r.
    apply ball_center.
  }
  destruct (Rle_dec y (Rmax ya yb)) as [Hy_max | Hy_max].
  2: {
    rewrite (RInt_ext _ (fun _ : R => 0)).
    2: { intros ??. apply Hf_hi. lra. }
    replace (λ x : R, f x y) with (λ x : R, 0).
    2: { apply functional_extensionality. intros ?. symmetry. apply Hf_hi. lra. }
    rewrite RInt_gen_0.
    rewrite RInt_const.
    rewrite /scal//=/mult//= Rmult_0_r.
    apply ball_center.
  }
  rewrite /ball/=/AbsRing_ball/=.
  have Hy_range : Rmin ya yb <= y <= Rmax ya yb by lra.
  (* First establish that the improper integral of f(·,y) exists *)
  have Hfy_ex : ex_RInt_gen (fun x => f x y) (at_point xa) (Rbar_locally Rbar.p_infty).
  { apply (@ex_RInt_gen_Ici_compare_IPCts xa g (fun x => f x y)); try done. }
  (* We have that xb > M >= xa, so xa <= xb *)
  have Hxa_xb : xa <= xb.
  { unfold M in Hxb. generalize (Rmax_r M0 xa). lra. }
  (* Apply tail bound to get the key inequality *)
  have Htail_bound : Rabs (RInt_gen (fun x => f x y) (at_point xa) (Rbar_locally Rbar.p_infty) - RInt (fun x => f x y) xa xb)
                     <= Rabs (RInt_gen g (at_point xa) (Rbar_locally Rbar.p_infty) - RInt g xa xb).
  { apply RInt_tail_bound with (xa := xa); try done.
    by apply IPCts_RInt.
  }
  rewrite /abs/=/minus/=.
  rewrite Rabs_minus_sym.
  eapply Rle_lt_trans; [exact Htail_bound | exact HM].
Qed.

(* NB. Dead code *)
Lemma ex_RInt_gen_indic (f : R → R) (xa xb : R) (Hxb : xa <= xb) :
  ex_RInt_gen (fun x => Iverson (Ici xb) x * f x) (at_point xa) (Rbar_locally Rbar.p_infty) →
  ex_RInt_gen f (at_point xb) (Rbar_locally Rbar.p_infty).
Proof.
  (* Convert both bodies to indicator functions *)
  intros [L HL].
  apply (ex_RInt_gen_ext_eq_Ici (f := fun x => Iverson (Ici xb) x * f x) (M := xb)).
  { intros x Hx.
    rewrite /Iverson.
    case_decide.
    { lra. }
    rewrite /Ici in H.
    lra. }
  exists L.
  have HFilter1 : ∀ (xa : R), Filter (at_point xa).
  { intros ?. apply Proper_StrongProper. apply at_point_filter. }
  have HFilter2 : Filter (Rbar_locally Rbar.p_infty).
  { apply Proper_StrongProper. apply Rbar_locally_filter. }
  replace L with (plus 0 L).
  2: { rewrite /plus//=. lra. }
  apply
    ((@is_RInt_gen_Chasles R_CompleteNormedModule (at_point xb) (Rbar_locally Rbar.p_infty))
    (HFilter1 _) HFilter2 (λ x : R, Iverson (Ici xb) x * f x) xa 0 L).
  2: { done. }
  replace 0 with (scal (xa - xb) 0).
  2: { rewrite /scal//=. rewrite /mult//=. lra. }
  rewrite is_RInt_gen_at_point.
  apply (is_RInt_ext (fun _ => 0)).
  2: { eapply @is_RInt_const. }
  intros ?.
  rewrite Rmin_right; try lra.
  rewrite Rmax_left; try lra.
  intros ?.
  rewrite Iverson_False; [lra|].
  rewrite /Ici//=.
  lra.
Qed.
*)
