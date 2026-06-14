(** The TRUNCATED discrete Laplace mechanism (bounded support), and its
    per-distance metric-DP coupling.

    Given a rate [num/den] (with [ε := num/den > 0]), a truncation half-width
    [A ≥ 0], and a center [loc], the truncated discrete Laplace distribution
    [trunc_lap_rat A num den loc] is supported on [{loc-A, …, loc+A}] with pmf

        z ↦ exp(-ε·|z-loc|) / Z_A      (z in support; 0 otherwise),

    where [Z_A := Σ_{k=-A}^{A} exp(-ε·|k|) = 1 + 2·Σ_{j=1}^{A} exp(-εj)] is the
    (location-independent) normaliser.

    The crux of this file is the per-distance approximate-DP coupling.  For ANY
    shift [s := loc' - loc] (UNCONDITIONALLY — no [|s| ≤ A]) we prove the TIGHT
    coupling [DPcoupl_trunc_lap_tight]

        DPcoupl (trunc_lap_rat A num den loc) (trunc_lap_rat A num den loc')
                eq  (|s|·ε)  (tlap_tail A num den |s|),

    where the additive error is the OPTIMAL value: the mass [Pr[Z > A-|s|]] of
    the "bad set" — the slice of [supp(loc)] that the shifted distribution cannot
    cover.  Writing [α := exp(-ε)], the closed forms are
      • [Δ ≤ A] (workhorse): [tlap_tail Δ = α^{A-Δ+1}(1-α^Δ) / (1+α-2α^{A+1})];
      • [Δ = 1] (dominant):   [= (1-α)·α^A / (1+α-2α^{A+1})];
      • [Δ = A]:              [= α(1-α^A) / (1+α-2α^{A+1})];
      • [Δ ≥ 2A+1] (disjoint): [= 1].
    The normaliser obeys [Z_A·(1-α) = 1+α-2α^{A+1}] ([tlap_Z_closed]).

    For [|s| ≤ A] the optimal [δ] coincides with the GROUP BOUND
        δ_A_s := (exp(-ε·A) / Z_A) · (exp(|s|·ε) - 1) / (exp ε - 1) = tlap_delta;
    for [|s| > A] it is STRICTLY smaller (the tail mass saturates toward [1]
    while [tlap_delta] keeps growing), so [tlap_tail ≤ tlap_delta] always
    ([tlap_tail_le_grp]).  The looser group-bound coupling [DPcoupl_trunc_lap]
    (now also UNCONDITIONAL) is recovered as a corollary of the tight one by
    weakening [δ] from [tlap_tail] up to [tlap_delta] via [DPcoupl_mono].

    This is the validating example for "metric approximate DP".

    This file is self-contained in [prob/]; the SampleFamily / WP / tape
    integration is a separate follow-up.  Mirrors the style of [expmech.v]. *)
From Stdlib Require Import Reals Psatz.
From clutch.prelude Require Import base.
From clutch.prob Require Export distribution.
From clutch.prob Require Import couplings_exp couplings_dp.
From clutch.prob Require Import couplings_dp_complete.
From stdpp Require Import list_numbers.

Local Open Scope R.

Section trunc_laplace_distr.

  (** ** Unnormalised weight, normaliser, and the distribution. *)

  (** The (closed) support index list [{loc-A, …, loc+A}]. *)
  Definition tlap_supp (A loc : Z) : list Z := seqZ (loc - A) (2 * A + 1).

  Lemma elem_of_tlap_supp (A loc z : Z) :
    z ∈ tlap_supp A loc ↔ (loc - A <= z <= loc + A)%Z.
  Proof. rewrite /tlap_supp elem_of_seqZ. lia. Qed.

  (** Unnormalised weight: [exp(-ε·|z-loc|)] on the support, [0] outside. *)
  Definition tlap_w (A num den loc : Z) (z : Z) : R :=
    if bool_decide (z ∈ tlap_supp A loc)
    then exp (- (IZR num / IZR den) * IZR (Z.abs (z - loc)))
    else 0%R.

  (** Normaliser [Z_A = Σ_z tlap_w]. *)
  Definition tlap_Z (A num den loc : Z) : R := SeriesC (tlap_w A num den loc).

  Lemma tlap_w_pos (A num den loc z : Z) : 0 <= tlap_w A num den loc z.
  Proof.
    rewrite /tlap_w. case_bool_decide; [left; apply exp_pos | lra].
  Qed.

  Lemma tlap_w_supp (A num den loc z : Z) :
    z ∈ tlap_supp A loc → 0 < tlap_w A num den loc z.
  Proof.
    intros Hin. rewrite /tlap_w bool_decide_eq_true_2; [|done]. apply exp_pos.
  Qed.

  Lemma ex_seriesC_tlap_w (A num den loc : Z) :
    ex_seriesC (tlap_w A num den loc).
  Proof.
    eapply ex_seriesC_ext;
      last apply (ex_seriesC_list (tlap_supp A loc)
                   (λ z, exp (- (IZR num / IZR den) * IZR (Z.abs (z - loc))))).
    intros z. rewrite /tlap_w. by case_bool_decide.
  Qed.

  (** The support is nonempty (since [2A+1 ≥ 1]), so the normaliser is positive. *)
  Lemma tlap_Z_pos (A num den loc : Z) : (0 <= A)%Z → 0 < tlap_Z A num den loc.
  Proof.
    intros HA. rewrite /tlap_Z.
    eapply Rlt_le_trans; last apply (SeriesC_ge_elem _ loc).
    - apply tlap_w_supp. apply elem_of_tlap_supp. lia.
    - intros; apply tlap_w_pos.
    - apply ex_seriesC_tlap_w.
  Qed.

  (** The normaliser is always [≥ 0] (a [SeriesC] of nonnegative weights). *)
  Lemma tlap_Z_nonneg (A num den loc : Z) : 0 <= tlap_Z A num den loc.
  Proof.
    rewrite /tlap_Z. apply SeriesC_ge_0'. intros; apply tlap_w_pos.
  Qed.

  Program Definition trunc_lap_rat (A num den loc : Z) : distr Z :=
    MkDistr (λ z, tlap_w A num den loc z / tlap_Z A num den loc) _ _ _.
  Next Obligation.
    intros A num den loc z. unfold Rdiv. apply Rmult_le_pos.
    - apply tlap_w_pos.
    - destruct (Rle_lt_or_eq_dec 0 _ (tlap_Z_nonneg A num den loc)) as [Hpos|Heq].
      + left. by apply Rinv_pos.
      + rewrite -Heq Rinv_0. lra.
  Qed.
  Next Obligation.
    intros A num den loc. setoid_rewrite Rdiv_def.
    apply ex_seriesC_scal_r, ex_seriesC_tlap_w.
  Qed.
  Next Obligation.
    intros A num den loc. setoid_rewrite Rdiv_def.
    rewrite SeriesC_scal_r -/(tlap_Z A num den loc).
    destruct (Rle_lt_or_eq_dec 0 (tlap_Z A num den loc) (tlap_Z_nonneg _ _ _ _))
      as [Hpos|Heq].
    - rewrite Rinv_r; [lra|lra].
    - rewrite -Heq Rinv_0 Rmult_0_r. lra.
  Qed.

  (** ** Total mass is [1] (when [0 ≤ A]). *)
  Lemma trunc_lap_rat_mass (A num den loc : Z) :
    (0 <= A)%Z → SeriesC (trunc_lap_rat A num den loc) = 1.
  Proof.
    intros HA. rewrite {1}/trunc_lap_rat /pmf. setoid_rewrite Rdiv_def.
    rewrite SeriesC_scal_r -/(tlap_Z A num den loc).
    pose proof (tlap_Z_pos A num den loc HA). rewrite Rinv_r; lra.
  Qed.

  (** Pointwise pmf, unfolded. *)
  Lemma trunc_lap_rat_unfold (A num den loc z : Z) :
    trunc_lap_rat A num den loc z
      = tlap_w A num den loc z / tlap_Z A num den loc.
  Proof. reflexivity. Qed.

  (** ** Shift-invariance of the normaliser.

      [Z_A] does not depend on [loc]: shifting [loc] reindexes the weights. *)
  Lemma tlap_Z_shift_inv (A num den loc loc' : Z) :
    tlap_Z A num den loc = tlap_Z A num den loc'.
  Proof.
    rewrite /tlap_Z.
    rewrite -(SeriesC_translate (tlap_w A num den loc') (loc' - loc)%Z).
    2:{ intros; apply tlap_w_pos. }
    2:{ apply ex_seriesC_tlap_w. }
    apply SeriesC_ext. intros z.
    rewrite /tlap_w.
    destruct (decide (z ∈ tlap_supp A loc)) as [Hin|Hin].
    - rewrite !bool_decide_eq_true_2.
      + do 3 f_equal. lia.
      + apply elem_of_tlap_supp. apply elem_of_tlap_supp in Hin. lia.
      + done.
    - rewrite !bool_decide_eq_false_2.
      + done.
      + rewrite elem_of_tlap_supp. rewrite elem_of_tlap_supp in Hin. lia.
      + done.
  Qed.

  (** ** The bad-set tail mass — the OPTIMAL additive error.

      [tlap_tail A num den Δ := Pr[Z > A - Δ]] for [Z ∼ trunc_lap_rat A num den 0]
      (the centered distribution).  This is the mass of the TOP slice
      [{z : A-Δ < z ≤ A}] of the support, i.e. exactly the "uncovered slice" that
      a shift of distance [Δ] cannot cover.  For [Δ ≤ A] this coincides with the
      group-bound [tlap_delta]; for [Δ > A] it is STRICTLY smaller (the tail mass
      saturates toward [1] while the group-bound keeps growing), so it is the
      tight optimal [δ]. *)
  Definition tlap_tail (A num den Δ : Z) : R :=
    SeriesC (λ z, if bool_decide (z ∈ tlap_supp A 0 ∧ (A - Δ < z)%Z)
                  then trunc_lap_rat A num den 0 z else 0%R).

  Lemma tlap_tail_nonneg (A num den Δ : Z) : 0 <= tlap_tail A num den Δ.
  Proof.
    rewrite /tlap_tail. apply SeriesC_ge_0'. intros z. case_bool_decide;
      [apply pmf_pos | lra].
  Qed.

  Lemma ex_seriesC_tlap_tail_ind (A num den Δ : Z) :
    ex_seriesC (λ z, if bool_decide (z ∈ tlap_supp A 0 ∧ (A - Δ < z)%Z)
                     then trunc_lap_rat A num den 0 z else 0%R).
  Proof.
    eapply ex_seriesC_le; last apply (pmf_ex_seriesC (trunc_lap_rat A num den 0)).
    intros z. case_bool_decide; split; try apply pmf_pos; try lra; apply Rle_refl.
  Qed.

  (** The tail mass is at most [1] (it is a sub-mass of a probability
      distribution of total mass [1]). *)
  Lemma tlap_tail_le_1 (A num den Δ : Z) : (0 <= A)%Z → tlap_tail A num den Δ <= 1.
  Proof.
    intros HA. rewrite /tlap_tail.
    etrans; last (right; apply (trunc_lap_rat_mass A num den 0 HA)).
    apply SeriesC_le; last apply (pmf_ex_seriesC (trunc_lap_rat A num den 0)).
    intros z. case_bool_decide; split; try apply pmf_pos; try lra; apply Rle_refl.
  Qed.

End trunc_laplace_distr.

(** * The per-distance metric-DP coupling *)

Section trunc_laplace_dp.

  Context (A num den : Z).
  Context (HA : (0 <= A)%Z).
  (** [ε := num/den], assumed positive. *)
  Context (Heps : (0 < IZR num / IZR den)%R).

  Local Notation ε := (IZR num / IZR den).

  (** The boundary slice that the shifted distribution [trunc_lap(loc+s)] cannot
      cover — i.e. the part of [supp(loc)] missing from [supp(loc+s)].  For a
      forward shift [s ≥ 0] this is the BOTTOM slice [{loc-A, …, loc-A+s-1}];
      for a backward shift [s < 0] it is the TOP slice [{loc+A+s+1, …, loc+A}].
      We characterise it sign-agnostically as the set difference; the concrete
      [seqZ] slice (per sign) is recovered in [tlap_bndry_slice] below. *)
  Definition tlap_bndry (loc s z : Z) : R :=
    if bool_decide (z ∈ tlap_supp A loc ∧ z ∉ tlap_supp A (loc + s))
    then trunc_lap_rat A num den loc z else 0%R.

  (** ** Weight-level bound on the overlap.

      If [z] lies in the support of [trunc_lap(loc+s)] (the shifted
      distribution), then [w(loc,z) ≤ exp(|s|·ε)·w(loc+s,z)].  Holds for a shift
      [s] of EITHER sign: the controlling inequality is the (two-sided)
      triangle bound [|z-(loc+s)| ≤ |z-loc| + |s|]. *)
  Lemma tlap_w_overlap_ratio (loc s z : Z) :
    z ∈ tlap_supp A (loc + s) →
    tlap_w A num den loc z
      <= exp (IZR (Z.abs s) * ε) * tlap_w A num den (loc + s) z.
  Proof using A num den Heps.
    intros Hz'.
    rewrite {2}/tlap_w bool_decide_eq_true_2; [|done].
    rewrite /tlap_w.
    case_bool_decide as Hz; last first.
    { (* z ∉ supp(loc): w(loc,z) = 0 *)
      apply Rmult_le_pos; [left; apply exp_pos|left; apply exp_pos]. }
    rewrite -exp_plus. apply exp_mono.
    (* Goal: -ε·|z-loc| <= |s|·ε + (-ε·|z-(loc+s)|).
       Suffices |z-(loc+s)| <= |z-loc| + |s|, by the triangle inequality. *)
    apply elem_of_tlap_supp in Hz, Hz'.
    assert (Htri : (Z.abs (z - (loc + s)) <= Z.abs (z - loc) + Z.abs s)%Z).
    { pose proof (Z.abs_triangle (z - loc) (loc - (loc + s))) as Ht.
      replace (z - loc + (loc - (loc + s)))%Z with (z - (loc + s))%Z in Ht by lia.
      replace (Z.abs (loc - (loc + s))) with (Z.abs s) in Ht
        by (rewrite -Z.abs_opp; f_equal; lia).
      lia. }
    assert (IZR (Z.abs (z - (loc + s))) <= IZR (Z.abs (z - loc)) + IZR (Z.abs s))%R
      as Htri'.
    { rewrite -plus_IZR. apply IZR_le. lia. }
    nra.
  Qed.

  (** ** Pmf-level decomposition (the key pointwise bound).

      [μ(loc) z ≤ exp(|s|·ε)·μ(loc+s) z + bndry(loc,s) z] for every [z].  Holds
      for a shift [s] of EITHER sign, UNCONDITIONALLY (no [|s| ≤ A] needed): the
      overlap ratio bound [tlap_w_overlap_ratio] is just the two-sided triangle
      inequality, and outside the overlap the [bndry] term absorbs the slack. *)
  Lemma tlap_pmf_decomp (loc s z : Z) :
    trunc_lap_rat A num den loc z
      <= exp (IZR (Z.abs s) * ε) * trunc_lap_rat A num den (loc + s) z
         + tlap_bndry loc s z.
  Proof using A num den HA Heps.
    pose proof (tlap_Z_pos A num den loc HA) as HZpos.
    rewrite !trunc_lap_rat_unfold.
    rewrite /tlap_bndry trunc_lap_rat_unfold.
    (* the normaliser is shift-invariant: replace [Z(loc+s)] by [Z(loc)] *)
    replace (tlap_Z A num den (loc + s)) with (tlap_Z A num den loc)
      by apply tlap_Z_shift_inv.
    set (ZA := tlap_Z A num den loc).
    set (w := tlap_w A num den loc z).
    set (w' := tlap_w A num den (loc + s) z).
    (* goal (modulo definitions):
         w / ZA <= exp(|s|ε) * (w' / ZA) + (if z∈slice then w / ZA else 0) *)
    destruct (decide (z ∈ tlap_supp A (loc + s))) as [Hin'|Hin'].
    - (* overlap: bndry term is 0; use the weight ratio bound *)
      rewrite bool_decide_eq_false_2; last first.
      { tauto. }
      rewrite Rplus_0_r. unfold Rdiv. rewrite -Rmult_assoc.
      apply Rmult_le_compat_r.
      { left. apply Rinv_pos. exact HZpos. }
      apply tlap_w_overlap_ratio; done.
    - (* z ∉ supp(loc+s): then exp(|s|ε)·μ' z = 0 *)
      assert (w' = 0) as Hw'0.
      { rewrite /w' /tlap_w bool_decide_eq_false_2; [done|exact Hin']. }
      rewrite Hw'0 Rdiv_0_l Rmult_0_r Rplus_0_l.
      destruct (decide (z ∈ tlap_supp A loc)) as [Hin|Hin].
      + (* z is in the boundary slice: equality *)
        rewrite bool_decide_eq_true_2; last first.
        { split; done. }
        lra.
      + (* z outside both supports: w = 0 *)
        assert (w = 0) as Hw0.
        { rewrite /w /tlap_w bool_decide_eq_false_2; [done|exact Hin]. }
        rewrite Hw0 Rdiv_0_l. case_bool_decide; lra.
  Qed.

  (** ** Boundary mass — the geometric sum.

      The total mass of the bottom boundary slice [{loc-A, …, loc-A+s-1}]. *)

  (** The exact group-bound boundary mass
        [δ_A_s = (exp(-ε·A)/Z_A) · (exp(|s|·ε) - 1)/(exp ε - 1)].
      Symmetric in the shift sign — it depends only on [|s|]. *)
  Definition tlap_delta (loc s : Z) : R :=
    (exp (- ε * IZR A) / tlap_Z A num den loc)
      * (exp (IZR (Z.abs s) * ε) - 1) / (exp ε - 1).

  (** Geometric-sum helper: the unnormalised boundary weight, summed over the
      slice [seqZ (loc-A) (Z.of_nat n)], in closed form. *)
  Lemma tlap_bndry_geom (loc : Z) (n : nat) :
    (Z.of_nat n <= A)%Z →
    foldr (Rplus ∘ (λ z, exp (ε * IZR (z - loc)))) 0%R
          (seqZ (loc - A) (Z.of_nat n))
      = exp (- ε * IZR A) * ((exp ε) ^ n - 1) / (exp ε - 1).
  Proof using A num den Heps.
    (* a [Rplus]-foldr's initial accumulator can be pulled out *)
    assert (Hacc : ∀ (g : Z → R) (l : list Z) (c : R),
              foldr (Rplus ∘ g) c l = foldr (Rplus ∘ g) 0 l + c).
    { intros g l. induction l as [|x l IH]; intros c; simpl.
      - lra.
      - rewrite (IH c). unfold compose. lra. }
    intros Hn.
    assert (Hexp1 : exp ε <> 1).
    { intros Hc. assert (ε = 0) as Hε0.
      { rewrite -exp_0 in Hc. apply exp_inv in Hc. lra. }
      lra. }
    assert (Hexpm1 : exp ε - 1 <> 0) by lra.
    induction n as [|n IHn].
    - simpl. lra.
    - rewrite seqZ_S foldr_app. simpl foldr.
      rewrite Hacc. rewrite IHn; [|lia].
      (* the new term [exp(ε·(loc-A+n-loc))] is [exp(-εA)·(exp ε)^n] *)
      replace (exp (ε * IZR (loc - A + Z.of_nat n - loc)))
        with (exp (- ε * IZR A) * (exp ε) ^ n).
      2:{ rewrite exp_pow -exp_plus. f_equal.
          replace (loc - A + Z.of_nat n - loc)%Z with (Z.of_nat n - A)%Z by lia.
          rewrite minus_IZR INR_IZR_INZ. nra. }
      simpl ((exp ε) ^ (S n)).
      field. exact Hexpm1.
  Qed.

  (** [foldr (Rplus ∘ ·)] respects pointwise equality on the list's elements. *)
  Lemma foldr_Rplus_ext (g h : Z → R) (l : list Z) :
    Forall (λ z, g z = h z) l →
    foldr (Rplus ∘ g) 0%R l = foldr (Rplus ∘ h) 0%R l.
  Proof.
    induction l as [|x l IH]; intros Hall; simpl; [done|].
    apply Forall_cons in Hall as [Hx Hl].
    unfold compose. rewrite Hx IH; [done|done].
  Qed.

  (** A scalar factors out of an [Rplus]-foldr. *)
  Lemma foldr_Rplus_scal_l (c : R) (g : Z → R) (l : list Z) :
    c * foldr (Rplus ∘ g) 0%R l = foldr (Rplus ∘ (λ z, c * g z)) 0%R l.
  Proof.
    induction l as [|x l IH]; simpl; [lra|].
    rewrite -IH. unfold compose. lra.
  Qed.

  Lemma tlap_bndry_nonneg (loc s z : Z) : 0 <= tlap_bndry loc s z.
  Proof.
    rewrite /tlap_bndry. case_bool_decide; [apply pmf_pos|lra].
  Qed.

  Lemma ex_seriesC_tlap_bndry (loc s : Z) : ex_seriesC (tlap_bndry loc s).
  Proof.
    eapply ex_seriesC_le; last apply (pmf_ex_seriesC (trunc_lap_rat A num den loc)).
    intros z. rewrite /tlap_bndry. case_bool_decide; split;
      try apply pmf_pos; try lra; try apply Rle_refl.
  Qed.

  (** ** The exact boundary mass (FORWARD slice): [SeriesC (bndry) = δ_A_s] for
      [0 ≤ s ≤ A].  The uncovered set [supp(loc) \ supp(loc+s)] is exactly the
      bottom slice [seqZ (loc-A) s]. *)
  Lemma tlap_bndry_mass_fwd (loc s : Z) :
    (0 <= s <= A)%Z →
    SeriesC (tlap_bndry loc s) = tlap_delta loc s.
  Proof using A num den HA Heps.
    intros Hs.
    pose proof (tlap_Z_pos A num den loc HA) as HZpos.
    (* 0. the set-difference indicator agrees with the bottom slice [seqZ (loc-A) s] *)
    rewrite (SeriesC_ext (tlap_bndry loc s)
               (λ z, if bool_decide (z ∈ seqZ (loc - A) s)
                     then trunc_lap_rat A num den loc z else 0%R)).
    2:{ intros z. rewrite /tlap_bndry.
        rewrite (bool_decide_ext (z ∈ tlap_supp A loc ∧ z ∉ tlap_supp A (loc + s))
                                 (z ∈ seqZ (loc - A) s)); [done|].
        rewrite elem_of_seqZ !elem_of_tlap_supp. lia. }
    (* 1. reduce the SeriesC over the finite slice to a foldr *)
    rewrite (SeriesC_list (seqZ (loc - A) s) (trunc_lap_rat A num den loc));
      [|apply NoDup_seqZ].
    (* 2. on the slice, [trunc_lap_rat loc z = exp(ε·(z-loc)) / Z_A] *)
    rewrite (foldr_Rplus_ext (trunc_lap_rat A num den loc)
               (λ z, exp (ε * IZR (z - loc)) / tlap_Z A num den loc)).
    2:{ apply Forall_forall. intros z Hz.
        apply elem_of_seqZ in Hz.
        rewrite trunc_lap_rat_unfold /tlap_w.
        rewrite bool_decide_eq_true_2; last (apply elem_of_tlap_supp; lia).
        do 2 f_equal.
        (* z < loc on the slice, so |z-loc| = loc-z = -(z-loc) *)
        rewrite (Z.abs_neq (z - loc)); [|lia].
        rewrite opp_IZR. lra. }
    (* 3. factor out [1 / Z_A] *)
    rewrite (foldr_Rplus_ext
               (λ z, exp (ε * IZR (z - loc)) / tlap_Z A num den loc)
               (λ z, / tlap_Z A num den loc * exp (ε * IZR (z - loc)))).
    2:{ apply Forall_forall. intros z _. rewrite Rdiv_def. lra. }
    rewrite -(foldr_Rplus_scal_l (/ tlap_Z A num den loc)
               (λ z, exp (ε * IZR (z - loc)))).
    (* 4. the geometric sum *)
    assert (Hids : s = Z.of_nat (Z.to_nat s)) by (rewrite Z2Nat.id; lia).
    rewrite {1}Hids.
    rewrite tlap_bndry_geom; [|rewrite Z2Nat.id; lia].
    (* 5. relate [(exp ε)^(Z.to_nat s)] to [exp (IZR (|s|) * ε)] *)
    rewrite exp_pow.
    replace (ε * INR (Z.to_nat s)) with (IZR (Z.abs s) * ε).
    2:{ rewrite INR_IZR_INZ Z2Nat.id; [|lia]. rewrite Z.abs_eq; [lra|lia]. }
    rewrite /tlap_delta. field. split.
    - lra.
    - assert (1 < exp ε); [|lra]. rewrite -exp_0. apply exp_increasing. lra.
  Qed.

  (** ** Reflection through the center [loc].  The truncated Laplacian is
      symmetric about [loc]: reflecting the index [z ↦ 2·loc - z] maps the
      uncovered slice for a shift [s] onto the uncovered slice for the OPPOSITE
      shift [-s], preserving the (symmetric) weight.  Hence the boundary mass at
      [s] equals the boundary mass at [-s] — the formal core of the mirror
      argument. *)
  Lemma tlap_bndry_reflect (loc s z : Z) :
    tlap_bndry loc s (2 * loc - z)%Z = tlap_bndry loc (- s) z.
  Proof using A num den.
    rewrite /tlap_bndry.
    (* the indicators agree: [2loc-z ∈ supp loc ⟺ z ∈ supp loc], and
       [2loc-z ∈ supp(loc+s) ⟺ z ∈ supp(loc-s)] *)
    rewrite (bool_decide_ext _ (z ∈ tlap_supp A loc ∧ z ∉ tlap_supp A (loc + - s))).
    2:{ rewrite !elem_of_tlap_supp. lia. }
    case_bool_decide as Hc; [|done].
    (* the weight is symmetric: [|2loc-z-loc| = |loc-z| = |z-loc|] *)
    rewrite !trunc_lap_rat_unfold /tlap_w.
    rewrite (bool_decide_ext ((2 * loc - z)%Z ∈ tlap_supp A loc) (z ∈ tlap_supp A loc)).
    2:{ rewrite !elem_of_tlap_supp. lia. }
    rewrite (bool_decide_eq_true_2 (z ∈ tlap_supp A loc)); [|tauto].
    do 3 f_equal. f_equal. lia.
  Qed.

  (** Boundary mass is symmetric in the shift sign: [mass(s) = mass(-s)].  Proved
      by the reflection [z ↦ 2·loc - z], an involutive injection, via
      [SeriesC_le_inj] in both directions. *)
  Lemma tlap_bndry_mass_reflect (loc s : Z) :
    SeriesC (tlap_bndry loc s) = SeriesC (tlap_bndry loc (- s)).
  Proof using A num den.
    (* the reflection [g z = 2loc - z] is an involution; reindexing [tlap_bndry
       loc s] by it gives [λ z, tlap_bndry loc s (2loc-z) = tlap_bndry loc (-s)]
       pointwise ([tlap_bndry_reflect]).  We first show the masses of [bndry] and
       its reflection are equal (involution-invariance via [SeriesC_le_inj] both
       ways), then rewrite the reflection pointwise. *)
    transitivity (SeriesC (λ z, tlap_bndry loc s (2 * loc - z)%Z)).
    2:{ apply SeriesC_ext. intros z. apply tlap_bndry_reflect. }
    apply Rle_antisym.
    - (* [SeriesC bndry <= SeriesC (bndry ∘ g)]: reindex [bndry∘g] by [g] *)
      opose proof (SeriesC_le_inj (λ z, tlap_bndry loc s (2 * loc - z)%Z)
                     (λ z, Some (2 * loc - z)%Z) _ _ _) as lb.
      { intros; apply tlap_bndry_nonneg. }
      { intros n1 n2 m h h'. inversion h; inversion h'; lia. }
      { apply (ex_seriesC_inj (λ z : Z, (2 * loc - z)%Z) (tlap_bndry loc s));
          [intros a b Hab; lia | intros; apply tlap_bndry_nonneg
          | apply ex_seriesC_tlap_bndry]. }
      simpl in lb. etrans; [|exact lb]. right.
      apply SeriesC_ext. intros z. f_equal. lia.
    - (* [SeriesC (bndry ∘ g) <= SeriesC bndry]: reindex [bndry] by [g] *)
      opose proof (SeriesC_le_inj (tlap_bndry loc s)
                     (λ z, Some (2 * loc - z)%Z) _ _ _) as ub.
      { intros; apply tlap_bndry_nonneg. }
      { intros n1 n2 m h h'. inversion h; inversion h'; lia. }
      { apply ex_seriesC_tlap_bndry. }
      simpl in ub. exact ub.
  Qed.

  (** ** The exact boundary mass, BOTH directions: [SeriesC (bndry) = δ_A_s] for
      [|s| ≤ A].  Forward ([s ≥ 0]) is [tlap_bndry_mass_fwd]; backward ([s < 0])
      reduces to the forward case at [-s] by the reflection symmetry. *)
  Lemma tlap_bndry_mass (loc s : Z) :
    (Z.abs s <= A)%Z →
    SeriesC (tlap_bndry loc s) = tlap_delta loc s.
  Proof using A num den HA Heps.
    intros Hs.
    destruct (Z_le_gt_dec 0 s) as [Hpos | Hneg].
    - apply tlap_bndry_mass_fwd. lia.
    - rewrite tlap_bndry_mass_reflect.
      rewrite tlap_bndry_mass_fwd; [|lia].
      rewrite /tlap_delta. rewrite Z.abs_opp. reflexivity.
  Qed.

  (** ** Boundary mass is location-invariant: the bad set is a translate of the
      centered one, and the (translation-invariant) pmf agrees pointwise after
      reindexing [z ↦ z + loc].  Holds for ALL shifts [s] (no [|s| ≤ A]). *)
  Lemma tlap_bndry_mass_loc_inv (loc s : Z) :
    SeriesC (tlap_bndry loc s) = SeriesC (tlap_bndry 0 s).
  Proof using A num den.
    rewrite -(SeriesC_translate (tlap_bndry loc s) loc).
    2:{ intros; apply tlap_bndry_nonneg. }
    2:{ apply ex_seriesC_tlap_bndry. }
    apply SeriesC_ext. intros z.
    rewrite /tlap_bndry.
    rewrite (bool_decide_ext ((z + loc)%Z ∈ tlap_supp A loc ∧ (z + loc)%Z ∉ tlap_supp A (loc + s))
                             (z ∈ tlap_supp A 0 ∧ z ∉ tlap_supp A (0 + s))).
    2:{ rewrite !elem_of_tlap_supp. lia. }
    case_bool_decide as Hc; [|done].
    rewrite !trunc_lap_rat_unfold /tlap_w.
    rewrite (bool_decide_ext ((z + loc)%Z ∈ tlap_supp A loc) (z ∈ tlap_supp A 0)).
    2:{ rewrite !elem_of_tlap_supp. lia. }
    replace (tlap_Z A num den loc) with (tlap_Z A num den 0) by apply tlap_Z_shift_inv.
    case_bool_decide as Hin; [|lra].
    f_equal. f_equal. f_equal. f_equal. lia.
  Qed.

  (** The bad set for a backward shift [s = -Δ] (with [Δ ≥ 0]) at center [0] is
      exactly the top tail slice [{z : A-Δ < z ≤ A}], so its mass IS [tlap_tail]. *)
  Lemma tlap_tail_eq_bndry (Δ : Z) :
    (0 <= Δ)%Z →
    tlap_tail A num den Δ = SeriesC (tlap_bndry 0 (- Δ)).
  Proof using A num den.
    intros HΔ. rewrite /tlap_tail /tlap_bndry.
    apply SeriesC_ext. intros z.
    rewrite (bool_decide_ext (z ∈ tlap_supp A 0 ∧ (A - Δ < z)%Z)
                             (z ∈ tlap_supp A 0 ∧ z ∉ tlap_supp A (0 + - Δ))); [done|].
    rewrite !elem_of_tlap_supp. lia.
  Qed.

  (** ** Master bad-set–mass identity, ALL shifts: the total boundary mass equals
      the tail mass [tlap_tail A num den |s|].  Combines location-invariance,
      sign-reflection, and [tlap_tail_eq_bndry].  This is the OPTIMAL [δ] that
      the tight coupling carries. *)
  Lemma tlap_bndry_mass_tail (loc s : Z) :
    SeriesC (tlap_bndry loc s) = tlap_tail A num den (Z.abs s).
  Proof using A num den.
    rewrite tlap_bndry_mass_loc_inv.
    rewrite (tlap_tail_eq_bndry (Z.abs s) (Z.abs_nonneg s)).
    destruct (Z_le_gt_dec 0 s) as [Hpos | Hneg].
    - rewrite (Z.abs_eq s Hpos). apply tlap_bndry_mass_reflect.
    - rewrite (Z.abs_neq s ltac:(lia)).
      replace (- - s)%Z with s by lia. reflexivity.
  Qed.

  (** ** Closed forms for the tail mass.

      Notation: write [α := exp(-ε)] (so [0 < α < 1]).  Each closed form below is
      stated with [α] spelled out as [exp(-ε)], and with the normaliser in the
      EXACT closed form [Z_A·(1-α) = 1+α-2α^{A+1}] (see [tlap_Z_closed]). *)

  (** Geometric-sum helper for the TOP slice: a run [seqZ start n] summed with
      the centered weight [exp(-ε·z)] is the geometric series with ratio [α]. *)
  Lemma tlap_top_geom (start : Z) (n : nat) :
    foldr (Rplus ∘ (λ z, exp (- ε * IZR z))) 0%R (seqZ start (Z.of_nat n))
      = exp (- ε * IZR start) * (1 - exp (- ε * IZR (Z.of_nat n))) / (1 - exp (- ε)).
  Proof using A num den Heps.
    assert (Hacc : ∀ (g : Z → R) (l : list Z) (c : R),
              foldr (Rplus ∘ g) c l = foldr (Rplus ∘ g) 0 l + c).
    { intros g l. induction l as [|x l IH]; intros c; simpl.
      - lra.
      - rewrite (IH c). unfold compose. lra. }
    assert (Halt1 : exp (- ε) <> 1).
    { intros Hc. assert (- ε = 0) as Hε0.
      { rewrite -exp_0 in Hc. apply exp_inv in Hc. lra. }
      lra. }
    assert (Halt : 1 - exp (- ε) <> 0) by lra.
    induction n as [|n IHn].
    - simpl. rewrite Rmult_0_r exp_0. lra.
    - rewrite seqZ_S foldr_app. simpl foldr.
      rewrite Hacc. rewrite IHn.
      replace (exp (- ε * IZR (start + Z.of_nat n)))
        with (exp (- ε * IZR start) * exp (- ε * IZR (Z.of_nat n))).
      2:{ rewrite -exp_plus. f_equal. rewrite plus_IZR. lra. }
      rewrite Nat2Z.inj_succ.
      replace (IZR (Z.succ (Z.of_nat n))) with (IZR (Z.of_nat n) + 1)
        by (rewrite -Z.add_1_r plus_IZR; lra).
      replace (exp (- ε * (IZR (Z.of_nat n) + 1)))
        with (exp (- ε * IZR (Z.of_nat n)) * exp (- ε)).
      2:{ rewrite -exp_plus. f_equal. lra. }
      field. exact Halt.
  Qed.

  (** ** Closed form of the normaliser:
        [(1-α)·Z_A = 1 + α - 2·α^{A+1}], i.e. [Z_A = (1+α-2α^{A+1})/(1-α)].
      Proved by splitting the support [{-A,…,A}] into the bottom run [{-A,…,-1}],
      the center [{0}], and the top run [{1,…,A}], and summing the two geometric
      halves ([tlap_bndry_geom] for the bottom, [tlap_top_geom] for the top). *)
  Lemma tlap_Z_closed :
    (1 - exp (- ε)) * tlap_Z A num den 0
      = 1 + exp (- ε) - 2 * exp (- ε * IZR (A + 1)).
  Proof using A num den HA Heps.
    rewrite /tlap_Z.
    rewrite (SeriesC_ext (tlap_w A num den 0)
               (λ z, if bool_decide (z ∈ tlap_supp A 0)
                     then exp (- ε * IZR (Z.abs z)) else 0%R)).
    2:{ intros z. rewrite /tlap_w. case_bool_decide; [|done].
        do 2 f_equal. rewrite Z.sub_0_r //. }
    rewrite (SeriesC_ext _
               (λ z, if bool_decide (z ∈ seqZ (- A) (2 * A + 1))
                     then exp (- ε * IZR (Z.abs z)) else 0%R)).
    2:{ intros z. rewrite /tlap_supp //. }
    rewrite (SeriesC_list (seqZ (- A) (2 * A + 1)) (λ z, exp (- ε * IZR (Z.abs z))));
      [|apply NoDup_seqZ].
    replace (2 * A + 1)%Z with (A + (A + 1))%Z by lia.
    rewrite (seqZ_app (- A) A (A + 1)); [|lia|lia].
    replace (- A + A)%Z with 0%Z by lia.
    replace (A + 1)%Z with (1 + A)%Z by lia.
    rewrite (seqZ_app 0 1 A); [|lia|lia].
    replace (0 + 1)%Z with 1%Z by lia.
    rewrite !foldr_app. simpl foldr.
    assert (Hacc : ∀ (g : Z → R) (l : list Z) (c : R),
              foldr (Rplus ∘ g) c l = foldr (Rplus ∘ g) 0 l + c).
    { intros g l. induction l as [|x l IH]; intros c; simpl.
      - lra.
      - rewrite (IH c). unfold compose. lra. }
    rewrite Hacc.
    rewrite (foldr_Rplus_ext (λ z, exp (- ε * IZR (Z.abs z)))
               (λ z, exp (ε * IZR (z - 0))) (seqZ (- A) A));
      last (apply Forall_forall; intros z Hz; apply elem_of_seqZ in Hz;
            f_equal; rewrite Z.sub_0_r (Z.abs_neq z); [|lia]; rewrite opp_IZR; lra).
    rewrite (foldr_Rplus_ext (λ z, exp (- ε * IZR (Z.abs z)))
               (λ z, exp (- ε * IZR z)) (seqZ 1 A));
      last (apply Forall_forall; intros z Hz; apply elem_of_seqZ in Hz;
            f_equal; f_equal; rewrite (Z.abs_eq z); [reflexivity | lia]).
    replace (seqZ (- A) A) with (seqZ (0 - A) (Z.of_nat (Z.to_nat A)))
      by (rewrite Z2Nat.id; [f_equal; lia | lia]).
    rewrite (tlap_bndry_geom 0 (Z.to_nat A) ltac:(rewrite Z2Nat.id; lia)).
    replace (seqZ 1 A) with (seqZ 1 (Z.of_nat (Z.to_nat A)))
      by (rewrite Z2Nat.id; [reflexivity | lia]).
    rewrite (tlap_top_geom 1 (Z.to_nat A)).
    rewrite !Z2Nat.id; [|lia..].
    rewrite exp_pow.
    replace (ε * INR (Z.to_nat A)) with (ε * IZR A)
      by (rewrite INR_IZR_INZ Z2Nat.id; [reflexivity | lia]).
    replace (Z.abs (Z.of_nat 0 + 0)) with 0%Z by lia.
    simpl (IZR 0). rewrite Rmult_0_r exp_0.
    assert (HexpA : exp (ε * IZR A) = / exp (- ε * IZR A)).
    { rewrite -exp_Ropp. f_equal. lra. }
    rewrite HexpA.
    assert (Ha : exp (- ε) <> 0) by (apply Rgt_not_eq, exp_pos).
    assert (HaA : exp (- ε * IZR A) <> 0) by (apply Rgt_not_eq, exp_pos).
    assert (Hexpε : exp ε - 1 <> 0).
    { assert (1 < exp ε); [|lra]. rewrite -exp_0. apply exp_increasing. lra. }
    assert (Halt : 1 - exp (- ε) <> 0).
    { assert (exp (- ε) < 1); [|lra]. rewrite -exp_0. apply exp_increasing. lra. }
    replace (exp (- ε * 1)) with (exp (- ε)) by (f_equal; lra).
    replace (exp (- ε * IZR (1 + A))) with (exp (- ε) * exp (- ε * IZR A)).
    2:{ rewrite -exp_plus. f_equal. rewrite plus_IZR. lra. }
    assert (Hexpε' : exp ε = / exp (- ε)) by (rewrite -exp_Ropp; f_equal; lra).
    rewrite Hexpε'.
    set (a := exp (- ε)) in *. set (b := exp (- ε * IZR A)) in *.
    field; repeat split; try assumption; intros HC; apply Halt; nra.
  Qed.

  (** ** The workhorse closed form ([Δ ≤ A]):
        [tlap_tail Δ = α^{A-Δ+1}·(1-α^Δ) / (1+α-2α^{A+1})].
      The top slice [{A-Δ+1,…,A}] lies entirely in the positive half (since
      [A-Δ+1 ≥ 1]), so its mass is a single geometric run. *)
  Lemma tlap_tail_le_A (Δ : Z) :
    (0 <= Δ <= A)%Z →
    tlap_tail A num den Δ
      = exp (- ε * IZR (A - Δ + 1)) * (1 - exp (- ε * IZR Δ))
        / (1 + exp (- ε) - 2 * exp (- ε * IZR (A + 1))).
  Proof using A num den HA Heps.
    intros HΔ.
    rewrite -tlap_Z_closed.
    pose proof (tlap_Z_pos A num den 0 HA) as HZpos.
    rewrite /tlap_tail.
    rewrite (SeriesC_ext _
               (λ z, if bool_decide (z ∈ seqZ (A - Δ + 1) Δ)
                     then trunc_lap_rat A num den 0 z else 0%R)).
    2:{ intros z. rewrite (bool_decide_ext (z ∈ tlap_supp A 0 ∧ (A - Δ < z)%Z)
                                            (z ∈ seqZ (A - Δ + 1) Δ)); [done|].
        rewrite elem_of_seqZ elem_of_tlap_supp. lia. }
    rewrite (SeriesC_list (seqZ (A - Δ + 1) Δ) (trunc_lap_rat A num den 0));
      [|apply NoDup_seqZ].
    rewrite (foldr_Rplus_ext (trunc_lap_rat A num den 0)
               (λ z, / tlap_Z A num den 0 * exp (- ε * IZR z)));
      last (apply Forall_forall; intros z Hz; apply elem_of_seqZ in Hz;
            rewrite trunc_lap_rat_unfold /tlap_w;
            rewrite bool_decide_eq_true_2; [|apply elem_of_tlap_supp; lia];
            rewrite Rdiv_def Rmult_comm; do 2 f_equal;
            rewrite Z.sub_0_r Z.abs_eq; [reflexivity | lia]).
    rewrite -(foldr_Rplus_scal_l (/ tlap_Z A num den 0) (λ z, exp (- ε * IZR z))).
    replace (seqZ (A - Δ + 1) Δ) with (seqZ (A - Δ + 1) (Z.of_nat (Z.to_nat Δ)))
      by (rewrite Z2Nat.id; [reflexivity | lia]).
    rewrite tlap_top_geom Z2Nat.id; [|lia].
    assert (Halt : 1 - exp (- ε) <> 0).
    { assert (exp (- ε) < 1); [|lra]. rewrite -exp_0. apply exp_increasing. lra. }
    field. split; [lra | exact Halt].
  Qed.

  (** The DOMINANT case [Δ=1]: [tlap_tail 1 = (1-α)·α^A / (1+α-2α^{A+1})]. *)
  Lemma tlap_tail_one :
    (1 <= A)%Z →
    tlap_tail A num den 1
      = (1 - exp (- ε)) * exp (- ε * IZR A)
        / (1 + exp (- ε) - 2 * exp (- ε * IZR (A + 1))).
  Proof using A num den HA Heps.
    intros HA1. rewrite (tlap_tail_le_A 1 ltac:(lia)).
    replace (A - 1 + 1)%Z with A by lia.
    replace (IZR 1) with 1 by (simpl; lra).
    replace (exp (- ε * 1)) with (exp (- ε)) by (f_equal; lra).
    rewrite (Rmult_comm (exp (- ε * IZR A)) (1 - exp (- ε))). reflexivity.
  Qed.

  (** The case [Δ=A]: [tlap_tail A = α·(1-α^A) / (1+α-2α^{A+1})]. *)
  Lemma tlap_tail_eq_A :
    (0 <= A)%Z →
    tlap_tail A num den A
      = exp (- ε) * (1 - exp (- ε * IZR A))
        / (1 + exp (- ε) - 2 * exp (- ε * IZR (A + 1))).
  Proof using A num den HA Heps.
    intros HA0. rewrite (tlap_tail_le_A A ltac:(lia)).
    replace (A - A + 1)%Z with 1%Z by lia.
    replace (IZR 1) with 1 by (simpl; lra).
    replace (exp (- ε * 1)) with (exp (- ε)) by (f_equal; lra). reflexivity.
  Qed.

  (** The DISJOINT case [Δ ≥ 2A+1]: the shift moves the support entirely off the
      old one, so the bad set is the WHOLE support and [tlap_tail = 1]. *)
  Lemma tlap_tail_disjoint (Δ : Z) :
    (2 * A + 1 <= Δ)%Z →
    tlap_tail A num den Δ = 1.
  Proof using A num den HA Heps.
    intros HΔ. rewrite /tlap_tail.
    rewrite -(trunc_lap_rat_mass A num den 0 HA).
    apply SeriesC_ext. intros z.
    destruct (decide (z ∈ tlap_supp A 0)) as [Hin|Hin].
    - (* on the support: [A-Δ < z] is automatic, the indicator keeps the pmf *)
      rewrite bool_decide_eq_true_2; [reflexivity|].
      split; [done|]. apply elem_of_tlap_supp in Hin. lia.
    - (* off the support: indicator is 0, but so is the pmf *)
      rewrite bool_decide_eq_false_2; last (intros [Hc _]; done).
      rewrite trunc_lap_rat_unfold /tlap_w bool_decide_eq_false_2; [|done].
      rewrite Rdiv_0_l. reflexivity.
  Qed.

  (** ** The TIGHT per-distance metric-DP coupling — the crux, ALL shifts.

      For a TWO-SIDED shift [s := loc' - loc] (UNCONDITIONALLY — no [|s| ≤ A]),
      the truncated discrete Laplace satisfies a DP coupling with the OPTIMAL
      additive error: the bad-set tail mass [tlap_tail A num den |s|].  The
      overlap multiplicative ratio [≤ exp(|s|·ε)] holds for ALL [s] (two-sided
      triangle inequality, [tlap_w_overlap_ratio]); the additive term is exactly
      the mass of the uncovered "bad set" [supp(loc) \ supp(loc+s)], which equals
      [tlap_tail |s|] for ALL [s] by the master identity [tlap_bndry_mass_tail].
      For [|s| ≤ A] this is the group bound; for [|s| > A] it is STRICTLY tighter
      (the tail mass saturates toward [1] while the group bound keeps growing);
      for [|s| ≥ 2A+1] the supports are disjoint and the mass is exactly [1]. *)
  Theorem DPcoupl_trunc_lap_tight (loc s : Z) :
    DPcoupl (trunc_lap_rat A num den loc) (trunc_lap_rat A num den (loc + s))
            eq (IZR (Z.abs s) * ε) (tlap_tail A num den (Z.abs s)).
  Proof using A num den HA Heps.
    apply DPcoupl_complete_eq. intros P.
    rewrite /prob.
    (* dominate the LHS pointwise by the decomposed RHS *)
    etrans.
    1:{ apply SeriesC_le.
      - intros z. split.
        + case_bool_decide; [apply pmf_pos|lra].
        + instantiate
            (1 := λ z, exp (IZR (Z.abs s) * ε) * (if bool_decide (P z)
                                          then trunc_lap_rat A num den (loc + s) z
                                          else 0)
                       + (if bool_decide (P z) then tlap_bndry loc s z else 0)).
          simpl. case_bool_decide as HP.
          * apply tlap_pmf_decomp.
          * rewrite Rmult_0_r Rplus_0_r. apply Rle_refl.
      - apply ex_seriesC_plus.
        + apply ex_seriesC_scal_l.
          eapply ex_seriesC_le; last apply (pmf_ex_seriesC (trunc_lap_rat A num den (loc + s))).
          intros z. case_bool_decide; split; try apply pmf_pos; try lra; apply Rle_refl.
        + eapply ex_seriesC_le; last apply ex_seriesC_tlap_bndry.
          intros z. case_bool_decide; split; try apply tlap_bndry_nonneg; try lra;
            apply Rle_refl. }
    (* split the sum: exp(|s|ε)·prob μ2 P + Σ (if P then bndry) *)
    rewrite SeriesC_plus.
    2:{ apply ex_seriesC_scal_l.
        eapply ex_seriesC_le; last apply (pmf_ex_seriesC (trunc_lap_rat A num den (loc + s))).
        intros z. case_bool_decide; split; try apply pmf_pos; try lra; apply Rle_refl. }
    2:{ eapply ex_seriesC_le; last apply ex_seriesC_tlap_bndry.
        intros z. case_bool_decide; split; try apply tlap_bndry_nonneg; try lra;
          apply Rle_refl. }
    rewrite SeriesC_scal_l.
    apply Rplus_le_compat_l.
    (* the boundary contribution is bounded by the TOTAL boundary mass = tail mass *)
    rewrite -(tlap_bndry_mass_tail loc s).
    apply SeriesC_le.
    - intros z. case_bool_decide; split; try apply tlap_bndry_nonneg; try lra;
        apply Rle_refl.
    - apply ex_seriesC_tlap_bndry.
  Qed.

  (** ** [tlap_tail] vs the group bound.

      For [|s| ≤ A] the tail mass coincides EXACTLY with the group-bound
      [tlap_delta] (both equal the bottom/top boundary slice mass; via the two
      mass identities). *)
  Lemma tlap_tail_eq_delta (loc s : Z) :
    (Z.abs s <= A)%Z →
    tlap_tail A num den (Z.abs s) = tlap_delta loc s.
  Proof using A num den HA Heps.
    intros Hs. rewrite -(tlap_bndry_mass_tail loc s). by apply tlap_bndry_mass.
  Qed.

  (** [tlap_delta] as a (un-normalised, un-clamped) geometric run: its mass is the
      sum, over the [|s|]-term run [{A-|s|+1,…,A}], of the CENTERED weight
      [exp(-ε·z)/Z_A].  Compared with [tlap_tail] (which sums [exp(-ε·|z|)/Z_A]
      over the CLAMPED slice), this is the same run but (i) using [z] instead of
      [|z|] in the exponent and (ii) WITHOUT clamping at the lower support edge —
      both of which only INCREASE the mass.  Hence [tlap_tail ≤ tlap_delta]. *)
  Lemma tlap_delta_run (loc s : Z) :
    tlap_delta loc s
      = SeriesC (λ z, if bool_decide ((A - Z.abs s < z)%Z ∧ (z <= A)%Z)
                      then exp (- ε * IZR z) / tlap_Z A num den 0 else 0%R).
  Proof using A num den HA Heps.
    pose proof (tlap_Z_pos A num den 0 HA) as HZpos.
    set (Δ := Z.abs s).
    assert (HΔ : (0 <= Δ)%Z) by apply Z.abs_nonneg.
    rewrite (SeriesC_ext _
               (λ z, if bool_decide (z ∈ seqZ (A - Δ + 1) Δ)
                     then exp (- ε * IZR z) / tlap_Z A num den 0 else 0%R)).
    2:{ intros z. rewrite (bool_decide_ext ((A - Δ < z)%Z ∧ (z <= A)%Z)
                                            (z ∈ seqZ (A - Δ + 1) Δ)); [done|].
        rewrite elem_of_seqZ. lia. }
    rewrite (SeriesC_list (seqZ (A - Δ + 1) Δ)
               (λ z, exp (- ε * IZR z) / tlap_Z A num den 0)); [|apply NoDup_seqZ].
    rewrite (foldr_Rplus_ext (λ z, exp (- ε * IZR z) / tlap_Z A num den 0)
               (λ z, / tlap_Z A num den 0 * exp (- ε * IZR z)));
      last (apply Forall_forall; intros z _; rewrite Rdiv_def Rmult_comm; reflexivity).
    rewrite -(foldr_Rplus_scal_l (/ tlap_Z A num den 0) (λ z, exp (- ε * IZR z))).
    replace (seqZ (A - Δ + 1) Δ) with (seqZ (A - Δ + 1) (Z.of_nat (Z.to_nat Δ)))
      by (rewrite Z2Nat.id; [reflexivity | lia]).
    rewrite tlap_top_geom Z2Nat.id; [|lia].
    rewrite /tlap_delta.
    assert (Halt : 1 - exp (- ε) <> 0).
    { assert (exp (- ε) < 1); [|lra]. rewrite -exp_0. apply exp_increasing. lra. }
    assert (Hexpε : exp ε - 1 <> 0).
    { assert (1 < exp ε); [|lra]. rewrite -exp_0. apply exp_increasing. lra. }
    replace (exp (- ε * IZR (A - Δ + 1))) with (exp (- ε * IZR A) * exp (ε * IZR Δ) * exp (- ε)).
    2:{ rewrite -!exp_plus. f_equal.
        replace (IZR (A - Δ + 1)) with (IZR A - IZR Δ + 1)
          by (rewrite plus_IZR minus_IZR; simpl; lra).
        lra. }
    replace (exp (- ε * IZR Δ)) with (/ exp (ε * IZR Δ)).
    2:{ rewrite -exp_Ropp. f_equal. lra. }
    replace (exp ε) with (/ exp (- ε)).
    2:{ rewrite -exp_Ropp. f_equal. lra. }
    set (a := exp (- ε)) in *. set (d := exp (ε * IZR Δ)) in *. set (b := exp (- ε * IZR A)) in *.
    assert (Ha : a <> 0) by (apply Rgt_not_eq, exp_pos).
    assert (Hd : d <> 0) by (apply Rgt_not_eq, exp_pos).
    replace (tlap_Z A num den loc) with (tlap_Z A num den 0) by apply tlap_Z_shift_inv.
    replace (exp (IZR (Z.abs s) * ε)) with d by (unfold d; rewrite Rmult_comm; reflexivity).
    field. repeat split; try assumption. intros HC. apply Halt. nra.
  Qed.

  (** ** The KEY inequality: the tail mass is at most the group bound, with
      EQUALITY for [|s| ≤ A] and (strict) SLACK beyond.  Proved by a pointwise
      [SeriesC_le] comparison of the [tlap_tail] indicator against the
      [tlap_delta_run] indicator: on the common range the only difference is
      [exp(-ε·|z|) ≤ exp(-ε·z)] (since [z ≤ |z|]), and the run carries extra
      (nonnegative) "virtual" terms past the lower support edge. *)
  Lemma tlap_tail_le_grp (loc s : Z) :
    tlap_tail A num den (Z.abs s) <= tlap_delta loc s.
  Proof using A num den HA Heps.
    pose proof (tlap_Z_pos A num den 0 HA) as HZpos.
    rewrite tlap_delta_run /tlap_tail.
    apply SeriesC_le.
    2:{ eapply ex_seriesC_ext.
        2:{ apply (ex_seriesC_list (seqZ (A - Z.abs s + 1) (Z.abs s))
                     (λ z, exp (- ε * IZR z) / tlap_Z A num den 0)). }
        intros z. rewrite (bool_decide_ext ((A - Z.abs s < z)%Z ∧ (z <= A)%Z)
                                            (z ∈ seqZ (A - Z.abs s + 1) (Z.abs s))); [done|].
        rewrite elem_of_seqZ. lia. }
    intros z. split.
    - case_bool_decide; [apply pmf_pos | lra].
    - case_bool_decide as Hb.
      + destruct Hb as [Hsupp Hlt].
        apply elem_of_tlap_supp in Hsupp.
        rewrite bool_decide_eq_true_2; last lia.
        rewrite trunc_lap_rat_unfold /tlap_w.
        rewrite bool_decide_eq_true_2; last (apply elem_of_tlap_supp; lia).
        apply Rmult_le_compat_r; [left; apply Rinv_pos; exact HZpos|].
        apply exp_mono. rewrite Z.sub_0_r. apply Rmult_le_compat_neg_l; [lra|].
        apply IZR_le. lia.
      + case_bool_decide; [|apply Rle_refl].
        apply Rmult_le_pos; [left; apply exp_pos | left; apply Rinv_pos; exact HZpos].
  Qed.

  (** ** The group-bound coupling, ALL shifts (the legacy profile), now derived
      as a COROLLARY of the tight coupling by weakening the additive error from
      the optimal [tlap_tail] up to the group bound [tlap_delta] via
      [DPcoupl_mono] (using [tlap_tail_le_grp]).  This is now UNCONDITIONAL: the
      old [|s| ≤ A] hypothesis is dropped. *)
  Theorem DPcoupl_trunc_lap (loc s : Z) :
    DPcoupl (trunc_lap_rat A num den loc) (trunc_lap_rat A num den (loc + s))
            eq (IZR (Z.abs s) * ε) (tlap_delta loc s).
  Proof using A num den HA Heps.
    eapply (DPcoupl_mono _ _ _ _ eq _ (IZR (Z.abs s) * ε) (IZR (Z.abs s) * ε)
              (tlap_tail A num den (Z.abs s)) (tlap_delta loc s));
      [ reflexivity | reflexivity | tauto | lra
      | apply tlap_tail_le_grp | apply DPcoupl_trunc_lap_tight ].
  Qed.

  (** ** Sanity checks. *)

  (** At [s = 0] the boundary mass [δ] vanishes (the slice is empty). *)
  Lemma tlap_delta_0 (loc : Z) : tlap_delta loc 0 = 0.
  Proof using A num den.
    rewrite /tlap_delta. simpl. rewrite Rmult_0_l exp_0. lra.
  Qed.

  (** Hence at [s = 0] the coupling is reflexive: [(0·ε, 0)]-DP, i.e. a plain
      coupling of a distribution with itself. *)
  Corollary DPcoupl_trunc_lap_refl (loc : Z) :
    DPcoupl (trunc_lap_rat A num den loc) (trunc_lap_rat A num den loc)
            eq 0 0.
  Proof using A num den HA Heps.
    pose proof (DPcoupl_trunc_lap loc 0) as H.
    rewrite Z.add_0_r in H.
    rewrite (tlap_delta_0 loc) in H.
    replace (IZR (Z.abs 0) * ε) with 0 in H by (rewrite Z.abs_0; simpl; lra).
    exact H.
  Qed.

  (** The coupling phrased directly in terms of the second center [loc'], now
      UNCONDITIONAL (the old [|loc'-loc| ≤ A] hypothesis is dropped). *)
  Corollary DPcoupl_trunc_lap_loc (loc loc' : Z) :
    DPcoupl (trunc_lap_rat A num den loc) (trunc_lap_rat A num den loc')
            eq (IZR (Z.abs (loc' - loc)) * ε) (tlap_delta loc (loc' - loc)).
  Proof using A num den HA Heps.
    pose proof (DPcoupl_trunc_lap loc (loc' - loc)) as H.
    replace (loc + (loc' - loc))%Z with loc' in H by lia.
    exact H.
  Qed.

  (** The TIGHT coupling phrased in terms of the second center [loc']: optimal
      additive error [tlap_tail |loc'-loc|], for ANY two centers. *)
  Corollary DPcoupl_trunc_lap_loc_tight (loc loc' : Z) :
    DPcoupl (trunc_lap_rat A num den loc) (trunc_lap_rat A num den loc')
            eq (IZR (Z.abs (loc' - loc)) * ε) (tlap_tail A num den (Z.abs (loc' - loc))).
  Proof using A num den HA Heps.
    pose proof (DPcoupl_trunc_lap_tight loc (loc' - loc)) as H.
    replace (loc + (loc' - loc))%Z with loc' in H by lia.
    exact H.
  Qed.

  (** NOTE on truncation removal.  As [A → ∞] the boundary mass
      [δ_A_s = (exp(-ε·A)/Z_A)·(exp(|s|·ε)-1)/(exp ε-1) → 0] (the prefactor
      [exp(-ε·A) → 0] while [Z_A → 1/(tanh(ε/2))] stays bounded), recovering the
      pure [(|s|·ε, 0)]-DP profile of the untruncated discrete Laplace.  We do
      not formalise the limit. *)

End trunc_laplace_dp.
