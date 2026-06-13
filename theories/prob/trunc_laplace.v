(** The TRUNCATED discrete Laplace mechanism (bounded support), and its
    per-distance metric-DP coupling.

    Given a rate [num/den] (with [ε := num/den > 0]), a truncation half-width
    [A ≥ 0], and a center [loc], the truncated discrete Laplace distribution
    [trunc_lap_rat A num den loc] is supported on [{loc-A, …, loc+A}] with pmf

        z ↦ exp(-ε·|z-loc|) / Z_A      (z in support; 0 otherwise),

    where [Z_A := Σ_{k=-A}^{A} exp(-ε·|k|) = 1 + 2·Σ_{j=1}^{A} exp(-εj)] is the
    (location-independent) normaliser.

    The crux of this file is the per-distance approximate-DP coupling: for a
    shift [s := loc' - loc] with [0 ≤ s ≤ A], we prove

        DPcoupl (trunc_lap_rat A num den loc) (trunc_lap_rat A num den loc')
                eq  (s·ε)  δ_A_s,

    with the EXACT group-bound boundary mass

        δ_A_s := (exp(-ε·A) / Z_A) · (exp(s·ε) - 1) / (exp ε - 1).

    This is the validating example for "metric approximate DP": the privacy
    profile is exactly the group-bound, with the [δ] coming solely from the
    bottom boundary slice [{loc-A, …, loc-A+s-1}] that the shifted distribution
    [trunc_lap(loc')] cannot cover.

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

End trunc_laplace_distr.

(** * The per-distance metric-DP coupling *)

Section trunc_laplace_dp.

  Context (A num den : Z).
  Context (HA : (0 <= A)%Z).
  (** [ε := num/den], assumed positive. *)
  Context (Heps : (0 < IZR num / IZR den)%R).

  Local Notation ε := (IZR num / IZR den).

  (** The bottom boundary slice [{loc-A, …, loc-A+s-1}] that the shifted
      distribution [trunc_lap(loc+s)] cannot cover. *)
  Definition tlap_bndry (loc s z : Z) : R :=
    if bool_decide (z ∈ seqZ (loc - A) s)
    then trunc_lap_rat A num den loc z else 0%R.

  (** ** Weight-level bound on the overlap.

      If [z] lies in the support of [trunc_lap(loc+s)] (the shifted
      distribution), then [w(loc,z) ≤ exp(s·ε)·w(loc+s,z)]. *)
  Lemma tlap_w_overlap_ratio (loc s z : Z) :
    (0 <= s)%Z →
    z ∈ tlap_supp A (loc + s) →
    tlap_w A num den loc z
      <= exp (IZR s * ε) * tlap_w A num den (loc + s) z.
  Proof using A num den Heps.
    intros Hs Hz'.
    rewrite {2}/tlap_w bool_decide_eq_true_2; [|done].
    rewrite /tlap_w.
    case_bool_decide as Hz; last first.
    { (* z ∉ supp(loc): w(loc,z) = 0 *)
      apply Rmult_le_pos; [left; apply exp_pos|left; apply exp_pos]. }
    rewrite -exp_plus. apply exp_mono.
    (* Goal: -ε·|z-loc| <= s·ε + (-ε·|z-(loc+s)|).
       Suffices |z-(loc+s)| <= |z-loc| + s, by the triangle inequality. *)
    apply elem_of_tlap_supp in Hz, Hz'.
    assert (Htri : (Z.abs (z - (loc + s)) <= Z.abs (z - loc) + s)%Z).
    { pose proof (Z.abs_triangle (z - loc) (loc - (loc + s))) as Ht.
      replace (z - loc + (loc - (loc + s)))%Z with (z - (loc + s))%Z in Ht by lia.
      replace (Z.abs (loc - (loc + s))) with s in Ht by (rewrite Z.abs_neq; lia).
      lia. }
    assert (IZR (Z.abs (z - (loc + s))) <= IZR (Z.abs (z - loc)) + IZR s)%R
      as Htri'.
    { rewrite -plus_IZR. apply IZR_le. lia. }
    nra.
  Qed.

  (** Membership in the boundary slice [seqZ (loc-A) s] is exactly
      "in [supp(loc)] but not in [supp(loc+s)]" (for [0 ≤ s ≤ A]). *)
  Lemma tlap_bndry_iff (loc s z : Z) :
    (0 <= s <= A)%Z →
    z ∈ seqZ (loc - A) s
    ↔ (z ∈ tlap_supp A loc ∧ z ∉ tlap_supp A (loc + s)).
  Proof.
    intros Hs. rewrite elem_of_seqZ !elem_of_tlap_supp.
    split; [lia|]. intros [? ?]. lia.
  Qed.

  (** ** Pmf-level decomposition (the key pointwise bound).

      [μ(loc) z ≤ exp(s·ε)·μ(loc+s) z + bndry(loc,s) z] for every [z]. *)
  Lemma tlap_pmf_decomp (loc s z : Z) :
    (0 <= s <= A)%Z →
    trunc_lap_rat A num den loc z
      <= exp (IZR s * ε) * trunc_lap_rat A num den (loc + s) z
         + tlap_bndry loc s z.
  Proof using A num den HA Heps.
    intros Hs.
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
         w / ZA <= exp(sε) * (w' / ZA) + (if z∈slice then w / ZA else 0) *)
    destruct (decide (z ∈ tlap_supp A (loc + s))) as [Hin'|Hin'].
    - (* overlap: bndry term is 0; use the weight ratio bound *)
      rewrite bool_decide_eq_false_2; last first.
      { rewrite tlap_bndry_iff; [|lia]. tauto. }
      rewrite Rplus_0_r. unfold Rdiv. rewrite -Rmult_assoc.
      apply Rmult_le_compat_r.
      { left. apply Rinv_pos. exact HZpos. }
      apply tlap_w_overlap_ratio; [lia|done].
    - (* z ∉ supp(loc+s): then exp(sε)·μ' z = 0 *)
      assert (w' = 0) as Hw'0.
      { rewrite /w' /tlap_w bool_decide_eq_false_2; [done|exact Hin']. }
      rewrite Hw'0 Rdiv_0_l Rmult_0_r Rplus_0_l.
      destruct (decide (z ∈ tlap_supp A loc)) as [Hin|Hin].
      + (* z is in the boundary slice: equality *)
        rewrite bool_decide_eq_true_2; last first.
        { rewrite tlap_bndry_iff; [|lia]. done. }
        lra.
      + (* z outside both supports: w = 0 *)
        assert (w = 0) as Hw0.
        { rewrite /w /tlap_w bool_decide_eq_false_2; [done|exact Hin]. }
        rewrite Hw0 Rdiv_0_l. case_bool_decide; lra.
  Qed.

  (** ** Boundary mass — the geometric sum.

      The total mass of the bottom boundary slice [{loc-A, …, loc-A+s-1}]. *)

  (** The exact group-bound boundary mass
        [δ_A_s = (exp(-ε·A)/Z_A) · (exp(s·ε) - 1)/(exp ε - 1)]. *)
  Definition tlap_delta (loc s : Z) : R :=
    (exp (- ε * IZR A) / tlap_Z A num den loc)
      * (exp (IZR s * ε) - 1) / (exp ε - 1).

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

  (** ** The exact boundary mass: [SeriesC (bndry) = δ_A_s]. *)
  Lemma tlap_bndry_mass (loc s : Z) :
    (0 <= s <= A)%Z →
    SeriesC (tlap_bndry loc s) = tlap_delta loc s.
  Proof using A num den HA Heps.
    intros Hs.
    pose proof (tlap_Z_pos A num den loc HA) as HZpos.
    (* 1. reduce the SeriesC over the finite slice to a foldr *)
    rewrite /tlap_bndry.
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
    (* 5. relate [(exp ε)^(Z.to_nat s)] to [exp (IZR s * ε)] *)
    rewrite exp_pow.
    replace (ε * INR (Z.to_nat s)) with (IZR s * ε).
    2:{ rewrite INR_IZR_INZ Z2Nat.id; [lra|lia]. }
    rewrite /tlap_delta. field. split.
    - lra.
    - assert (1 < exp ε); [|lra]. rewrite -exp_0. apply exp_increasing. lra.
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

  (** ** The per-distance metric-DP coupling — the crux.

      For a forward shift [s := loc' - loc] with [0 ≤ s ≤ A], the truncated
      discrete Laplace satisfies a DP coupling with the EXACT group-bound
      privacy profile [(s·ε, δ_A_s)]. *)
  Theorem DPcoupl_trunc_lap (loc s : Z) :
    (0 <= s <= A)%Z →
    DPcoupl (trunc_lap_rat A num den loc) (trunc_lap_rat A num den (loc + s))
            eq (IZR s * ε) (tlap_delta loc s).
  Proof using A num den HA Heps.
    intros Hs.
    apply DPcoupl_complete_eq. intros P.
    rewrite /prob.
    (* dominate the LHS pointwise by the decomposed RHS *)
    etrans.
    1:{ apply SeriesC_le.
      - intros z. split.
        + case_bool_decide; [apply pmf_pos|lra].
        + (* if P z then μ1 z else 0 <=
               exp(sε)·(if P z then μ2 z else 0) + (if P z then bndry z else 0) *)
          instantiate
            (1 := λ z, exp (IZR s * ε) * (if bool_decide (P z)
                                          then trunc_lap_rat A num den (loc + s) z
                                          else 0)
                       + (if bool_decide (P z) then tlap_bndry loc s z else 0)).
          simpl. case_bool_decide as HP.
          * apply tlap_pmf_decomp; lia.
          * rewrite Rmult_0_r Rplus_0_r. apply Rle_refl.
      - (* summability of the dominating function *)
        apply ex_seriesC_plus.
        + apply ex_seriesC_scal_l.
          eapply ex_seriesC_le; last apply (pmf_ex_seriesC (trunc_lap_rat A num den (loc + s))).
          intros z. case_bool_decide; split; try apply pmf_pos; try lra; apply Rle_refl.
        + eapply ex_seriesC_le; last apply ex_seriesC_tlap_bndry.
          intros z. case_bool_decide; split; try apply tlap_bndry_nonneg; try lra;
            apply Rle_refl. }
    (* split the sum: exp(sε)·prob μ2 P + Σ (if P then bndry) *)
    rewrite SeriesC_plus.
    2:{ apply ex_seriesC_scal_l.
        eapply ex_seriesC_le; last apply (pmf_ex_seriesC (trunc_lap_rat A num den (loc + s))).
        intros z. case_bool_decide; split; try apply pmf_pos; try lra; apply Rle_refl. }
    2:{ eapply ex_seriesC_le; last apply ex_seriesC_tlap_bndry.
        intros z. case_bool_decide; split; try apply tlap_bndry_nonneg; try lra;
          apply Rle_refl. }
    rewrite SeriesC_scal_l.
    apply Rplus_le_compat_l.
    (* the boundary contribution is bounded by the total boundary mass = δ *)
    rewrite -(tlap_bndry_mass loc s Hs).
    apply SeriesC_le.
    - intros z. case_bool_decide; split; try apply tlap_bndry_nonneg; try lra;
        apply Rle_refl.
    - apply ex_seriesC_tlap_bndry.
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
    pose proof (DPcoupl_trunc_lap loc 0 ltac:(lia)) as H.
    rewrite Z.add_0_r in H.
    rewrite (tlap_delta_0 loc) in H.
    replace (IZR 0 * ε) with 0 in H by (simpl; lra).
    exact H.
  Qed.

  (** The coupling phrased directly in terms of the second center [loc']. *)
  Corollary DPcoupl_trunc_lap_loc (loc loc' : Z) :
    (0 <= loc' - loc <= A)%Z →
    DPcoupl (trunc_lap_rat A num den loc) (trunc_lap_rat A num den loc')
            eq (IZR (loc' - loc) * ε) (tlap_delta loc (loc' - loc)).
  Proof using A num den HA Heps.
    intros Hs.
    pose proof (DPcoupl_trunc_lap loc (loc' - loc) Hs) as H.
    replace (loc + (loc' - loc))%Z with loc' in H by lia.
    exact H.
  Qed.

  (** NOTE on the symmetric direction.  For a backward shift [loc' < loc] the
      argument is fully analogous: the uncovered boundary slice is the TOP
      slice [{loc+A-|s|+1, …, loc+A}] of [trunc_lap(loc)] (where
      [trunc_lap(loc')] has no support), and the same geometric computation
      yields the same [δ] with [|s|] in place of [s].  We formalise the forward
      direction [0 ≤ s] here; the backward case is symmetric (swap the roles of
      [loc]/[loc'] and reflect the support).

      NOTE on truncation removal.  As [A → ∞] the boundary mass
      [δ_A_s = (exp(-ε·A)/Z_A)·(exp(s·ε)-1)/(exp ε-1) → 0] (the prefactor
      [exp(-ε·A) → 0] while [Z_A → 1/(tanh(ε/2))] stays bounded), recovering the
      pure [(s·ε, 0)]-DP profile of the untruncated discrete Laplace.  We do not
      formalise the limit. *)

End trunc_laplace_dp.
