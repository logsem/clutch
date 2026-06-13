(** The discrete EXPONENTIAL MECHANISM distribution over a finite candidate set,
    and its ε-DP coupling.

    Given a rate [num/den] and a score vector [scores : list Z], the exponential
    mechanism samples an index [i ∈ [0, length scores)] with probability
    proportional to [exp ((num/den)·scoreᵢ)].  This is the fundamental object;
    the [SampleFamily]/WP-rule/adequacy layers come later.  Outcome type is [Z]
    (the chosen index). *)
From Stdlib Require Import Reals Psatz.
From clutch.prelude Require Import base.
From clutch.prob Require Export distribution.
From clutch.prob Require Import couplings_exp couplings_dp.
From clutch.prob Require Import couplings_dp_complete.

Local Open Scope R.

Section exponential_mechanism.

  (** The index set [{0,…,length scores−1}], as a list of [Z]. *)
  Definition expmech_idxs (scores : list Z) : list Z :=
    seqZ 0 (Z.of_nat (length scores)).

  (** unnormalised weight of index [i] *)
  Definition expmech_w (num den : Z) (scores : list Z) (i : Z) : R :=
    if bool_decide (0 <= i)%Z && bool_decide (i < Z.of_nat (length scores))%Z
    then exp ((IZR num / IZR den) * IZR (scores !!! Z.to_nat i))
    else 0%R.

  (** normaliser *)
  Definition expmech_Z (num den : Z) (scores : list Z) : R :=
    SeriesC (expmech_w num den scores).

  (** ** Support characterisation: [w] is supported on [expmech_idxs]. *)

  Lemma elem_of_expmech_idxs (scores : list Z) (i : Z) :
    i ∈ expmech_idxs scores ↔ (0 <= i)%Z ∧ (i < Z.of_nat (length scores))%Z.
  Proof.
    rewrite /expmech_idxs elem_of_seqZ. lia.
  Qed.

  Lemma expmech_w_eq_list (num den : Z) (scores : list Z) (i : Z) :
    expmech_w num den scores i =
      if bool_decide (i ∈ expmech_idxs scores)
      then exp ((IZR num / IZR den) * IZR (scores !!! Z.to_nat i)) else 0%R.
  Proof.
    rewrite /expmech_w.
    destruct (decide (i ∈ expmech_idxs scores)) as [Hin|Hin].
    - rewrite (bool_decide_eq_true_2 (i ∈ _)); [|done].
      pose proof (proj1 (elem_of_expmech_idxs scores i) Hin) as [Hi1 Hi2].
      rewrite (bool_decide_eq_true_2 (0 <= i)%Z); [|done].
      rewrite (bool_decide_eq_true_2 (i < _)%Z); [|done]. done.
    - rewrite (bool_decide_eq_false_2 (i ∈ _)); [|done].
      destruct (bool_decide (0 <= i)%Z
                && bool_decide (i < Z.of_nat (length scores))%Z)
        eqn:Hb; [|done].
      exfalso. apply Hin, elem_of_expmech_idxs.
      apply andb_prop in Hb. destruct Hb as [Hb1 Hb2].
      apply bool_decide_eq_true_1 in Hb1, Hb2. done.
  Qed.

  Lemma expmech_w_pos (num den : Z) (scores : list Z) (i : Z) :
    0 <= expmech_w num den scores i.
  Proof.
    rewrite /expmech_w. case_bool_decide; simpl; [|lra].
    case_bool_decide; simpl; [|lra]. left. apply exp_pos.
  Qed.

  Lemma expmech_w_supp (num den : Z) (scores : list Z) (i : Z) :
    (0 <= i)%Z → (i < Z.of_nat (length scores))%Z →
    0 < expmech_w num den scores i.
  Proof.
    intros H1 H2. rewrite /expmech_w.
    rewrite bool_decide_eq_true_2; [|done].
    rewrite bool_decide_eq_true_2; [|done]. simpl. apply exp_pos.
  Qed.

  Lemma ex_seriesC_expmech_w (num den : Z) (scores : list Z) :
    ex_seriesC (expmech_w num den scores).
  Proof.
    eapply ex_seriesC_ext; [intro; symmetry; apply expmech_w_eq_list|].
    apply ex_seriesC_list.
  Qed.

  Lemma expmech_Z_pos (num den : Z) (scores : list Z) :
    scores ≠ [] → 0 < expmech_Z num den scores.
  Proof.
    intros Hne. rewrite /expmech_Z.
    eapply Rlt_le_trans; last apply (SeriesC_ge_elem _ 0%Z).
    - apply expmech_w_supp; [lia|].
      destruct scores; [done|]. simpl. lia.
    - intros; apply expmech_w_pos.
    - apply ex_seriesC_expmech_w.
  Qed.

  (** ** The exponential mechanism distribution. *)

  Program Definition expmech (num den : Z) (scores : list Z) : distr Z :=
    match scores with
    | [] => dret 0%Z
    | _ => MkDistr (λ i, expmech_w num den scores i / expmech_Z num den scores)
                   _ _ _
    end.
  Next Obligation.
    intros num den scores wc Hne <- i. unfold Rdiv.
    apply Rmult_le_pos; [apply expmech_w_pos|].
    left. apply Rinv_0_lt_compat, expmech_Z_pos. by intros ->.
  Qed.
  Next Obligation.
    intros num den scores wc Hne <-. setoid_rewrite Rdiv_def.
    apply ex_seriesC_scal_r, ex_seriesC_expmech_w.
  Qed.
  Next Obligation.
    intros num den scores wc Hne <-.
    setoid_rewrite Rdiv_def. rewrite SeriesC_scal_r.
    rewrite -/(expmech_Z num den wc).
    apply Req_le, Rdiv_diag.
    pose proof (expmech_Z_pos num den wc ltac:(by intros ->)). lra.
  Qed.
  Next Obligation. intros num den scores z l. done. Qed.

  Lemma expmech_mass (num den : Z) (scores : list Z) :
    SeriesC (expmech num den scores) = 1.
  Proof.
    destruct scores as [|s l] eqn:Hs.
    - rewrite /expmech. apply dret_mass.
    - rewrite /expmech {1}/pmf. setoid_rewrite Rdiv_def.
      rewrite SeriesC_scal_r -/(expmech_Z num den (s :: l)).
      apply Rdiv_diag.
      pose proof (expmech_Z_pos num den (s :: l) ltac:(done)). lra.
  Qed.

  (** ** The two-factor ratio bound (textbook exponential mechanism). *)

  (** Per-term weight bound under per-coordinate sensitivity [Δ ≥ 1].  With
      [Δ = 1] this is exactly the sensitivity-1 bound [exp(ε')·w(s')]. *)
  Lemma expmech_w_ratio (Δ : Z) (num den : Z) (scores scores' : list Z)
    (HΔ : (1 <= Δ)%Z)
    (Hlen : length scores = length scores')
    (Hpos : (0 <= IZR num / IZR den)%R)
    (Hadj : ∀ k, (Z.abs (scores !!! k - scores' !!! k) <= Δ)%Z) (i : Z) :
    expmech_w num den scores i
      <= exp (IZR Δ * (IZR num / IZR den)) * expmech_w num den scores' i.
  Proof.
    rewrite /expmech_w Hlen.
    case_bool_decide as Hi1; simpl; last first.
    { rewrite Rmult_0_r. lra. }
    case_bool_decide as Hi2; simpl; last first.
    { rewrite Rmult_0_r. lra. }
    rewrite -exp_plus. apply exp_mono.
    set (k := Z.to_nat i).
    pose proof (Hadj k) as Hk. rewrite Z.abs_le in Hk.
    apply Rle_trans with (IZR num / IZR den * IZR (scores' !!! k + Δ)).
    - apply Rmult_le_compat_l; [exact Hpos|]. apply IZR_le. lia.
    - rewrite plus_IZR. lra.
  Qed.

  (** Normaliser ratio bound: [Z(s') ≤ exp(Δ·ε')·Z(s)]. *)
  Lemma expmech_Z_ratio (Δ : Z) (num den : Z) (scores scores' : list Z)
    (HΔ : (1 <= Δ)%Z)
    (Hlen : length scores = length scores')
    (Hpos : (0 <= IZR num / IZR den)%R)
    (Hadj : ∀ k, (Z.abs (scores !!! k - scores' !!! k) <= Δ)%Z) :
    expmech_Z num den scores'
      <= exp (IZR Δ * (IZR num / IZR den)) * expmech_Z num den scores.
  Proof.
    rewrite /expmech_Z -SeriesC_scal_l.
    apply SeriesC_le; last first.
    { apply ex_seriesC_scal_l, ex_seriesC_expmech_w. }
    intros i. split; [apply expmech_w_pos|].
    (* termwise: w(s') i <= exp(Δ·ε') * w(s) i, by symmetry of adjacency *)
    apply (expmech_w_ratio Δ num den scores' scores HΔ).
    - lia.
    - exact Hpos.
    - intros k. rewrite Z.abs_le. pose proof (Hadj k) as Hk.
      rewrite Z.abs_le in Hk. lia.
  Qed.

  (** pmf of [expmech] on a nonempty score vector. *)
  Lemma expmech_unfold (num den : Z) (s : Z) (l : list Z) (i : Z) :
    expmech num den (s :: l) i
      = expmech_w num den (s :: l) i / expmech_Z num den (s :: l).
  Proof. reflexivity. Qed.

  (** The pointwise pmf ratio bound: [expmech s i ≤ exp(2·Δ·ε')·expmech s' i].
      With [Δ = 1] this recovers the sensitivity-1 bound [exp(2ε')·expmech s' i]. *)
  Lemma expmech_pmf_ratio (Δ : Z) (num den : Z) (scores scores' : list Z)
    (HΔ : (1 <= Δ)%Z)
    (Hlen : length scores = length scores')
    (Hpos : (0 <= IZR num / IZR den)%R)
    (Hadj : ∀ k, (Z.abs (scores !!! k - scores' !!! k) <= Δ)%Z) (i : Z) :
    expmech num den scores i
      <= exp (2 * IZR Δ * (IZR num / IZR den)) * expmech num den scores' i.
  Proof.
    assert (HΔpos : (0 <= IZR Δ)%R) by (apply IZR_le; lia).
    destruct scores as [|s l] eqn:Hs.
    { (* both empty: both are [dret 0]; cost [2·Δ·ε' ≥ 0] *)
      destruct scores' as [|s' l']; [|simpl in Hlen; lia].
      rewrite /expmech.
      transitivity (1 * dret 0%Z i); [rewrite Rmult_1_l; lra|].
      apply Rmult_le_compat_r; [apply pmf_pos|].
      rewrite -exp_0. apply exp_mono. pose proof (exp_pos 0). nra. }
    destruct scores' as [|s' l'] eqn:Hs'; [simpl in Hlen; lia|].
    rewrite !expmech_unfold.
    set (Zs := expmech_Z num den (s :: l)).
    set (Zs' := expmech_Z num den (s' :: l')).
    assert (HZs : 0 < Zs) by (apply expmech_Z_pos; done).
    assert (HZs' : 0 < Zs') by (apply expmech_Z_pos; done).
    set (eps := IZR Δ * (IZR num / IZR den)).
    pose proof (expmech_w_ratio Δ num den (s::l) (s'::l') HΔ Hlen Hpos Hadj i) as Hw.
    fold eps in Hw.
    pose proof (expmech_Z_ratio Δ num den (s::l) (s'::l') HΔ Hlen Hpos Hadj) as HZr.
    fold eps Zs Zs' in HZr.
    pose proof (expmech_w_pos num den (s'::l') i) as Hwp'.
    pose proof (exp_pos eps) as Hep.
    assert (Hexp2 : exp (2 * IZR Δ * (IZR num / IZR den)) = exp eps * exp eps).
    { rewrite -exp_plus. f_equal. subst eps. lra. }
    rewrite Hexp2.
    (* factor 1: bound [w(s)i ≤ exp(Δ·ε')·w(s')i] *)
    apply Rle_trans with (exp eps * expmech_w num den (s' :: l') i / Zs).
    { apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact HZs|].
      exact Hw. }
    rewrite (Rmult_assoc (exp eps) (exp eps)).
    rewrite Rdiv_def Rmult_assoc.
    apply Rmult_le_compat_l; [left; exact Hep|].
    rewrite Rdiv_def.
    rewrite (Rmult_comm (exp eps)) Rmult_assoc.
    apply Rmult_le_compat_l; [exact Hwp'|].
    (* factor 2: [/ Zs ≤ exp(Δ·ε')·/ Zs'], i.e. [Zs' ≤ exp(Δ·ε')·Zs] *)
    apply (Rmult_le_reg_r Zs); [exact HZs|].
    rewrite Rinv_l; [|lra].
    apply (Rmult_le_reg_r Zs'); [exact HZs'|].
    rewrite Rmult_1_l.
    rewrite Rmult_assoc (Rmult_comm (/ Zs')) -Rmult_assoc.
    replace (exp eps * / Zs' * Zs * Zs') with (exp eps * Zs).
    { exact HZr. }
    field. lra.
  Qed.

  (** ** The (Δ·ε)-DP coupling of the exponential mechanism (cost [2·Δ·ε']).
      With [Δ = 1] this recovers the sensitivity-1 cost [2·ε']. *)

  Lemma DPcoupl_expmech (Δ : Z) (num den : Z) (scores scores' : list Z)
    (HΔ : (1 <= Δ)%Z)
    (Hlen : length scores = length scores')
    (Hpos : (0 <= IZR num / IZR den)%R)
    (Hadj : ∀ k, (Z.abs (scores !!! k - scores' !!! k) <= Δ)%Z) :
    DPcoupl (expmech num den scores) (expmech num den scores')
            eq (2 * IZR Δ * (IZR num / IZR den)) 0.
  Proof.
    apply DPcoupl_complete_eq. intros P.
    rewrite /prob Rplus_0_r -SeriesC_scal_l.
    apply SeriesC_le; last first.
    { apply ex_seriesC_scal_l.
      eapply ex_seriesC_le;
        last apply (pmf_ex_seriesC (expmech num den scores')).
      intros a. case_bool_decide; split; try apply pmf_pos; try real_solver. }
    intros a. split.
    - case_bool_decide; [apply pmf_pos|lra].
    - case_bool_decide.
      + apply (expmech_pmf_ratio Δ); assumption.
      + rewrite Rmult_0_r. lra.
  Qed.

End exponential_mechanism.
