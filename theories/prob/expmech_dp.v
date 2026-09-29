(** Headline differential-privacy statement for the discrete exponential
    mechanism [expmech] (defined in [prob.expmech]): "the exponential
    mechanism is ε-DP".

    This wraps the per-output ε-DP coupling [DPcoupl_expmech] into a
    [diffpriv_approx] statement (the standard, end-user-facing DP predicate
    from [prob.differential_privacy]) via [DPcoupl_diffpriv].  The adjacency
    [d_scores] is a plain [R]-valued metric on score vectors — no
    [Distance]-record axioms are needed: neighbouring score vectors (same
    length, per-coordinate difference [≤ 1]) are at distance [0], everything
    else at distance [2 > 1].  Cost is [2·(num/den)] with no additive slack
    ([δ = 0]). *)
From Stdlib Require Import Reals Psatz.
From clutch.prelude Require Import base.
From clutch.prob Require Export distribution.
From clutch.prob Require Import couplings_dp differential_privacy.
From clutch.prob Require Import expmech.

Local Open Scope R.

Section expmech_dp.

  (** Adjacency on score vectors: distance [0] for "1-sensitive neighbours"
      (same length and per-coordinate difference [≤ 1]), distance [2]
      otherwise.  A plain [R]-valued adjacency — no [Distance] record needed.

      The per-coordinate condition is stated over the bounded index range
      [seq 0 (length scores)] (via [Forall]) to keep [d_scores] *decidable*
      (the unbounded [∀ k] over all of [nat] is not, a priori).  It matches
      the unbounded [∀ k] used by [DPcoupl_expmech] because [scores !!! k] for
      out-of-range [k] is the [inhabitant] default [0] on both lists (see
      [adj_bounded_to_unbounded]). *)
  Definition d_scores (Δ : Z) (scores scores' : list Z) : R :=
    if bool_decide
         (length scores = length scores'
          ∧ Forall (λ k, (Z.abs (scores !!! k - scores' !!! k) <= Δ)%Z)
                   (seq 0 (length scores)))
    then 0%R else 2%R.

  (** Off-range indices read [0] on both lists (total-lookup default), so the
      bounded per-coordinate bound entails the unbounded one demanded by the
      coupling lemma [DPcoupl_expmech]. *)
  Lemma adj_bounded_to_unbounded (Δ : Z) (HΔ : (1 <= Δ)%Z) (scores scores' : list Z)
    (Hlen : length scores = length scores')
    (HF : Forall (λ k, (Z.abs (scores !!! k - scores' !!! k) <= Δ)%Z)
                 (seq 0 (length scores))) :
    ∀ k, (Z.abs (scores !!! k - scores' !!! k) <= Δ)%Z.
  Proof.
    intros k. destruct (decide (k < length scores)%nat) as [Hk|Hk].
    - rewrite Forall_forall in HF. apply HF, elem_of_seq. lia.
    - rewrite (list_lookup_total_alt scores k).
      rewrite (list_lookup_total_alt scores' k).
      rewrite (lookup_ge_None_2 scores k); [|lia].
      rewrite (lookup_ge_None_2 scores' k); [|lia]. simpl. lia.
  Qed.

  (** The exponential mechanism [λ scores, expmech num den scores] is
      [(2·Δ·(num/den))]-DP (with [δ = 0]) for the score-vector adjacency
      [d_scores Δ] (query sensitivity [Δ ≥ 1]), whenever the rate is
      non-negative.  With [Δ = 1] this recovers the sensitivity-1 statement
      [(2·(num/den))]-DP for [d_scores 1].  Proved by lifting the per-output
      coupling [DPcoupl_expmech] through [DPcoupl_diffpriv]: from
      [d_scores Δ s s' ≤ 1] (so the [bool_decide] is true, since otherwise the
      distance would be [2 > 1]) we recover the length and per-coordinate
      conditions that [DPcoupl_expmech] needs. *)
  Lemma expmech_diffpriv (Δ : Z) (num den : Z)
    (HΔ : (1 <= Δ)%Z)
    (Hpos : (0 <= IZR num / IZR den)%R) :
    diffpriv_approx (d_scores Δ) (expmech num den)
      (2 * IZR Δ * (IZR num / IZR den)) 0.
  Proof.
    apply DPcoupl_diffpriv. intros s s' Hd.
    assert (Hb : length s = length s'
                 ∧ Forall (λ k, (Z.abs (s !!! k - s' !!! k) <= Δ)%Z)
                          (seq 0 (length s))).
    { revert Hd. rewrite /d_scores. case_bool_decide as Hb; [|lra].
      intros _. exact Hb. }
    destruct Hb as [Hlen HF].
    apply (DPcoupl_expmech Δ).
    - exact HΔ.
    - exact Hlen.
    - exact Hpos.
    - by apply (adj_bounded_to_unbounded Δ HΔ).
  Qed.

End expmech_dp.
