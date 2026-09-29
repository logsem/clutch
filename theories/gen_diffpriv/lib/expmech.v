(** Reusable discrete-EXPONENTIAL-MECHANISM library for the generic DP logic —
    the [expmech] analogue of [lib.laplace] / [lib.exponential].

    Importing this file and providing a [SampleIn expmech_family S] instance
    makes the [ExpMech] surface notation and the [wp_couple_expmech] mechanism
    rule available at WHATEVER index the family occupies in [S] (recovered from
    [SampleIn] via [sample_idx], never hardcoded).  As with [lib.laplace], a
    client needs only:
      Definition Sem : Sig := [...; expmech_family; ...].
      #[global] Instance : SampleIn expmech_family Sem := ltac:(solve_SampleIn).
      Section foo. Context `{!diffprivGS Sem Σ}.
    and then writes [ExpMech num den scores] in programs and applies
    [wp_couple_expmech].

    Unlike the noise mechanisms (Laplace / one-sided exponential), the
    exponential mechanism does NOT couple two outputs by a SHIFT: its
    underlying coupling [DPcoupl_expmech] is along plain equality ([eq]) with a
    fixed multiplicative cost [2·(num/den)] (and zero additive slack), valid
    for any two score vectors of equal length whose coordinates differ by at
    most [1].  This is exactly the textbook exponential-mechanism guarantee,
    here repackaged as a WP coupling rule by lifting [DPcoupl_expmech] through
    the family's [sf_inj] with [DPcoupl_map] / [DPcoupl_mono] and plugging it
    into the generic prog-couple seam [wp_couple_sample_gen]. *)
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import differential_privacy distribution exponential expmech couplings couplings_app couplings_dp.
(* re-export the client-facing layer so [Require Import expmech] alone provides
   the WP rules, coupling seams, proof-mode tactics, notation and families *)
From clutch.gen_diffpriv Require Export primitive_laws coupling_rules proofmode.
From clutch.gen_prob_lang Require Export families inject.
From iris.prelude Require Import options.

Local Open Scope R.

(** [ExpMech num den scores tape] samples the exponential-mechanism family at
    parameter [(num, den, scores)] using sample tape [tape] ([#()] for a
    direct, tape-less sample).  Same 4-argument surface form as [Laplace] /
    [Exp], but the third argument is a *list of scores* (a value carrying the
    [Inject_list] encoding) rather than a single location; the family's index
    in the ambient signature is recovered from [SampleIn expmech_family _]. *)
Notation ExpMech num den scores tape :=
  (Sample (sample_idx (D := expmech_family)) (Pair num (Pair den scores)) tape)
  (only parsing).

Section expmech.
  Context {S : Sig} `{!SampleIn expmech_family S} `{!diffprivGS S Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang S)).
  (* the family's index in [S], recovered from the [SampleIn] instance *)
  Local Notation lidx := (@sample_idx expmech_family S _).

  (** The core exponential-mechanism draw coupling, on the family's outcome
      type [Z] (the chosen index): sampling at scores [scores] (impl) vs
      [scores'] (spec) is coupled along plain equality at multiplicative cost
      [2·(num/den)] whenever the score vectors have equal length and
      per-coordinate sensitivity [1].  Family-level fact (independent of [S]),
      discharged by the reusable [DPcoupl_expmech]. *)
  Lemma DPcoupl_expmech_draw (Δ : Z) (num den : Z) (scores scores' : list Z)
    (HΔ : (1 <= Δ)%Z)
    (Hlen : length scores = length scores')
    (Hpos : (0 <= IZR num / IZR den)%R)
    (Hadj : ∀ k, (Z.abs (scores !!! k - scores' !!! k) <= Δ)%Z) :
    DPcoupl (sf_sample expmech_family (num, den, scores))
            (sf_sample expmech_family (num, den, scores'))
            eq (2 * IZR Δ * (IZR num / IZR den)) 0.
  Proof. simpl. by apply (DPcoupl_expmech Δ). Qed.

  (** The exponential mechanism is ε-DP at the WP level (for [ε = 2·(num/den)],
      [δ = 0]): sampling at scores [scores] (impl) vs [scores'] (spec) couples
      to EQUAL chosen indices, at multiplicative error [2·(num/den)], under
      equal length and per-coordinate sensitivity [1].  Obtained by
      instantiating the GENERIC prog-couple seam [wp_couple_sample_gen] with
      [DPcoupl_expmech_draw] at index [sample_idx] (so this one rule serves
      every signature containing [expmech_family]).

      The parameters are written with explicit [pair] (rather than [(.,.)])
      to keep the tuple in Coq's term scope: inside the [Sample]/[Val]
      notation the surface [(a, b)] would parse as a program-level [Pair]. *)
  Lemma wp_couple_expmech (Δ : Z) (num den : Z) (scores scores' : list Z)
    (HΔ : (1 <= Δ)%Z)
    (Hlen : length scores = length scores')
    (Hpos : (0 <= IZR num / IZR den)%R)
    (Hadj : ∀ k, (Z.abs (scores !!! k - scores' !!! k) <= Δ)%Z)
    (ε' : R) K E :
    ε' = (2 * IZR Δ * (IZR num / IZR den)) →
    {{{ ⤇ fill K (Sample lidx
                    (Val (sf_param_to_val expmech_family (pair (pair num den) scores')))
                    (Val (LitV LitUnit))) ∗ ↯m ε' }}}
      Sample lidx
        (Val (sf_param_to_val expmech_family (pair (pair num den) scores)))
        (Val (LitV LitUnit)) @ E
      {{{ (i : Z), RET #i; ⤇ fill K #i }}}.
  Proof.
    iIntros (Hε' Φ) "(Hr & Hε) HΦ".
    assert (HΔpos : (0 <= IZR Δ)%R) by (apply IZR_le; lia).
    iApply (wp_couple_sample_gen S lidx
              (sf_param_to_val expmech_family (num, den, scores))
              (sf_param_to_val expmech_family (num, den, scores'))
              (dmap (sf_inj expmech_family) (sf_sample expmech_family (num, den, scores)))
              (dmap (sf_inj expmech_family) (sf_sample expmech_family (num, den, scores')))
              (λ v v', ∃ i : Z, v = #i ∧ v' = #i) K E ε'
              (sig_sample_at expmech_family S (num, den, scores))
              (sig_sample_at expmech_family S (num, den, scores')) _ with "[$Hr $Hε]").
    { iIntros "!>" (v v') "(Hspec & %HR)". destruct HR as (i & -> & ->).
      iApply ("HΦ" $! i with "Hspec"). }
    (* the single DP obligation: lift the exponential-mechanism draw coupling
       (along [eq]) through [sf_inj]; cost [2·Δ·(num/den)] *)
    Unshelve.
    apply DPcoupl_map;
      [subst ε'; apply Rmult_le_pos; [nra | exact Hpos] | lra | ].
    eapply (DPcoupl_mono _ _ _ _ eq _ ε' ε' 0 0);
      [ intros; reflexivity
      | intros; reflexivity
      | intros a a' ->; by exists a'
      | lra | lra
      | subst ε'; by apply (DPcoupl_expmech_draw Δ) ].
  Qed.

  (** The surface-form exponential-mechanism coupling rule, stated on the
      [ExpMech] notation (with the [(num,den,scores)] parameter as an
      un-reduced [Pair] and the scores list as an injected value [$scores]).
      The proof reduces the [Pair] params on both sides ([wp_pures]/[tp_pures])
      and then applies the reduced-form [wp_couple_expmech]. *)
  Lemma hoare_couple_expmech (Δ : Z) (num den : Z) (scores scores' : list Z)
    (HΔ : (1 <= Δ)%Z)
    (Hlen : length scores = length scores')
    (Hpos : (0 <= IZR num / IZR den)%R)
    (Hadj : ∀ k, (Z.abs (scores !!! k - scores' !!! k) <= Δ)%Z)
    (ε' : R) K E :
    ε' = (2 * IZR Δ * (IZR num / IZR den)) →
    {{{ ⤇ fill K (ExpMech #num #den (Val (inject scores')) #()) ∗ ↯m ε' }}}
      ExpMech #num #den (Val (inject scores)) #() @ E
      {{{ (i : Z), RET #i; ⤇ fill K #i }}}.
  Proof.
    iIntros (Hε' Φ) "(Hr & Hε) HΦ".
    wp_pures. tp_pures.
    iApply (wp_couple_expmech Δ num den scores scores' HΔ Hlen Hpos Hadj ε' K E Hε'
              with "[$Hr $Hε]").
    iApply "HΦ".
  Qed.

  (** The exact (error-free) coupling: identical score vectors couple perfectly
      along the diagonal at zero cost (the reflexive coupling [ARcoupl_eq]
      lifted to [DPcoupl]).  No sensitivity hypothesis needed here. *)
  Lemma hoare_couple_expmech_exact (num den : Z) (scores : list Z) K E :
    {{{ ⤇ fill K (ExpMech #num #den (Val (inject scores)) #()) }}}
      ExpMech #num #den (Val (inject scores)) #() @ E
      {{{ (i : Z), RET #i; ⤇ fill K #i }}}.
  Proof.
    iIntros (Φ) "Hr HΦ".
    wp_pures. tp_pures.
    iMod ecm_zero as "Hε".
    iApply (wp_couple_sample_gen S lidx
              (sf_param_to_val expmech_family (num, den, scores))
              (sf_param_to_val expmech_family (num, den, scores))
              (dmap (sf_inj expmech_family) (sf_sample expmech_family (num, den, scores)))
              (dmap (sf_inj expmech_family) (sf_sample expmech_family (num, den, scores)))
              (λ v v', ∃ i : Z, v = #i ∧ v' = #i) K E 0
              (sig_sample_at expmech_family S (num, den, scores))
              (sig_sample_at expmech_family S (num, den, scores)) _ with "[$Hr $Hε]").
    { iIntros "!>" (v v') "(Hspec & %HR)". destruct HR as (i & -> & ->).
      iApply ("HΦ" $! i with "Hspec"). }
    (* the reflexive coupling of the exponential-mechanism draw, lifted through sf_inj *)
    Unshelve.
    apply (DPcoupl_map (sf_inj expmech_family) (sf_inj expmech_family)
             (sf_sample expmech_family (num, den, scores))
             (sf_sample expmech_family (num, den, scores))
             (λ v v', ∃ i : Z, v = #i ∧ v' = #i) 0 0); [lra | lra | ].
    eapply (DPcoupl_mono (sf_sample expmech_family (num, den, scores))
              (sf_sample expmech_family (num, den, scores))
              (sf_sample expmech_family (num, den, scores))
              (sf_sample expmech_family (num, den, scores))
              (=) (λ a a', ∃ i : Z, sf_inj expmech_family a = #i ∧ sf_inj expmech_family a' = #i)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra
      | apply ARcoupl_to_DPcoupl, ARcoupl_eq ].
  Qed.

End expmech.

(** [couple_expmech Δ with "[…]"] — the ergonomic coupling step for the discrete
    exponential mechanism.  It reduces the [Pair] params to a [PairV]
    ([wp_pures]/[tp_pures]), focuses the [Sample] on both sides
    ([wp_bind]/[tp_bind]), and applies the value-form [wp_couple_expmech]
    inferring [num/den/scores/scores'/ε'/K/E] from the goal — the author supplies
    only the per-coordinate sensitivity bound [Δ] and the resource pattern.

    Unlike the noise mechanisms ([couple_laplace]/[couple_exp]), the exponential
    mechanism couples the two chosen indices along plain EQUALITY (no shift
    argument), at the fixed multiplicative cost [2·Δ·(num/den)] and zero additive
    slack — so the precondition is the SAME two-resource [⤇ ∗ ↯m] shape and the
    pattern is the 2-way [\"[$Hr $Hε]\"].  The remaining side-conditions are
    DATA-dependent rather than arithmetic: alongside the trivial [HΔ : 1 ≤ Δ],
    [Hpos], [Hε'] (closed by [lia]/[assumption]/[reflexivity]), the score-vector
    obligations [Hlen : length scores = length scores'] and
    [Hadj : ∀ k, |scores!!!k − scores'!!!k| ≤ Δ] must come from in-context
    hypotheses ([assumption]) — they cannot be synthesised by the tactic and are
    left as goals when no matching hypothesis is in scope. *)
Tactic Notation "couple_expmech" uconstr(Δ) "with" constr(pat) :=
  wp_pures; tp_pures;
  wp_bind (Sample _ _ _); tp_bind (Sample _ _ _);
  (* [unshelve] turns the goals THIS [iApply] shelves — [HΔ]/[Hlen]/[Hpos]/[Hadj]
     and the equational [Hε'] — into regular front goals, without globally
     un-shelving unrelated goals. *)
  unshelve (iApply (wp_couple_expmech Δ _ _ _ _ _ _ _ _ _ _ _ with pat));
  (* best-effort discharge: arithmetic [HΔ]/[Hpos]/[Hε'] by [lia]/[reflexivity],
     and the data-dependent [Hlen]/[Hadj] by [assumption] when in scope.  The
     postcondition continuation is the goal left. *)
  try first
    [ reflexivity
    | assumption
    | lia
    | (simpl; lra) ].

Section expmech_canary.
  Context {Sg : Sig} `{!SampleIn expmech_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** CANARY: two surface-form [ExpMech #num #den $scores #()] draws over adjacent
      score vectors couple to EQUAL chosen indices, at multiplicative cost
      [2·Δ·(num/den)] — driven entirely by the [couple_expmech] tactic.  Stated
      over the [ExpMech] notation (i.e. [expr], with an un-reduced [Pair] param and
      the scores list injected as a value) so it exercises the surface path a
      program takes; demonstrates the (equality-coupling, no-shift) convenience
      layer end to end.  The data-dependent side-conditions [Hlen]/[Hadj] are
      passed as hypotheses and closed by the tactic via [assumption]. *)
  Lemma wp_expmech_canary (Δ num den : Z) (scores scores' : list Z)
    (HΔ : (1 <= Δ)%Z)
    (Hlen : length scores = length scores')
    (Hpos : (0 <= IZR num / IZR den)%R)
    (Hadj : ∀ k, (Z.abs (scores !!! k - scores' !!! k) <= Δ)%Z) K E :
    {{{ ⤇ fill K (ExpMech #num #den (Val (inject scores')) #())
        ∗ ↯m (2 * IZR Δ * (IZR num / IZR den)) }}}
      ExpMech #num #den (Val (inject scores)) #() @ E
      {{{ (i : Z), RET #i; ⤇ fill K #i }}}.
  Proof.
    (* destructure the bundled precondition first, so the spec [⤇] is a standalone
       hypothesis for the [tp_pures]/[tp_bind] inside the tactic. *)
    iIntros (Φ) "(Hr & Hε) HΦ".
    couple_expmech Δ with "[$Hr $Hε]".
    iApply "HΦ".
  Qed.

End expmech_canary.
