(** Reusable randomised-response (RR) sampling library for the generic DP logic.

    Importing this file and providing a [SampleIn RR_coin Sg] instance makes the
    [RR] surface notation and the [wp_couple_RR] mechanism rules available at
    WHATEVER index the family occupies in the signature [Sg] — the index is
    recovered from the [SampleIn] instance via [sample_idx], never hardcoded
    (mirroring [lib/coin.v], [lib/uniform.v] and [lib/laplace.v]).

    [RR_coin] (see [gen_prob_lang.families]) is the (num, den)-parameterised
    noisy-bit SOURCE: at parameter [(num, den)] it samples [biased_coin r] with
    [r = exp(ε) / (exp(ε) + 1)], [ε = num / den].  The randomised-response
    MECHANISM releases a private bit [x] as [x XOR c] for such a coin [c]; this
    is [ε]-DP (a purely MULTIPLICATIVE guarantee, [δ = 0]) on the discrete bit
    metric — verified as the validating example in
    [examples.randomized_response].

    Two draw couplings are exposed:
      - the EXACT (identity) coupling, cost [(0,0)] — the same RR coin coupled
        with itself along EQUALITY (for adjacent inputs at distance 0);
      - the FLIP coupling, cost [(ε, 0)] — the same RR coin coupled with itself
        along NEGATION (for adjacent inputs at distance 1, where the spec coin
        must flip so the two XOR-released bits agree).  This is where the RR
        privacy parameter [ε = num/den] is spent.

    A client development therefore needs only:
      Definition Srr : Sig := [...; RR_coin; ...].
      #[global] Instance : SampleIn RR_coin Srr := ltac:(solve_SampleIn).
      Section foo. Context `{!diffprivGS Srr Σ}.
    and then writes [RR #num #den #()] in programs and applies [wp_couple_RR] /
    [wp_couple_RR_exact] in proofs. *)
From Stdlib Require Import ZArith Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import differential_privacy distribution couplings couplings_app couplings_dp.
(* re-export the client-facing layer so [Require Import randomized_response] alone
   provides the WP rules, coupling seams, proof-mode tactics, notation and
   families. *)
From clutch.gen_diffpriv Require Export primitive_laws coupling_rules proofmode diffpriv_rules.
From clutch.gen_prob_lang Require Export families.
From iris.prelude Require Import options.

Local Open Scope R.

(** [RR num den tape] samples the randomised-response coin family at parameter
    [(num, den)] (two [Z] literals, with bias [exp(ε)/(exp(ε)+1)], [ε = num/den])
    using sample tape [tape] ([#()] for a direct, tape-less sample).  The
    family's index in the ambient signature is recovered from the
    [SampleIn RR_coin _] instance — NOT hardcoded. *)
Notation RR num den tape :=
  (Sample (sample_idx (D := RR_coin)) (Pair num den) tape)
  (only parsing).

(** Value-form of [RR] (direct, tape-less): the [(num,den)] parameters already
    reduced to a [PairV] of [LitV (LitInt _)], as they appear AFTER
    [wp_pures]/[tp_pures].  The coupling rules below are stated on [RRV] so their
    preconditions match post-reduction goals; the [couple_RR] tactic relies on
    this shape. *)
Notation RRV num den :=
  (Sample (sample_idx (D := RR_coin))
     (Val (PairV (LitV (LitInt num)) (LitV (LitInt den))))
     (Val (LitV LitUnit)))
  (only parsing).

Section randomized_response.
  Context {Sg : Sig} `{!SampleIn RR_coin Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  (* the family's index in [Sg], recovered from the [SampleIn] instance *)
  Local Notation ridx := (@sample_idx RR_coin Sg _).

  (** The core RR draw EXACT coupling, on the family's outcome type [bool]:
      drawing the SAME RR coin on both sides couples the two booleans along
      equality, at ZERO cost (the two sides sample the literally identical
      [biased_coin]).  Family-level fact (independent of [Sg]). *)
  Lemma DPcoupl_RR_draw_exact (num den : Z) :
    DPcoupl (sf_sample RR_coin (num, den))
            (sf_sample RR_coin (num, den))
            (λ b b', b = b') 0 0.
  Proof. simpl. apply DPcoupl_biased_coin. Qed.

  (** The core RR draw FLIP coupling: drawing the SAME RR coin on both sides,
      coupled along NEGATION ([c' = negb c]), at multiplicative cost
      [ε = num/den] (no [δ]).  This is where the RR privacy parameter is spent —
      flipping the spec coin so that the two XOR-released bits of adjacent inputs
      agree.  Requires [0 ≤ ε], discharged from [DPcoupl_biased_coin_flip] with
      the family's own bias [exp(ε)/(exp(ε)+1)] and validity proof
      [rr_bias_valid]. *)
  Lemma DPcoupl_RR_draw_flip (num den : Z) (Hε : 0 <= IZR num / IZR den) :
    DPcoupl (sf_sample RR_coin (num, den))
            (sf_sample RR_coin (num, den))
            (λ c c', c' = negb c) (IZR num / IZR den) 0.
  Proof.
    simpl.
    set (E := exp (IZR num / IZR den)).
    pose proof (exp_pos (IZR num / IZR den)) as HEpos. fold E in HEpos.
    assert (HE1 : 1 <= E) by (apply exp_pos_ge_1; exact Hε).
    assert (Hden : 0 < E + 1) by lra.
    assert (Hcompl : 1 - E / (E + 1) = / (E + 1)) by (field; lra).
    apply DPcoupl_biased_coin_flip; fold E; rewrite Hcompl.
    - (* r ≤ exp ε · (1 − r): E/(E+1) ≤ E·/(E+1); definitional equality. *)
      unfold Rdiv. right. reflexivity.
    - (* 1 − r ≤ exp ε · r: /(E+1) ≤ E·(E/(E+1)), i.e. 1 ≤ E². *)
      unfold Rdiv. rewrite -Rmult_assoc. rewrite -{1}(Rmult_1_l (/ (E + 1))).
      apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra|].
      rewrite -{1}(Rmult_1_l 1). apply Rmult_le_compat; lra.
  Qed.

  (** The EXACT RR coupling at the WP level: sampling at parameter [(num,den)]
      (impl) vs the same [(num,den)] (spec) couples to EQUAL booleans, at ZERO
      cost.  Obtained by instantiating the generic prog-couple seam
      [wp_couple_sample_gen] with [DPcoupl_RR_draw_exact] at the recovered index
      [ridx]. *)
  Lemma wp_couple_RR_exact (num den : Z) K E :
    {{{ ⤇ fill K (Sample ridx
                    (Val (PairV (LitV (LitInt num)) (LitV (LitInt den))))
                    (Val (LitV LitUnit))) }}}
      Sample ridx
        (Val (PairV (LitV (LitInt num)) (LitV (LitInt den))))
        (Val (LitV LitUnit)) @ E
      {{{ (b : bool), RET #b; ⤇ fill K #b }}}.
  Proof.
    iIntros (Φ) "Hr HΦ".
    iMod ecm_zero as "Hε".
    iApply (wp_couple_sample_gen Sg ridx
              (sf_param_to_val RR_coin (num, den))
              (sf_param_to_val RR_coin (num, den))
              (dmap (sf_inj RR_coin) (sf_sample RR_coin (num, den)))
              (dmap (sf_inj RR_coin) (sf_sample RR_coin (num, den)))
              (λ v v', ∃ b : bool, v = #b ∧ v' = #b) K E 0
              (sig_sample_at RR_coin Sg (num, den))
              (sig_sample_at RR_coin Sg (num, den)) _ with "[$Hr Hε]").
    { simpl. iFrame. }
    { iIntros "!>" (v v') "(Hspec & %HR)".
      destruct HR as (b & -> & ->). iApply ("HΦ" $! b with "Hspec"). }
    Unshelve.
    apply (DPcoupl_map (sf_inj RR_coin) (sf_inj RR_coin)
             (sf_sample RR_coin (num, den)) (sf_sample RR_coin (num, den))
             (λ v v', ∃ b : bool, v = #b ∧ v' = #b) 0 0); [lra | lra | ].
    eapply (DPcoupl_mono (sf_sample RR_coin (num, den))
              (sf_sample RR_coin (num, den))
              (sf_sample RR_coin (num, den))
              (sf_sample RR_coin (num, den))
              (λ b b', b = b')
              (λ a a', ∃ b : bool, sf_inj RR_coin a = #b ∧ sf_inj RR_coin a' = #b)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra
      | apply DPcoupl_RR_draw_exact ].
  Qed.

  (** The FLIP RR coupling at the WP level: sampling at parameter [(num,den)]
      (impl) vs the same [(num,den)] (spec) couples the impl outcome [b] with the
      spec outcome [negb b], at multiplicative cost [ε = num/den] (no [δ]).  This
      is the privacy-spending coupling used by the RR mechanism for adjacent
      (distance-1) inputs. *)
  Lemma wp_couple_RR (num den : Z) (ε : R) K E :
    IZR num / IZR den = ε →
    0 <= IZR num / IZR den →
    {{{ ⤇ fill K (Sample ridx
                    (Val (PairV (LitV (LitInt num)) (LitV (LitInt den))))
                    (Val (LitV LitUnit))) ∗ ↯m ε }}}
      Sample ridx
        (Val (PairV (LitV (LitInt num)) (LitV (LitInt den))))
        (Val (LitV LitUnit)) @ E
      {{{ (b : bool), RET #b; ⤇ fill K #(negb b) }}}.
  Proof.
    iIntros (Hε εpos Φ) "(Hr & Hε) HΦ".
    iApply (wp_couple_sample_gen Sg ridx
              (sf_param_to_val RR_coin (num, den))
              (sf_param_to_val RR_coin (num, den))
              (dmap (sf_inj RR_coin) (sf_sample RR_coin (num, den)))
              (dmap (sf_inj RR_coin) (sf_sample RR_coin (num, den)))
              (λ v v', ∃ b : bool, v = #b ∧ v' = #(negb b)) K E ε
              (sig_sample_at RR_coin Sg (num, den))
              (sig_sample_at RR_coin Sg (num, den)) _ with "[$Hr $Hε]").
    { iIntros "!>" (v v') "(Hspec & %HR)".
      destruct HR as (b & -> & ->). iApply ("HΦ" $! b with "Hspec"). }
    (* the single DP obligation: lift the RR flip draw coupling through sf_inj *)
    Unshelve.
    apply (DPcoupl_map (sf_inj RR_coin) (sf_inj RR_coin)
             (sf_sample RR_coin (num, den)) (sf_sample RR_coin (num, den))
             (λ v v', ∃ b : bool, v = #b ∧ v' = #(negb b)) ε 0);
      [subst ε; exact εpos | lra | ].
    eapply (DPcoupl_mono (sf_sample RR_coin (num, den))
              (sf_sample RR_coin (num, den))
              (sf_sample RR_coin (num, den))
              (sf_sample RR_coin (num, den))
              (λ c c', c' = negb c)
              (λ a a', ∃ b : bool, sf_inj RR_coin a = #b ∧ sf_inj RR_coin a' = #(negb b))
              ε ε 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a | lra | lra
      | subst ε; by apply DPcoupl_RR_draw_flip ].
  Qed.

  (** The surface-form EXACT RR coupling rule, stated on the [RR] notation (with
      the [(num,den)] parameter as an un-reduced [Pair]). *)
  Lemma hoare_couple_RR_exact (num den : Z) K E :
    {{{ ⤇ fill K (RR #num #den #()) }}}
      RR #num #den #() @ E
      {{{ (b : bool), RET #b; ⤇ fill K #b }}}.
  Proof.
    iIntros (Φ) "Hr HΦ".
    wp_pures. tp_pures.
    iApply (wp_couple_RR_exact num den K E with "Hr").
    iApply "HΦ".
  Qed.

  (** The surface-form FLIP RR coupling rule, stated on the [RR] notation. *)
  Lemma hoare_couple_RR (num den : Z) (ε : R) K E :
    IZR num / IZR den = ε →
    0 <= IZR num / IZR den →
    {{{ ⤇ fill K (RR #num #den #()) ∗ ↯m ε }}}
      RR #num #den #() @ E
      {{{ (b : bool), RET #b; ⤇ fill K #(negb b) }}}.
  Proof.
    iIntros (Hε εpos Φ) "(Hr & Hε) HΦ".
    wp_pures. tp_pures.
    iApply (wp_couple_RR num den ε K E Hε εpos with "[$Hr $Hε]").
    iApply "HΦ".
  Qed.

End randomized_response.

(** [couple_RR with "[$Hr $Hε]"] — the ergonomic FLIP coupling step.  It reduces
    the [(num,den)] params to a [PairV] of literals ([wp_pures]/[tp_pures]),
    focuses the [Sample] on both sides ([wp_bind]/[tp_bind]), and applies the
    value-form [wp_couple_RR] inferring [num/den/ε/K/E] from the goal — the
    author supplies only the resource pattern.  The side-conditions
    ([IZR num/IZR den = ε], [0 ≤ ε]) are auto-discharged best effort; the
    postcondition continuation is the single remaining goal.  Mirrors
    [couple_coin] / [couple_laplace]. *)
Tactic Notation "couple_RR" "with" constr(pat) :=
  wp_pures; tp_pures;
  wp_bind (Sample _ _ _); tp_bind (Sample _ _ _);
  unshelve (iApply (wp_couple_RR _ _ _ _ _ with pat));
  try first [ reflexivity | assumption | lra | (simpl; lra) ].

(** [couple_RR_exact with "[$Hr]"] — the ergonomic EXACT (zero-cost) coupling
    step. *)
Tactic Notation "couple_RR_exact" "with" constr(pat) :=
  wp_pures; tp_pures;
  wp_bind (Sample _ _ _); tp_bind (Sample _ _ _);
  iApply (wp_couple_RR_exact _ _ _ _ with pat).

Section RR_canary.
  Context {Sg : Sig} `{!SampleIn RR_coin Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** CANARY: two surface-form [RR #num #den #()] draws couple along negation at
      cost [ε], driven entirely by the [couple_RR] tactic. *)
  Lemma wp_RR_flip_canary (num den : Z) (ε : R) K E :
    IZR num / IZR den = ε →
    0 <= IZR num / IZR den →
    {{{ ⤇ fill K (RR #num #den #()) ∗ ↯m ε }}}
      RR #num #den #() @ E
      {{{ (b : bool), RET #b; ⤇ fill K #(negb b) }}}.
  Proof.
    iIntros (Hε εpos Φ) "(Hr & Hcr) HΦ".
    couple_RR with "[$Hr $Hcr]".
    iApply "HΦ".
  Qed.

End RR_canary.
