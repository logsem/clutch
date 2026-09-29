(** Reusable coin-sampling library for the generic DP logic.

    Importing this file and providing a [SampleIn coin_family Sg] instance makes
    the [Coin] surface notation and the [wp_couple_coin] mechanism rule
    available at WHATEVER index the family occupies in the signature [Sg] — the
    index is recovered from the [SampleIn] instance via [sample_idx], never
    hardcoded (mirroring [lib/uniform.v] and [lib/laplace.v]).

    The headline content is the 0-cost EXACT (identity) coupling: two coin draws
    with the SAME bin-weights [(w1, w2)] couple perfectly (no [ε], no [δ]) along
    EQUALITY of the sampled booleans — the two sides sample the literally
    identical [biased_coin], so the diagonal coupling is free.  This is the
    foundation on which the DIFFERENT-weight (TV-distance / error-bearing)
    variant needed for crypto rejection-sampling will build (deferred — see note
    at the end of this file).

    A client development therefore needs only:
      Definition Scoin : Sig := [...; coin_family; ...].
      #[global] Instance : SampleIn coin_family Scoin := ltac:(solve_SampleIn).
      Section foo. Context `{!diffprivGS Scoin Σ}.
    and then writes [Coin #w1 #w2 #()] in programs and applies [wp_couple_coin]
    in proofs. *)
From Stdlib Require Import ZArith.
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import differential_privacy distribution couplings couplings_app couplings_dp.
(* re-export the client-facing layer so [Require Import coin] alone provides
   the WP rules, coupling seams, proof-mode tactics, notation and families. *)
From clutch.gen_diffpriv Require Export primitive_laws coupling_rules proofmode diffpriv_rules.
From clutch.gen_prob_lang Require Export families.
From iris.prelude Require Import options.

Local Open Scope R.

(** [Coin w1 w2 tape] samples the coin family at parameter [(w1, w2)] (two [Z]
    bin-weight literals, with [P(true) = w2 / (w1 + w2)]) using sample tape
    [tape] ([#()] for a direct, tape-less sample).  The family's index in the
    ambient signature is recovered from the [SampleIn coin_family _] instance —
    NOT hardcoded. *)
Notation Coin w1 w2 tape :=
  (Sample (sample_idx (D := coin_family)) (Pair w1 w2) tape)
  (only parsing).

(** Value-form of [Coin] (direct, tape-less): the bin-weights already reduced to
    a [PairV] of [LitV (LitInt _)], as they appear AFTER [wp_pures]/[tp_pures]
    (which evaluate the [Pair] into a [PairV]).  The coupling rule below is
    stated on [CoinV] so its preconditions match post-reduction goals; the
    [couple_coin] tactic relies on this shape. *)
Notation CoinV w1 w2 :=
  (Sample (sample_idx (D := coin_family))
     (Val (PairV (LitV (LitInt w1)) (LitV (LitInt w2))))
     (Val (LitV LitUnit)))
  (only parsing).

Section coin.
  Context {Sg : Sig} `{!SampleIn coin_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  (* the family's index in [Sg], recovered from the [SampleIn] instance *)
  Local Notation cidx := (@sample_idx coin_family Sg _).

  (** The core coin draw EXACT coupling, on the family's outcome type [bool]:
      drawing the SAME bin-weighted coin on both sides couples the two booleans
      along equality, at ZERO cost (no [ε], no [δ]).  Family-level fact
      (independent of [Sg]), discharged by the reusable [DPcoupl_biased_coin]
      (the self-coupling [ARcoupl_eq] of [biased_coin] lifted to [DPcoupl]). *)
  Lemma DPcoupl_coin_draw (w1 w2 : nat) :
    DPcoupl (sf_sample coin_family (w1, w2))
            (sf_sample coin_family (w1, w2))
            (λ b b', b = b') 0 0.
  Proof. simpl. apply DPcoupl_biased_coin. Qed.

  (** The exact coin coupling at the WP level: sampling at bin-weights
      [(w1, w2)] (impl) vs the same [(w1, w2)] (spec), both pairs of [Z] literals
      [#w1 #w2] with [0 ≤ w1], [0 ≤ w2], couples to EQUAL booleans, at ZERO cost
      (no [↯m], no [↯]).  Obtained by instantiating the generic prog-couple seam
      [wp_couple_sample_gen] with [DPcoupl_coin_draw] — at the recovered index
      [cidx], so this one rule serves every signature containing
      [coin_family]. *)
  Lemma wp_couple_coin (w1 w2 : Z) K E :
    (0 <= w1)%Z →
    (0 <= w2)%Z →
    {{{ ⤇ fill K (Sample cidx
                    (Val (PairV (LitV (LitInt w1)) (LitV (LitInt w2))))
                    (Val (LitV LitUnit))) }}}
      Sample cidx
        (Val (PairV (LitV (LitInt w1)) (LitV (LitInt w2))))
        (Val (LitV LitUnit)) @ E
      {{{ (b : bool), RET #b; ⤇ fill K #b }}}.
  Proof.
    iIntros (Hw1 Hw2 Φ) "Hr HΦ".
    iMod ecm_zero as "Hε".
    (* [w1 = Z.of_nat (Z.to_nat w1)] under [0 ≤ w1] (likewise [w2]), so the value
       params [#w1 #w2] equal [sf_param_to_val coin_family (Z.to_nat w1, Z.to_nat w2)];
       rewrite the WHOLE goal to the [nat] form so the program subject matches the
       [wp_couple_sample_gen] rule. *)
    set (n1 := Z.to_nat w1). set (n2 := Z.to_nat w2).
    assert (Hn1 : w1 = Z.of_nat n1) by (subst n1; rewrite Z2Nat.id //).
    assert (Hn2 : w2 = Z.of_nat n2) by (subst n2; rewrite Z2Nat.id //).
    rewrite Hn1 Hn2.
    iApply (wp_couple_sample_gen Sg cidx
              (sf_param_to_val coin_family (n1, n2))
              (sf_param_to_val coin_family (n1, n2))
              (dmap (sf_inj coin_family) (sf_sample coin_family (n1, n2)))
              (dmap (sf_inj coin_family) (sf_sample coin_family (n1, n2)))
              (λ v v', ∃ b : bool, v = #b ∧ v' = #b) K E 0
              (sig_sample_at coin_family Sg (n1, n2))
              (sig_sample_at coin_family Sg (n1, n2)) _ with "[Hr Hε]").
    { (* the param value [#n1 #n2] matches [sf_param_to_val coin_family (n1,n2)] *)
      simpl. iFrame. }
    { iIntros "!>" (v v') "(Hspec & %HR)".
      destruct HR as (b & -> & ->). iApply ("HΦ" $! b with "Hspec"). }
    (* the single DP obligation: lift the exact coin draw coupling through sf_inj *)
    Unshelve.
    apply (DPcoupl_map (sf_inj coin_family) (sf_inj coin_family)
             (sf_sample coin_family (n1, n2)) (sf_sample coin_family (n1, n2))
             (λ v v', ∃ b : bool, v = #b ∧ v' = #b) 0 0); [lra | lra | ].
    eapply (DPcoupl_mono (sf_sample coin_family (n1, n2))
              (sf_sample coin_family (n1, n2))
              (sf_sample coin_family (n1, n2))
              (sf_sample coin_family (n1, n2))
              (λ b b', b = b')
              (λ a a', ∃ b : bool, sf_inj coin_family a = #b ∧ sf_inj coin_family a' = #b)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra
      | apply DPcoupl_coin_draw ].
  Qed.

  (** The surface-form exact coin coupling rule, stated on the [Coin] notation
      (with the [(w1, w2)] parameter as an un-reduced [Pair]).  The proof reduces
      the [Pair] params on both sides ([wp_pures]/[tp_pures]) and then applies the
      reduced-form [wp_couple_coin]. *)
  Lemma hoare_couple_coin_exact (w1 w2 : Z) K E :
    (0 <= w1)%Z →
    (0 <= w2)%Z →
    {{{ ⤇ fill K (Coin #w1 #w2 #()) }}}
      Coin #w1 #w2 #() @ E
      {{{ (b : bool), RET #b; ⤇ fill K #b }}}.
  Proof.
    iIntros (Hw1 Hw2 Φ) "Hr HΦ".
    wp_pures. tp_pures.
    iApply (wp_couple_coin w1 w2 K E Hw1 Hw2 with "Hr").
    iApply "HΦ".
  Qed.

End coin.

(** [couple_coin with "[$Hr]"] — the ergonomic coupling step.  It reduces the
    bin-weights to a [PairV] of literals ([wp_pures]/[tp_pures]), focuses the
    [Sample] on both sides ([wp_bind]/[tp_bind]), and applies the value-form
    [wp_couple_coin] inferring [w1/w2/K/E] from the goal — the author supplies
    only the resource pattern (there is no privacy choice for the exact
    coupling).  The side-conditions ([0 ≤ w1], [0 ≤ w2], the weights'
    nonnegativity) are auto-discharged best effort ([lia]/[done]); the
    postcondition continuation is the single remaining goal.  Mirrors
    [couple_uniform]. *)
Tactic Notation "couple_coin" "with" constr(pat) :=
  wp_pures; tp_pures;
  wp_bind (Sample _ _ _); tp_bind (Sample _ _ _);
  (* [unshelve] (the tactical) turns the goals THIS [iApply] shelves — only the
     [0 ≤ w1]/[0 ≤ w2] side-conditions — into regular front goals, without
     globally un-shelving unrelated goals the way the [Unshelve] command would. *)
  unshelve (iApply (wp_couple_coin _ _ _ _ with pat));
  (* best-effort discharge of [0 ≤ w1]/[0 ≤ w2]; the postcondition continuation
     is the single goal left *)
  try first [ lia | done | (simpl; lia) ].

Section coin_canary.
  Context {Sg : Sig} `{!SampleIn coin_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** CANARY: two surface-form [Coin #w1 #w2 #()] draws couple, at zero cost,
      with the spec output EQUAL to the impl output — driven entirely by the
      [couple_coin] tactic.  Stated over the [Coin] notation (i.e. [expr], with
      un-reduced bin-weights) so it exercises the surface path a program takes;
      demonstrates the convenience layer end to end. *)
  Lemma wp_coin_exact_canary (w1 w2 : Z) K E :
    (0 <= w1)%Z →
    (0 <= w2)%Z →
    {{{ ⤇ fill K (Coin #w1 #w2 #()) }}}
      Coin #w1 #w2 #() @ E
      {{{ (b : bool), RET #b; ⤇ fill K #b }}}.
  Proof.
    iIntros (Hw1 Hw2 Φ) "Hr HΦ".
    (* the whole proof is one ergonomic coupling step: [couple_coin] reduces the
       weights, focuses the [Sample]s, applies [wp_couple_coin], discharges the
       [0 ≤ w1]/[0 ≤ w2] side-conditions, and unifies the postcondition with
       [HΦ]. *)
    couple_coin with "[$Hr]".
  Qed.

End coin_canary.

(** DIFFERENT-WEIGHT coupling — DEFERRED.  The TV-distance / error-bearing
    coupling [DPcoupl (biased_coin r) (biased_coin r') (=) 0 δ] (with
    [δ = |r − r'|], the statistical distance between two differently-biased
    coins), needed for the crypto rejection-sampling case study, is NOT added
    here.  The foundation is the EXACT same-weight coupling above; the
    different-weight variant would mirror the δ-bearing uniform
    collision-avoidance variants and can be added when the crypto port needs it.
    See [lib/uniform.v]'s analogous note. *)
