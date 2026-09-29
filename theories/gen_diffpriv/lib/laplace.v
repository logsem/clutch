(** Reusable discrete-Laplace library for the generic DP logic.

    Importing this file and providing a [SampleIn laplace_family S] instance
    makes the [Laplace] surface notation and the [wp_couple_laplace] mechanism
    rule available at WHATEVER index the family occupies in the signature [S] —
    the index is recovered from the [SampleIn] instance via [sample_idx], never
    hardcoded.  No per-development canonical-structure or [spec_updateGS]
    boilerplate is required: the WP elaborates through the ∀S canonical chain
    (pinned by the in-context [diffprivGS]) and the spec layer resolves through
    the [diffprivGS_spec_updateGS] instance.

    A client development therefore needs only:
      Definition Slap : Sig := [...; laplace_family; ...].
      #[global] Instance : SampleIn laplace_family Slap := ltac:(solve_SampleIn).
      Section foo. Context `{!diffprivGS Slap Σ}.
    and then writes [Laplace num den mean] in programs and applies
    [wp_couple_laplace] in proofs. *)
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import differential_privacy distribution couplings couplings_app couplings_dp.
(* re-export the client-facing layer so [Require Import laplace] alone provides
   the WP rules, coupling seams, proof-mode tactics, notation and families.
   [diffpriv_rules] brings the distribution-agnostic DP combinators
   ([hoare_diffpriv_metric], [hoare_sensitive], the composition lemmas) that the Laplace
   MECHANISM ([hoare_laplace_diffpriv]) instantiates. *)
From clutch.gen_diffpriv Require Export primitive_laws coupling_rules proofmode diffpriv_rules.
From clutch.gen_prob_lang Require Export families.
From iris.prelude Require Import options.

Local Open Scope R.

(** [Laplace num den mean tape] samples the Laplace family at parameter
    [(num, den, mean)] using sample tape [tape] ([#()] for a direct,
    tape-less sample).  This 4-argument surface form matches the [prob_lang]
    [Laplace] constructor so case studies port verbatim; the family's index in
    the ambient signature is recovered from the [SampleIn laplace_family _]
    instance — NOT hardcoded. *)
Notation Laplace num den mean tape :=
  (Sample (sample_idx (D := laplace_family)) (Pair num (Pair den mean)) tape)
  (only parsing).

(** Value-form of [Laplace] (direct, tape-less): the [(num,den,mean)] parameters
    already reduced to a [PairV] triple, as they appear AFTER [wp_pures]/[tp_pures]
    (which evaluate the [Pair] into a [PairV]).  The coupling rules below are
    stated on [LaplaceV] so their preconditions read cleanly and match
    post-reduction goals; the [couple_laplace] tactic relies on this shape. *)
Notation LaplaceV num den mean :=
  (Sample (sample_idx (D := laplace_family))
     (Val (PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean)))))
     (Val (LitV LitUnit)))
  (only parsing).

Section laplace.
  Context {S : Sig} `{!SampleIn laplace_family S} `{!diffprivGS S Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang S)).
  (* the family's index in [S], recovered from the [SampleIn] instance *)
  Local Notation lidx := (@sample_idx laplace_family S _).

  (** The core Laplace draw coupling, on the family's outcome type [Z]:
      shifting the location by [k] costs [|k'| · ε] error when the two locations
      differ by at most [k'].  Family-level fact (independent of [S]),
      discharged by the reusable [Mcoupl_laplace]. *)
  Lemma DPcoupl_laplace_draw (num den loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (Hpos : (0 < IZR num / IZR den)%R) :
    DPcoupl (sf_sample laplace_family (num, den, loc))
            (sf_sample laplace_family (num, den, loc'))
            (λ z z', (z + k = z')%Z) (IZR k' * (IZR num / IZR den)) 0.
  Proof.
    simpl. rewrite /laplace_rat.
    destruct (decide (0 < IZR num / IZR den)) as [εpos | nε]; [|lra].
    apply Mcoupl_to_DPcoupl.
    by apply (Mcoupl_laplace (mkposreal _ εpos) loc loc' k k' Hdist).
  Qed.

  (** The Laplace mechanism is ε-DP at the WP level: sampling at location [loc]
      (impl) vs [loc'] (spec) couples to outputs that agree after shifting the
      spec by [k], at multiplicative error [|k'|·ε].  Obtained by instantiating
      the GENERIC prog-couple seam [wp_couple_sample_gen] with the single Laplace
      draw coupling [DPcoupl_laplace_draw] — at the index [sample_idx], so this
      one rule serves every signature containing [laplace_family]. *)
  Lemma wp_couple_laplace (loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    {{{ ⤇ fill K (Sample lidx
                    (Val (PairV (LitV (LitInt num))
                            (PairV (LitV (LitInt den)) (LitV (LitInt loc')))))
                    (Val (LitV LitUnit))) ∗ ↯m ε' }}}
      Sample lidx
        (Val (PairV (LitV (LitInt num))
                (PairV (LitV (LitInt den)) (LitV (LitInt loc)))))
        (Val (LitV LitUnit)) @ E
      {{{ (z : Z), RET #z; ⤇ fill K #(z + k) }}}.
  Proof.
    iIntros (Hε εpos Hε' Φ) "(Hr & Hε) HΦ".
    iApply (wp_couple_sample_gen S lidx
              (sf_param_to_val laplace_family (num, den, loc))
              (sf_param_to_val laplace_family (num, den, loc'))
              (dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc)))
              (dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc')))
              (λ v v', ∃ z : Z, v = #z ∧ v' = #(z + k)) K E ε'
              (sig_sample_at laplace_family S (num, den, loc))
              (sig_sample_at laplace_family S (num, den, loc')) _ with "[$Hr $Hε]").
    { iIntros "!>" (v v') "(Hspec & %HR)". destruct HR as (z & -> & ->).
      iApply ("HΦ" $! z with "Hspec"). }
    (* the single DP obligation: lift the Laplace draw coupling through sf_inj *)
    Unshelve.
    apply DPcoupl_map; [subst ε'; apply Rmult_le_pos; [apply IZR_le; lia | lra] | lra | ].
    eapply (DPcoupl_mono _ _ _ _ (λ z z', (z + k = z')%Z) _ ε' ε' 0 0);
      [ intros; reflexivity
      | intros; reflexivity
      | intros z z' Hzz'; exists z; split; [done | by rewrite Hzz']
      | lra | lra
      | subst ε'; rewrite -Hε; by apply DPcoupl_laplace_draw ].
  Qed.

  (** The surface-form Laplace coupling rule, stated on the [Laplace] notation
      (with the [(num,den,loc)] parameter as an un-reduced [Pair]) so it matches
      the [prob_lang] [hoare_couple_laplace] API.  The proof reduces the [Pair]
      params on both sides ([wp_pures]/[tp_pures]) and then applies the
      reduced-form [wp_couple_laplace]. *)
  Lemma hoare_couple_laplace (loc loc' k k' : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR k' * ε) →
    {{{ ⤇ fill K (Laplace #num #den #loc' #()) ∗ ↯m ε' }}}
      Laplace #num #den #loc #() @ E
      {{{ (z : Z), RET #z; ⤇ fill K #(z + k) }}}.
  Proof.
    iIntros (Hε εpos Hε' Φ) "(Hr & Hε) HΦ".
    wp_pures. tp_pures.
    iApply (wp_couple_laplace loc loc' k k' Hdist num den ε ε' K E Hε εpos Hε'
              with "[$Hr $Hε]").
    iApply "HΦ".
  Qed.

  (** The exact (error-free) coupling: identical locations couple perfectly
      (the two sides sample the SAME distribution, coupled along the diagonal at
      zero cost — the reflexive coupling, [ARcoupl_eq] lifted to [DPcoupl]). *)
  Lemma hoare_couple_laplace_exact (loc num den : Z) K E :
    {{{ ⤇ fill K (Laplace #num #den #loc #()) }}}
      Laplace #num #den #loc #() @ E
      {{{ (z : Z), RET #z; ⤇ fill K #z }}}.
  Proof.
    iIntros (Φ) "Hr HΦ".
    wp_pures. tp_pures.
    iMod ecm_zero as "Hε".
    iApply (wp_couple_sample_gen S lidx
              (sf_param_to_val laplace_family (num, den, loc))
              (sf_param_to_val laplace_family (num, den, loc))
              (dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc)))
              (dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc)))
              (λ v v', ∃ z : Z, v = #z ∧ v' = #z) K E 0
              (sig_sample_at laplace_family S (num, den, loc))
              (sig_sample_at laplace_family S (num, den, loc)) _ with "[$Hr $Hε]").
    { iIntros "!>" (v v') "(Hspec & %HR)". destruct HR as (z & -> & ->).
      iApply ("HΦ" $! z with "Hspec"). }
    (* the reflexive coupling of the Laplace draw, lifted through sf_inj *)
    Unshelve.
    apply (DPcoupl_map (sf_inj laplace_family) (sf_inj laplace_family)
             (sf_sample laplace_family (num, den, loc)) (sf_sample laplace_family (num, den, loc))
             (λ v v', ∃ z : Z, v = #z ∧ v' = #z) 0 0); [lra | lra | ].
    eapply (DPcoupl_mono (sf_sample laplace_family (num, den, loc))
              (sf_sample laplace_family (num, den, loc))
              (sf_sample laplace_family (num, den, loc))
              (sf_sample laplace_family (num, den, loc))
              (=) (λ a a', ∃ z : Z, sf_inj laplace_family a = #z ∧ sf_inj laplace_family a' = #z)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra
      | apply ARcoupl_to_DPcoupl, ARcoupl_eq ].
  Qed.

  (** The Laplace MECHANISM as a (rescaled) internally-DP program: at
      multiplicative cost [c · (num/den)] for inputs at distance [dZ x x' ≤ c].
      This is the composition-ready [hoare_diffpriv_metric] form — group privacy and
      k-adjacency come from the rescaling parameter [c], NOT from any chaining /
      interpolation of refinements (the refinement here couples one impl run to
      one spec run and is not transitive).  The proof is a SINGLE distance-[c]
      coupling: [hoare_couple_laplace … 0] shifts by 0 with [k'] bounding
      [|x − x'|], so the cost [IZR k' · ε] is weakened up to [c · ε] via [adj].
      Ported from [clutch.diffpriv.diffpriv_rules.hoare_laplace_diffpriv]. *)
  Fact hoare_laplace_diffpriv (num den : Z) :
    ⌜0 < IZR num / IZR den⌝ -∗
    hoare_diffpriv_metric S (λ: "loc", Laplace #num #den "loc" #())%V (IZR num / IZR den) 0 dZ Z.
  Proof.
    iIntros "%Hpos". rewrite /hoare_diffpriv_metric /dZ /=. iIntros (K c x x' adj).
    iIntros (φ) "!> [f' [ε δ]] hφ".
    tp_pures. wp_pures.
    tp_bind (Sample _ _ _). wp_bind (Sample _ _ _).
    (* value-form rule: the [Pair] params have reduced to [PairV] (gen gotcha) *)
    iApply (wp_couple_laplace x x' 0%Z (Z.abs (x - x'))
              ltac:(apply Zabs_ind; lia) num den (IZR num / IZR den)
              (IZR (Z.abs (x - x')) * (IZR num / IZR den)) K ⊤
              eq_refl Hpos eq_refl with "[$f' ε]").
    2:{ setoid_rewrite Z.add_0_r. iIntros "!> %z f'". iApply ("hφ" $! z). iFrame. }
    (* the single distance-c credit: weaken c·ε down to |x−x'|·ε via [adj] *)
    iApply ecm_weaken. 2: iFrame. split.
    - apply Rmult_le_pos; [apply IZR_le, Z.abs_nonneg | lra].
    - apply Rmult_le_compat_r; [lra|]. rewrite abs_IZR. exact adj.
  Qed.

End laplace.

(** ** Consolidated coupling tactics

    Across the noise families (laplace / exp / trunc_laplace) the convenience
    coupling tactics shared ONE skeleton that varied on only two axes:

      (1) DO-BIND — whether to focus the [Sample] on both sides first.  The
          [couple_X]/[couple_X_cost] variants atomically run
          [wp_pures; tp_pures; wp_bind; tp_bind] before applying the rule; the
          [couple_X_apply] variant DROPS that prefix so the caller can do the
          bind manually and interleave setup between bind and apply.

      (2) CREDIT-CLOSER — whether the side-condition battery also closes the
          residual [↯m ε'] credit goal.  At EXACT-cost sites the caller eagerly
          [$]-frames the credit (pattern [\"[$Hr $Hε]\"]) so no credit goal
          remains and [reflexivity]/[simpl; lra] pin the equational [Hε'].  At
          COST-reconciliation sites the caller ROUTES the credit unframed
          (pattern [\"[$Hr Hε]\"]); the credit goal [↯m (k'·ε)] then survives the
          battery (its tactics fire only on first-order side-goals, never on the
          [iProp] credit) and is left for the caller's [ecm_eq]/[ecm_weaken].

    Axis (2) MERGES the old [couple_X] (exact-cost) and [couple_X_cost] (non-exact
    cost) into the single [couple_X]: a GUARDED side-condition battery
    ([couple_discharge]) — [reflexivity] / [apply Zabs_ind; lia] / [lia] /
    [simpl; lra], plus a [match … |- R => fail] -guarded [assumption] — handles
    both regimes.  The guard is the crux: it stops the [assumption] fallback from
    instantiating a bare [ε]/[ε'] real-valued value-evar with an in-context
    distance bound [c : R] at the routed (cost) sites, while still letting
    [reflexivity]/[simpl; lra] pin the equational [Hε'] at the framed (exact)
    sites.  So which regime you get is chosen by the caller's resource pattern,
    not by the tactic name — one tactic absorbs both.

    The APPLY variant ([couple_X_apply]) keeps its OWN slimmer battery
    ([couple_discharge_apply]): the interleaved sites that use it hand-write the
    residual closers ([ecm_eq]/[lra]/[iFrame] bullets), so the apply battery must
    NOT include the [simpl; lra] closer that [couple_X] uses for the framed [Hε']
    — that would consume a goal the caller's bullet expects.  This is the one
    per-family difference that resists the merge; it is kept as a distinct
    (shared-across-families) discharge tactic rather than folded into one.

    The result is TWO tactics per family — [couple_X] (bind + [couple_discharge])
    and [couple_X_apply] (no bind + [couple_discharge_apply]) — sharing the family-
    agnostic [couple_bind] skeleton and the two discharge batteries (all three now
    living in [gen_diffpriv.proofmode], reused verbatim by [exponential] and
    [trunc_laplace]), plus a thin family-specific [couple_*_iapply] wrapping the
    [unshelve (iApply …)] step. *)

(** [couple_laplace_iapply k k' pat] — the family-specific apply step shared by
    [couple_laplace] and [couple_laplace_apply].  [unshelve] (the tactical, not
    the [Unshelve] command) turns ONLY the goals THIS [iApply] shelves (the
    distance side-condition [Hdist]) into regular front goals. *)
Ltac couple_laplace_iapply k k' pat :=
  unshelve (iApply (wp_couple_laplace _ _ k k' _ _ _ _ _ _ _ with pat)).

(** [couple_laplace k k' with "[…]"] — the ergonomic coupling step.  Focuses the
    [Sample] on both sides ([couple_bind]) and applies the value-form
    [wp_couple_laplace] inferring [loc/loc'/num/den/ε/ε'/K/E] from the goal — the
    author supplies only the privacy choice [k] (shift) and [k'] (cost bound) and
    the resource pattern.  Subsumes both the old exact-cost [couple_laplace]
    (eager-frame the credit with [\"[$Hr $Hε]\"]) and the old non-exact
    [couple_laplace_cost] (route the credit unframed with [\"[$Hr Hε]\"], leaving
    the clean [↯m (k'·ε)] goal for an [ecm_eq]/[ecm_weaken] reconciliation): which
    regime you get is chosen by the resource pattern, not by the tactic name. *)
Tactic Notation "couple_laplace" uconstr(k) uconstr(k') "with" constr(pat) :=
  couple_bind; couple_laplace_iapply k k' pat; couple_discharge.

(** [couple_laplace_apply k k' with "[$Hr Hε]"] — the APPLY-ONLY variant, for
    INTERLEAVED coupling sites where essential setup happens BETWEEN focusing the
    [Sample] and applying the coupling rule (e.g. an [ecm_split]/[ecm_eq]/[replace]
    of the credit).  PRECONDITION: the caller has ALREADY focused the [Sample] on
    both sides (its own [couple_bind]-equivalent) and done any interleaved setup;
    this tactic runs ONLY the [unshelve (iApply …)] + the slimmer
    [couple_discharge_apply] battery, leaving the credit goal and the hand-closed
    residual goals (and postcondition) for the caller. *)
Tactic Notation "couple_laplace_apply" uconstr(k) uconstr(k') "with" constr(pat) :=
  couple_laplace_iapply k k' pat; couple_discharge_apply.

Section laplace_apply_canary.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** CANARY for the APPLY-ONLY [couple_laplace_apply]: identical to the [cost]
      canary, but the caller does the [wp_bind]/[tp_bind] MANUALLY (mimicking an
      interleaved site) before calling the apply-only tactic — exercising that
      [couple_laplace_apply] does NOT itself re-bind the [Sample] and works once
      the caller has focused both sides.  The credit is ROUTED (unframed [Hε],
      pattern [\"[$Hr Hε]\"]) into the residual [↯m (k'·ε)] goal; here the cost is
      exact so the residual is closed by re-framing [Hε] (a real cost-recon site
      would [iApply ecm_*] there). *)
  Lemma wp_laplace_shift_canary_apply (loc loc' k k' num den : Z)
    (Hdist : (Z.abs (k + loc - loc') <= k')%Z)
    (Hpos : 0 < IZR num / IZR den) K E :
    {{{ ⤇ fill K (Laplace #num #den #loc' #()) ∗ ↯m (IZR k' * (IZR num / IZR den)) }}}
      Laplace #num #den #loc #() @ E
      {{{ (z : Z), RET #z; ⤇ fill K #(z + k) }}}.
  Proof.
    iIntros (Φ) "(Hr & Hε) HΦ".
    (* MANUAL bind on both sides — the interleaved-site idiom the apply-only
       tactic supports (and where setup could be interposed here) *)
    wp_pures. tp_pures.
    wp_bind (Sample _ _ _). tp_bind (Sample _ _ _).
    couple_laplace_apply k k' with "[$Hr Hε]".
    (* residual credit goal [↯m (k'·ε)] — closed here by re-framing the routed
       [Hε] (exact cost); a non-exact site would [iApply ecm_*] instead *)
    2: iApply "HΦ".
    iFrame "Hε".
  Qed.

End laplace_apply_canary.
