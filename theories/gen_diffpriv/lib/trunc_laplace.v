(** Reusable TRUNCATED discrete-Laplace library for the generic DP logic — the
    metric approximate-DP client.

    This mirrors [lib.laplace] but for the bounded-support truncated discrete
    Laplace family [trunc_laplace_family] (see [gen_prob_lang/families.v]), whose
    per-distance coupling [prob/trunc_laplace.v.DPcoupl_trunc_lap] is the EXACT
    group-bound profile [(s·ε, δ₁·grp ε s)] (with [ε = num/den],
    [δ₁ = exp(-ε·A)/Z_A], shift [s]).  Importing this file and providing a
    [SampleIn trunc_laplace_family S] instance makes the [TruncLaplace] surface
    notation and the [wp_couple_trunc_laplace] mechanism rule available at
    WHATEVER index the family occupies in the signature [S].

    The truncation half-width [A] is a genuine RUNTIME sample parameter (the
    fourth [Z] of [trunc_laplace_family]'s [(A,num,den,loc)] interface), NOT a
    Coq-level family index — so [A] is chosen at sample time, and the
    side-conditions [0 <= A] (and the regime [0 <= s <= A]) that
    [DPcoupl_trunc_lap] requires are HYPOTHESES on the runtime [A].  The family's
    sample at param [(A,num,den,loc)] is [trunc_lap_rat (Z.max 0 A) num den loc];
    at runtime [A >= 0] the clamp is the identity ([Z.max 0 A = A]), connecting it
    to [DPcoupl_trunc_lap]'s [trunc_lap_rat A] via a small [Z.max_r] rewrite.

    Unlike [lib.laplace], the draw coupling carries a NONZERO additive error
    [δ = tlap_delta], so we go through [wp_couple_sample_gen_dp] (the
    δ-carrying program-couple seam) rather than [wp_couple_sample_gen].  The
    mechanism is packaged as a [hoare_diffpriv_metric] instance — the validating
    example for the group-bound metric approximate-DP definition. *)
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import differential_privacy distribution couplings couplings_app couplings_dp.
From clutch.prob Require Import trunc_laplace.
From clutch.gen_diffpriv Require Export primitive_laws coupling_rules proofmode diffpriv_rules.
From clutch.gen_prob_lang Require Import inject.
From clutch.gen_prob_lang Require Export families.
From iris.prelude Require Import options.

Local Open Scope R.

(** [TruncLaplace A num den mean tape] samples the truncated discrete Laplace
    family at parameter [(A,num,den,mean)] — with [A] the RUNTIME truncation
    half-width — using sample tape [tape] ([#()] for a direct, tape-less sample).
    As in [lib.laplace], the family's index in the ambient signature is recovered
    from the [SampleIn] instance — NOT hardcoded.  The value parameter is the
    nested pair [(A, (num, (den, mean)))] matching [trunc_laplace_family]'s
    [(A,num,den,loc)] [mkZNoise4] encoding. *)
Notation TruncLaplace A num den mean tape :=
  (Sample (sample_idx (D := trunc_laplace_family))
          (Pair A (Pair num (Pair den mean))) tape)
  (only parsing).

(** Value-form of [TruncLaplace] (direct, tape-less): the nested
    [(A, (num, (den, mean)))] parameter already reduced to a [PairV] tree, as it
    appears AFTER [wp_pures]/[tp_pures].  The coupling rule [wp_couple_trunc_laplace]
    is stated on this shape so its precondition matches post-reduction goals; the
    [couple_trunc_laplace] tactic relies on it.  Mirrors [LaplaceV]/[ExpV], but
    with the extra leading truncation half-width [A]. *)
Notation TruncLaplaceV A num den mean :=
  (Sample (sample_idx (D := trunc_laplace_family))
     (Val (PairV (LitV (LitInt A))
             (PairV (LitV (LitInt num))
                (PairV (LitV (LitInt den)) (LitV (LitInt mean))))))
     (Val (LitV LitUnit)))
  (only parsing).

Section trunc_laplace_lib.
  Context {S : Sig} `{!SampleIn trunc_laplace_family S} `{!diffprivGS S Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang S)).
  (* the family's index in [S], recovered from the [SampleIn] instance *)
  Local Notation tlidx := (@sample_idx trunc_laplace_family S _).

  (** The fixed additive boundary mass [δ₁ = exp(-ε·A)/Z_A].  Independent of the
      location (the normaliser [tlap_Z] is shift-invariant), so we pin [loc = 0]. *)
  Definition tlap_del (A num den : Z) : R :=
    exp (- (IZR num / IZR den) * IZR A) / tlap_Z A num den 0.

  (** [tlap_delta] factors as [tlap_del · grp ε |s|] — the group-bound shape.
      Now over the two-sided shift: [tlap_delta] depends only on [|s|]. *)
  Lemma tlap_delta_grp (A num den loc s : Z) :
    tlap_delta A num den loc s
      = tlap_del A num den * grp (IZR num / IZR den) (IZR (Z.abs s)).
  Proof.
    rewrite /tlap_delta /tlap_del /grp.
    rewrite (tlap_Z_shift_inv A num den loc 0).
    lra.
  Qed.

  (** The family's clamped sample equals [trunc_lap_rat A …] for runtime [A >= 0]
      ([Z.max 0 A = A]).  This is what connects [trunc_laplace_family]'s sample to
      [DPcoupl_trunc_lap]'s [trunc_lap_rat A].  Holds DEFINITIONALLY up to the
      [Z.max] clamp, which the [0 <= A] hypothesis discharges via [Z.max_r]. *)
  Lemma sf_sample_trunc (A num den loc : Z) (HA : (0 <= A)%Z) :
    sf_sample trunc_laplace_family (A, num, den, loc) = trunc_lap_rat A num den loc.
  Proof.
    simpl. by rewrite (Z.max_r 0 A HA).
  Qed.

  (** The core truncated-Laplace draw coupling, on the family's outcome type [Z]:
      for a TWO-SIDED shift [s] with [|s| ≤ A], sampling at [loc] (impl) couples
      to sampling at [loc+s] (spec) along the DIAGONAL ([z = z']) at cost
      [(|s| · ε)] multiplicative AND [tlap_delta A num den loc s] additive.
      Family-level fact, discharged by the reusable two-sided [DPcoupl_trunc_lap]
      after the [Z.max 0 A = A] clamp rewrite ([sf_sample_trunc], needs [0 <= A]). *)
  Lemma DPcoupl_trunc_lap_draw (A num den loc s : Z)
    (HA : (0 <= A)%Z)
    (Hs : (Z.abs s <= A)%Z)
    (Hpos : (0 < IZR num / IZR den)%R) :
    DPcoupl (sf_sample trunc_laplace_family (A, num, den, loc))
            (sf_sample trunc_laplace_family (A, num, den, (loc + s)%Z))
            eq (IZR (Z.abs s) * (IZR num / IZR den)) (tlap_delta A num den loc s).
  Proof.
    rewrite !sf_sample_trunc //. by apply (DPcoupl_trunc_lap A num den HA Hpos loc s Hs).
  Qed.

  (** The truncated-Laplace mechanism at the WP level: sampling at location [loc]
      (impl) vs [loc+s] (spec), TWO-SIDED [|s| ≤ A], couples to EQUAL outputs at
      multiplicative cost [|s|·ε] and additive cost [tlap_delta A num den loc s].
      Obtained by instantiating the δ-carrying prog-couple seam
      [wp_couple_sample_gen_dp] with the single draw coupling
      [DPcoupl_trunc_lap_draw] — at the recovered index [sample_idx].  [A] is a
      RUNTIME [Z] argument with [0 <= A] a hypothesis. *)
  Lemma wp_couple_trunc_laplace (A loc s : Z)
    (HA : (0 <= A)%Z)
    (Hs : (Z.abs s <= A)%Z)
    (num den : Z) (ε ε' δ' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (IZR (Z.abs s) * ε) →
    δ' = tlap_delta A num den loc s →
    {{{ ⤇ fill K (Sample tlidx
                    (Val (PairV (LitV (LitInt A))
                            (PairV (LitV (LitInt num))
                               (PairV (LitV (LitInt den)) (LitV (LitInt (loc + s)))))))
                    (Val (LitV LitUnit))) ∗ ↯m ε' ∗ ↯ δ' }}}
      Sample tlidx
        (Val (PairV (LitV (LitInt A))
                (PairV (LitV (LitInt num))
                   (PairV (LitV (LitInt den)) (LitV (LitInt loc))))))
        (Val (LitV LitUnit)) @ E
      {{{ (z : Z), RET #z; ⤇ fill K #z }}}.
  Proof.
    iIntros (Hε εpos Hε' Hδ' Φ) "(Hr & Hε & Hδ) HΦ".
    iApply (wp_couple_sample_gen_dp S tlidx
              (sf_param_to_val trunc_laplace_family (A, num, den, loc))
              (sf_param_to_val trunc_laplace_family (A, num, den, (loc + s)%Z))
              (dmap (sf_inj trunc_laplace_family) (sf_sample trunc_laplace_family (A, num, den, loc)))
              (dmap (sf_inj trunc_laplace_family) (sf_sample trunc_laplace_family (A, num, den, (loc + s)%Z)))
              (λ v v', ∃ z : Z, v = #z ∧ v' = #z) K E ε' δ'
              _
              (sig_sample_at trunc_laplace_family S (A, num, den, loc))
              (sig_sample_at trunc_laplace_family S (A, num, den, (loc + s)%Z)) _ with "[$Hr $Hε $Hδ]").
    { iIntros "!>" (v v') "(Hspec & %HR)". destruct HR as (z & -> & ->).
      iApply ("HΦ" $! z with "Hspec"). }
    (* two obligations: the additive-credit nonnegativity [0 <= δ'], and the
       single δ-carrying DP obligation — lift the truncated draw coupling
       through [sf_inj]. *)
    Unshelve.
    - subst δ'. rewrite tlap_delta_grp.
      apply Rmult_le_pos.
      + rewrite /tlap_del. apply Rcomplements.Rdiv_le_0_compat;
          [left; apply exp_pos | apply (tlap_Z_pos A num den 0 HA)].
      + apply grp_nonneg; [lra | apply IZR_le; lia].
    - apply DPcoupl_map.
      { subst ε'. apply Rmult_le_pos; [apply IZR_le; lia | lra]. }
      { subst δ'. rewrite tlap_delta_grp.
        apply Rmult_le_pos.
        - rewrite /tlap_del. apply Rcomplements.Rdiv_le_0_compat;
            [left; apply exp_pos | apply (tlap_Z_pos A num den 0 HA)].
        - apply grp_nonneg; [lra | apply IZR_le; lia]. }
      eapply (DPcoupl_mono _ _ _ _ eq _ ε' ε' δ' δ');
        [ intros; reflexivity
        | intros; reflexivity
        | intros z z' Hzz'; exists z; split; [done | by rewrite Hzz']
        | lra | lra
        | subst ε' δ'; rewrite -Hε; by apply DPcoupl_trunc_lap_draw ].
  Qed.

  (** [grp ε ·] is monotone in the distance (for [ε > 0]): the numerator
      [exp(c·ε)-1] is increasing in [c] and the denominator [exp ε - 1 > 0]. *)
  Lemma grp_mono (eps c1 c2 : R) :
    0 < eps -> 0 <= c1 -> c1 <= c2 -> grp eps c1 <= grp eps c2.
  Proof.
    intros Heps Hc1 Hle. rewrite /grp.
    apply Rmult_le_compat_r.
    - left. apply Rinv_pos.
      cut (1 < exp eps); [lra|]. rewrite -exp_0. apply exp_increasing. lra.
    - apply Rplus_le_compat_r.
      destruct (Rle_lt_or_eq_dec _ _ Hle) as [Hlt | <-].
      + left. apply exp_increasing. apply Rmult_lt_compat_r; lra.
      + lra.
  Qed.

  (** The TRUNCATED-LAPLACE MECHANISM as a group-bound metric approximate-DP
      program — the validating CLIENT for [hoare_diffpriv_metric].

      At base rate [ε = num/den] and additive base mass [tlap_del A num den], for
      inputs at distance [dZ x x' ≤ c] the mechanism demands [↯m (c·ε)] AND
      [↯ (tlap_del · grp ε c)], and the two output draws agree — exactly the
      [hoare_diffpriv_metric] precondition shape with [eps := ε],
      [del := tlap_del A num den].  [A] is a RUNTIME [Z] argument with [0 <= A] a
      hypothesis.

      TWO-SIDED.  Thanks to the now two-sided coupling [DPcoupl_trunc_lap]
      ([|s| ≤ A]), this holds for shifts of EITHER sign — the [Hfwd : x ≤ x']
      hypothesis is GONE.  The lone surviving regime side-condition is the
      genuine truncation constraint [c ≤ IZR A] (so [|s| ≤ dZ x x' ≤ c ≤ A] and
      the coupling applies); the truncated Laplacian's privacy is honestly only a
      group bound up to its half-width [A], so [c ≤ A] cannot be dropped (for
      [c > A] the two supports can be disjoint and the demanded
      [tlap_del · grp ε c < 1] does not cover them).  Modulo [c ≤ IZR A] the
      conclusion is verbatim the [hoare_diffpriv_metric] triple for ALL [x, x'].
      [hoare_trunc_laplace_diffpriv] below packages this into a bare
      [hoare_diffpriv_metric] instance on the TRUNCATED metric [dZ_trunc A], which
      is [dZ] in range ([|x-x'| ≤ A]) and jumps to a saturation threshold
      [tlap_Cstar] beyond it — past which the demanded additive credit already
      exceeds [1], so the disjoint-support case is closed by the trivial coupling
      [DPcoupl_1].

      PROOF.  The SAME single-coupling structure as [lib.laplace]'s
      [hoare_laplace_diffpriv]: [tp_pures]/[wp_pures] then [tp_bind]/[wp_bind]
      the [Sample], apply the value-form [wp_couple_trunc_laplace] at the actual
      shift [s = x'-x] (so impl loc [x], spec loc [x + s = x']), and weaken its
      [(|s|·ε, tlap_del·grp ε |s|)] profile DOWN from the demanded
      [(c·ε, tlap_del·grp ε c)] credits — multiplicative via [ecm_weaken]
      ([|s| ≤ c]); additive via [ec_weaken] and [grp_mono]
      ([grp ε |s| ≤ grp ε c]). *)
  Lemma trunc_laplace_diffpriv_body (A num den : Z) (K : ectx (gen_ectx_lang S))
    (c : R) (x x' : Z)
    (HA : (0 <= A)%Z)               (* runtime truncation half-width [A ≥ 0] *)
    (Hpos : 0 < IZR num / IZR den)
    (HcA  : c <= IZR A)             (* distance below the truncation half-width *)
    (adj  : dZ x x' <= c) :
    {{{ ⤇ fill K ((λ: "loc", TruncLaplace #A #num #den "loc" #())%V (inject x'))
        ∗ ↯m (c * (IZR num / IZR den))
        ∗ ↯ (tlap_del A num den * grp (IZR num / IZR den) c) }}}
      (λ: "loc", TruncLaplace #A #num #den "loc" #())%V (inject x)
    {{{ (y : Z), RET (inject y); ⤇ fill K (Val (inject y)) }}}.
  Proof.
    rewrite /dZ /=.
    iIntros (φ) "(f' & ε & δ) hφ".
    tp_pures. wp_pures.
    (* the actual shift [s = x'-x] (EITHER sign), and [|s| ≤ A] since
       [|s| ≤ dZ x x' ≤ c ≤ A] *)
    set (s := (x' - x)%Z).
    assert (Habs : dZ x x' = IZR (Z.abs s))
      by (rewrite /dZ /= /s -abs_IZR; f_equal; lia).
    assert (Hsc : IZR (Z.abs s) <= c) by (rewrite -Habs; exact adj).
    assert (HsA : (Z.abs s <= A)%Z) by (apply le_IZR; etrans; [exact Hsc | exact HcA]).
    (* align the spec location [x'] with the coupling's [x + s] form *)
    replace x' with (x + s)%Z by (rewrite /s; lia).
    tp_bind (Sample _ _ _). wp_bind (Sample _ _ _).
    (* value-form rule at loc [x], shift [s] (so spec loc [x + s = x']) *)
    iApply (wp_couple_trunc_laplace A x s HA HsA num den
              (IZR num / IZR den) (IZR (Z.abs s) * (IZR num / IZR den))
              (tlap_delta A num den x s) K ⊤
              eq_refl Hpos eq_refl eq_refl with "[$f' ε δ]").
    (* weaken the demanded [(c·ε, tlap_del·grp ε c)] DOWN to the consumed
       [(|s|·ε, tlap_delta x s) = (|s|·ε, tlap_del·grp ε |s|)] *)
    - rewrite tlap_delta_grp.
      iSplitL "ε".
      + iApply ecm_weaken; [|iFrame]. split.
        * apply Rmult_le_pos; [apply IZR_le; lia | lra].
        * apply Rmult_le_compat_r; [lra | exact Hsc].
      + iApply ec_weaken; [|iFrame]. split.
        * apply Rmult_le_pos.
          -- rewrite /tlap_del. apply Rcomplements.Rdiv_le_0_compat;
               [left; apply exp_pos
               | apply (clutch.prob.trunc_laplace.tlap_Z_pos A num den 0 HA)].
          -- apply grp_nonneg; [lra | apply IZR_le; lia].
        * apply Rmult_le_compat_l.
          -- rewrite /tlap_del. apply Rcomplements.Rdiv_le_0_compat;
               [left; apply exp_pos
               | apply (clutch.prob.trunc_laplace.tlap_Z_pos A num den 0 HA)].
          -- apply grp_mono; [lra | apply IZR_le; lia | exact Hsc].
    - iIntros "!> %z f'". iApply ("hφ" $! z). iFrame.
  Qed.

End trunc_laplace_lib.

(** [couple_trunc_laplace A s with "[…]"] — the ergonomic coupling step for the
    truncated discrete Laplace.  It reduces the nested [Pair] param to a [PairV]
    tree ([wp_pures]/[tp_pures]), focuses the [Sample] on both sides
    ([wp_bind]/[tp_bind]), and applies the value-form [wp_couple_trunc_laplace]
    inferring [loc/num/den/ε/ε'/δ'/K/E] from the goal — the author supplies only
    the runtime truncation half-width [A] and the forward shift [s] (so impl loc
    [loc], spec loc [loc+s]), together with the resource pattern.

    Unlike [couple_laplace]/[couple_exp] (δ = 0, two resources), this coupling is
    built over the δ-carrying seam [wp_couple_sample_gen_dp], so its precondition
    threads THREE resources — the spec [⤇], the multiplicative credit [↯m ε'] AND
    the additive credit [↯ δ'] — hence the pattern is the 3-way [\"[$Hr $Hε $Hδ]\"].
    Side-conditions: the regime hypotheses [HA : 0 ≤ A] and [Hs : 0 ≤ s ≤ A]
    (discharged best effort by [lia] / [split; lia]) and the equational
    [Hε]/[Hpos]/[Hε']/[Hδ'] (by [reflexivity]/[assumption]); the postcondition
    continuation is the single remaining goal. *)
Tactic Notation "couple_trunc_laplace" uconstr(A) uconstr(s) "with" constr(pat) :=
  wp_pures; tp_pures;
  wp_bind (Sample _ _ _); tp_bind (Sample _ _ _);
  (* [unshelve] turns the goals THIS [iApply] shelves — the regime side-conditions
     [HA]/[Hs] and the equational [Hε]/[εpos]/[Hε']/[Hδ'] — into regular front
     goals, without globally un-shelving unrelated goals. *)
  unshelve (iApply (wp_couple_trunc_laplace A _ s _ _ _ _ _ _ _ _ _ with pat));
  (* best-effort discharge of [HA]/[Hs] (regime) and [Hε]/[εpos]/[Hε']/[Hδ']
     (equational); the δ-credit [↯ δ'] is threaded by the 3-way resource pattern.
     The postcondition continuation is the single goal left. *)
  try first
    [ reflexivity
    | assumption
    | lia
    | (split; lia)
    | (simpl; lra) ].

(** [couple_trunc_laplace_cost A s with "[$Hr Hε Hδ]"] — the NO-EAGER-FRAME
    variant of [couple_trunc_laplace], for COST-RECONCILIATION sites where the
    cost steps are not exact (reconciled by the caller's [ecm_eq]/[ecm_weaken]).
    Mirrors [couple_trunc_laplace] but does NOT [$]-frame the credits: the
    caller's spec pattern (e.g. [\"[$Hr Hε Hδ]\"]) frames only the spec resource
    [⤇] with [$], and ROUTES the multiplicative credit [Hε] AND the additive
    δ-credit [Hδ] — both WITHOUT [$] — into the residual credit goals' contexts.
    Eagerly [$]-framing either would unify its evar to the in-context amount and
    turn the equational [Hε' : ε' = s·ε] / [Hδ' : δ' = tlap_delta …] into
    non-trivial equations — the failure mode at non-exact cost sites.  Still
    auto-discharges the regime side-conditions [HA]/[Hs] by [lia]/[split; lia]
    and pins [ε']/[δ'] to their rule-natural values by [reflexivity]; the two
    residual credit goals [↯m (s·ε)] / [↯ δ'] (with the in-context credits
    available) and the postcondition are left for the caller.  The [|- R => fail]
    guard stops [assumption] from grabbing a stray [c : R] for the bare
    value-evar goals. *)
Tactic Notation "couple_trunc_laplace_cost" uconstr(A) uconstr(s) "with" constr(pat) :=
  wp_pures; tp_pures;
  wp_bind (Sample _ _ _); tp_bind (Sample _ _ _);
  unshelve (iApply (wp_couple_trunc_laplace A _ s _ _ _ _ _ _ _ _ _ with pat));
  (* discharge [HA]/[Hs]/[Hε]/[εpos]/[Hε']/[Hδ'] (the equational ones pin
     [ε']/[δ'] by [reflexivity]); both credit goals [↯m ε']/[↯ δ'] are left for
     the caller's [ecm_*].  The [|- R => fail] guard prevents [assumption] from
     instantiating a bare value-evar goal of type [R] with an in-context [c]. *)
  try first
    [ lia
    | (split; lia)
    | reflexivity
    | (match goal with |- R => fail 1 | _ => assumption end) ].

(** [couple_trunc_laplace_apply A s with "[$Hr Hε Hδ]"] — the APPLY-ONLY variant
    of [couple_trunc_laplace_cost], for INTERLEAVED coupling sites where
    essential setup happens BETWEEN focusing the [Sample] and applying the
    coupling rule (e.g. an [ecm_split]/[ecm_eq]/[replace] of a credit).  The
    bundled [couple_trunc_laplace]/[couple_trunc_laplace_cost] atomically run
    [wp_pures; tp_pures; wp_bind; tp_bind] BEFORE the [iApply], so they cannot
    accommodate work done between the bind and the apply — that is what this
    variant drops.

    PRECONDITION: the caller has ALREADY focused the [Sample] on both sides — via
    its OWN [wp_bind (Sample _ _ _); tp_bind (Sample _ _ _)] (and any [wp_pures]/
    [tp_pures] needed to reduce the nested [Pair] param to a [PairV] tree) — and
    has done any interleaved setup.  This tactic does ONLY the [unshelve (iApply
    …)] + side-condition discharge: it auto-discharges the regime [HA]/[Hs] by
    [lia]/[split; lia] and [Hε]/[εpos]/[Hε']/[Hδ'] (pinning [ε']/[δ'] to their
    rule-natural values by [reflexivity]), routes BOTH credits [Hε]/[Hδ] WITHOUT
    [$] (so they stay available for the caller's [ecm_*]) and leaves the two
    residual credit goals [↯m (s·ε)] / [↯ δ'] and the postcondition continuation
    for the caller.  Like [couple_trunc_laplace_cost], the [|- R => fail] guard
    stops [assumption] from grabbing a stray [c : R] for the bare value-evar
    goals. *)
Tactic Notation "couple_trunc_laplace_apply" uconstr(A) uconstr(s) "with" constr(pat) :=
  unshelve (iApply (wp_couple_trunc_laplace A _ s _ _ _ _ _ _ _ _ _ with pat));
  (* discharge [HA]/[Hs]/[Hε]/[εpos]/[Hε']/[Hδ'] (the equational ones pin
     [ε']/[δ'] by [reflexivity]); both credit goals [↯m ε']/[↯ δ'] are left for
     the caller's [ecm_*].  The [|- R => fail] guard prevents [assumption] from
     instantiating a bare value-evar goal of type [R] with an in-context [c]. *)
  try first
    [ lia
    | (split; lia)
    | reflexivity
    | (match goal with |- R => fail 1 | _ => assumption end) ].

Section trunc_laplace_canary.
  Context {Sg : Sig} `{!SampleIn trunc_laplace_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** CANARY: two surface-form [TruncLaplace #A #num #den #loc #()] draws couple
      to EQUAL outputs, at multiplicative cost [s·(num/den)] and additive cost
      [tlap_delta A num den loc s] — driven entirely by the [couple_trunc_laplace]
      tactic.  Stated over the [TruncLaplace] notation (i.e. [expr], with the
      un-reduced nested [Pair] param) so it exercises the surface path a program
      takes; the THREE resources (spec [⤇], multiplicative [↯m] and additive [↯])
      are threaded by the 3-way pattern, demonstrating the δ-carrying convenience
      layer end to end.  The regime side-conditions [0 ≤ A] and [0 ≤ s ≤ A] are
      passed as hypotheses and closed by the tactic via [assumption]/[lia]. *)
  Lemma wp_trunc_laplace_shift_canary (A loc s num den : Z)
    (HA : (0 <= A)%Z)
    (Hs : (Z.abs s <= A)%Z)
    (Hpos : 0 < IZR num / IZR den) K E :
    {{{ ⤇ fill K (TruncLaplace #A #num #den #(loc + s) #())
        ∗ ↯m (IZR (Z.abs s) * (IZR num / IZR den))
        ∗ ↯ (tlap_delta A num den loc s) }}}
      TruncLaplace #A #num #den #loc #() @ E
      {{{ (z : Z), RET #z; ⤇ fill K #z }}}.
  Proof.
    (* destructure the bundled 3-resource precondition first, so the spec [⤇] is a
       standalone hypothesis for the [tp_pures]/[tp_bind] inside the tactic. *)
    iIntros (Φ) "(Hr & Hε & Hδ) HΦ".
    couple_trunc_laplace A s with "[$Hr $Hε $Hδ]".
    iApply "HΦ".
  Qed.

  (** CANARY for the NO-EAGER-FRAME [couple_trunc_laplace_cost]: identical
      statement, but BOTH credits are ROUTED (unframed [Hε]/[Hδ], pattern
      [\"[$Hr Hε Hδ]\"]) into their residual [↯m (s·ε)] / [↯ δ'] goals rather than
      [$]-framed.  Here the costs are exact so the residual goals are closed by
      simply re-framing [Hε]/[Hδ]; a real cost-reconciliation site would instead
      run [iApply ecm_eq; …] / [iApply ecm_weaken; …] there.  Exercises that
      [couple_trunc_laplace_cost] elaborates, auto-discharges the regime/equational
      side-conditions, and leaves the two credit goals clean. *)
  Lemma wp_trunc_laplace_shift_canary_cost (A loc s num den : Z)
    (HA : (0 <= A)%Z)
    (Hs : (Z.abs s <= A)%Z)
    (Hpos : 0 < IZR num / IZR den) K E :
    {{{ ⤇ fill K (TruncLaplace #A #num #den #(loc + s) #())
        ∗ ↯m (IZR (Z.abs s) * (IZR num / IZR den))
        ∗ ↯ (tlap_delta A num den loc s) }}}
      TruncLaplace #A #num #den #loc #() @ E
      {{{ (z : Z), RET #z; ⤇ fill K #z }}}.
  Proof.
    iIntros (Φ) "(Hr & Hε & Hδ) HΦ".
    couple_trunc_laplace_cost A s with "[$Hr Hε Hδ]".
    (* residual combined credit goal [↯m (s·ε) ∗ ↯ δ'] — closed here by re-framing
       the routed [Hε]/[Hδ] (exact cost); a non-exact site would [iApply ecm_*]. *)
    2: iApply "HΦ".
    iFrame "Hε Hδ".
  Qed.

  (** CANARY for the APPLY-ONLY [couple_trunc_laplace_apply]: identical
      statement, but the caller does the [wp_bind]/[tp_bind] MANUALLY (mimicking
      an interleaved site) before calling the apply-only tactic — exercising
      that [couple_trunc_laplace_apply] does NOT itself re-bind the [Sample] and
      works once the caller has focused both sides.  BOTH credits are ROUTED
      (unframed [Hε]/[Hδ], pattern [\"[$Hr Hε Hδ]\"]) into their residual goals;
      here the costs are exact so the residuals are closed by re-framing. *)
  Lemma wp_trunc_laplace_shift_canary_apply (A loc s num den : Z)
    (HA : (0 <= A)%Z)
    (Hs : (Z.abs s <= A)%Z)
    (Hpos : 0 < IZR num / IZR den) K E :
    {{{ ⤇ fill K (TruncLaplace #A #num #den #(loc + s) #())
        ∗ ↯m (IZR (Z.abs s) * (IZR num / IZR den))
        ∗ ↯ (tlap_delta A num den loc s) }}}
      TruncLaplace #A #num #den #loc #() @ E
      {{{ (z : Z), RET #z; ⤇ fill K #z }}}.
  Proof.
    iIntros (Φ) "(Hr & Hε & Hδ) HΦ".
    (* MANUAL bind on both sides — the interleaved-site idiom the apply-only
       tactic supports (and where setup could be interposed here) *)
    wp_pures. tp_pures.
    wp_bind (Sample _ _ _). tp_bind (Sample _ _ _).
    couple_trunc_laplace_apply A s with "[$Hr Hε Hδ]".
    (* residual combined credit goal [↯m (s·ε) ∗ ↯ δ'] — closed here by re-framing
       the routed [Hε]/[Hδ] (exact cost); a non-exact site would [iApply ecm_*]. *)
    2: iApply "HΦ".
    iFrame "Hε Hδ".
  Qed.

End trunc_laplace_canary.
