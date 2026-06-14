(** FLAGSHIP MULTI-NOISE SHOWCASE: a SELECT-THEN-MEASURE differentially-private
    mechanism that uses TWO noise families in ONE signature.

    The canonical select-then-measure pipeline:
      (1) SELECTION   — report-noisy-max with ONE-SIDED EXPONENTIAL noise
                        ([report_noisy_max_exp]) privately picks the index [i]
                        of the best-scoring candidate over [evalQ]'s [N] scores;
      (2) MEASUREMENT — the selected candidate's true score [evalQ i ds] is then
                        released through the TRUNCATED discrete Laplace mechanism
                        ([lib.trunc_laplace]).

    This is the load-bearing demonstration that the gen stack supports
    MULTI-NOISE pipelines: the program runs over a SINGLE language instance whose
    signature [Sg] carries BOTH noise families simultaneously —
      [Context {Sg : Sig} `{!SampleIn exp_family Sg} `{!SampleIn trunc_laplace_family Sg}]
    — and we compose the privacy of the exp-RNM selection (reused VERBATIM as a
    black box, via [rnm_exp_pres_diffpriv]) with the privacy of the truncated
    Laplace measurement (via the [couple_trunc_laplace] tactic) by the
    postprocessing/sequential-composition discipline: the selection RELEASES an
    index that is EQUAL on the two adjacent runs, after which the adaptive
    measurement on the selected query is coupled to equal outputs.

    REUSED THEOREMS (privacy NOT re-derived here):
      - [report_noisy_max_exp.rnm_exp_pres_diffpriv]  (exp-RNM selection privacy)
      - [trunc_laplace.wp_couple_trunc_laplace] / the [couple_trunc_laplace] tactic
        (truncated-Laplace measurement coupling). *)
From clutch.prob Require Import differential_privacy trunc_laplace.
From clutch.gen_diffpriv Require Import adequacy all.
From clutch.gen_diffpriv.lib Require Import trunc_laplace.
From clutch.gen_prob_lang Require Import gwp.list inject families.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_exp report_noisy_max_generic.
From iris.prelude Require Import options.

Local Open Scope R.

Section select_then_measure.
  (* The two-noise signature: ONE language instance, BOTH the exponential noise
     (for the selection) AND the truncated Laplace (for the measurement). *)
  Context {Sg : Sig}
          `{!SampleIn exp_family Sg}
          `{!SampleIn trunc_laplace_family Sg}
          `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** The select-then-measure program.  [evalQ] is the query evaluator
      ([evalQ i ds] = the score/value of candidate [i] on database [ds]); the
      selection parameters [(num, den, N)] feed the exp-RNM; the measurement
      parameters [(A, num', den')] feed the truncated Laplace. *)
  Definition select_then_measure
    (evalQ : val) (N num den A num' den' : Z) : val :=
    λ: "ds",
      let: "i" := report_noisy_max_exp_presampling num den evalQ #N "ds" in
      let: "v" := evalQ "i" "ds" in
      let: "noisy_v" := TruncLaplace #A #num' #den' "v" #() in
      ("i", "noisy_v").

  (** Forward-monotone Δ-sensitivity of the per-candidate query, IN the adjacency
      direction.  For inputs at distance [dDB db db' <= IZR C], evaluating the
      selected candidate [i] yields scores [v] (on [db]) and [v'] (on [db'])
      whose forward gap [v' - v] is NONNEGATIVE and bounded by [Δ·C].  This is the
      honest regime hypothesis matching the FORWARD scope of the truncated-Laplace
      coupling ([trunc_laplace.v]'s proven [0 ≤ s ≤ A] direction): it holds for the
      common class of monotone queries (e.g. counts that only grow when a record
      is added). *)
  Definition query_fwd_sensitive
    (evalQ : val) (Δ C : Z) DB (dDB : Distance DB) : iProp Σ :=
    ∀ (iv : val) K (db db' : DB),
      ⌜dDB db db' <= IZR C⌝ -∗
      {{{ ⤇ fill K (evalQ iv (Val (inject db'))) }}}
        evalQ iv (Val (inject db))
      {{{ (v : Z), RET (#v); ∃ v' : Z,
            ⤇ fill K (Val #v') ∗ ⌜(0 <= v' - v)%Z⌝ ∗ ⌜(v' - v <= Δ * C)%Z⌝ }}}.

  (** ** Privacy of select-then-measure (WP-refinement form).

      At adjacency [dDB db db' <= IZR C], the impl run on [db] and the spec run on
      [db'] couple to EQUAL outputs (the released pair [(i, noisy_v)] is the same
      on both sides), at COMBINED multiplicative budget
        selection: [C·(Δ·(num/den))]  +  measurement: [(Δ·C)·(num'/den')]
      and additive budget = the measurement's group-bound mass
        [tlap_del A num' den' · grp (num'/den') (Δ·C)].

      The two-noise composition is the postprocessing/sequential discipline: the
      exp-RNM SELECTION releases an index that the coupling forces to be IDENTICAL
      on both runs, so the adaptive MEASUREMENT — which depends on that index and
      the database — runs on the same candidate on both sides and is coupled by the
      truncated Laplace.  Selection privacy is the BLACK BOX
      [rnm_exp_pres_diffpriv]; measurement privacy is [couple_trunc_laplace]. *)
  Lemma select_then_measure_diffpriv
    (Δ C : Z) (num den A num' den' : Z) (N : nat) (evalQ : val)
    DB (dDB : Distance DB) (db db' : DB) K :
    (1 <= Δ)%Z →
    (1 <= C)%Z →
    (0 <= A)%Z →
    (Δ * C <= A)%Z →
    (0 < IZR num / IZR (2 * den))%R →
    (0 < IZR num' / IZR den')%R →
    (∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) →
    (dDB db db' <= IZR C)%R →
    query_fwd_sensitive evalQ Δ C DB dDB -∗
    {{{ ↯m (IZR C * (IZR Δ * (IZR num / IZR den)))
        ∗ ↯m (IZR (Δ * C) * (IZR num' / IZR den'))
        ∗ ↯ (tlap_del A num' den' * grp (IZR num' / IZR den') (IZR (Δ * C)))
        ∗ ⤇ fill K (select_then_measure evalQ N num den A num' den' (Val (inject db'))) }}}
      select_then_measure evalQ N num den A num' den' (Val (inject db))
    {{{ (out : val), RET out; ∃ (out' : val), ⤇ fill K out' ∗ ⌜out = out'⌝ }}}.
  Proof.
    iIntros (HΔ HC HA HΔCA Hposnum Hposnum' Hsens Hadj) "#Hqfwd".
    iIntros (Φ) "!# (εsel & εmeas & δmeas & rhs) HΦ".
    rewrite /select_then_measure.
    wp_pures. tp_pures.
    (* ---- (1) SELECTION: exp report-noisy-max, reused as a BLACK BOX. ----
       The exp-RNM releases the argmax index; the coupling forces the SAME index
       [vi] on both adjacent runs ([vi = vi']).  This is the postprocessing seam:
       the adaptive measurement that follows runs on the identical candidate. *)
    wp_bind (report_noisy_max_exp_presampling _ _ _ _ _).
    tp_bind (report_noisy_max_exp_presampling _ _ _ _ _).
    iApply (rnm_exp_pres_diffpriv Δ C num den evalQ DB dDB N _
              HΔ HC Hposnum Hsens db db' Hadj with "[$εsel $rhs]").
    iIntros "!>" (vi) "(%vi' & rhs & %Heqi)".
    subst vi'.
    wp_pures. iSimpl in "rhs"; tp_pures.
    (* ---- (2a) Evaluate the selected query on the two databases. ----
       Forward-Δ-sensitivity: the released score [v] (impl) and [v'] (spec) have a
       nonnegative gap [0 ≤ v'-v ≤ Δ·C]. *)
    wp_bind (evalQ _ _). tp_bind (evalQ _ _).
    iApply ("Hqfwd" $! vi _ db db' Hadj with "[$rhs]").
    iIntros "!>" (v) "(%v' & rhs & %Hfwd0 & %Hgap)".
    wp_pures. iSimpl in "rhs"; tp_pures.
    (* ---- (2b) MEASUREMENT: truncated Laplace at the actual forward shift. ----
       [s = v'-v] is the runtime shift; [0 ≤ s ≤ A] (as [s ≤ Δ·C ≤ A]). *)
    set (s := (v' - v)%Z).
    assert (Hs0 : (0 <= s)%Z) by (subst s; lia).
    assert (HsΔC : (s <= Δ * C)%Z) by (subst s; lia).
    assert (HsA : (0 <= s <= A)%Z) by (subst s; lia).
    replace v' with (v + s)%Z by (subst s; lia).
    (* Weaken the supplied measurement credits DOWN from the demanded group bound
       at distance [Δ·C] to the consumed bound at the actual shift [s]:
       multiplicative via [ecm_weaken] ([s ≤ Δ·C]); additive via [ec_weaken] +
       [grp_mono] ([grp ε s ≤ grp ε (Δ·C)]).  Exactly the weakening internal to
       [hoare_trunc_laplace_diffpriv], discharged here at the actual runtime shift. *)
    assert (Hεw : (0 <= IZR s * (IZR num' / IZR den')
                   <= IZR (Δ * C) * (IZR num' / IZR den'))%R)
      by (split; [apply Rmult_le_pos; [apply IZR_le; lia | lra]
                 | apply Rmult_le_compat_r; [lra | apply IZR_le; lia]]).
    assert (Hδw : (0 <= trunc_laplace.tlap_delta A num' den' v s
                   <= tlap_del A num' den' * grp (IZR num' / IZR den') (IZR (Δ * C)))%R)
      by (rewrite tlap_delta_grp; split;
          [ apply Rmult_le_pos;
            [ rewrite /tlap_del; apply Rcomplements.Rdiv_le_0_compat;
              [left; apply exp_pos | apply (clutch.prob.trunc_laplace.tlap_Z_pos A num' den' 0 HA)]
            | apply grp_nonneg; [lra | apply IZR_le; lia] ]
          | apply Rmult_le_compat_l;
            [ rewrite /tlap_del; apply Rcomplements.Rdiv_le_0_compat;
              [left; apply exp_pos | apply (clutch.prob.trunc_laplace.tlap_Z_pos A num' den' 0 HA)]
            | apply grp_mono; [lra | apply IZR_le; lia | apply IZR_le; lia] ] ]).
    iDestruct (ecm_weaken _ _ Hεw with "εmeas") as "εm".
    iDestruct (ec_weaken _ _ Hδw with "δmeas") as "δm".
    (* Couple the two truncated-Laplace draws to EQUAL outputs (the ergonomic
       [couple_trunc_laplace] tactic), at the forward shift [s]. *)
    couple_trunc_laplace A s with "[$rhs $εm $δm]".
    iIntros "!>" (z) "rhs".
    (* reduce the SPEC let first (while the impl WP is still live), then the impl *)
    iSimpl in "rhs". tp_pures.
    wp_pures.
    (* both runs release the identical pair [(vi, #z)] *)
    iApply "HΦ". iExists (vi, #z)%V. iFrame. done.
  Qed.

End select_then_measure.
