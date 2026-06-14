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

    The whole pipeline is stated as the internal-DP notion
    [hoare_diffpriv_classic_at]: a single program, an adjacency RADIUS [C], a
    combined multiplicative budget and the measurement's additive group mass.

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

  (** ** Privacy of select-then-measure (internal-DP, [hoare_diffpriv_classic_at]).

      For databases at adjacency [dDB db db' <= IZR C], the impl run on [db] and
      the spec run on [db'] couple to EQUAL outputs (the released pair
      [(i, noisy_v)] — index [i] and noisy score — is the same on both sides), at
      COMBINED multiplicative budget
        [eps = IZR (Δ*C) · (num/den + num'/den')]
      (the selection's [IZR C·(IZR Δ·(num/den))] plus the measurement's
      [IZR (Δ*C)·(num'/den')]) and additive budget = the measurement's group-bound
      mass [tlap_del A num' den' · grp (num'/den') (IZR (Δ*C))].

      The per-candidate Δ-sensitivity is supplied ONCE, as the [hoare_sensitive]
      hypothesis [Hsens]; it drives BOTH the selection (handed to the exp-RNM
      black box) AND the measurement (instantiated at the selected index to bound
      the runtime shift).

      The two-noise composition is the postprocessing/sequential discipline: the
      exp-RNM SELECTION releases an index that the coupling forces to be IDENTICAL
      on both runs, so the adaptive MEASUREMENT — which depends on that index and
      the database — runs on the same candidate on both sides and is coupled by the
      truncated Laplace.  Selection privacy is the BLACK BOX
      [rnm_exp_pres_diffpriv]; measurement privacy is [couple_trunc_laplace]. *)
  Lemma select_then_measure_diffpriv
    (Δ C : Z) (num den A num' den' : Z) (N : nat) (evalQ : val)
    DB (dDB : Distance DB) :
    (1 <= Δ)%Z →
    (1 <= C)%Z →
    (0 <= A)%Z →
    (0 < IZR num / IZR (2 * den))%R →
    (0 < IZR num' / IZR den')%R →
    (∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) →
    ⊢ hoare_diffpriv_classic_at Sg (select_then_measure evalQ N num den A num' den')
        (IZR (Δ * C) * (IZR num / IZR den + IZR num' / IZR den'))
        (tlap_del A num' den' * grp (IZR num' / IZR den') (IZR (Δ * C)))
        (IZR C) dDB (fin (Nat.max 1 N) * Z)%type.
  Proof.
    iIntros (HΔ HC HA Hposnum Hposnum' Hsens).
    rewrite /hoare_diffpriv_classic_at.
    iIntros (K db db') "%Hadj".
    iIntros (Φ) "!# (rhs & ε & δmeas) HΦ".
    (* Split the combined multiplicative budget into the SELECTION credit and the
       MEASUREMENT credit, distributing the product over the sum and reconciling
       [IZR (Δ*C)·(num/den) = IZR C·(IZR Δ·(num/den))]. *)
    set (εsel := (IZR C * (IZR Δ * (IZR num / IZR den)))%R).
    set (εmeas := (IZR (Δ * C) * (IZR num' / IZR den'))%R).
    (* [0 < num/den]: from [0 < num/(2·den)], note [num/den = 2·(num/(2·den))]
       (the denominator [2·den ≠ 0], else the strictly-positive quotient is 0). *)
    assert (Hd2 : (IZR (2 * den) ≠ 0)%R).
    { intros Heq. rewrite Heq Rdiv_def Rinv_0 Rmult_0_r in Hposnum. lra. }
    assert (Hnd : (0 < IZR num / IZR den)%R).
    { rewrite (_ : (IZR num / IZR den = 2 * (IZR num / IZR (2 * den)))%R).
      - lra.
      - rewrite mult_IZR. rewrite mult_IZR in Hd2. field.
        intros Hd; rewrite Hd in Hd2; lra. }
    assert (HεselP : (0 <= εsel)%R).
    { subst εsel. apply Rmult_le_pos; [apply IZR_le; lia|].
      apply Rmult_le_pos; [apply IZR_le; lia| lra]. }
    assert (HεmeasP : (0 <= εmeas)%R).
    { subst εmeas. apply Rmult_le_pos; [apply IZR_le; lia| apply Rlt_le; exact Hposnum']. }
    assert (Heps : (IZR (Δ * C) * (IZR num / IZR den + IZR num' / IZR den')
                    = εsel + εmeas)%R).
    { subst εsel εmeas. rewrite Rmult_plus_distr_l mult_IZR. lra. }
    rewrite Heps.
    iDestruct (ecm_split _ _ HεselP HεmeasP with "ε") as "[εsel εmeas]".
    rewrite /select_then_measure.
    wp_pures. tp_pures.
    (* ---- (1) SELECTION: exp report-noisy-max, reused as a BLACK BOX. ----
       The exp-RNM releases the argmax index; the coupling forces the SAME index
       on both adjacent runs (both runs release [inject y] for the SAME
       [y : fin (Nat.max 1 N)]).  This is the postprocessing seam: the adaptive
       measurement that follows runs on the identical candidate. *)
    wp_bind (report_noisy_max_exp_presampling _ _ _ _ _).
    tp_bind (report_noisy_max_exp_presampling _ _ _ _ _).
    iPoseProof (rnm_exp_pres_diffpriv Δ C num den evalQ DB dDB N
                  HΔ HC Hposnum Hsens) as "Hrnm".
    rewrite /hoare_diffpriv_classic_at.
    iMod ec_zero as "δ0".
    iApply ("Hrnm" $! _ db db' Hadj with "[$rhs $εsel $δ0]").
    iIntros "!>" (y) "rhs".
    (* Both runs released the SAME index [inject y = #(Z.of_nat (fin_to_nat y))].
       Set [i := Z.of_nat (fin_to_nat y)] — the index the measurement is taken at. *)
    set (i := Z.of_nat (fin_to_nat y)).
    wp_pures. iSimpl in "rhs"; tp_pures.
    (* ---- (2a) Evaluate the selected query on the two databases. ----
       Plain Δ-sensitivity at the selected index [i]: the released score [v]
       (impl) and [v'] (spec) satisfy [dZ v v' <= IZR Δ · dDB db db'], hence with
       [dDB db db' <= IZR C] the absolute gap [|v'-v| ≤ Δ·C] — NO sign restriction. *)
    wp_bind (evalQ _ _). tp_bind (evalQ _ _).
    assert (HΔpos : (0 <= IZR Δ)%R) by (apply IZR_le; lia).
    iPoseProof (Hsens i) as "Hs".
    iApply ("Hs" $! HΔpos _ db db' with "[$rhs]").
    iIntros "!>" (vv) "(%v & %v' & -> & rhs & %Hd)".
    (* Convert the [dZ]-bound into the [Z.abs] form the truncated-Laplace step
       wants: [dZ v v' = Rabs (IZR (v - v'))] and [IZR Δ · dDB db db' ≤ IZR (Δ*C)]. *)
    assert (Hgap : (Z.abs (v' - v) <= Δ * C)%Z).
    { assert (Hbnd : (dZ v v' <= IZR (Δ * C))%R).
      { apply Rle_trans with (r2 := (IZR Δ * dDB db db')%R); first exact Hd.
        rewrite mult_IZR. apply Rmult_le_compat_l; [apply IZR_le; lia| exact Hadj]. }
      pose proof (dZ_bounded_cases v v' (Δ * C) Hbnd) as [Hlo Hhi].
      apply Z.abs_le; lia. }
    wp_pures. iSimpl in "rhs"; tp_pures.
    (* ---- (2b) MEASUREMENT: truncated Laplace at the actual (signed) shift. ----
       [s = v'-v] is the runtime shift of EITHER sign; only [|s| ≤ Δ·C] matters.
       A no longer bounds the shift (the truncated-Laplace redesign decoupled the
       shift from the width A; A enters only through the additive [tlap_del] base).
       The two-sided coupling is unconditional in the shift and carries the |·| cost. *)
    set (s := (v' - v)%Z).
    assert (HsΔC : (Z.abs s <= Δ * C)%Z) by (subst s; lia).
    replace v' with (v + s)%Z by (subst s; lia).
    (* Weaken the supplied measurement credits DOWN from the demanded group bound
       at distance [Δ·C] to the consumed bound at the actual |shift| [|s|]:
       multiplicative via [ecm_weaken] ([|s| ≤ Δ·C]); additive via [ec_weaken] +
       [grp_mono] ([grp ε |s| ≤ grp ε (Δ·C)]).  Exactly the weakening internal to
       [hoare_trunc_laplace_diffpriv], discharged here at the actual runtime shift. *)
    assert (Hεw : (0 <= IZR (Z.abs s) * (IZR num' / IZR den')
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
       [couple_trunc_laplace] tactic), at the two-sided shift [s]. *)
    couple_trunc_laplace A s with "[$rhs $εm $δm]".
    iIntros "!>" (z) "rhs".
    (* reduce the SPEC let first (while the impl WP is still live), then the impl *)
    iSimpl in "rhs". tp_pures.
    wp_pures.
    (* both runs release the identical pair [(y, z)] : [fin (Nat.max 1 N) * Z];
       [inject (y,z) = PairV (inject y) #z] matches the program's returned pair. *)
    iApply ("HΦ" $! (y, z)). simpl. iExact "rhs".
  Qed.

End select_then_measure.
