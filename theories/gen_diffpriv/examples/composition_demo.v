(** MULTI-RELEASE composition demo: a natural "release two noisy statistics"
    program proved differentially private by ASSEMBLING the three OPEN composition
    laws of [gen_diffpriv.diffpriv_rules] — sens∘dp, adaptive dp-seq, and
    post-processing — as a SYSTEM.

    THE PROGRAM.  The textbook dp-seq use case: release two noisy counts of a
    dataset under a SINGLE shared adjacency budget, then return the pair.

      multi_release P1 P2 num den :=
        λ: "ds",
          let: "c1" := Laplace #num #den (list_count P1 "ds") #() in  (* release 1 *)
          let: "c2" := Laplace #num #den (list_count P2 "ds") #() in  (* release 2 *)
          ("c1", "c2").                                                (* pairing  *)

    [list_count P] = [list_length ∘ list_filter P] is 1-sensitive (reused from
    [privacy_filter]'s [count_sens]); each noisy count is [(num/den)]-DP by the
    SENS∘DP law; the two releases compose by ADAPTIVE DP-SEQ to [(2·num/den, 0)];
    and the final deterministic pairing is absorbed by POST-PROCESSING.

    THE THEOREM.  [hoare_diffpriv_metric Sg (multi_release …) (2·(num/den)) 0
    (dlist Z) (Z*Z)] at adjacency, over a signature with [laplace_family].

    HOW THE LAWS COMPOSE (the validation point — these laws COMPILE but were not
    previously exercised by any case study; auto_avg's pre-split-credit structure
    could not drive the SINGLE-shared-budget dp-seq).  We write
    [multi_release ds = G (F ds) ds] with [F] = release 1, [G] = the curried
    continuation [λ c1 ds, let c2 := release2 ds in (c1,c2)] — exactly the
    [g (f a) a] shape of the adaptive seq law.  The three discriminating roles:

      - SENS∘DP — [diffpriv_metric_sensitive_comp_at], THE load-bearing law here.
        Each noisy count is [list_count P] (1-sensitive, by [count_sens]) ∘ the
        [(num/den)]-DP Laplace mechanism ([hoare_laplace_diffpriv]); the composite
        is [(1·(num/den)) = (num/den)]-DP.  This law is [iApply]'d THREE times:
        twice in [multi_release_diffpriv] (release 1 and release 2) and once in
        [cont_release_diffpriv]; plus [noisy_count_diffpriv] packages it via
        [count_query_diffpriv] (the reified sens∘dp).

      - ADAPTIVE DP-SEQ — composing [F] (εf = num/den) with the continuation [G c1]
        (εg = num/den) under the SINGLE adjacency budget [c]: the budgets ADD to
        [(2·num/den, 0)].  GENUINELY load-bearing: the proof splits the one
        adjacency credit [c·(2·num/den)] into two [c·(num/den)] halves
        ([ecm_split]) — one per release — exactly the regime auto_avg's pre-split
        credits could not exercise.  [dlist Z] would supply the named law's
        [dA_nat] hypothesis (its distance is [IZR (list_dist xs ys)] with
        [list_dist] a nonneg [Z], hence equals some [INR n]).

      - POST-PROCESSING — the trailing deterministic pairing [λ c2, (c1,c2)]: once
        [c1=c1'] and [c2=c2'] are coupled, the pair is returned identically on both
        runs for NO extra budget (the release → postproc ⟹ release collapse).
        [cont_release_diffpriv] packages exactly this — release 2 then the pairing —
        as one [(num/den)]-DP release, the per-value [G]-obligation dp-seq consumes.

    HONEST SCOPING (the experiment's finding).  The named OPEN lemmas
    [diffpriv_metric_seq_comp_at] / [diffpriv_metric_postprocess_at] could NOT be
    [iApply]'d at this program: their conclusions are Texan triples about the bare
    [g (f (inject x)) (inject x)] / [g (f (inject x))], and landing the goal on
    that EXACT folded shape is blocked — the program-step tactics cannot fire the
    [multi_release]/[cont_release] wrapper β over an *abstract list-valued*
    [inject ds] (the internal [simpl] mangles [inject_list ds] into a stuck
    [match]; the greedy [wp_pures] over-reduces THROUGH the [noisy_count] release;
    and object-level β is not Coq conversion, so [change]/[iApply] cannot bridge
    it either).  The dp-seq budget-split and the postprocessing pairing are
    therefore realized INLINE (mirroring the named laws' own proofs), while the
    SENS∘DP releases they sequence ARE driven by the named
    [diffpriv_metric_sensitive_comp_at].  [cont_release_diffpriv] /
    [noisy_count_diffpriv] below ARE the packaged seq/postproc sub-obligations,
    proved standalone. *)
From iris.base_logic Require Export na_invariants.
From clutch.prelude Require Import tactics.
From clutch.common Require Import inject.
From clutch.prob Require Import differential_privacy.
From clutch.gen_diffpriv Require Import adequacy all.
From clutch.gen_diffpriv.lib Require Import laplace.
From clutch.gen_prob_lang Require Import inject families.
From clutch.gen_prob_lang.spec Require Import spec_ra spec_rules.
From clutch.gen_diffpriv.examples Require Import privacy_filter.
From clutch.gen_prob_lang.gwp Require Import gen_weakestpre arith list.
From iris.prelude Require Import options.

(** Keep the family index [sample_idx] folded so the [Laplace] surface notation
    matches the library coupling rules syntactically (cf. [privacy_filter]). *)
#[global] Opaque sample_idx.

#[local] Open Scope R.

(** The [Laplace] surface notation desugars to [Sample sample_idx …] with
    [sample_idx] depending on the signature [Sg] and its [SampleIn laplace_family
    Sg] instance, so — like the [privacy_filter]/[sum_queries] originals — the
    program definitions are NOT closed [val]s and must live in a section carrying
    [Sg]. *)
Section laplace_programs.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg}.

  (** A noisy-count RELEASE as a bare composite [g_lap (query ds)] — the Laplace
      mechanism closure post-composing the [list_count] query.  This is precisely
      the term [count_query_diffpriv] proves [(num/den)]-DP (sens∘dp), and is the
      [f] of the seq law / the [f] of the postprocess law.

      KEY: the OUTER lambda is an [expr] ([Rec], NO [%V]), matching
      [count_query_diffpriv]'s conclusion EXACTLY — a closed [val] would coerce to
      [Val (RecV …)], a distinct AST node that does NOT unify (the val-vs-Rec
      seam, cf. [sum_queries]'s [%E] helpers).  It is still applied as a function
      inside [multi_release] (an [expr] applied to an arg is fine). *)
  Definition noisy_count (vP : val) (num den : Z) : expr :=
    (λ:"x", (λ:"loc", Laplace #num #den "loc" #())%V
              ((λ:"x", privacy_filter.list_count vP "x")%V "x")).

  (** The continuation [G] of the adaptive dp-seq: given the first release [c1]
      and the dataset [ds], do the SECOND release and pair.  [multi_release ds] is
      then literally [G (noisy_count P1 num den ds) ds] — the [g (f a) a] shape.
      An [expr] (same val-vs-Rec discipline as [noisy_count]): its outer lambdas
      are [Rec]s so the seq/postprocess laws' [g] unifies and the betas reduce
      cleanly. *)
  Definition cont_release (vP2 : val) (num den : Z) : expr :=
    (λ:"c1" "ds", let: "c2" := noisy_count vP2 num den "ds" in ("c1", "c2")).

  (** The whole program: [G (F ds) ds].  An [expr] for the same reason. *)
  Definition multi_release (vP1 vP2 : val) (num den : Z) : expr :=
    (λ:"ds", cont_release vP2 num den (noisy_count vP1 num den "ds") "ds").

End laplace_programs.

(** Keep the dataset injection and the three program wrappers out of [simpl]'s
    reach: [wp_pure]/[tp_pure] run [simpl] on the focused expression, and [simpl]
    would otherwise turn the abstract [inject_list ds] argument into a stuck
    [match ds with …] (so the wrapper β no longer has a syntactic-value argument
    and will NOT fire), and would dissolve the [noisy_count]/[cont_release]
    releases past the point the composition laws match.  [simpl never] makes the
    single-step [wp_pure]/[tp_pure] fire EXACTLY the intended outer β and stop. *)
Arguments inject_list : simpl never.
Arguments noisy_count : simpl never.
Arguments cont_release : simpl never.
Arguments multi_release : simpl never.

Section composition_demo.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** A predicate value [vP] decides [P] on both the impl and the spec side — the
      hypotheses [count_query_diffpriv] needs to make a noisy count [(num/den)]-DP. *)
  Definition decides_pred (P : Z → bool) (vP : val) : iProp Σ :=
    (∀ x : Z, {{{ True }}} vP (inject x) {{{ w, RET w; ⌜w = inject (P x)⌝ }}}) ∗
    (∀ x : Z, G{{{ True }}} vP (inject x) @ gwp_spec (Sg:=Sg) ; ⊤ {{{ w, RET w; ⌜w = inject (P x)⌝ }}}).

  (** SENS∘DP, packaged.  A single noisy count [noisy_count vP num den] is
      [(num/den)]-DP releasing a [Z].  This is the standalone sens∘dp composition
      ([list_count] 1-sensitive ∘ Laplace mechanism), obtained from
      [count_query_diffpriv].  It is the [f]-obligation of the dp-seq law and the
      [f]-obligation inside the post-processing law. *)
  Lemma noisy_count_diffpriv (P : Z → bool) (vP : val) (num den : Z) :
    (0 < IZR num / IZR den)%R →
    decides_pred P vP -∗
    hoare_diffpriv_metric Sg (noisy_count vP num den) (IZR num / IZR den) 0 (dlist Z) Z.
  Proof.
    iIntros (Hpos) "[#Hf #Hf']".
    iApply (count_query_diffpriv P vP num den Hpos with "Hf Hf'").
  Qed.

  (** POST-PROCESSING-COLLAPSE (the per-value [G]-obligation of dp-seq).  The
      continuation [cont_release vP2 num den] applied to a first release [c1] is
      the SECOND noisy count, then the deterministic pairing [λ c2, (c1, c2)].
      Its DP is the release → postproc ⟹ release collapse: the noisy count is
      [(num/den)]-DP (SENS∘DP, via [diffpriv_metric_sensitive_comp_at] — couples
      [c2=c2']), and the trailing pairing is FREE (deterministic, identical on both
      coupled runs).  So [cont_release vP2 num den (inject c1)] is [(num/den)]-DP —
      exactly the per-value [hoare_diffpriv_metric (g (inject b)) εg δg] obligation
      the dp-seq law demands.  (The named [diffpriv_metric_postprocess_at] is not
      [iApply]'d here — its bare [g (f (inject x))] shape is unreachable by the
      step tactics, see the file header — so the pairing is collapsed inline; the
      noisy-count release it sits on top of IS the named SENS∘DP law.) *)
  Lemma cont_release_diffpriv (P2 : Z → bool) (vP2 : val) (num den : Z) (c1 : Z) :
    (0 < IZR num / IZR den)%R →
    decides_pred P2 vP2 -∗
    hoare_diffpriv_metric Sg
      (cont_release vP2 num den (Val (inject c1)))
      (IZR num / IZR den) 0 (dlist Z) (Z * Z)%type.
  Proof.
    iIntros (Hpos) "[#Hf #Hf']".
    rewrite /hoare_diffpriv_metric.
    iIntros (K c ds ds' Hadj Φ) "!> (Hrhs & ε & δ) HΦ".
    (* Expose the continuation body on both sides: [cont_release … (inject c1)
       (inject ds)] reduces to [let: "c2" := <release2> in (#c1, "c2")] with
       [<release2> = (λ loc, Laplace …) (list_count vP2 (inject ds))] — the bare
       SENS∘DP composite (the [noisy_count] release).  ([tp_pures]/[wp_pures]
       reduce symmetrically here because the dataset metric makes the wrappers
       fire; the residual [Sample] is the only impure head.) *)
    rewrite /cont_release /noisy_count. tp_pures; wp_pures.
    (* RELEASE 2 via SENS∘DP: focus the bare composite
       [(λ loc, Laplace …) (list_count vP2 (inject ds))] and apply the open
       sens∘dp law — [list_count vP2] is 1-sensitive ([count_sens]) and the
       Laplace mechanism is [(num/den)]-DP ([hoare_laplace_diffpriv]); their
       composite is [(1·(num/den)) = (num/den)]-DP.  This couples [c2 = c2']. *)
    tp_bind ((λ: "loc", Laplace #num #den "loc" #())%V (privacy_filter.list_count vP2 _)).
    wp_bind ((λ: "loc", Laplace #num #den "loc" #())%V (privacy_filter.list_count vP2 _)).
    iApply (diffpriv_metric_sensitive_comp_at Sg
              (privacy_filter.list_count vP2)
              (λ: "loc", Laplace #num #den "loc" #())%V
              (IZR num / IZR den) 0 1 (dlist Z) dZ (C := Z) Hpos Rlt_0_1
              _ c ds ds' Hadj
              with "[] [] [Hrhs ε δ]").
    { iApply (count_sens P2 vP2 with "Hf Hf'"). }
    { iApply (hoare_laplace_diffpriv num den). iPureIntro. exact Hpos. }
    { (* credit reconciliation: [1·c·eps = c·eps] and [0·grp … = 0] *)
      iFrame "Hrhs". iSplitL "ε".
      - iApply (ecm_eq with "ε"). lra.
      - iApply (ec_eq with "δ"). lra. }
    (* POST-PROCESSING (the deterministic pairing): now that [c2 = c2'] is coupled,
       run the trailing [λ c2, (#c1, c2)] identically on both sides — no budget,
       the postprocessing-collapse content. *)
    iIntros "!>" (c2) "Hrhs". simpl. tp_pures; wp_pures.
    iApply ("HΦ" $! (c1, c2)). iExact "Hrhs".
  Qed.

  (** THE PRIVACY THEOREM.

      [multi_release vP1 vP2 num den] is [(2·(num/den), 0)]-DP from the dataset
      metric [dlist Z] to the product release [Z*Z], at adjacency.

      The composition, as a SYSTEM (the [F]/[G] sub-obligations are exactly
      [noisy_count_diffpriv] / [cont_release_diffpriv] above):
        - ADAPTIVE DP-SEQ: split the SINGLE adjacency credit [c·(2·num/den)] into
          two [c·(num/den)] halves ([ecm_split]) — one per release — and sequence
          release 1 with the continuation [G c1].  Budgets ADD to [(2·num/den, 0)].
        - SENS∘DP (named [diffpriv_metric_sensitive_comp_at]): release 1 and
          release 2 are each [list_count] (1-sensitive, [count_sens]) ∘ Laplace
          ([hoare_laplace_diffpriv]), [(num/den)]-DP; couples [c1=c1'], [c2=c2'].
        - POST-PROCESSING: the trailing pairing [(c1,c2)] is returned identically
          on the coupled runs — no extra budget.

      dp-seq is GENUINELY load-bearing — it is the budget SPLIT across the two
      releases under one shared adjacency budget, the regime auto_avg's pre-split
      credits could not exercise.  See the file header for why the named dp-seq /
      postprocessing *lemmas* are realized inline (mirroring their own proofs)
      rather than [iApply]'d, while the SENS∘DP *lemma* IS applied directly. *)
  Theorem multi_release_diffpriv
    (P1 P2 : Z → bool) (vP1 vP2 : val) (num den : Z) :
    (0 < IZR num / IZR den)%R →
    decides_pred P1 vP1 -∗
    decides_pred P2 vP2 -∗
    hoare_diffpriv_metric Sg
      (multi_release vP1 vP2 num den)
      (2 * (IZR num / IZR den)) 0 (dlist Z) (Z * Z)%type.
  Proof.
    iIntros (Hpos) "[#Hf1 #Hf1'] #Hp2".
    rewrite /hoare_diffpriv_metric.
    iIntros (K c ds ds' Hadj Φ) "!> (Hrhs & ε & δ) HΦ".
    (* ADAPTIVE DP-SEQ (by hand — see the file header for why the OPEN
       [diffpriv_metric_seq_comp_at] could not be [iApply]'d at the wrapped
       [multi_release] program): split the SINGLE adjacency budget
       [2·(num/den)] into [num/den] (release 1) + [num/den] (the continuation =
       release 2 + pair).  The two halves are paid by [ε1]/[ε2]. *)
    assert (Hc0 : 0 <= c).
    { eapply Rle_trans; [apply (distance_pos (Distance:=dlist Z) ds ds')|exact Hadj]. }
    assert (Hhalf : 0 <= c * (IZR num / IZR den))
      by (apply Rmult_le_pos; [exact Hc0|apply Rlt_le, Hpos]).
    iDestruct (ecm_eq _ (c * (IZR num / IZR den) + c * (IZR num / IZR den)) with "ε")
      as "ε"; [lra|].
    iDestruct (ecm_split (c * (IZR num / IZR den)) (c * (IZR num / IZR den))
                 Hhalf Hhalf with "ε") as "[ε1 ε2]".
    iMod ec_zero as "δ0". iMod ec_zero as "δ0'".
    (* Abstract the dataset injections as opaque values so EVERY wrapper β fires
       cleanly ([wp_pures]'s internal [simpl] would otherwise mangle the literal
       [inject_list ds] into a stuck [match]); [subst] restores the [inject ds]
       form the sens∘dp law builds. *)
    set (dsv := @inject (list Z) val (distance_car (dlist Z)) ds).
    set (dsv' := @inject (list Z) val (distance_car (dlist Z)) ds').
    rewrite /multi_release /cont_release /noisy_count. tp_pures; wp_pures.
    (* RELEASE 1 (SENS∘DP), [(num/den)]-DP: [list_count vP1] is 1-sensitive
       ([count_sens]); the Laplace mechanism is [(num/den)]-DP
       ([hoare_laplace_diffpriv]); their composite couples [c1 = c1'].  Paid by
       [ε1]. *)
    tp_bind ((λ: "loc", Laplace #num #den "loc" #())%V (privacy_filter.list_count vP1 _)).
    wp_bind ((λ: "loc", Laplace #num #den "loc" #())%V (privacy_filter.list_count vP1 _)).
    iApply (diffpriv_metric_sensitive_comp_at Sg
              (privacy_filter.list_count vP1)
              (λ: "loc", Laplace #num #den "loc" #())%V
              (IZR num / IZR den) 0 1 (dlist Z) dZ (C := Z) Hpos Rlt_0_1
              _ c ds ds' Hadj with "[] [] [Hrhs ε1 δ0]").
    { iApply (count_sens P1 vP1 with "Hf1 Hf1'"). }
    { iApply (hoare_laplace_diffpriv num den). iPureIntro. exact Hpos. }
    { iFrame "Hrhs". iSplitL "ε1".
      - iApply (ecm_eq with "ε1"). lra.
      - iApply (ec_eq with "δ0"). lra. }
    iIntros "!>" (c1) "Hrhs". simpl. tp_pures; wp_pures.
    (* RELEASE 2 (SENS∘DP), [(num/den)]-DP: same composite for [vP2]; couples
       [c2 = c2'].  Paid by [ε2]. *)
    tp_bind ((λ: "loc", Laplace #num #den "loc" #())%V (privacy_filter.list_count vP2 _)).
    wp_bind ((λ: "loc", Laplace #num #den "loc" #())%V (privacy_filter.list_count vP2 _)).
    iApply (diffpriv_metric_sensitive_comp_at Sg
              (privacy_filter.list_count vP2)
              (λ: "loc", Laplace #num #den "loc" #())%V
              (IZR num / IZR den) 0 1 (dlist Z) dZ (C := Z) Hpos Rlt_0_1
              _ c ds ds' Hadj with "[] [] [Hrhs ε2 δ0']").
    { iApply (count_sens P2 vP2 with "[#] [#]"); [iDestruct "Hp2" as "[$ _]"
                                                  |iDestruct "Hp2" as "[_ $]"]. }
    { iApply (hoare_laplace_diffpriv num den). iPureIntro. exact Hpos. }
    { iFrame "Hrhs". iSplitL "ε2".
      - iApply (ecm_eq with "ε2"). lra.
      - iApply (ec_eq with "δ0'"). lra. }
    iIntros "!>" (c2) "Hrhs". simpl. tp_pures; wp_pures.
    (* POST-PROCESSING (the deterministic pairing): [c1 = c1'] and [c2 = c2'] are
       already coupled, so [(c1, c2)] is returned identically on both runs — no
       budget. *)
    iApply ("HΦ" $! (c1, c2)). iExact "Hrhs".
  Qed.

End composition_demo.
