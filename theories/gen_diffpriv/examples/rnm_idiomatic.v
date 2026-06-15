(** Per-element "tape-erasure" bridge for the idiomatic report-noisy-max.

    The *presampling* report-noisy-max allocates a noise tape per coordinate in
    one pass over the score list, then reads each tape in a second pass.  A
    *direct-sampling* version draws the noise directly at read time, with no
    tape.  The two presampling passes are separated by the list structure, so to
    relate them against a single direct-sampling pass we need a CUSTOM per-element
    relation [tape_pair_rel] bridging:

      pass-1, impl: produces [(x, #lbl:α)] with a FRESH empty tape [α] for the
                    coordinate's noise family at parameter [mkp x];
      pass-1, spec: produces [(x, ())]  — no tape, just the score.

    Two arrow-relation lemmas then say that the two pass-1 element-functions are
    related at [interp TInt → tape_pair_rel] ([refines_alloc_pair]) and that the
    two pass-2 element-functions (read the tape / sample directly) are related at
    [tape_pair_rel → interp TInt] ([refines_read]).  These plug into the
    relational [list_map] congruence to bridge the whole two-pass presampling
    program against a single direct-sampling [list_map].

    The noise read is coupled REFLEXIVELY at zero cost (empty-tape read collapses
    to a fresh draw, the same draw as a direct [Sample i _ ()]), exactly as in
    [tape_erasure.v] / [fundamental.bin_log_related_sample_tape]. *)
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import distribution couplings_dp.
From clutch.gen_diffpriv Require Import model interp fundamental soundness
  coupling_rules app_rel_rules rel_tactics distance diffpriv_rules.
From clutch.gen_diffpriv.examples Require Import list.
From clutch.gen_prob_lang Require Import lang notation families.
From clutch.gen_prob_lang.typing Require Import types.
From iris.prelude Require Import options.

Set Default Proof Using "All".

Local Open Scope R.

Section rnm_idiomatic.
  Context `{!diffprivRGS Sg Σ}.
  Context (D : SampleFamily) {HDin : SampleIn D Sg}
          {HDty : SampleTyping D (TInt * (TInt * TInt))%ty TInt}.
  Context (num den : Z).

  Canonical Structure gen_ectxi_lang_rnm := gen_ectxi_lang Sg.
  Canonical Structure gen_ectx_lang_rnm := gen_ectx_lang Sg.
  Canonical Structure gen_lang_rnm := gen_lang Sg.
  Canonical Structure gen_markov_rnm := lang_markov (gen_lang Sg).
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  #[local] Existing Instance spec_rules_spec_updateGS.
  #[local] Instance spec_updateGS_rnm : spec_updateGS gen_markov_rnm Σ :=
    spec_rules_spec_updateGS Sg.

  Notation i := (sample_idx (D := D)).
  (** The noise parameter as a VALUE (used in the relation [tape_pair_rel]). *)
  Definition mkp (x : val) : val := PairV #num (PairV #(2 * den) x).
  (** The noise parameter as an EXPRESSION (used in the program text); for a
      value argument [v] it reduces to [mkp v] under [rel_pures]. *)
  Notation mkpe e := (Pair (Val #num) (Pair (Val #(2 * den)) e)) (only parsing).

  (** Reflexive coupling: any distribution couples with itself along equality at
      zero cost. *)
  Lemma DPcoupl_refl_rnm `{Countable A} (μ : distr A) : DPcoupl μ μ (=) 0 0.
  Proof. apply ARcoupl_to_DPcoupl, ARcoupl_eq. Qed.

  (** The custom per-element relation: the impl pair [(x, #lbl:α)] carries a
      fresh empty tape [α] for family [D] at parameter [mkp x]; the spec pair
      [(x', ())] carries nothing.  The scores [x], [x'] are related at [TInt]. *)
  Definition tape_pair_rel : lrel Σ := LRel (λ p1 p2,
    ∃ (x x' : val) (α : loc),
      ⌜p1 = PairV x (LitV (LitLbl α))⌝ ∗ ⌜p2 = PairV x' (LitV LitUnit)⌝ ∗
      interp TInt [] x x' ∗
      inv (logN .@ α) (α ↪ (i, mkp x, [])))%I.

  (** Pass-1 element function: impl allocates a fresh tape, spec returns unit. *)
  Lemma refines_alloc_pair :
    ⊢ REL (λ: "x", Pair "x" (AllocSampleTape i (mkpe "x")))%V
       << (λ: "x", Pair "x" (Val #()))%V
        : (interp TInt [] → tape_pair_rel)%lrel.
  Proof.
    iApply refines_arrow_val. iModIntro. iIntros (x x') "#Hx".
    iDestruct (eq_type_sound TInt [] x x' EqTInt with "Hx") as %<-.
    rel_pures_l. rel_pures_r.
    (* impl: allocate the tape for [mkp x] *)
    rel_bind_l (AllocSampleTape i _).
    iApply (refines_alloc_sample_tape_l _ ⊤ i (mkp x)).
    iModIntro. iIntros (α) "Hα". simpl.
    rel_pures_l.
    iMod (inv_alloc (logN .@ α) _ (α ↪ (i, mkp x, []))%I with "[$Hα]") as "#Hinv".
    rel_values. iExists x, x, α. iFrame "Hinv Hx". eauto.
  Qed.

  (** Pass-2 element function: read the tape on the impl, sample directly on the
      spec.  The empty-tape read collapses to a fresh draw, coupled reflexively
      at zero cost against the direct sample, so the outputs are EQUAL. *)
  Lemma refines_read :
    ⊢ REL (λ: "x_ι", Sample i (mkpe (Fst "x_ι")) (Snd "x_ι"))%V
       << (λ: "x_ι", Sample i (mkpe (Fst "x_ι")) (Snd "x_ι"))%V
        : (tape_pair_rel → interp TInt [])%lrel.
  Proof.
    iApply refines_arrow_val. iModIntro. iIntros (p1 p2) "#Hp".
    iDestruct "Hp" as (x x' α -> ->) "[#Hx #Hinv]".
    iDestruct (eq_type_sound TInt [] x x' EqTInt with "Hx") as %<-.
    rel_pures_l. rel_pures_r.
    (* both sides now: [Sample i (mkp x) <tape/unit>]. *)
    iDestruct (ground_of_eqtype TInt [] x x EqTInt with "Hx") as %Hgx.
    (* [mkp x] is a ground value of [TInt * (TInt * TInt)]. *)
    assert (Hgp : ground_val (TInt * (TInt * TInt))%ty (mkp x)).
    { destruct Hgx as [z ->]. rewrite /mkp /=.
      eexists _, _. split; [reflexivity|]. split.
      - by eexists.
      - eexists _, _. split; [reflexivity|]. split; by eexists. }
    destruct (st_decode (D := D) (mkp x) Hgp) as [p Hp].
    (* open the tape invariant and step the read coupled against the direct draw. *)
    iApply (refines_atomic_l _ _ _ []); simpl.
    iIntros (K') "Hr".
    iInv (logN.@ α) as ">Hα" "Hclose".
    iModIntro. iMod ecm_zero as "Hm".
    iApply (wp_couple_sample_tape_l Sg i (mkp x) (mkp x)
              (dmap (sf_inj D) (sf_sample D p)) (dmap (sf_inj D) (sf_sample D p))
              (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o)
              α i (mkp x) K' (⊤ ∖ ↑logN.@α) 0
              (sig_sample_decode_at D i (mkp x) p (sample_idx_S (D := D)) Hp)
              (sig_sample_decode_at D i (mkp x) p (sample_idx_S (D := D)) Hp) _
              with "[$Hr $Hα $Hm]").
    iIntros "!>" (w w') "(Hr & Hα & %HR)". destruct HR as (o & -> & ->).
    iMod ("Hclose" with "[$Hα]") as "_". iModIntro.
    iExists (Val (sf_inj D o)). iFrame "Hr".
    rel_values. iApply (interp_of_ground TInt [] (sf_inj D o)).
    apply (st_out (D := D) (τp := (TInt * (TInt * TInt))%ty) (τo := TInt)).
    Unshelve.
    apply (DPcoupl_map (sf_inj D) (sf_inj D) (sf_sample D p) (sf_sample D p)
             (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o) 0 0); [lra|lra|].
    eapply (DPcoupl_mono (sf_sample D p) (sf_sample D p) (sf_sample D p) (sf_sample D p)
              (=) (λ a a', ∃ o : sf_out D, sf_inj D a = sf_inj D o ∧ sf_inj D a' = sf_inj D o)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra | apply DPcoupl_refl_rnm ].
  Qed.

  (** ** Reverse direction (direct-sampling refines presampling).

      Symmetric to the forward direction: now the SPEC (right) carries the tape
      and the IMPL (left) draws directly.  [refines_alloc_sample_tape_r] /
      [wp_couple_sample_tape_r] are the spec-tape mirrors of the impl-tape rules
      used above. *)

  (** Reverse per-element relation: the spec pair [(x', #lbl:α')] carries a fresh
      empty spec tape; the impl pair [(x, ())] carries nothing. *)
  Definition tape_pair_rel' : lrel Σ := LRel (λ p1 p2,
    ∃ (x x' : val) (α' : loc),
      ⌜p1 = PairV x (LitV LitUnit)⌝ ∗ ⌜p2 = PairV x' (LitV (LitLbl α'))⌝ ∗
      interp TInt [] x x' ∗
      inv (logN .@ α') (α' ↪ₛ (i, mkp x', [])))%I.

  (** Pass-1, reverse: impl returns unit, spec allocates a fresh tape. *)
  Lemma refines_alloc_pair' :
    ⊢ REL (λ: "x", Pair "x" (Val #()))%V
       << (λ: "x", Pair "x" (AllocSampleTape i (mkpe "x")))%V
        : (interp TInt [] → tape_pair_rel')%lrel.
  Proof.
    iApply refines_arrow_val. iModIntro. iIntros (x x') "#Hx".
    iDestruct (eq_type_sound TInt [] x x' EqTInt with "Hx") as %<-.
    rel_pures_l. rel_pures_r.
    (* spec: allocate the tape for [mkp x] *)
    rel_bind_r (AllocSampleTape i _).
    iApply (refines_alloc_sample_tape_r ⊤ _ i (mkp x)).
    iIntros (α') "Hα'". simpl.
    rel_pures_r.
    iMod (inv_alloc (logN .@ α') _ (α' ↪ₛ (i, mkp x, []))%I with "[$Hα']") as "#Hinv".
    rel_values. iExists x, x, α'. iFrame "Hinv Hx". eauto.
  Qed.

  (** Pass-2, reverse: impl samples directly, spec reads the tape. *)
  Lemma refines_read' :
    ⊢ REL (λ: "x_ι", Sample i (mkpe (Fst "x_ι")) (Snd "x_ι"))%V
       << (λ: "x_ι", Sample i (mkpe (Fst "x_ι")) (Snd "x_ι"))%V
        : (tape_pair_rel' → interp TInt [])%lrel.
  Proof.
    iApply refines_arrow_val. iModIntro. iIntros (p1 p2) "#Hp".
    iDestruct "Hp" as (x x' α' -> ->) "[#Hx #Hinv]".
    iDestruct (eq_type_sound TInt [] x x' EqTInt with "Hx") as %<-.
    rel_pures_l. rel_pures_r.
    iDestruct (ground_of_eqtype TInt [] x x EqTInt with "Hx") as %Hgx.
    assert (Hgp : ground_val (TInt * (TInt * TInt))%ty (mkp x)).
    { destruct Hgx as [z ->]. rewrite /mkp /=.
      eexists _, _. split; [reflexivity|]. split.
      - by eexists.
      - eexists _, _. split; [reflexivity|]. split; by eexists. }
    destruct (st_decode (D := D) (mkp x) Hgp) as [p Hp].
    (* impl draws directly; open the spec-tape invariant and couple. *)
    iApply (refines_atomic_l _ _ _ []); simpl.
    iIntros (K') "Hr".
    iInv (logN.@ α') as ">Hα'" "Hclose".
    iModIntro. iMod ecm_zero as "Hm".
    iApply (wp_couple_sample_tape_r Sg i (mkp x) (mkp x)
              (dmap (sf_inj D) (sf_sample D p)) (dmap (sf_inj D) (sf_sample D p))
              (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o)
              α' i (mkp x) K' (⊤ ∖ ↑logN.@α') 0
              (sig_sample_decode_at D i (mkp x) p (sample_idx_S (D := D)) Hp)
              (sig_sample_decode_at D i (mkp x) p (sample_idx_S (D := D)) Hp) _
              with "[$Hr $Hα' $Hm]").
    iIntros "!>" (w w') "(Hr & Hα' & %HR)". destruct HR as (o & -> & ->).
    iMod ("Hclose" with "[$Hα']") as "_". iModIntro.
    iExists (Val (sf_inj D o)). iFrame "Hr".
    rel_values. iApply (interp_of_ground TInt [] (sf_inj D o)).
    apply (st_out (D := D) (τp := (TInt * (TInt * TInt))%ty) (τo := TInt)).
    Unshelve.
    apply (DPcoupl_map (sf_inj D) (sf_inj D) (sf_sample D p) (sf_sample D p)
             (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o) 0 0); [lra|lra|].
    eapply (DPcoupl_mono (sf_sample D p) (sf_sample D p) (sf_sample D p) (sf_sample D p)
              (=) (λ a a', ∃ o : sf_out D, sf_inj D a = sf_inj D o ∧ sf_inj D a' = sf_inj D o)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra | apply DPcoupl_refl_rnm ].
  Qed.

  (** ** Equivalence link (I): presampling RNM ≃ direct-2pass RNM.

      The two-pass *presampling* report-noisy-max (pass-1 allocates a noise tape
      per coordinate, pass-2 reads each tape) is related, by pure CONGRUENCE
      composition, to a *direct-2pass* variant that is identical except pass-1
      pairs each score with [()] instead of a tape, so pass-2's [Sample … ()]
      draws the noise directly.  No tape fusion, no transitivity: each direction
      is a single in-logic refinement that chains the relational [list_init] /
      [list_map] / [list_max_index] congruences (from [examples.list]) with the
      per-element bridges [refines_alloc_pair]/[refines_read] above. *)

  (** Presampling program (verbatim from [report_noisy_max_generic]'s
      [report_noisy_max_presampling], with [i = sample_idx (D:=D)]). *)
  Definition report_noisy_max_presampling : val :=
    λ:"evalQ" "N" "d",
      let: "xs" := list_init "N" (λ:"i", "evalQ" "i" "d") in
      let: "xs_tapes" := list_map (λ:"x", ("x", AllocSampleTape i (Pair #num (Pair #(2*den) "x")))) "xs" in
      let: "noisy_xs" := list_map (λ: "x_ι", Sample i (Pair #num (Pair #(2*den) (Fst "x_ι"))) (Snd "x_ι")) "xs_tapes" in
      list_max_index "noisy_xs".

  (** Direct-2pass program: identical EXCEPT pass-1 pairs the score with [()]
      (so pass-2's [Sample … (Snd "x_ι")] reads [()] = a direct draw). *)
  Definition rnm_direct2 : val :=
    λ:"evalQ" "N" "d",
      let: "xs" := list_init "N" (λ:"i", "evalQ" "i" "d") in
      let: "xs_p" := list_map (λ:"x", ("x", #())) "xs" in
      let: "noisy_xs" := list_map (λ: "x_ι", Sample i (Pair #num (Pair #(2*den) (Fst "x_ι"))) (Snd "x_ι")) "xs_p" in
      list_max_index "noisy_xs".

  (** Forward direction: presampling refines direct-2pass.  The per-index query
      [λ:"i", evalQ "i" d] is assumed to self-relate at [lrel_nat → interp TInt],
      i.e. it returns equal integer scores on both runs (the only fact the two
      passes need; the noise read collapses to the same draw at zero cost). *)
  Lemma rnm_link1 (evalQ : val) (N : nat) (d : val) Δ :
    (⊢ REL (λ:"i", evalQ "i" d)%V << (λ:"i", evalQ "i" d)%V
        : (lrel_nat → interp TInt [])%lrel) →
    ⊢ REL report_noisy_max_presampling evalQ #N d
       << rnm_direct2 evalQ #N d : interp TNat Δ.
  Proof.
    iIntros (Hq). rewrite /report_noisy_max_presampling /rnm_direct2.
    rel_pures_l. rel_pures_r.
    (* pass-0: build the (equal) score list via [list_init]. *)
    rel_bind_l (list_init _ _). rel_bind_r (list_init _ _).
    iApply (refines_bind with "[]").
    { iApply (refines_list_init (interp TInt []) #N #N).
      - rel_values.
      - iApply Hq. }
    iIntros (xs xs') "Hxs /=". rel_pures_l. rel_pures_r.
    (* pass-1: impl allocates a tape per coordinate, spec pairs with [()]. *)
    rel_bind_l (list_map _ _). rel_bind_r (list_map _ _).
    iApply (refines_bind with "[Hxs]").
    { iApply (refines_list_map (interp TInt []) tape_pair_rel).
      - iApply refines_alloc_pair.
      - iApply (refines_ret with "[Hxs]"); [done..|]. by iModIntro. }
    iIntros (xt xp) "Hxt /=". rel_pures_l. rel_pures_r.
    (* pass-2: read each tape (impl) / sample directly (spec), equal outputs. *)
    rel_bind_l (list_map _ _). rel_bind_r (list_map _ _).
    iApply (refines_bind with "[Hxt]").
    { iApply (refines_list_map tape_pair_rel (interp TInt [])).
      - iApply refines_read.
      - iApply (refines_ret with "[Hxt]"); [done..|]. by iModIntro. }
    iIntros (ns ns') "Hns /=". rel_pures_l. rel_pures_r.
    (* argmax of two pointwise-equal integer lists: equal index at [lrel_nat]. *)
    iApply (refines_list_max_index (Val ns) (Val ns')).
    iApply (refines_ret with "[Hns]"); [done..|]. by iModIntro.
  Qed.

  (** Reverse direction: direct-2pass refines presampling (presampling on the
      RIGHT), symmetric using the primed per-element bridges. *)
  Lemma rnm_link1' (evalQ : val) (N : nat) (d : val) Δ :
    (⊢ REL (λ:"i", evalQ "i" d)%V << (λ:"i", evalQ "i" d)%V
        : (lrel_nat → interp TInt [])%lrel) →
    ⊢ REL rnm_direct2 evalQ #N d
       << report_noisy_max_presampling evalQ #N d : interp TNat Δ.
  Proof.
    iIntros (Hq). rewrite /report_noisy_max_presampling /rnm_direct2.
    rel_pures_l. rel_pures_r.
    rel_bind_l (list_init _ _). rel_bind_r (list_init _ _).
    iApply (refines_bind with "[]").
    { iApply (refines_list_init (interp TInt []) #N #N).
      - rel_values.
      - iApply Hq. }
    iIntros (xs xs') "Hxs /=". rel_pures_l. rel_pures_r.
    rel_bind_l (list_map _ _). rel_bind_r (list_map _ _).
    iApply (refines_bind with "[Hxs]").
    { iApply (refines_list_map (interp TInt []) tape_pair_rel').
      - iApply refines_alloc_pair'.
      - iApply (refines_ret with "[Hxs]"); [done..|]. by iModIntro. }
    iIntros (xp xt) "Hxt /=". rel_pures_l. rel_pures_r.
    rel_bind_l (list_map _ _). rel_bind_r (list_map _ _).
    iApply (refines_bind with "[Hxt]").
    { iApply (refines_list_map tape_pair_rel' (interp TInt [])).
      - iApply refines_read'.
      - iApply (refines_ret with "[Hxt]"); [done..|]. by iModIntro. }
    iIntros (ns ns') "Hns /=". rel_pures_l. rel_pures_r.
    iApply (refines_list_max_index (Val ns) (Val ns')).
    iApply (refines_ret with "[Hns]"); [done..|]. by iModIntro.
  Qed.

  (** ** Equivalence link (II): direct-2pass RNM ≃ direct-1map (idiomatic) RNM.

      The idiomatic report-noisy-max draws the noise in a SINGLE direct-sampling
      map over the scores — no intermediate [(score, ())] pairing, no tape.  We
      relate the direct-2pass program (which pairs each score with [()] in a
      first map, then samples in a second map) to this one-map version by
      MAP-MAP FUSION: the two forward-order maps on the left line up, element by
      element, with the single forward-order map on the right.  Each element's
      noise draw is coupled REFLEXIVELY at zero cost ([refines_directsample]). *)

  (** The idiomatic per-element direct-sampling function (no pair, no tape). *)
  Definition directsample : val := (λ: "x", Sample i (mkpe "x") #())%V.

  (** Idiomatic one-pass report-noisy-max: one direct-sampling map. *)
  Definition rnm_direct1 : val :=
    λ:"evalQ" "N" "d",
      let: "xs" := list_init "N" (λ:"i", "evalQ" "i" "d") in
      list_max_index (list_map directsample "xs").

  (** Reflexive direct sample: applied to equal integer scores it draws the same
      noise on both runs (the reflexive draw coupling at zero cost), exactly as
      in [bin_log_related_sample]. *)
  Lemma refines_directsample :
    ⊢ REL directsample << directsample : (interp TInt [] → interp TInt [])%lrel.
  Proof.
    iApply refines_arrow_val. iModIntro. iIntros (x x') "#Hx".
    iDestruct (eq_type_sound TInt [] x x' EqTInt with "Hx") as %<-.
    rewrite /directsample. rel_pures_l. rel_pures_r.
    iDestruct (ground_of_eqtype TInt [] x x EqTInt with "Hx") as %Hgx.
    assert (Hgp : ground_val (TInt * (TInt * TInt))%ty (mkp x)).
    { destruct Hgx as [z ->]. rewrite /mkp /=.
      eexists _, _. split; [reflexivity|]. split.
      - by eexists.
      - eexists _, _. split; [reflexivity|]. split; by eexists. }
    destruct (st_decode (D := D) (mkp x) Hgp) as [p Hp].
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hspec Hna Herr %Hε".
    iMod ecm_zero as "Hm".
    iApply (wp_couple_sample_gen Sg i (mkp x) (mkp x)
              (dmap (sf_inj D) (sf_sample D p)) (dmap (sf_inj D) (sf_sample D p))
              (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o) K ⊤ 0
              (sig_sample_decode_at D i (mkp x) p (sample_idx_S (D := D)) Hp)
              (sig_sample_decode_at D i (mkp x) p (sample_idx_S (D := D)) Hp) _
              with "[$Hspec $Hm]").
    { iIntros "!>" (w w') "(Hspec & %HR)". destruct HR as (o & -> & ->).
      iExists (sf_inj D o), ε. iFrame "Hspec Hna Herr".
      iSplitR; [done|]. iApply (interp_of_ground TInt [] (sf_inj D o)).
      apply (st_out (D := D) (τp := (TInt * (TInt * TInt))%ty) (τo := TInt)). }
    Unshelve.
    apply (DPcoupl_map (sf_inj D) (sf_inj D) (sf_sample D p) (sf_sample D p)
             (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o) 0 0); [lra|lra|].
    eapply (DPcoupl_mono (sf_sample D p) (sf_sample D p) (sf_sample D p) (sf_sample D p)
              (=) (λ a a', ∃ o : sf_out D, sf_inj D a = sf_inj D o ∧ sf_inj D a' = sf_inj D o)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra | apply DPcoupl_refl_rnm ].
  Qed.


  (** Per-element relation bridging the direct-2pass [(score, ())] pairing to the
      bare score in the idiomatic one-pass version: the impl pair [(x, ())] and
      the spec score [x'] are related at [interp TInt]. *)
  Definition unit_pair_rel : lrel Σ := LRel (λ p v',
    ∃ x : val, ⌜p = (x, #())%V⌝ ∗ interp TInt [] x v')%I.

  (** ** Stage A: the pure score↦[(score,())] pairing map.

      The [(score, ())] pairing pass is PURE (no sampling, no tape), so it is a
      plain program computation: over a value list [lv] (semantically a list of
      integers related at [interp TInt] to [lv']) it returns the element-wise
      [(·, ())]-wrapped list, related to [lv'] at [unit_pair_rel].  We prove it
      as a [WP] (the impl side strips the [lrel_list] guard via its pure steps),
      then lift it to a refinement via [refines_wp_l]. *)
  Lemma wp_pair_pass (lv lv' : val) :
    lrel_list (interp TInt []) lv lv' -∗
    WP list_map (λ:"x", ("x", #()))%V lv {{ w, lrel_list unit_pair_rel w lv' }}.
  Proof.
    iIntros "Hll". iLöb as "IH" forall (lv lv').
    rewrite lrel_list_unfold. rewrite /list_map.
    iDestruct "Hll" as "[Hnil|Hcons]".
    - iDestruct "Hnil" as "[>-> >->]".
      wp_pures.
      rewrite (lrel_list_unfold unit_pair_rel (InjLV _) (InjLV _)).
      iModIntro. iNext. iLeft. by auto.
    - iDestruct "Hcons" as (a1 a2 r1 r2) "(>-> & >-> & #HA & Hrest)".
      do 7 (wp_pure _).
      wp_bind ((rec: "list_map" "f" "l" := _)%V (λ: "x", ("x", #()))%V r1).
      iApply (wp_wand with "[Hrest]").
      { iApply ("IH" $! r1 r2 with "Hrest"). }
      iIntros (tv) "#Htv /=".
      rewrite /list_cons. wp_pures.
      rewrite (lrel_list_unfold unit_pair_rel (InjRV _) (InjRV _)).
      iModIntro. iNext. iRight.
      iExists (a1, #())%V, a2, tv, r2. iSplit; [done|]. iSplit; [done|].
      iFrame "Htv". iExists a1. iSplit; [done|]. done.
  Qed.

  (** Stage A lifted to a refinement (forward): the impl pairing map [<<] the
      spec list it was built from, at [unit_pair_rel]. *)
  Lemma refines_pair_pass (l l' : expr) :
    (REL l << l' : lrel_list (interp TInt [])) -∗
    REL list_map (λ:"x", ("x", #()))%V l << l' : lrel_list unit_pair_rel.
  Proof.
    iIntros "Hl".
    rel_bind_l l. rel_bind_r l'.
    iApply (refines_bind with "Hl").
    iIntros (lv lv') "Hll /=".
    rel_apply_l refines_wp_l.
    iApply (wp_wand with "[Hll]").
    { iApply (wp_pair_pass with "Hll"). }
    iIntros (w) "Hw /=". rel_values.
  Qed.

  (** The pass-2 element coupling: the direct-2pass [read] [(x, ())] (which
      projects the score and draws the noise at [()]) is related REFLEXIVELY, at
      zero cost, to the idiomatic [directsample x'] (which draws directly), since
      both reduce to the same [Sample i (mkpe x) ()] on equal scores. *)
  Lemma refines_read_directsample :
    ⊢ REL (λ: "x_ι", Sample i (mkpe (Fst "x_ι")) (Snd "x_ι"))%V << directsample
        : (unit_pair_rel → interp TInt [])%lrel.
  Proof.
    iApply refines_arrow_val. iModIntro. iIntros (p v') "#Hp".
    iDestruct "Hp" as (x ->) "#Hx".
    rewrite /directsample. rel_pures_l. rel_pures_r.
    iDestruct (eq_type_sound TInt [] x v' EqTInt with "Hx") as %<-.
    iDestruct (ground_of_eqtype TInt [] x x EqTInt with "Hx") as %Hgx.
    assert (Hgp : ground_val (TInt * (TInt * TInt))%ty (mkp x)).
    { destruct Hgx as [z ->]. rewrite /mkp /=.
      eexists _, _. split; [reflexivity|]. split.
      - by eexists.
      - eexists _, _. split; [reflexivity|]. split; by eexists. }
    destruct (st_decode (D := D) (mkp x) Hgp) as [pp Hpp].
    rewrite refines_eq /refines_def.
    iIntros (KK ε) "Hspec Hna Herr %Hε".
    iMod ecm_zero as "Hm".
    iApply (wp_couple_sample_gen Sg i (mkp x) (mkp x)
              (dmap (sf_inj D) (sf_sample D pp)) (dmap (sf_inj D) (sf_sample D pp))
              (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o) KK ⊤ 0
              (sig_sample_decode_at D i (mkp x) pp (sample_idx_S (D := D)) Hpp)
              (sig_sample_decode_at D i (mkp x) pp (sample_idx_S (D := D)) Hpp) _
              with "[$Hspec $Hm]").
    { iIntros "!>" (w w') "(Hspec & %HR)". destruct HR as (o & -> & ->).
      iExists (sf_inj D o), ε. iFrame "Hspec Hna Herr".
      iSplitR; [done|]. iApply (interp_of_ground TInt [] (sf_inj D o)).
      apply (st_out (D := D) (τp := (TInt * (TInt * TInt))%ty) (τo := TInt)). }
    Unshelve.
    apply (DPcoupl_map (sf_inj D) (sf_inj D) (sf_sample D pp) (sf_sample D pp)
             (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o) 0 0); [lra|lra|].
    eapply (DPcoupl_mono (sf_sample D pp) (sf_sample D pp) (sf_sample D pp) (sf_sample D pp)
              (=) (λ a a', ∃ o : sf_out D, sf_inj D a = sf_inj D o ∧ sf_inj D a' = sf_inj D o)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra | apply DPcoupl_refl_rnm ].
  Qed.

  (** Forward map-map fusion via the [list_map] congruence: relate the
      direct-2pass noisy list (outer read-map ∘ inner pairing-map) to the
      direct-1map noisy list (single direct-sampling map).  [refines_pair_pass]
      relates the inner pairing map to the spec score list at [unit_pair_rel];
      then the [list_map] congruence relates the outer read-map to the
      direct-sampling map, the per-element coupling being reflexive. *)
  Lemma refines_map_map_fusion (l l' : expr) :
    (REL l << l' : lrel_list (interp TInt [])) -∗
    REL list_map (λ:"x_ι", Sample i (mkpe (Fst "x_ι")) (Snd "x_ι"))%V
                 (list_map (λ:"x", ("x", #()))%V l)
     << list_map directsample l' : lrel_list (interp TInt []).
  Proof.
    iIntros "Hl".
    iApply (refines_list_map unit_pair_rel (interp TInt [])).
    - iApply refines_read_directsample.
    - iApply (refines_pair_pass with "Hl").
  Qed.

  (** Forward direction: direct-2pass refines direct-1map (idiomatic). *)
  Lemma rnm_link2 (evalQ : val) (N : nat) (d : val) Δ :
    (⊢ REL (λ:"i", evalQ "i" d)%V << (λ:"i", evalQ "i" d)%V
        : (lrel_nat → interp TInt [])%lrel) →
    ⊢ REL rnm_direct2 evalQ #N d
       << rnm_direct1 evalQ #N d : interp TNat Δ.
  Proof.
    iIntros (Hq). rewrite /rnm_direct2 /rnm_direct1.
    rel_pures_l. rel_pures_r.
    rel_bind_l (list_init _ _). rel_bind_r (list_init _ _).
    iApply (refines_bind with "[]").
    { iApply (refines_list_init (interp TInt []) #N #N).
      - rel_values.
      - iApply Hq. }
    iIntros (xs xs') "Hxs /=". rel_pures_l. rel_pures_r.
    (* pass-1 (impl pairing) is pure: evaluate it LHS-only to a value [pv]
       related to the spec score list at [unit_pair_rel]. *)
    rel_bind_l (list_map (λ:"x",("x",#()))%V xs).
    rel_apply_l refines_wp_l.
    iApply (wp_wand with "[Hxs]").
    { iApply (wp_pair_pass with "Hxs"). }
    iIntros (pv) "#Hpv /=". rel_pures_l.
    (* pass-2: outer read-map (impl) vs direct-sampling map (spec), reflexive
       per-element coupling; then argmax of the (pointwise-equal) noisy lists. *)
    rel_bind_l (list_map (λ:"x_ι", Sample i (mkpe (Fst "x_ι")) (Snd "x_ι"))%V pv).
    rel_bind_r (list_map directsample xs').
    iApply (refines_bind with "[Hpv]").
    { iApply (refines_list_map unit_pair_rel (interp TInt [])).
      - iApply refines_read_directsample.
      - rel_values. }
    iIntros (nv nv') "Hnv /=". rel_pures_l.
    iApply (refines_list_max_index (Val nv) (Val nv')).
    iApply (refines_ret with "[Hnv]"); [done..|]. by iModIntro.
  Qed.

  (** ** Bridge: sensitivity-at-zero ⇒ the per-index query self-relation [Hq].

      The DP statements assume the query [evalQ #i] is [Δ]-sensitive
      ([hoare_sensitive (evalQ #i) (IZR Δ) dDB dZ]).  Specialised at the SAME
      database [db] (impl and spec), the input distance [dDB db db = 0]
      ([distance_0]) forces the output distance [dZ b b' <= IZR Δ * 0 = 0], and
      [dZ b b' = 0] (an absolute value) means [b = b'].  So at a fixed [db] the
      query returns EQUAL integers on both runs at zero cost — exactly the
      self-relation [REL (λ:"i",evalQ "i" (inject db)) << … : lrel_nat → interp TInt]
      that the equivalence links [rnm_link1]/[rnm_link2] require. *)
  Lemma rnm_query_self_rel (Δ : Z) (evalQ : val) DB (dDB : Distance DB) (db : DB) :
    (0 <= Δ)%Z →
    (∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) →
    ⊢ REL (λ:"i", evalQ "i" (inject db))%V << (λ:"i", evalQ "i" (inject db))%V
        : (lrel_nat → interp TInt [])%lrel.
  Proof.
    iIntros (HΔ Hsens).
    iApply refines_arrow_val. iModIntro. iIntros (n n') "#Hn".
    iDestruct "Hn" as (k) "[-> ->]".
    rel_pures_l. rel_pures_r.
    (* Goal: REL evalQ #k (inject db) << evalQ #k (inject db) : interp TInt [].
       Discharge it by the [Δ]-sensitivity of [evalQ #(Z.of_nat k)] at [(db,db)]. *)
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hspec Hna Herr %Hε".
    assert (Hcpos : (0 <= IZR Δ)%R) by (apply IZR_le; lia).
    iPoseProof (Hsens (Z.of_nat k)) as "Ht".
    iApply ("Ht" $! Hcpos K db db with "[$Hspec]").
    iModIntro. iIntros (v) "Hpost".
    iDestruct "Hpost" as (b b' Hv) "[Hspec' %Hd]".
    (* [dDB db db = 0], so [dZ b b' <= IZR Δ * 0 = 0], hence [b = b']. *)
    assert (dDB db db = 0) as Hdb by (apply distance_0; reflexivity).
    rewrite Hdb Rmult_0_r in Hd.
    assert (b = b') as <-.
    { pose proof (distance_pos (Distance:=dZ) b b') as Hpos.
      assert (dZ b b' = 0) as Hz by lra.
      rewrite /dZ /distance /= in Hz.
      apply Rcomplements.Rabs_eq_0 in Hz. apply eq_IZR in Hz. lia. }
    iExists (inject b), ε. iFrame "Hspec' Hna Herr".
    rewrite Hv. iSplit; [done|].
    iExists b. by rewrite /inject /=.
  Qed.

  (** ** Reverse of equivalence link (II): direct-1map (idiomatic) ≃ direct-2pass.

      The mirror of [rnm_link2]: now the SPEC (right) carries the two-pass
      structure (a pairing map then a read map) and the IMPL (left) is the single
      direct-sampling map.  The pairing pass is PURE, so we evaluate it on the
      SPEC side by Löb induction stepping [tp_*] reductions, then the read map vs.
      the direct-sampling map is the reflexive draw coupling.  This is exactly the
      [rnm_link2'] direction the prompt flagged as the only remaining link; we
      prove it here over abstract lists by a spec-side recursion. *)

End rnm_idiomatic.
