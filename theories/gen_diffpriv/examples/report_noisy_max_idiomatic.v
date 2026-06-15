(** Per-element "tape-erasure" bridge for the idiomatic report-noisy-max, over
    the [gen_prob_lang.gwp.list] combinators (the ones the REAL presampling
    program [report_noisy_max_generic.report_noisy_max_presampling] is built
    from).  This is the [gwp.list] re-pointing of [rnm_idiomatic.v], so that the
    resulting [lim_exec] program-equivalence connects to the RNM DP theorem
    [rnm_pres_diffpriv].

    The differences from [rnm_idiomatic.v] (over [examples.list]) are:
      - the relational list congruences come from [gwp_list_rel] (for [gwp.list]'s
        combinators) rather than from [examples.list];
      - [gwp.list]'s [list_init] counts DOWN from [len] to [1] prepending (so
        [list_init len f = [f len; …; f 1]]) with NO trailing [list_rev], so the
        reverse-direction concrete-score extraction runs the down-count loop and
        needs NO spec-side [list_rev];
      - the spec-side pairing map in the reverse link is run to a value via
        [gwp_list_map (g := gwp_spec)] rather than a bespoke [spec_list_map].

    Everything else (the [Sample]/[AllocSampleTape]/pair per-element bridges) is
    library-agnostic and copied verbatim. *)
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import distribution couplings couplings_dp.
From clutch.gen_diffpriv Require Import model interp fundamental soundness
  coupling_rules app_rel_rules rel_tactics primitive_laws distance diffpriv_rules
  compatibility.
From clutch.gen_diffpriv.examples Require Import gwp_list_rel report_noisy_max_generic.
From clutch.gen_prob_lang Require Import lang notation families inject tactics metatheory znoise.
From clutch.gen_prob_lang Require Import gwp.list.
From clutch.gen_prob_lang.typing Require Import types.
From iris.prelude Require Import options.

Set Default Proof Using "All".

Local Open Scope R.

Section idiomatic.
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
    iDestruct (ground_of_eqtype TInt [] x x EqTInt with "Hx") as %Hgx.
    assert (Hgp : ground_val (TInt * (TInt * TInt))%ty (mkp x)).
    { destruct Hgx as [z ->]. rewrite /mkp /=.
      eexists _, _. split; [reflexivity|]. split.
      - by eexists.
      - eexists _, _. split; [reflexivity|]. split; by eexists. }
    destruct (st_decode (D := D) (mkp x) Hgp) as [p Hp].
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

  (** ** Reverse direction (direct-sampling refines presampling). *)

  Definition tape_pair_rel' : lrel Σ := LRel (λ p1 p2,
    ∃ (x x' : val) (α' : loc),
      ⌜p1 = PairV x (LitV LitUnit)⌝ ∗ ⌜p2 = PairV x' (LitV (LitLbl α'))⌝ ∗
      interp TInt [] x x' ∗
      inv (logN .@ α') (α' ↪ₛ (i, mkp x', [])))%I.

  Lemma refines_alloc_pair' :
    ⊢ REL (λ: "x", Pair "x" (Val #()))%V
       << (λ: "x", Pair "x" (AllocSampleTape i (mkpe "x")))%V
        : (interp TInt [] → tape_pair_rel')%lrel.
  Proof.
    iApply refines_arrow_val. iModIntro. iIntros (x x') "#Hx".
    iDestruct (eq_type_sound TInt [] x x' EqTInt with "Hx") as %<-.
    rel_pures_l. rel_pures_r.
    rel_bind_r (AllocSampleTape i _).
    iApply (refines_alloc_sample_tape_r ⊤ _ i (mkp x)).
    iIntros (α') "Hα'". simpl.
    rel_pures_r.
    iMod (inv_alloc (logN .@ α') _ (α' ↪ₛ (i, mkp x, []))%I with "[$Hα']") as "#Hinv".
    rel_values. iExists x, x, α'. iFrame "Hinv Hx". eauto.
  Qed.

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

  (** ** Equivalence link (I): presampling RNM ≃ direct-2pass RNM. *)

  (** Presampling program (verbatim from [report_noisy_max_generic]'s
      [report_noisy_max_presampling], with [i = sample_idx (D:=D)]). *)
  Definition report_noisy_max_presampling : val :=
    λ:"evalQ" "N" "d",
      let: "xs" := list_init "N" (λ:"i", "evalQ" "i" "d") in
      let: "xs_tapes" := list_map (λ:"x", ("x", AllocSampleTape i (Pair #num (Pair #(2*den) "x")))) "xs" in
      let: "noisy_xs" := list_map (λ: "x_ι", Sample i (Pair #num (Pair #(2*den) (Fst "x_ι"))) (Snd "x_ι")) "xs_tapes" in
      list_max_index "noisy_xs".

  Definition rnm_direct2 : val :=
    λ:"evalQ" "N" "d",
      let: "xs" := list_init "N" (λ:"i", "evalQ" "i" "d") in
      let: "xs_p" := list_map (λ:"x", ("x", #())) "xs" in
      let: "noisy_xs" := list_map (λ: "x_ι", Sample i (Pair #num (Pair #(2*den) (Fst "x_ι"))) (Snd "x_ι")) "xs_p" in
      list_max_index "noisy_xs".

  Lemma rnm_link1 (evalQ : val) (N : nat) (d : val) Δ :
    (⊢ REL (λ:"i", evalQ "i" d)%V << (λ:"i", evalQ "i" d)%V
        : (lrel_nat → interp TInt [])%lrel) →
    ⊢ REL report_noisy_max_presampling evalQ #N d
       << rnm_direct2 evalQ #N d : interp TNat Δ.
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
    { iApply (refines_list_map (interp TInt []) tape_pair_rel).
      - iApply refines_alloc_pair.
      - iApply (refines_ret with "[Hxs]"); [done..|]. by iModIntro. }
    iIntros (xt xp) "Hxt /=". rel_pures_l. rel_pures_r.
    rel_bind_l (list_map _ _). rel_bind_r (list_map _ _).
    iApply (refines_bind with "[Hxt]").
    { iApply (refines_list_map tape_pair_rel (interp TInt [])).
      - iApply refines_read.
      - iApply (refines_ret with "[Hxt]"); [done..|]. by iModIntro. }
    iIntros (ns ns') "Hns /=". rel_pures_l. rel_pures_r.
    iApply (refines_list_max_index (Val ns) (Val ns')).
    iApply (refines_ret with "[Hns]"); [done..|]. by iModIntro.
  Qed.

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

  (** ** Equivalence link (II): direct-2pass RNM ≃ direct-1map (idiomatic) RNM. *)

  Definition directsample : val := (λ: "x", Sample i (mkpe "x") #())%V.

  Definition rnm_direct1 : val :=
    λ:"evalQ" "N" "d",
      let: "xs" := list_init "N" (λ:"i", "evalQ" "i" "d") in
      list_max_index (list_map directsample "xs").

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

  Definition unit_pair_rel : lrel Σ := LRel (λ p v',
    ∃ x : val, ⌜p = (x, #())%V⌝ ∗ interp TInt [] x v')%I.

  (** Stage A: the pure score↦[(score,())] pairing map. *)
  Lemma wp_pair_pass (lv lv' : val) :
    lrel_list (interp TInt []) lv lv' -∗
    WP list_map (λ:"x", ("x", #()))%V lv {{ w, lrel_list unit_pair_rel w lv' }}.
  Proof.
    iIntros "Hll". iLöb as "IH" forall (lv lv').
    rewrite lrel_list_unfold.
    iDestruct "Hll" as "[Hnil|Hcons]".
    - iDestruct "Hnil" as "[>-> >->]".
      rewrite /list_map. wp_pures.
      rewrite (lrel_list_unfold unit_pair_rel (InjLV _) (InjLV _)).
      iModIntro. iNext. iLeft. by auto.
    - iDestruct "Hcons" as (a1 a2 r1 r2) "(>-> & >-> & #HA & Hrest)".
      rewrite {2}/list_map. do 5 (wp_pure _). rewrite -/list_map.
      wp_pure _.
      wp_bind (list_map (λ: "x", ("x", #()))%V (Snd (a1, r1)%V)).
      wp_pure _.
      iApply (wp_wand with "[Hrest]").
      { iApply ("IH" $! r1 r2 with "Hrest"). }
      iIntros (tv) "#Htv /=".
      wp_pures. rewrite /list_cons. wp_pures.
      rewrite (lrel_list_unfold unit_pair_rel (InjRV _) (InjRV _)).
      iModIntro. iNext. iRight.
      iExists (a1, #())%V, a2, tv, r2. iSplit; [done|]. iSplit; [done|].
      iFrame "Htv". iExists a1. iSplit; [done|]. done.
  Qed.

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
    rel_bind_l (list_map (λ:"x",("x",#()))%V xs).
    rel_apply_l refines_wp_l.
    iApply (wp_wand with "[Hxs]").
    { iApply (wp_pair_pass with "Hxs"). }
    iIntros (pv) "#Hpv /=". rel_pures_l.
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

  (** ** Bridge: sensitivity-at-zero ⇒ the per-index query self-relation [Hq]. *)
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
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hspec Hna Herr %Hε".
    assert (Hcpos : (0 <= IZR Δ)%R) by (apply IZR_le; lia).
    iPoseProof (Hsens (Z.of_nat k)) as "Ht".
    iApply ("Ht" $! Hcpos K db db with "[$Hspec]").
    iModIntro. iIntros (v) "Hpost".
    iDestruct "Hpost" as (b b' Hv) "[Hspec' %Hd]".
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

      Mirror of [rnm_link2].  The SPEC (right) carries the two passes (a pairing
      map then a read map); the IMPL (left) is the single direct-sampling map.
      To break the call-by-value deadlock we concretise the (equal) score lists
      with [refines_list_init_concrete], then run the spec pairing map to a value
      via [gwp_list_map (g := gwp_spec)] — the [gwp.list] spec-side analogue of
      [examples.list]'s bespoke [spec_list_map].  Unlike [examples.list],
      [gwp.list]'s [list_init] needs NO trailing [list_rev], so there is no
      spec-side reversal to run. *)

  (** Concrete-list relation: two value-lists carry the SAME concrete list of
      integers [zs] on both sides (no guarded-recursion [▷]). *)
  Definition rel_concrete_int : lrel Σ := LRel (λ v v',
    ∃ zs : list Z, ⌜is_list (A := Z) zs v ∧ is_list (A := Z) zs v'⌝)%I.

  (** [list_init] producing a CONCRETE equal integer list on both sides.  Mirrors
      [refines_list_init] (from [gwp_list_rel]) but, because the per-index query
      returns EQUAL integers (the [Hq] self-relation), the result lists are the
      SAME concrete [list Z], tracked through the down-count loop accumulator.
      [gwp.list]'s [list_init] prepends [f i] for [i] counting down from [k] to
      [1], so no final [list_rev] is needed. *)
  Lemma refines_list_init_concrete (f f' : val) (M : nat) :
    □ (REL f << f' : (lrel_nat → interp TInt [])%lrel) -∗
    REL list_init #M f << list_init #M f' : rel_concrete_int.
  Proof.
    iIntros "#Hf". rewrite /list_init.
    do 3 (rel_pure_l _). do 3 (rel_pure_r _).
    rewrite /list_cons.
    iAssert (□ ∀ (j : nat) (av av' : val) (acc : list Z),
                ⌜is_list (A := Z) acc av ∧ is_list (A := Z) acc av'⌝ -∗
                REL (rec: "aux" "acc" "i" :=
                       if: "i" = #0 then "acc"
                       else "aux"
                              ((λ: "elem" "list", SOME ("elem", "list"))%V
                                 (Val f "i") "acc") ("i" - #1))%V av #j
                 << (rec: "aux" "acc" "i" :=
                       if: "i" = #0 then "acc"
                       else "aux"
                              ((λ: "elem" "list", SOME ("elem", "list"))%V
                                 (Val f' "i") "acc") ("i" - #1))%V av' #j
                 : rel_concrete_int)%I as "#Hloop".
    { iModIntro. iIntros (j). iInduction j as [|j] "IH"; iIntros (av av' acc [Hav Hav']).
      - (* counter 0: both runs return the (equal-concrete) accumulator. *)
        rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r. rel_values.
      - (* counter [S j]: cons [f #(S j)] onto both accumulators, recurse at [j]. *)
        rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r.
        rel_bind_l (f _)%E. rel_bind_r (f' _)%E.
        iApply (refines_bind with "[]").
        { iApply (refines_app with "Hf"). rel_values. }
        iIntros (hv hv') "#Hhead /=".
        iDestruct "Hhead" as (z) "[-> ->]".
        do 5 (rel_pure_l _). do 5 (rel_pure_r _).
        replace (Z.of_nat (S j) - 1)%Z with (Z.of_nat j) by lia.
        iApply ("IH" $! (InjRV (#z, av)) (InjRV (#z, av')) (z :: acc)).
        iPureIntro; split; simpl; eauto. }
    do 2 (rel_pure_l _). do 2 (rel_pure_r _).
    iApply ("Hloop" $! M _ _ []). by iPureIntro.
  Qed.

  (** Reverse per-element pairing relation: the impl bare score [v] is related to
      the spec pair [(x', ())] at [interp TInt] (between [v] and [x']). *)
  Definition unit_pair_rel' : lrel Σ := LRel (λ v p,
    ∃ x' : val, ⌜p = (x', #())%V⌝ ∗ interp TInt [] v x')%I.

  (** Pass-2 element coupling (reverse): the idiomatic [directsample] (impl) is
      related REFLEXIVELY at zero cost to the direct-2pass [read] [(x',())]. *)
  Lemma refines_directsample_read :
    ⊢ REL directsample << (λ: "x_ι", Sample i (mkpe (Fst "x_ι")) (Snd "x_ι"))%V
        : (unit_pair_rel' → interp TInt [])%lrel.
  Proof.
    iApply refines_arrow_val. iModIntro. iIntros (v p) "#Hp".
    iDestruct "Hp" as (x' ->) "#Hx".
    rewrite /directsample. rel_pures_l. rel_pures_r.
    iDestruct (eq_type_sound TInt [] v x' EqTInt with "Hx") as %<-.
    iDestruct (ground_of_eqtype TInt [] v v EqTInt with "Hx") as %Hgx.
    assert (Hgp : ground_val (TInt * (TInt * TInt))%ty (mkp v)).
    { destruct Hgx as [z ->]. rewrite /mkp /=.
      eexists _, _. split; [reflexivity|]. split.
      - by eexists.
      - eexists _, _. split; [reflexivity|]. split; by eexists. }
    destruct (st_decode (D := D) (mkp v) Hgp) as [pp Hpp].
    rewrite refines_eq /refines_def.
    iIntros (KK ε) "Hspec Hna Herr %Hε".
    iMod ecm_zero as "Hm".
    iApply (wp_couple_sample_gen Sg i (mkp v) (mkp v)
              (dmap (sf_inj D) (sf_sample D pp)) (dmap (sf_inj D) (sf_sample D pp))
              (λ w w', ∃ o : sf_out D, w = sf_inj D o ∧ w' = sf_inj D o) KK ⊤ 0
              (sig_sample_decode_at D i (mkp v) pp (sample_idx_S (D := D)) Hpp)
              (sig_sample_decode_at D i (mkp v) pp (sample_idx_S (D := D)) Hpp) _
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

  (** Bridge: from the concrete equal integer list build the reverse pairing
      relation between the impl score list [lv] and the spec [(score,())]-paired
      list [pv'] (the result of running the spec pairing map). *)
  Lemma is_list_pair_unit_rel (zs : list Z) (lv pv' : val) :
    is_list (A := Z) zs lv → is_list (A := val) (List.map (λ z : Z, (#z, #())%V) zs) pv' →
    ⊢ lrel_list unit_pair_rel' lv pv'.
  Proof.
    iInduction zs as [|z zs] "IH" forall (lv pv'); iIntros (Hlv Hpv').
    - simpl in *. subst. rewrite (lrel_list_unfold unit_pair_rel' (InjLV _) (InjLV _)).
      iNext. iLeft. by auto.
    - simpl in Hlv. destruct Hlv as (lr & -> & Hlr).
      simpl in Hpv'. destruct Hpv' as (pr & -> & Hpr).
      rewrite (lrel_list_unfold unit_pair_rel' (InjRV _) (InjRV _)).
      iNext. iRight. iExists (#z), (#z, #())%V, lr, pr.
      iSplit; [done|]. iSplit; [done|].
      iSplitR.
      { iExists (#z). iSplit; [done|]. iExists z. by rewrite /inject /=. }
      iApply ("IH" $! lr pr); by iPureIntro.
  Qed.

  (** Reverse direction: direct-1map (idiomatic) refines direct-2pass. *)
  Lemma rnm_link2' (evalQ : val) (N : nat) (d : val) Δ :
    (⊢ REL (λ:"i", evalQ "i" d)%V << (λ:"i", evalQ "i" d)%V
        : (lrel_nat → interp TInt [])%lrel) →
    ⊢ REL rnm_direct1 evalQ #N d
       << rnm_direct2 evalQ #N d : interp TNat Δ.
  Proof.
    iIntros (Hq). rewrite /rnm_direct1 /rnm_direct2.
    rel_pures_l. rel_pures_r.
    rel_bind_l (list_init _ _). rel_bind_r (list_init _ _).
    iApply (refines_bind with "[]").
    { iApply refines_list_init_concrete. iModIntro. iApply Hq. }
    iIntros (xs xs') "Hxs /=".
    iDestruct "Hxs" as (zs) "%Hc". destruct Hc as [Hxs_l Hxs_r].
    rel_pures_l. rel_pures_r.
    (* run the spec pairing map fully to a value via [gwp_list_map (g:=gwp_spec)],
       the [gwp.list] spec-side analogue of [examples.list]'s [spec_list_map]. *)
    rel_bind_r (list_map (λ:"x",("x",#()))%V xs').
    iApply (refines_steps_r _ ⊤ (list_max_index (list_map directsample xs))
              (list_map (λ:"x",("x",#()))%V xs')
              (Val (inject (List.map (λ z : Z, (#z, #())%V) zs)))).
    { iIntros (K) "Hspec".
      iMod (gwp_list_map (g := gwp_spec) (A := Z) (B := val) zs
              (λ z : Z, (#z, #())%V) (λ:"x",("x",#()))%V xs' ⊤
              with "[] [] [$Hspec]") as (rv) "Hpost".
      { iSplit; [|iPureIntro; apply Hxs_r].
        iIntros (z) "!> %Φ0 _ HΦ %K0 Hs". tp_pures. iModIntro.
        iExists (#z, #())%V. iFrame "Hs". iApply "HΦ". done. }
      { iIntros (w) "H". iExact "H". }
      iModIntro. iDestruct "Hpost" as "[Hspec %Hrv]".
      apply is_list_inject in Hrv. rewrite Hrv. iFrame. }
    iModIntro.
    rel_pures_r. simpl. rel_pures_r.
    (* pass-2: direct-sampling map (impl) vs read map (spec), reflexive coupling;
       then argmax of the (pointwise-equal) noisy lists. *)
    rel_bind_l (list_map directsample xs).
    rel_bind_r (list_map _ (inject_list _)).
    iApply (refines_bind with "[]").
    { iApply (refines_list_map unit_pair_rel' (interp TInt [])).
      - iApply refines_directsample_read.
      - iApply (refines_ret with "[]"); [done..|]. iModIntro.
        iApply (is_list_pair_unit_rel zs xs
                  (inject (List.map (λ z : Z, (#z, #())%V) zs))); [done|].
        by apply is_list_inject. }
    iIntros (nv nv') "Hnv /=".
    rel_pures_r.
    iApply (refines_list_max_index (Val nv) (Val nv')).
    iApply (refines_ret with "[Hnv]"); [done..|]. by iModIntro.
  Qed.

End idiomatic.

(** ** Capstone: idiomatic ≡ the REAL presampling at the [lim_exec] level.

    The four relational links ([rnm_link1]/[rnm_link2] forward,
    [rnm_link1']/[rnm_link2'] reverse), over the [gwp.list] combinators, cash out
    by adequacy into a POINTWISE [lim_exec] equality between the one-pass
    idiomatic program [rnm_direct1] and the two-pass presampling program — and the
    presampling program here is DEFINITIONALLY the REAL
    [report_noisy_max_generic.report_noisy_max_presampling sample mass num den]
    (taking [D := mkZNoise sample mass]), so the equality transports to the RNM
    DP theorem [rnm_pres_diffpriv].

    No termination / mass-1 argument: each [REL e << e' : interp TNat] yields
    ([refines_coupling] + [DPcoupl_eq_elim] at [ε=δ=0], where [exp 0 = 1]) a
    one-directional pointwise [≤], and the FOUR links give both directions of the
    chain presampling ≃ direct2 ≃ direct1, so pointwise antisymmetry closes the
    equality. *)
Section idiomatic_lim_exec.
  Context (Sg : Sig).
  Context (sample : Z → Z → Z → distr Z)
          (mass : ∀ num den mean, (SeriesC (sample num den mean) = 1)%R).
  Local Notation D := (mkZNoise sample mass).
  Context {HDin0 : SampleIn D Sg}.
  (** [SampleTyping_mkZNoise] is only a [Lemma] (not a global instance) for an
      abstract [sample]/[mass]; register it locally so the links' [SampleTyping]
      side-condition resolves for [D = mkZNoise sample mass]. *)
  Local Instance HDty0 : SampleTyping D (TInt * (TInt * TInt))%ty TInt :=
    SampleTyping_mkZNoise sample mass.

  (** A single refinement [∀ diffprivRGS, REL e << e' : interp TNat []] cashes out
      to a pointwise [lim_exec] inequality (the [eq]-coupling at zero cost). *)
  Lemma rnm_lim_exec_le (e e' : expr) (σ : state) :
    (∀ `{!diffprivRGS Sg diffprivRΣ}, ⊢ REL e << e' : interp TNat []) →
    ∀ a, (lim_exec (δ := lang_markov (gen_lang Sg)) (e, σ) a
          <= lim_exec (δ := lang_markov (gen_lang Sg)) (e', σ) a)%R.
  Proof.
    intros Hrel a.
    pose proof (refines_coupling Sg diffprivRΣ (λ _, interp TNat []) eq e e' σ σ
                  ltac:(by iIntros (???) "[%n [-> ->]]") Hrel) as Hcpl.
    pose proof (DPcoupl_eq_elim _ _ _ _ Hcpl a) as Hle.
    rewrite exp_0 Rmult_1_l Rplus_0_r in Hle. exact Hle.
  Qed.

  (** Idiomatic [rnm_direct1] and the REAL two-pass
      [report_noisy_max_generic.report_noisy_max_presampling] induce the SAME
      output distribution at every database, given the per-index query
      [Δ]-sensitivity (which provides the [Hq] self-relation the links need). *)
  Lemma rnm_idiomatic_lim_exec_eq (Δ : Z) num den (evalQ : val)
        DB (dDB : Distance DB) (N : nat) (σ : state) :
    (0 <= Δ)%Z →
    (∀ `{!diffprivGS Sg diffprivRΣ}, ∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) →
    ∀ (db : DB),
      lim_exec (δ := lang_markov (gen_lang Sg))
        ((rnm_direct1 D num den evalQ #N (inject db)), σ)
      = lim_exec (δ := lang_markov (gen_lang Sg))
        ((report_noisy_max_generic.report_noisy_max_presampling
            sample mass (Sg := Sg) num den evalQ #N (inject db)), σ).
  Proof.
    intros HΔ Hsens db.
    (* the REAL presampling program is definitionally the section-local one at
       [D := mkZNoise sample mass]. *)
    assert (Hprog :
      report_noisy_max_generic.report_noisy_max_presampling
        sample mass (Sg := Sg) num den
      = report_noisy_max_presampling D num den) by reflexivity.
    rewrite Hprog.
    assert (Hq : ∀ (Hr : diffprivRGS Sg diffprivRΣ),
              ⊢ REL (λ:"i", evalQ "i" (inject db))%V << (λ:"i", evalQ "i" (inject db))%V
                  : (lrel_nat → interp TInt [])%lrel).
    { intros Hr.
      iApply (rnm_query_self_rel D num den Δ evalQ DB dDB db HΔ).
      intros. iApply Hsens. }
    apply distr_ext => a. apply Rle_antisym.
    - (* idiomatic ≤ presampling : direct1 << direct2 << presampling *)
      eapply Rle_trans.
      + apply (rnm_lim_exec_le (rnm_direct1 D num den evalQ #N (inject db))
                 (rnm_direct2 D num den evalQ #N (inject db)) σ).
        intros. iApply (rnm_link2' D). iApply (Hq _).
      + apply (rnm_lim_exec_le (rnm_direct2 D num den evalQ #N (inject db))
                 (report_noisy_max_presampling D num den evalQ #N (inject db)) σ).
        intros. iApply (rnm_link1' D). iApply (Hq _).
    - (* presampling ≤ idiomatic : presampling << direct2 << direct1 *)
      eapply Rle_trans.
      + apply (rnm_lim_exec_le (report_noisy_max_presampling D num den evalQ #N (inject db))
                 (rnm_direct2 D num den evalQ #N (inject db)) σ).
        intros. iApply (rnm_link1 D). iApply (Hq _).
      + apply (rnm_lim_exec_le (rnm_direct2 D num den evalQ #N (inject db))
                 (rnm_direct1 D num den evalQ #N (inject db)) σ).
        intros. iApply (rnm_link2 D). iApply (Hq _).
  Qed.

End idiomatic_lim_exec.
