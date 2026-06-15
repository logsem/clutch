(** Tape-erasure equivalence for the generic DP logical relation.

    Allocating a fresh uniform sample-tape and reading it once is contextually
    EQUIVALENT to sampling directly:

      tape_sampler   = λ n, let α = AllocSampleTape unif n in Sample unif n α
      direct_sampler = λ n, Sample unif n #()

    An empty tape's read collapses to a fresh draw from [sig_sample] (head_step's
    [SampleTapeEmptyS]/[SampleTapeOtherS]), the same distribution that a direct
    [Sample _ ()] draws via [SampleNoTapeS].  The MIXED coupling rules
    [wp_couple_sample_tape_l] / [wp_couple_sample_tape_r] couple a tape read
    against a direct sample at zero cost, so the two programs refine each other in
    both directions; [refines_sound] then yields contextual equivalence. *)
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import distribution couplings_dp.
From clutch.gen_diffpriv Require Import model interp fundamental soundness
  coupling_rules app_rel_rules rel_tactics.
From clutch.gen_prob_lang Require Import lang notation families.
From clutch.gen_prob_lang.typing Require Import types contextual_refinement.
From iris.prelude Require Import options.

Local Open Scope R.

Section tape_erasure_sec.
  Context (Sg : Sig).
  Context `{!SampleIn uniform_family Sg}.

  Notation unif := (sample_idx (D := uniform_family)).

  Definition tape_sampler : val :=
    (λ: "n", let: "α" := AllocSampleTape unif "n" in
             Sample unif "n" "α")%V.
  Definition direct_sampler : val :=
    (λ: "n", Sample unif "n" #())%V.

  Context `{!diffprivRGS Sg Σ}.
  Canonical Structure gen_ectxi_lang_te := gen_ectxi_lang Sg.
  Canonical Structure gen_ectx_lang_te := gen_ectx_lang Sg.
  Canonical Structure gen_lang_te := gen_lang Sg.
  Canonical Structure gen_markov_te := lang_markov (gen_lang Sg).
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  #[local] Existing Instance spec_rules_spec_updateGS.
  #[local] Instance spec_updateGS_te : spec_updateGS gen_markov_te Σ :=
    spec_rules_spec_updateGS Sg.

  (** Reflexive coupling helper (re-stated locally). *)
  Lemma DPcoupl_refl_te `{Countable A} (μ : distr A) : DPcoupl μ μ (=) 0 0.
  Proof. apply ARcoupl_to_DPcoupl, ARcoupl_eq. Qed.

  (** The uniform family at index [unif] decodes a [nat]-literal parameter
      [#(N:nat)] (= [sf_param_to_val uniform_family N]) and samples [unif N]. *)
  Lemma sig_sample_unif (N : nat) :
    sig_sample Sg unif (LitV (LitInt (Z.of_nat N)))
      = Some (dmap (sf_inj uniform_family) (sf_sample uniform_family N)).
  Proof.
    unfold sig_sample. rewrite (sample_idx_S (D := uniform_family)) /=.
    rewrite Nat2Z.id /=. reflexivity.
  Qed.

  Lemma tape_refines_direct Δ :
    ⊢ REL tape_sampler << direct_sampler : interp (TNat → TInt) Δ.
  Proof.
    rewrite /tape_sampler /direct_sampler.
    iApply refines_arrow_val. iModIntro. iIntros (n n') "#Hn".
    iDestruct "Hn" as (N) "[-> ->]".
    rel_pures_l. rel_pures_r.
    (* LHS: allocate the impl tape, then reduce the let. *)
    rel_bind_l (AllocSampleTape unif _).
    iApply (refines_alloc_sample_tape_l _ ⊤ unif (LitV (LitInt (Z.of_nat N)))).
    iModIntro. iIntros (α) "Hα". simpl.
    rel_pures_l.
    (* couple the tape read against the direct sample, at zero cost. *)
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hspec Hna Herr %Hε".
    iMod ecm_zero as "Hm".
    iApply (wp_couple_sample_tape_l Sg unif
              (LitV (LitInt (Z.of_nat N))) (LitV (LitInt (Z.of_nat N)))
              (dmap (sf_inj uniform_family) (sf_sample uniform_family N))
              (dmap (sf_inj uniform_family) (sf_sample uniform_family N))
              (λ w w', ∃ o : sf_out uniform_family, w = sf_inj uniform_family o ∧ w' = sf_inj uniform_family o)
              α unif (LitV (LitInt (Z.of_nat N))) K ⊤ 0
              (sig_sample_unif N) (sig_sample_unif N) _
              with "[$Hspec $Hα $Hm]").
    iIntros "!>" (w w') "(Hspec & Hα & %HR)". destruct HR as (o & -> & ->).
    iExists (sf_inj uniform_family o), ε. iFrame "Hspec Hna Herr".
    iSplitR; [done|].
    iApply (interp_of_ground TInt Δ (sf_inj uniform_family o)).
    apply (st_out (D := uniform_family) (τp := TNat) (τo := TInt)).
    Unshelve.
    apply (DPcoupl_map (sf_inj uniform_family) (sf_inj uniform_family)
             (sf_sample uniform_family N) (sf_sample uniform_family N)
             (λ w w', ∃ o : sf_out uniform_family, w = sf_inj uniform_family o ∧ w' = sf_inj uniform_family o) 0 0); [lra|lra|].
    eapply (DPcoupl_mono (sf_sample uniform_family N) (sf_sample uniform_family N)
              (sf_sample uniform_family N) (sf_sample uniform_family N)
              (=) (λ a a', ∃ o : sf_out uniform_family, sf_inj uniform_family a = sf_inj uniform_family o ∧ sf_inj uniform_family a' = sf_inj uniform_family o)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra | apply DPcoupl_refl_te ].
  Qed.

  Lemma direct_refines_tape Δ :
    ⊢ REL direct_sampler << tape_sampler : interp (TNat → TInt) Δ.
  Proof.
    rewrite /tape_sampler /direct_sampler.
    iApply refines_arrow_val. iModIntro. iIntros (n n') "#Hn".
    iDestruct "Hn" as (N) "[-> ->]".
    rel_pures_l. rel_pures_r.
    (* RHS: allocate the spec tape, then reduce the let. *)
    rel_bind_r (AllocSampleTape unif _).
    iApply (refines_alloc_sample_tape_r ⊤ _ unif (LitV (LitInt (Z.of_nat N)))).
    iIntros (α') "Hα'". simpl.
    rel_pures_r.
    rewrite refines_eq /refines_def.
    iIntros (K ε) "Hspec Hna Herr %Hε".
    iMod ecm_zero as "Hm".
    iApply (wp_couple_sample_tape_r Sg unif
              (LitV (LitInt (Z.of_nat N))) (LitV (LitInt (Z.of_nat N)))
              (dmap (sf_inj uniform_family) (sf_sample uniform_family N))
              (dmap (sf_inj uniform_family) (sf_sample uniform_family N))
              (λ w w', ∃ o : sf_out uniform_family, w = sf_inj uniform_family o ∧ w' = sf_inj uniform_family o)
              α' unif (LitV (LitInt (Z.of_nat N))) K ⊤ 0
              (sig_sample_unif N) (sig_sample_unif N) _
              with "[$Hspec $Hα' $Hm]").
    iIntros "!>" (w w') "(Hspec & Hα' & %HR)". destruct HR as (o & -> & ->).
    iExists (sf_inj uniform_family o), ε. iFrame "Hspec Hna Herr".
    iSplitR; [done|].
    iApply (interp_of_ground TInt Δ (sf_inj uniform_family o)).
    apply (st_out (D := uniform_family) (τp := TNat) (τo := TInt)).
    Unshelve.
    apply (DPcoupl_map (sf_inj uniform_family) (sf_inj uniform_family)
             (sf_sample uniform_family N) (sf_sample uniform_family N)
             (λ w w', ∃ o : sf_out uniform_family, w = sf_inj uniform_family o ∧ w' = sf_inj uniform_family o) 0 0); [lra|lra|].
    eapply (DPcoupl_mono (sf_sample uniform_family N) (sf_sample uniform_family N)
              (sf_sample uniform_family N) (sf_sample uniform_family N)
              (=) (λ a a', ∃ o : sf_out uniform_family, sf_inj uniform_family a = sf_inj uniform_family o ∧ sf_inj uniform_family a' = sf_inj uniform_family o)
              0 0 0 0);
      [ intros; reflexivity | intros; reflexivity
      | intros a a' ->; by exists a' | lra | lra | apply DPcoupl_refl_te ].
  Qed.

End tape_erasure_sec.

(** Contextual equivalence, both directions, from the fundamental soundness
    theorem ([refines_sound]). *)
Lemma tape_sampler_ctx_le (Sg : Sig) `{!SampleIn uniform_family Sg}
  Σ' `{!diffprivRGpreS Σ'} :
  ctx_refines Sg ∅ (tape_sampler Sg) (direct_sampler Sg) (TNat → TInt)%ty.
Proof.
  apply (refines_sound Sg Σ'). intros ? Δ. iApply tape_refines_direct.
Qed.

Lemma tape_sampler_ctx_ge (Sg : Sig) `{!SampleIn uniform_family Sg}
  Σ' `{!diffprivRGpreS Σ'} :
  ctx_refines Sg ∅ (direct_sampler Sg) (tape_sampler Sg) (TNat → TInt)%ty.
Proof.
  apply (refines_sound Sg Σ'). intros ? Δ. iApply direct_refines_tape.
Qed.
