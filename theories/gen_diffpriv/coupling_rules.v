(** Coupling rules for the generic DP weakest precondition.

    The centerpiece is [wp_couple_tapes_gen]: the GENERIC state-step tape
    coupling, parametric in an ABSTRACT [DPcoupl μ μ' R'] of the two family
    draws.  This is the reuse seam — the per-distribution DP content (Laplace
    shift, Gaussian, RR_coin, …) enters only through that hypothesis; the tape
    plumbing (presampling erasure + spec-side state step) is shared.  Concrete
    per-family coupling rules instantiate the bridge. *)
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From clutch.prelude Require Import stdpp_ext fin.
From clutch.prob Require Import differential_privacy distribution couplings_dp.
From clutch.diffpriv Require Import lifting ectx_lifting.
From clutch.base_logic Require Export error_credits_mult error_credits.
From clutch.gen_diffpriv Require Export primitive_laws.
From clutch.gen_prob_lang Require Import notation tactics metatheory erasure.
From clutch.gen_prob_lang.spec Require Export spec_ra.
(* import gen_prob_lang.lang LAST so concrete expr/val/state shadow the
   [language] record projections re-exported transitively *)
From clutch.gen_prob_lang Require Import lang.

Local Open Scope R.

Section rules.
  Context (Sg : Sig).
  Let gen_markov_cpl := lang_markov (gen_lang Sg).
  Context `{!diffprivGS Sg Σ}.
  #[local] Existing Instance spec_rules_spec_updateGS.
  #[local] Instance spec_updateGS_cpl : spec_updateGS gen_markov_cpl Σ :=
    spec_rules_spec_updateGS Sg.

  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  (* Pin [fill] to the gen evaluation contexts (no global canonical language). *)
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** helper: push a spec evaluation context through a prim-step coupling *)
  Lemma DPcoupl_steps_ctx_bind_r `{Countable A} (μ : distr A)
    e1' σ1' R (ε δ : nonnegreal) K :
    to_val e1' = None →
    DPcoupl μ (prim_step e1' σ1') R ε δ →
    DPcoupl μ (prim_step (fill K e1') σ1')
      (λ a '(e2', σ2'), ∃ e2'', (e2', σ2') = (fill K e2'', σ2') ∧ R a (e2'', σ2')) ε δ.
  Proof.
    intros Hv Hcpl.
    rewrite fill_dmap //= -(dret_id_right μ) /=.
    eapply (DPcoupl_dbind' ε 0 _ δ 0); [lra|done|done|lra| |done].
    intros ? [] ?.
    apply DPcoupl_dret=>/=; [done|done|]. eauto.
  Qed.

  (** Generic state-step tape coupling: from an abstract DP coupling of the two
      family draws [μ = sig_sample Sg i pv] and [μ' = sig_sample Sg i pv'], get
      the WP rule that advances two tapes [α]/[α'] by coupled draws. *)
  Lemma wp_couple_tapes_gen (i : nat) (pv pv' : val) (μ μ' : distr val)
    α α' xs xs' (R' : val → val → Prop) e Φ (ε' : R) E :
    sig_sample Sg i pv = Some μ →
    sig_sample Sg i pv' = Some μ' →
    DPcoupl μ μ' R' ε' 0 →
    ▷ α ↪ (i, pv, xs) ∗ ▷ α' ↪ₛ (i, pv', xs') ∗ ↯m ε' -∗
    (∀ v v', ⌜R' v v'⌝ -∗
        α ↪ (i, pv, xs ++ [v]) ∗ α' ↪ₛ (i, pv', xs' ++ [v']) -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hμ Hμ' Hcpl) "(>Hα & >Hα' & Hε) HΦ".
    iApply wp_lift_step_spec_couple.
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & Hε2 & Hδ2)".
    iDestruct "Hauth2" as "(HK & Hh2 & Ht2)".
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(ε'' & ε_now_rest & foo & Hε'').
    iDestruct (ghost_map_lookup with "Ht2 Hα'") as %Hαs'.
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %Hαs.
    iApply (spec_coupl_erasables_weak
      (λ σ2 σ2', ∃ v v', R' v v' ∧
         σ2 = state_upd_stapes <[α:=(i,pv,xs++[v])]> σ1 ∧
         σ2' = state_upd_stapes <[α':=(i,pv',xs'++[v'])]> σ1')
      (state_step Sg σ1 α) (state_step Sg σ1' α')
      ε'' ε_now_rest ε_now 0%NNR δ_now δ_now);
      [done | apply nnreal_ext; simpl; lra | | by eapply state_step_erasable
       | (eapply state_step_erasable; apply Hαs') | ].
    1:{ erewrite (state_step_unfold Sg σ1 α i pv xs Hαs).
        erewrite (state_step_unfold Sg σ1' α' i pv' xs' Hαs').
        rewrite Hμ Hμ'.
        apply DPcoupl_map; [apply cond_nonneg | apply cond_nonneg | ].
        rewrite Hε''.
        eapply (DPcoupl_mono μ μ μ' μ' R' _ ε' ε' 0 0); [done|done| |lra|lra|exact Hcpl].
        intros x y HR. exists x, y. done. }
    iIntros (σ2 σ2' (v & v' & HR & -> & ->)).
    iApply spec_coupl_ret.
    iMod (ghost_map_update (i, pv, xs ++ [v]) with "Ht1 Hα") as "[$ Hα]".
    iMod (ghost_map_update (i, pv', xs' ++ [v']) with "Ht2 Hα'") as "[$ Hα']".
    iMod (ecm_supply_decrease with "Hε2 Hε") as (ε1 ε2 Hε1 Heq2) "H".
    iModIntro. iMod "Hclose'" as "_".
    iDestruct ("HΦ" $! v v' HR with "[$Hα $Hα']") as "Hwp".
    iFrame "Hh1 HK Hh2 Hwp Hδ2".
    assert (ε2 = ε_now_rest) as ->.
    { apply nnreal_ext. apply (f_equal nonneg) in Hε1, foo. simpl in Hε1, foo. lra. }
    iModIntro. rewrite /mult_ec_supply. iFrame "H".
  Qed.

  (** Per-family specialization: for ANY family [D] in the signature, a coupling
      of its two draws [sf_sample D p] / [sf_sample D p'] (on the outcome type
      [sf_out D]) yields the tape-coupling rule.  Adding a new distribution's
      coupling thus costs exactly one [DPcoupl] obligation — the reuse seam. *)
  Lemma wp_couple_tapes_family (D : SampleFamily) `{!SampleIn D Sg}
    (p p' : sf_param D) α α' xs xs' (Rout : sf_out D → sf_out D → Prop)
    e Φ (ε' : R) E :
    (0 <= ε')%R →
    DPcoupl (sf_sample D p) (sf_sample D p') Rout ε' 0 →
    ▷ α ↪ (sample_idx, sf_param_to_val D p, xs) ∗
    ▷ α' ↪ₛ (sample_idx, sf_param_to_val D p', xs') ∗ ↯m ε' -∗
    (∀ a a', ⌜Rout a a'⌝ -∗
        α ↪ (sample_idx, sf_param_to_val D p, xs ++ [sf_inj D a]) ∗
        α' ↪ₛ (sample_idx, sf_param_to_val D p', xs' ++ [sf_inj D a']) -∗
        WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hε Hcpl) "(Hα & Hα' & Hcred) HΦ".
    assert (DPcoupl (dmap (sf_inj D) (sf_sample D p)) (dmap (sf_inj D) (sf_sample D p'))
              (λ v v', ∃ a a', Rout a a' ∧ v = sf_inj D a ∧ v' = sf_inj D a') ε' 0) as Hcpl'.
    { apply DPcoupl_map; [done | lra | ].
      eapply (DPcoupl_mono (sf_sample D p) (sf_sample D p) (sf_sample D p') (sf_sample D p')
                Rout _ ε' ε' 0 0);
        [intros; reflexivity | intros; reflexivity | | lra | lra | exact Hcpl].
      intros x y Hxy. exists x, y. done. }
    iApply (wp_couple_tapes_gen sample_idx (sf_param_to_val D p) (sf_param_to_val D p')
              (dmap (sf_inj D) (sf_sample D p)) (dmap (sf_inj D) (sf_sample D p'))
              α α' xs xs' _ e Φ ε' E
              (sig_sample_at D Sg p) (sig_sample_at D Sg p') Hcpl' with "[$Hα $Hα' $Hcred]").
    iIntros (v v' (a & a' & Ha & -> & ->)) "Htapes".
    iApply ("HΦ" $! a a' Ha with "Htapes").
  Qed.

  (** Generic PROGRAM-step coupling (no tapes): directly couple two
      [Sample i _ #()] head-steps (impl + spec) via an abstract draw coupling.
      The analogue of the Laplace [hoare_couple_laplace], factored. *)
  Lemma wp_couple_sample_gen (i : nat) (pv pv' : val) (μ μ' : distr val)
    (R' : val → val → Prop) K E (ε' : R) :
    sig_sample Sg i pv = Some μ →
    sig_sample Sg i pv' = Some μ' →
    DPcoupl μ μ' R' ε' 0 →
    {{{ ⤇ fill K (Sample i (Val pv') (Val (LitV LitUnit))) ∗ ↯m ε' }}}
      Sample i (Val pv) (Val (LitV LitUnit)) @ E
    {{{ (v v' : val), RET v; ⤇ fill K (Val v') ∗ ⌜R' v v'⌝ }}}.
  Proof.
    iIntros (Hμ Hμ' Hcpl Φ) "(Hr & Hε) HΦ".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & (Hε2 & Hδ))".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(ε'' & ε_now_rest & foo & Hε'').
    assert (Hps1 : language.prim_step (Sample i (Val pv) (Val (LitV LitUnit))) σ1 = dmap (λ v, (Val v, σ1)) μ).
    { simpl. erewrite head_prim_step_eq; last first.
      { destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ); lra|].
        eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS. }
      simpl. rewrite Hμ. done. }
    assert (Hps1' : language.prim_step (Sample i (Val pv') (Val (LitV LitUnit))) σ1' = dmap (λ v, (Val v, σ1')) μ').
    { simpl. erewrite head_prim_step_eq; last first.
      { destruct (SeriesC_gtz_ex μ' (pmf_pos μ')) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ'); lra|].
        eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS. }
      simpl. rewrite Hμ'. done. }
    iApply (prog_coupl_steps_simple ε_now_rest ε'' ε_now δ_now 0%NNR);
      [done | apply nnreal_ext; simpl; lra | | | | ].
    - apply head_prim_reducible. destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ); lra|].
      eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS.
    - apply reducible_fill. apply head_prim_reducible. destruct (SeriesC_gtz_ex μ' (pmf_pos μ')) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ'); lra|].
      eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS.
    - apply (DPcoupl_steps_ctx_bind_r _ _ _
              (λ ρ ρ' : cfg, ∃ v v', R' v v' ∧ ρ = (Val v, σ1) ∧ ρ' = (Val v', σ1'))); [done|].
      rewrite Hps1 Hps1' /dmap.
      eapply (DPcoupl_dbind' ε'' 0 ε'' 0 0 0); [lra|done|done|lra| |rewrite Hε''; exact Hcpl].
      intros w w' Hww'. apply DPcoupl_dret; [done|done|]. exists w, w'. done.
    - iIntros (e2 σ2 e2' σ2' (e2'' & [=->] & (w & w' & Hww' & [=-> ->] & [=-> ->]))).
      iMod (spec_update_prog (fill K (Val w')) with "Hauth2 Hr") as "[$ Hspec]".
      iMod (ecm_supply_decrease with "Hε2 Hε") as (a b Herr Heq) "H".
      do 2 iModIntro. iMod "Hclose'" as "_". iModIntro. iFrame "Hh1 Ht1".
      rewrite -wp_value.
      iSplitR "Hspec HΦ".
      2: { iApply ("HΦ" $! w w'). iFrame "Hspec". done. }
      rewrite /err_interp /=. iFrame "Hδ".
      assert (b = ε_now_rest) as ->.
      { apply nnreal_ext. apply (f_equal nonneg) in Herr, foo. simpl in *. lra. }
      rewrite /mult_ec_supply. iFrame "H".
  Qed.

  (** δ-CARRYING generic PROGRAM-step coupling.  Exactly [wp_couple_sample_gen]
      but the abstract draw coupling may carry a nonzero ADDITIVE error [δ']
      (paid by an extra [↯ δ'] credit), in addition to the multiplicative [ε'].
      This is what an APPROXIMATE-DP mechanism (e.g. the truncated Laplace, whose
      per-distance coupling [DPcoupl_trunc_lap] has [δ = tlap_delta > 0]) needs:
      the existing [wp_couple_sample_gen] hard-wires [δ = 0].  Purely ADDITIVE —
      it sits alongside [wp_couple_sample_gen] and changes nothing existing. *)
  Lemma wp_couple_sample_gen_dp (i : nat) (pv pv' : val) (μ μ' : distr val)
    (R' : val → val → Prop) K E (ε' δ' : R) :
    (0 <= δ')%R →
    sig_sample Sg i pv = Some μ →
    sig_sample Sg i pv' = Some μ' →
    DPcoupl μ μ' R' ε' δ' →
    {{{ ⤇ fill K (Sample i (Val pv') (Val (LitV LitUnit))) ∗ ↯m ε' ∗ ↯ δ' }}}
      Sample i (Val pv) (Val (LitV LitUnit)) @ E
    {{{ (v v' : val), RET v; ⤇ fill K (Val v') ∗ ⌜R' v v'⌝ }}}.
  Proof.
    iIntros (Hδ'pos Hμ Hμ' Hcpl Φ) "(Hr & Hε & Hδc) HΦ".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & (Hε2 & Hδ))".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(ε'' & ε_now_rest & foo & Hε'').
    iDestruct (ec_supply_ec_inv with "Hδ Hδc") as %(δ'' & δ_now_rest & foo_δ & Hδ'').
    assert (Hps1 : language.prim_step (Sample i (Val pv) (Val (LitV LitUnit))) σ1 = dmap (λ v, (Val v, σ1)) μ).
    { simpl. erewrite head_prim_step_eq; last first.
      { destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ); lra|].
        eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS. }
      simpl. rewrite Hμ. done. }
    assert (Hps1' : language.prim_step (Sample i (Val pv') (Val (LitV LitUnit))) σ1' = dmap (λ v, (Val v, σ1')) μ').
    { simpl. erewrite head_prim_step_eq; last first.
      { destruct (SeriesC_gtz_ex μ' (pmf_pos μ')) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ'); lra|].
        eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS. }
      simpl. rewrite Hμ'. done. }
    iApply (prog_coupl_steps_simple ε_now_rest ε'' ε_now δ_now_rest δ'' δ_now);
      [done | exact foo_δ | | | | ].
    - apply head_prim_reducible. destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ); lra|].
      eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS.
    - apply reducible_fill. apply head_prim_reducible. destruct (SeriesC_gtz_ex μ' (pmf_pos μ')) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ'); lra|].
      eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS.
    - apply (DPcoupl_steps_ctx_bind_r _ _ _
              (λ ρ ρ' : cfg, ∃ v v', R' v v' ∧ ρ = (Val v, σ1) ∧ ρ' = (Val v', σ1'))); [done|].
      rewrite Hps1 Hps1' /dmap.
      eapply (DPcoupl_dbind' ε'' 0 ε'' δ'' 0 δ''); [lra|lra|done|lra| |rewrite Hε'' Hδ''; exact Hcpl].
      intros w w' Hww'. apply DPcoupl_dret; [done|done|]. exists w, w'. done.
    - iIntros (e2 σ2 e2' σ2' (e2'' & [=->] & (w & w' & Hww' & [=-> ->] & [=-> ->]))).
      iMod (spec_update_prog (fill K (Val w')) with "Hauth2 Hr") as "[$ Hspec]".
      iMod (ecm_supply_decrease with "Hε2 Hε") as (a b Herr Heq) "H".
      iMod (ec_supply_decrease with "Hδ Hδc") as (aδ bδ Herrδ Heqδ) "Hd".
      do 2 iModIntro. iMod "Hclose'" as "_". iModIntro. iFrame "Hh1 Ht1".
      rewrite -wp_value.
      iSplitR "Hspec HΦ".
      2: { iApply ("HΦ" $! w w'). iFrame "Hspec". done. }
      rewrite /err_interp /=.
      assert (b = ε_now_rest) as ->.
      { apply nnreal_ext. apply (f_equal nonneg) in Herr, foo. simpl in *. lra. }
      assert (bδ = δ_now_rest) as ->.
      { apply nnreal_ext. apply (f_equal nonneg) in Herrδ, foo_δ. simpl in *. lra. }
      rewrite /mult_ec_supply /add_ec_supply. iFrame "H Hd".
  Qed.

  (** Empty-tape PROGRAM-step coupling.  The tape-based analogue of
      [wp_couple_sample_gen]: couple two labelled samples [Sample i _ #lbl:α]
      whose tapes [α]/[α'] are EMPTY.  An empty tape's read collapses to a fresh
      draw from [sig_sample Sg i pv] regardless of the tape's stored descriptor
      [(i1,pv1)] (head_step's empty-match and descriptor-mismatch branches
      coincide; cf. [SampleTapeEmptyS]/[SampleTapeOtherS]), so the [DPcoupl]
      obligation is identical to [wp_couple_sample_gen] and the tapes are
      returned unchanged.  This is what makes typing the tape form of [Sample]
      sound (see [refines_sample_tape]). *)
  Lemma wp_couple_sample_tape_gen (i : nat) (pv pv' : val) (μ μ' : distr val)
    (R' : val → val → Prop) (α α' : loc) i1 pv1 i1' pv1' K E (ε' : R) :
    sig_sample Sg i pv = Some μ →
    sig_sample Sg i pv' = Some μ' →
    DPcoupl μ μ' R' ε' 0 →
    {{{ ⤇ fill K (Sample i (Val pv') (Val (LitV (LitLbl α')))) ∗
        α ↪ (i1, pv1, []) ∗ α' ↪ₛ (i1', pv1', []) ∗ ↯m ε' }}}
      Sample i (Val pv) (Val (LitV (LitLbl α))) @ E
    {{{ (v v' : val), RET v;
        ⤇ fill K (Val v') ∗ α ↪ (i1, pv1, []) ∗ α' ↪ₛ (i1', pv1', []) ∗ ⌜R' v v'⌝ }}}.
  Proof.
    iIntros (Hμ Hμ' Hcpl Φ) "(Hr & Hα & Hα' & Hε) HΦ".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & (Hε2 & Hδ))".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(ε'' & ε_now_rest & foo & Hε'').
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %Hβ.
    iDestruct (spec_auth_lookup_tape with "Hauth2 Hα'") as %Hβ'.
    assert (Hps1 : language.prim_step (Sample i (Val pv) (Val (LitV (LitLbl α)))) σ1 = dmap (λ v, (Val v, σ1)) μ).
    { simpl. erewrite head_prim_step_eq; last first.
      { destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ); lra|].
        eexists (_,_). apply head_step_support_equiv_rel.
        destruct (decide (i = i1 ∧ pv = pv1)) as [Hd|Hd].
        - destruct Hd as [-> ->]. eapply SampleTapeEmptyS; [exact Hβ | exact Hμ | exact Hw].
        - eapply SampleTapeOtherS; [exact Hβ | exact Hd | exact Hμ | exact Hw]. }
      simpl. rewrite Hβ. case_bool_decide as Hd; rewrite Hμ //. }
    assert (Hps1' : language.prim_step (Sample i (Val pv') (Val (LitV (LitLbl α')))) σ1' = dmap (λ v, (Val v, σ1')) μ').
    { simpl. erewrite head_prim_step_eq; last first.
      { destruct (SeriesC_gtz_ex μ' (pmf_pos μ')) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ'); lra|].
        eexists (_,_). apply head_step_support_equiv_rel.
        destruct (decide (i = i1' ∧ pv' = pv1')) as [Hd|Hd].
        - destruct Hd as [-> ->]. eapply SampleTapeEmptyS; [exact Hβ' | exact Hμ' | exact Hw].
        - eapply SampleTapeOtherS; [exact Hβ' | exact Hd | exact Hμ' | exact Hw]. }
      simpl. rewrite Hβ'. case_bool_decide as Hd; rewrite Hμ' //. }
    iApply (prog_coupl_steps_simple ε_now_rest ε'' ε_now δ_now 0%NNR);
      [done | apply nnreal_ext; simpl; lra | | | | ].
    - apply head_prim_reducible. destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ); lra|].
      eexists (_,_). apply head_step_support_equiv_rel.
      destruct (decide (i = i1 ∧ pv = pv1)) as [Hd|Hd];
        [destruct Hd as [-> ->]; eapply SampleTapeEmptyS | eapply SampleTapeOtherS]; eauto.
    - apply reducible_fill. apply head_prim_reducible. destruct (SeriesC_gtz_ex μ' (pmf_pos μ')) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ'); lra|].
      eexists (_,_). apply head_step_support_equiv_rel.
      destruct (decide (i = i1' ∧ pv' = pv1')) as [Hd|Hd];
        [destruct Hd as [-> ->]; eapply SampleTapeEmptyS | eapply SampleTapeOtherS]; eauto.
    - apply (DPcoupl_steps_ctx_bind_r _ _ _
              (λ ρ ρ' : cfg, ∃ v v', R' v v' ∧ ρ = (Val v, σ1) ∧ ρ' = (Val v', σ1'))); [done|].
      rewrite Hps1 Hps1' /dmap.
      eapply (DPcoupl_dbind' ε'' 0 ε'' 0 0 0); [lra|done|done|lra| |rewrite Hε''; exact Hcpl].
      intros w w' Hww'. apply DPcoupl_dret; [done|done|]. exists w, w'. done.
    - iIntros (e2 σ2 e2' σ2' (e2'' & [=->] & (w & w' & Hww' & [=-> ->] & [=-> ->]))).
      iMod (spec_update_prog (fill K (Val w')) with "Hauth2 Hr") as "[$ Hspec]".
      iMod (ecm_supply_decrease with "Hε2 Hε") as (a b Herr Heq) "H".
      do 2 iModIntro. iMod "Hclose'" as "_". iModIntro. iFrame "Hh1 Ht1".
      rewrite -wp_value.
      iSplitR "Hspec HΦ Hα Hα'".
      2: { iApply ("HΦ" $! w w'). iFrame "Hspec Hα Hα'". done. }
      rewrite /err_interp /=. iFrame "Hδ".
      assert (b = ε_now_rest) as ->.
      { apply nnreal_ext. apply (f_equal nonneg) in Herr, foo. simpl in *. lra. }
      rewrite /mult_ec_supply. iFrame "H".
  Qed.

  (** MIXED PROGRAM-step coupling, impl-tape side.  The impl reads an EMPTY tape
      [α] (its read collapses to a fresh draw, exactly as in
      [wp_couple_sample_tape_gen]) while the spec samples DIRECTLY [Sample i _ ()]
      (a fresh [SampleNoTapeS] draw, exactly as in [wp_couple_sample_gen]).  The
      [DPcoupl] obligation and the [α]-tape (returned unchanged) are unaffected.
      Used to relate tape-allocated sampling on the left against direct sampling
      on the right (the tape-erasure equivalence). *)
  Lemma wp_couple_sample_tape_l (i : nat) (pv pv' : val) (μ μ' : distr val)
    (R' : val → val → Prop) (α : loc) i1 pv1 K E (ε' : R) :
    sig_sample Sg i pv = Some μ →
    sig_sample Sg i pv' = Some μ' →
    DPcoupl μ μ' R' ε' 0 →
    {{{ ⤇ fill K (Sample i (Val pv') (Val (LitV LitUnit))) ∗
        α ↪ (i1, pv1, []) ∗ ↯m ε' }}}
      Sample i (Val pv) (Val (LitV (LitLbl α))) @ E
    {{{ (v v' : val), RET v;
        ⤇ fill K (Val v') ∗ α ↪ (i1, pv1, []) ∗ ⌜R' v v'⌝ }}}.
  Proof.
    iIntros (Hμ Hμ' Hcpl Φ) "(Hr & Hα & Hε) HΦ".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & (Hε2 & Hδ))".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(ε'' & ε_now_rest & foo & Hε'').
    iDestruct (ghost_map_lookup with "Ht1 Hα") as %Hβ.
    assert (Hps1 : language.prim_step (Sample i (Val pv) (Val (LitV (LitLbl α)))) σ1 = dmap (λ v, (Val v, σ1)) μ).
    { simpl. erewrite head_prim_step_eq; last first.
      { destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ); lra|].
        eexists (_,_). apply head_step_support_equiv_rel.
        destruct (decide (i = i1 ∧ pv = pv1)) as [Hd|Hd].
        - destruct Hd as [-> ->]. eapply SampleTapeEmptyS; [exact Hβ | exact Hμ | exact Hw].
        - eapply SampleTapeOtherS; [exact Hβ | exact Hd | exact Hμ | exact Hw]. }
      simpl. rewrite Hβ. case_bool_decide as Hd; rewrite Hμ //. }
    assert (Hps1' : language.prim_step (Sample i (Val pv') (Val (LitV LitUnit))) σ1' = dmap (λ v, (Val v, σ1')) μ').
    { simpl. erewrite head_prim_step_eq; last first.
      { destruct (SeriesC_gtz_ex μ' (pmf_pos μ')) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ'); lra|].
        eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS. }
      simpl. rewrite Hμ'. done. }
    iApply (prog_coupl_steps_simple ε_now_rest ε'' ε_now δ_now 0%NNR);
      [done | apply nnreal_ext; simpl; lra | | | | ].
    - apply head_prim_reducible. destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ); lra|].
      eexists (_,_). apply head_step_support_equiv_rel.
      destruct (decide (i = i1 ∧ pv = pv1)) as [Hd|Hd];
        [destruct Hd as [-> ->]; eapply SampleTapeEmptyS | eapply SampleTapeOtherS]; eauto.
    - apply reducible_fill. apply head_prim_reducible. destruct (SeriesC_gtz_ex μ' (pmf_pos μ')) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ'); lra|].
      eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS.
    - apply (DPcoupl_steps_ctx_bind_r _ _ _
              (λ ρ ρ' : cfg, ∃ v v', R' v v' ∧ ρ = (Val v, σ1) ∧ ρ' = (Val v', σ1'))); [done|].
      rewrite Hps1 Hps1' /dmap.
      eapply (DPcoupl_dbind' ε'' 0 ε'' 0 0 0); [lra|done|done|lra| |rewrite Hε''; exact Hcpl].
      intros w w' Hww'. apply DPcoupl_dret; [done|done|]. exists w, w'. done.
    - iIntros (e2 σ2 e2' σ2' (e2'' & [=->] & (w & w' & Hww' & [=-> ->] & [=-> ->]))).
      iMod (spec_update_prog (fill K (Val w')) with "Hauth2 Hr") as "[$ Hspec]".
      iMod (ecm_supply_decrease with "Hε2 Hε") as (a b Herr Heq) "H".
      do 2 iModIntro. iMod "Hclose'" as "_". iModIntro. iFrame "Hh1 Ht1".
      rewrite -wp_value.
      iSplitR "Hspec HΦ Hα".
      2: { iApply ("HΦ" $! w w'). iFrame "Hspec Hα". done. }
      rewrite /err_interp /=. iFrame "Hδ".
      assert (b = ε_now_rest) as ->.
      { apply nnreal_ext. apply (f_equal nonneg) in Herr, foo. simpl in *. lra. }
      rewrite /mult_ec_supply. iFrame "H".
  Qed.

  (** MIXED PROGRAM-step coupling, spec-tape side (mirror of
      [wp_couple_sample_tape_l]).  The impl samples DIRECTLY [Sample i _ ()] while
      the spec reads an EMPTY tape [α'].  Used to relate direct sampling on the
      left against tape-allocated sampling on the right. *)
  Lemma wp_couple_sample_tape_r (i : nat) (pv pv' : val) (μ μ' : distr val)
    (R' : val → val → Prop) (α' : loc) i1' pv1' K E (ε' : R) :
    sig_sample Sg i pv = Some μ →
    sig_sample Sg i pv' = Some μ' →
    DPcoupl μ μ' R' ε' 0 →
    {{{ ⤇ fill K (Sample i (Val pv') (Val (LitV (LitLbl α')))) ∗
        α' ↪ₛ (i1', pv1', []) ∗ ↯m ε' }}}
      Sample i (Val pv) (Val (LitV LitUnit)) @ E
    {{{ (v v' : val), RET v;
        ⤇ fill K (Val v') ∗ α' ↪ₛ (i1', pv1', []) ∗ ⌜R' v v'⌝ }}}.
  Proof.
    iIntros (Hμ Hμ' Hcpl Φ) "(Hr & Hα' & Hε) HΦ".
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & (Hε2 & Hδ))".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(ε'' & ε_now_rest & foo & Hε'').
    iDestruct (spec_auth_lookup_tape with "Hauth2 Hα'") as %Hβ'.
    assert (Hps1 : language.prim_step (Sample i (Val pv) (Val (LitV LitUnit))) σ1 = dmap (λ v, (Val v, σ1)) μ).
    { simpl. erewrite head_prim_step_eq; last first.
      { destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ); lra|].
        eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS. }
      simpl. rewrite Hμ. done. }
    assert (Hps1' : language.prim_step (Sample i (Val pv') (Val (LitV (LitLbl α')))) σ1' = dmap (λ v, (Val v, σ1')) μ').
    { simpl. erewrite head_prim_step_eq; last first.
      { destruct (SeriesC_gtz_ex μ' (pmf_pos μ')) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ'); lra|].
        eexists (_,_). apply head_step_support_equiv_rel.
        destruct (decide (i = i1' ∧ pv' = pv1')) as [Hd|Hd].
        - destruct Hd as [-> ->]. eapply SampleTapeEmptyS; [exact Hβ' | exact Hμ' | exact Hw].
        - eapply SampleTapeOtherS; [exact Hβ' | exact Hd | exact Hμ' | exact Hw]. }
      simpl. rewrite Hβ'. case_bool_decide as Hd; rewrite Hμ' //. }
    iApply (prog_coupl_steps_simple ε_now_rest ε'' ε_now δ_now 0%NNR);
      [done | apply nnreal_ext; simpl; lra | | | | ].
    - apply head_prim_reducible. destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ); lra|].
      eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS.
    - apply reducible_fill. apply head_prim_reducible. destruct (SeriesC_gtz_ex μ' (pmf_pos μ')) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ'); lra|].
      eexists (_,_). apply head_step_support_equiv_rel.
      destruct (decide (i = i1' ∧ pv' = pv1')) as [Hd|Hd];
        [destruct Hd as [-> ->]; eapply SampleTapeEmptyS | eapply SampleTapeOtherS]; eauto.
    - apply (DPcoupl_steps_ctx_bind_r _ _ _
              (λ ρ ρ' : cfg, ∃ v v', R' v v' ∧ ρ = (Val v, σ1) ∧ ρ' = (Val v', σ1'))); [done|].
      rewrite Hps1 Hps1' /dmap.
      eapply (DPcoupl_dbind' ε'' 0 ε'' 0 0 0); [lra|done|done|lra| |rewrite Hε''; exact Hcpl].
      intros w w' Hww'. apply DPcoupl_dret; [done|done|]. exists w, w'. done.
    - iIntros (e2 σ2 e2' σ2' (e2'' & [=->] & (w & w' & Hww' & [=-> ->] & [=-> ->]))).
      iMod (spec_update_prog (fill K (Val w')) with "Hauth2 Hr") as "[$ Hspec]".
      iMod (ecm_supply_decrease with "Hε2 Hε") as (a b Herr Heq) "H".
      do 2 iModIntro. iMod "Hclose'" as "_". iModIntro. iFrame "Hh1 Ht1".
      rewrite -wp_value.
      iSplitR "Hspec HΦ Hα'".
      2: { iApply ("HΦ" $! w w'). iFrame "Hspec Hα'". done. }
      rewrite /err_interp /=. iFrame "Hδ".
      assert (b = ε_now_rest) as ->.
      { apply nnreal_ext. apply (f_equal nonneg) in Herr, foo. simpl in *. lra. }
      rewrite /mult_ec_supply. iFrame "H".
  Qed.

End rules.
