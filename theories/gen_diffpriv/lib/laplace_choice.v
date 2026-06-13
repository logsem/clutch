(** The "choice" Laplace coupling [hoare_couple_laplace_choice] for the generic
    DP logic — the core coupling behind the Sparse Vector Technique.

    Unlike [hoare_couple_laplace] (a single shift coupling), this rule couples a
    single Laplace draw with a CASE SPLIT on a threshold [T]: in the
    above-threshold region the spec draw is shifted by 1 (paying [ε] more), and
    in the below-threshold region the coupling is exact and the error budget is
    *refunded*.  This needs the two-region program-step coupling
    [prog_coupl_steps] (reused from the Λ-generic core), fed the per-region
    Laplace prim-step couplings; it cannot be derived from the single-coupling
    seam [wp_couple_sample_gen].

    Ported from [diffpriv.coupling_rules.hoare_couple_laplace_choice], with the
    [prob_lang] [Laplace] head-step replaced by the generic [Sample] head-step
    (whose prim-step is [dmap (λ v, (Val v, σ)) μ] for [μ = sig_sample …], exactly
    as in [wp_couple_sample_gen]). *)
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import differential_privacy distribution couplings couplings_app couplings_dp.
From clutch.diffpriv Require Import lifting ectx_lifting.
From clutch.gen_prob_lang Require Import notation tactics metatheory erasure lang.
From clutch.gen_diffpriv.lib Require Export laplace.
From clutch.common Require Import language ectx_language.

Local Open Scope R.

Section laplace_choice.
  Context {S : Sig} `{!SampleIn laplace_family S} `{!diffprivGS S Σ}.
  Canonical Structure gen_ectxi_lang_lch := gen_ectxi_lang S.
  Canonical Structure gen_ectx_lang_lch := gen_ectx_lang S.
  Canonical Structure gen_lang_lch := gen_lang S.
  Canonical Structure gen_markov_lch := lang_markov (gen_lang S).
  #[local] Existing Instance spec_rules_spec_updateGS.
  #[local] Instance spec_updateGS_lch : spec_updateGS gen_markov_lch Σ :=
    spec_rules_spec_updateGS S.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang S)).
  Local Notation lidx := (@sample_idx laplace_family S _).

  (** The threshold "choice" coupling.  [loc]/[loc'] are the adjacent locations
      (within distance 1); the impl draw [z] and spec draw [z'] are coupled so
      that on the above-threshold region ([T ≤ z]) we get [T+1 ≤ z'], and on the
      below-threshold region ([z < T]) we get [z' < T+1] with the [ε'] budget
      refunded. *)
  Lemma wp_couple_laplace_choice (loc loc' T : Z)
    (dist_loc : (Z.abs (loc - loc') <= 1)%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (2 * ε) →
    {{{ ⤇ fill K (Sample lidx
                    (Val (PairV (LitV (LitInt num))
                            (PairV (LitV (LitInt den)) (LitV (LitInt loc')))))
                    (Val (LitV LitUnit))) ∗ ↯m ε' }}}
      Sample lidx
        (Val (PairV (LitV (LitInt num))
                (PairV (LitV (LitInt den)) (LitV (LitInt loc)))))
        (Val (LitV LitUnit)) @ E
      {{{ (z : Z), RET #z;
          ∃ z' : Z, ⤇ fill K #z'
                 ∗ ( ⌜(T <= z ∧ T + 1 <= z')⌝
                     ∨ (⌜z < T ∧ z' < T + 1⌝ ∗ ↯m ε'))%Z }}}.
  Proof.
    iIntros (Hε εpos Hε' Φ) "(Hr & Hε) Hcnt".
    set (pv := sf_param_to_val laplace_family (num, den, loc)).
    set (pv' := sf_param_to_val laplace_family (num, den, loc')).
    set (μ := dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc))).
    set (μ' := dmap (sf_inj laplace_family) (sf_sample laplace_family (num, den, loc'))).
    assert (Hμ : sig_sample S lidx pv = Some μ).
    { apply (sig_sample_at laplace_family S (num, den, loc)). }
    assert (Hμ' : sig_sample S lidx pv' = Some μ').
    { apply (sig_sample_at laplace_family S (num, den, loc')). }
    iApply wp_lift_step_prog_couple; [done|].
    iIntros (σ1 e1' σ1' ε_now δ_now) "((Hh1 & Ht1) & Hauth2 & (Hε2 & Hδ))".
    iDestruct (spec_auth_prog_agree with "Hauth2 Hr") as %->.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose'".
    iDestruct (ecm_supply_ecm_inv with "Hε2 Hε") as %(x & ε_now_rest & H_ε_now & Hε'').
    (* prim-step distributions (cf. [wp_couple_sample_gen]) *)
    assert (Hps1 : common.language.prim_step (Sample lidx (Val pv) (Val (LitV LitUnit))) σ1
                   = dmap (λ v, (Val v, σ1)) μ).
    { simpl. erewrite head_prim_step_eq; last first.
      { destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ); lra|].
        eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS. }
      simpl. rewrite Hμ. done. }
    assert (Hps1' : common.language.prim_step (Sample lidx (Val pv') (Val (LitV LitUnit))) σ1'
                    = dmap (λ v, (Val v, σ1')) μ').
    { simpl. erewrite head_prim_step_eq; last first.
      { destruct (SeriesC_gtz_ex μ' (pmf_pos μ')) as [w Hw]; [rewrite (sig_sample_mass _ _ _ _ Hμ'); lra|].
        eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS. }
      simpl. rewrite Hμ'. done. }
    assert (Hred : reducible (Sample lidx (Val pv) (Val (LitV LitUnit)), σ1)).
    { apply head_prim_reducible. destruct (SeriesC_gtz_ex μ (pmf_pos μ)) as [w Hw];
        [rewrite (sig_sample_mass _ _ _ _ Hμ); lra|].
      eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS. }
    assert (Hred' : reducible (Sample lidx (Val pv') (Val (LitV LitUnit)), σ1')).
    { apply head_prim_reducible. destruct (SeriesC_gtz_ex μ' (pmf_pos μ')) as [w Hw];
        [rewrite (sig_sample_mass _ _ _ _ Hμ'); lra|].
      eexists (_,_). apply head_step_support_equiv_rel. by eapply SampleNoTapeS. }
    (* per-region prim-step coupling: shift the spec draw by [k] at error [|k'|·ε] *)
    assert (Hprimcpl : ∀ (k k' : Z), (Z.abs (k + loc - loc') <= k')%Z →
              DPcoupl (common.language.prim_step (Sample lidx (Val pv) (Val (LitV LitUnit))) σ1)
                (common.language.prim_step (Sample lidx (Val pv') (Val (LitV LitUnit))) σ1')
                (λ ρ2 ρ2', ∃ (z : Z), ρ2 = (Val #z, σ1) ∧ ρ2' = (Val #(z + k), σ1'))
                (IZR k' * ε) 0).
    { intros k k' Hdist.
      assert (Hk' : (0 <= IZR k')%R) by (apply IZR_le; revert Hdist; apply Zabs_ind; lia).
      rewrite Hps1 Hps1'.
      (* push the coupling through the outer [λ v, (Val v, σ)] dmap *)
      apply DPcoupl_map; [apply Rmult_le_pos; [exact Hk'|lra] | lra | ].
      subst μ μ'.
      (* push through the [sf_inj] dmap *)
      apply DPcoupl_map; [apply Rmult_le_pos; [exact Hk'|lra] | lra | ].
      eapply (DPcoupl_mono _ _ _ _ (λ z z', (z + k = z')%Z) _
                (IZR k' * ε) (IZR k' * ε) 0 0);
        [ done | done
        | intros a a' Haa'; exists a; split; [reflexivity | rewrite -Haa'; reflexivity]
        | lra | lra
        | rewrite -Hε; by apply (DPcoupl_laplace_draw num den loc loc' k k' Hdist) ]. }
    (* the choice predicate and the two region relations *)
    set (P := (λ '(ez, _), ∃ z : Z, ez = Val (LitV (LitInt z)) ∧ T <= z)%Z
              : (gen_prob_lang.expr * gen_prob_lang.state)%type → Prop).
    set (R := (λ ρ ρ' : gen_prob_lang.expr * gen_prob_lang.state,
                  ρ.2 = σ1 ∧ ρ'.2 = σ1' ∧
                  (P ρ → let (ez, ez') := (ρ.1, ρ'.1) in
                  ∃ z z' : Z, ez = Val (LitV (LitInt z)) ∧ ez' = Val (LitV (LitInt z')) ∧
                                T <= z ∧ T + 1 <= z')%Z)).
    set (RR := (λ a '(e2', σ2'), ∃ e2'', (e2', σ2') = (fill K e2'', σ2') ∧ R a (e2'', σ2'))).
    set (R' := (λ ρ ρ' : gen_prob_lang.expr * gen_prob_lang.state,
                   ρ.2 = σ1 ∧ ρ'.2 = σ1' ∧
                   (¬ P ρ → let (ez, ez') := (ρ.1, ρ'.1) in
                   ∃ z z' : Z, ez = Val (LitV (LitInt z)) ∧ ez' = Val (LitV (LitInt z')) ∧
                                 z < T ∧ z' < T + 1)%Z)).
    set (RR' := (λ a '(e2', σ2'), ∃ e2'', (e2', σ2') = (fill K e2'', σ2') ∧ R' a (e2'', σ2'))).
    opose proof (prog_coupl_steps ε_now_rest x ε_now 0 ε_now
                   δ_now 0 0 δ_now
                   P RR RR')%NNR as pcs.
    (* inline only the relation [set]s into [pcs] (cheap), so the per-region
       bullets see the unfolded [∃ e2'', …] structure — a full [simpl in pcs]
       would instead blow up on the gen canonical-structure terms. *)
    rewrite /RR in pcs. rewrite /RR' in pcs.
    (* Discharge the [prog_coupl_steps] side conditions explicitly: an [=> //]
       here would run [done] on the huge [DPcoupl]/continuation subgoals, which
       is pathologically slow on the gen canonical-structure terms. *)
    iApply pcs; clear pcs.
    1: exact H_ε_now.
    1,2: apply nnreal_ext; simpl; lra.
    1: exact Hred.
    1: by apply reducible_fill.

    (* disjointness of R / R' under P *)
    - intros [? ?] [? ?] [? ?]. intros P_ρ nP_ρ'. subst R R' P; cbn in *. intros [h h'].
      destruct h as (e1'' & eq'' & R_ρρ').
      destruct h' as (? & eq''' & R'_ρρ').
      apply R_ρρ' in P_ρ. apply R'_ρρ' in nP_ρ'.
      destruct P_ρ as [?[?[?[?[]]]]]. destruct nP_ρ' as [?[?[?[?[]]]]].
      subst. simplify_eq. lia.

    (* above threshold: shift the spec by 1, distance |1 + loc - loc'| *)
    - intros. replace 0%R with (nonneg 0%NNR) => //.
      apply DPcoupl_steps_ctx_bind_r => //.
      eapply DPcoupl_mono; last first.
      1: eapply (Hprimcpl 1%Z (Z.abs (1 + loc - loc')) ltac:(lia)).
      all: try by intuition eauto.
      { rewrite Hε'' Hε' -Hε. apply Rmult_le_compat_r; [lra|].
        replace 2%R with (IZR 2) by (simpl; lra). apply IZR_le.
        revert dist_loc. apply Zabs_ind; lia. }
      + simpl. intros [e σ] [e' σ'] (z & eq_ez & eq_ez'). repeat split. 1,2: simpl; by simplify_eq.
        intros Pe. destruct Pe as (ey & eq_ey & above). simpl.
        exists z, (z + 1)%Z. repeat split; simplify_eq => //. lia.

    (* below threshold: exact coupling (shift by [loc'-loc]), zero error *)
    - intros. replace 0%R with (nonneg 0%NNR) => //. apply DPcoupl_steps_ctx_bind_r => //.
      eapply DPcoupl_mono; last first.
      1: eapply (Hprimcpl (loc' - loc)%Z (Z.abs ((loc' - loc) + loc - loc')) ltac:(lia)).
      all: try by intuition eauto.
      (* the below-region target error is [0], so the budget goal reduces to
         [0 ≤ 0]; dispatch by goal shape so the relation goal is left for below. *)
      all: lazymatch goal with
           | |- (_ <= _)%R =>
               assert (Hk0 : Z.abs ((loc' - loc) + loc - loc') = 0%Z) by lia;
               rewrite Hk0; change (IZR 0) with 0%R; rewrite Rmult_0_l; apply cond_nonneg
           | |- _ => idtac
           end.
      simpl. intros [e σ] [e' σ'] (z & eq_ez & eq_ez'). repeat split. 1,2: simpl; by simplify_eq.
      intros nPe. exists z, (z + (loc' - loc))%Z. repeat split; simplify_eq => //.
      * subst P R R'; simpl in *. destruct (decide (z < T)%Z) => //.
        exfalso. apply nPe. exists z. split => //. lia.
      * subst P R R'; simpl in *. destruct (decide (z < T)%Z). 1: lia.
        exfalso; apply nPe; exists z; split => //; lia.

    (* the continuation, region by region *)
    - iIntros (e2 σ2 e2' σ2').
      destruct (decide (P (e2, σ2))) as [p | n].
      + iSplitL; last first.
        { iIntros ([nP_ρ2 R'_ρ2]). exfalso. done. }
        iIntros (((ze2 & eqe2 & Pe2) & (e2'' & [eq_e2'' R_ρ2ρ2']))).
        unfold R in R_ρ2ρ2'.
        simpl in R_ρ2ρ2'. destruct R_ρ2ρ2' as (<- & <- & R_ρ2ρ2'). specialize (R_ρ2ρ2' p).
        destruct R_ρ2ρ2' as (z & z' & eq_e2_z & eq_e2''_z' & z_above & z'_above).
        inversion eq_e2''. simplify_eq.
        iMod (spec_update_prog (fill K #(_)) with "Hauth2 Hr") as "[$ Hspec0]".
        iMod (ecm_supply_decrease with "Hε2 Hε") as (???Herr Hε''') "H".
        do 2 iModIntro.
        iMod "Hclose'" as "_".
        iModIntro. iFrame.
        rewrite -wp_value.
        iDestruct ("Hcnt" with "[$Hspec0]") as "$".
        { iLeft. done. }
        simplify_eq. rewrite Hε'' Hε''' in Herr.
        rewrite Rplus_comm in Herr. apply Rplus_eq_reg_r in Herr. clear -Herr.
        apply nnreal_ext in Herr. subst. iFrame.

      + iSplitR.
        { iIntros ([P_ρ2 R_ρ2]). exfalso. done. }
        iIntros ((nP_ρ2 & (e2'' & [eq_e2'' R'_ρ2ρ2']))).
        unfold R' in R'_ρ2ρ2'.
        simpl in R'_ρ2ρ2'. destruct R'_ρ2ρ2' as (<- & <- & R'_ρ2ρ2'). specialize (R'_ρ2ρ2' nP_ρ2).
        destruct R'_ρ2ρ2' as (z & z' & eq_e2_z & eq_e2''_z' & z_below & z'_below).
        inversion eq_e2''. simplify_eq.
        iMod (spec_update_prog (fill K #(_)) with "Hauth2 Hr") as "[$ Hspec0]".
        do 2 iModIntro.
        iMod "Hclose'" as "_".
        iModIntro. iFrame.
        rewrite -wp_value.
        iDestruct ("Hcnt" with "[$Hspec0 Hε]") as "$".
        { iRight. iFrame. done. }
        Unshelve. all: exact 0%Z.
  Qed.

  (** Surface-notation wrapper (Pair-headed [Laplace] parameter), for clients
      that prefer to apply the rule before reducing the parameter [Pair] to a
      value.  The primary rule is the value-form [wp_couple_laplace_choice];
      this just [wp_pures]/[tp_pures] the surface notation down to it. *)
  Lemma hoare_couple_laplace_choice (loc loc' T : Z)
    (dist_loc : (Z.abs (loc - loc') <= 1)%Z)
    (num den : Z) (ε ε' : R) K E :
    IZR num / IZR den = ε →
    0 < IZR num / IZR den →
    ε' = (2 * ε) →
    {{{ ⤇ fill K (Laplace #num #den #loc' #()) ∗ ↯m ε' }}}
      Laplace #num #den #loc #() @ E
      {{{ (z : Z), RET #z;
          ∃ z' : Z, ⤇ fill K #z'
                 ∗ ( ⌜(T <= z ∧ T + 1 <= z')⌝
                     ∨ (⌜z < T ∧ z' < T + 1⌝ ∗ ↯m ε'))%Z }}}.
  Proof.
    iIntros (Hε εpos Hε' Φ) "[Hspec Hε] Hcnt". tp_pures. wp_pures.
    iApply (wp_couple_laplace_choice loc loc' T dist_loc num den ε ε' K E Hε εpos Hε'
              with "[$Hspec $Hε] Hcnt").
  Qed.

End laplace_choice.
