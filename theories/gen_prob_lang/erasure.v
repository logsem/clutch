(** Presampling erasure for [gen_prob_lang].  Ported from [prob_lang/erasure.v],
    collapsing its two parallel tracks (uniform [state_step] + Laplace
    [state_step_laplace]) into the single generic [state_step S].  The target
    consumed downstream is [state_step_erasable] / [iterM_state_step_erasable].

    The family draw [μ = sig_sample S i pv] replaces [dunifP N]; the
    per-distribution cross-product of [prob_lang]'s [ind_case_*] helpers
    collapses to one [Sample]/[AllocSampleTape] case analysis. *)
From Stdlib Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Lim_seq.
From stdpp Require Import fin_maps fin_map_dom.
From clutch.prelude Require Import stdpp_ext.
From clutch.common Require Import exec language ectx_language erasable.
From clutch.gen_prob_lang Require Import notation lang metatheory.
From clutch.prob Require Import couplings couplings_app markov distribution
  differential_privacy couplings_dp.
From iris.prelude Require Import options.

Local Open Scope R.

Section gen_erasure.
  Context (S : Sig).
  (* Pin [gen_lang S] as the canonical language so [pexec]/[exec]/[prim_step]/
     [fill_lift]/[decomp] resolve at the generic language. *)
  Canonical Structure gen_ectxi_lang_S := gen_ectxi_lang S.
  Canonical Structure gen_ectx_lang_S := gen_ectx_lang S.
  Canonical Structure gen_lang_S := gen_lang S.

  Section erasure_helpers.
    Variable (m : nat).
    Hypothesis IH :
      ∀ (e1 : expr) (σ1 : state) α i pv xs μ,
      stapes σ1 !! α = Some (i, pv, xs) →
      sig_sample S i pv = Some μ →
      Rcoupl
        (dmap (λ x, x.1) (pexec m (e1, σ1)))
        (dmap (λ x, x.1) (μ ≫= (λ v, pexec m (e1, state_upd_stapes <[α := (i, pv, xs ++ [v])]> σ1)))) eq.

    Local Lemma ind_case_det e σ α i pv xs μ K :
      stapes σ !! α = Some (i, pv, xs) →
      sig_sample S i pv = Some μ →
      is_det_head_step e σ = true →
      Rcoupl
        (dmap (fill_lift K) (head_step S e σ) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ))
        (μ ≫= (λ v, dmap (fill_lift K)
                      (head_step S e (state_upd_stapes <[α := (i, pv, xs ++ [v])]> σ))
                      ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ)))
        (=).
    Proof using S m IH.
      intros Hα Hμ (e2 & (σ2 & Hdet))%is_det_head_step_true%det_step_pred_ex_rel.
      erewrite 1!det_head_step_singleton; [|done..].
      erewrite (dbind_ext_right μ); last first.
      { intros v.
        assert (det_head_step_rel e (state_upd_stapes <[α := (i, pv, xs ++ [v])]> σ) e2
                  (state_upd_stapes <[α := (i, pv, xs ++ [v])]> σ2)) as Hd.
        { inversion Hdet; subst; try (econstructor; eauto).
          rewrite state_upd_stapes_heap. econstructor; eauto. }
        erewrite (det_head_step_singleton _ _ _ _ _ Hd). reflexivity. }
      rewrite !dmap_dret.
      setoid_rewrite (dmap_dret (fill_lift K)).
      rewrite !dret_id_left.
      erewrite det_step_eq_tapes in Hα; [|done].
      erewrite (distr_ext (μ ≫= _) _); last first.
      { intros. apply dbind_pmf_ext; [|done..]. intros.
        rewrite dret_id_left. done. }
      rewrite -dmap_dbind. eapply IH; done.
    Qed.

    Local Lemma ind_case_dzero e σ α i pv xs μ K :
      stapes σ !! α = Some (i, pv, xs) →
      sig_sample S i pv = Some μ →
      head_step S e σ = dzero →
      Rcoupl
        (dmap (fill_lift K) (head_step S e σ) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ))
        (μ ≫= (λ v, dmap (fill_lift K)
                      (head_step S e (state_upd_stapes <[α := (i, pv, xs ++ [v])]> σ))
                      ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ)))
        eq.
    Proof using S m.
      intros Hα Hμ Hz.
      rewrite Hz.
      erewrite (dbind_ext_right μ); last first.
      { intros v. erewrite head_step_dzero_upd_tapes; [|done|done|done].
        rewrite dmap_dzero dbind_dzero. reflexivity. }
      rewrite dmap_dzero dbind_dzero dzero_dbind.
      apply Rcoupl_dzero_dzero.
    Qed.

    Local Lemma ind_case_alloc_sample_tape σ α i pv xs μ j qv K :
      stapes σ !! α = Some (i, pv, xs) →
      sig_sample S i pv = Some μ →
      Rcoupl
        (dmap (fill_lift K) (head_step S (AllocSampleTape j (Val qv)) σ) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ))
        (μ ≫= (λ v, dmap (fill_lift K)
                      (head_step S (AllocSampleTape j (Val qv)) (state_upd_stapes <[α := (i, pv, xs ++ [v])]> σ))
                      ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ)))
        eq.
    Proof using S m IH.
      intros Hα Hμ.
      rewrite dmap_dret dret_id_left -/exec.
      setoid_rewrite (dmap_dret (fill_lift K)).
      erewrite (distr_ext (μ ≫= _)); last first.
      { intros. apply dbind_pmf_ext; [|done..].
        intros. rewrite dret_id_left. done. }
      rewrite -dmap_dbind.
      revert IH; intro IHm.
      apply lookup_total_correct in Hα as Hαtot.
      pose proof (elem_fresh_ne _ _ _ Hα) as Hne.
      erewrite dbind_ext_right; last first.
      { intros v.
        rewrite -(fresh_loc_upd_some _ _ (i, pv, xs)); [|done].
        rewrite (fresh_loc_upd_swap σ α (i, pv, xs) (j, qv, [])) //. }
      eapply IHm; [|done].
      by apply fresh_loc_lookup.
    Qed.

    (* The direct (no-tape) sample on family [j] at [qv]; commutes with the
       presample on [α] (it never reads [α]). *)
    Local Lemma ind_case_sample_no_tape σ α i pv xs μ j qv K :
      stapes σ !! α = Some (i, pv, xs) →
      sig_sample S i pv = Some μ →
      Rcoupl
        (dmap (fill_lift K) (head_step S (Sample j (Val qv) (Val $ LitV LitUnit)) σ) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ))
        (μ ≫= (λ v, dmap (fill_lift K)
                      (head_step S (Sample j (Val qv) (Val $ LitV LitUnit)) (state_upd_stapes <[α := (i, pv, xs ++ [v])]> σ))
                      ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ)))
        eq.
    Proof using S m IH.
      intros Hα Hμ.
      rewrite /head_step.
      destruct (sig_sample S j qv) as [d|] eqn:Hd; last first.
      { rewrite dmap_dzero dbind_dzero.
        erewrite (dbind_ext_right μ); last first.
        { intros v. reflexivity. }
        rewrite dzero_dbind. apply Rcoupl_dzero_dzero. }
      rewrite {1 2}/dmap.
      erewrite (dbind_ext_right μ); last first.
      { intros v. rewrite {1 2}/dmap. do 2 rewrite -dbind_assoc -/exec. reflexivity. }
      rewrite -/exec /=.
      rewrite -!dbind_assoc -/exec.
      rewrite dbind_comm.
      eapply Rcoupl_dbind; [|apply Rcoupl_eq].
      intros ?? ->.
      do 2 rewrite dret_id_left.
      erewrite (distr_ext (μ ≫= _)); last first.
      { intros. apply dbind_pmf_ext; [|done..].
        intros. rewrite !dret_id_left; done. }
      rewrite -dmap_dbind.
      eapply IH; done.
    Qed.

    (* Labelled sample on tape [β].  Splits on [β = α]. *)
    Local Lemma ind_case_sample_tape σ α β i pv xs μ j qv K :
      stapes σ !! α = Some (i, pv, xs) →
      sig_sample S i pv = Some μ →
      Rcoupl
        (dmap (fill_lift K) (head_step S (Sample j (Val qv) (Val $ LitV $ LitLbl β)) σ) ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ))
        (μ ≫= (λ v, dmap (fill_lift K)
                      (head_step S (Sample j (Val qv) (Val $ LitV $ LitLbl β)) (state_upd_stapes <[α := (i, pv, xs ++ [v])]> σ))
                      ≫= λ ρ, dmap (λ x, x.1) (pexec m ρ)))
        eq.
    Proof using S m IH.
      intros Hα Hμ.
      rewrite /head_step.
      destruct (decide (β = α)) as [-> | Hβα]; revgoals.
      { simpl.
        setoid_rewrite (lookup_insert_ne (stapes σ) α β); [|done..].
        destruct (stapes σ !! β) as [[[i' pv'] xs'] |] eqn:Hβ; revgoals.
        { rewrite dmap_dzero dbind_dzero.
          erewrite (dbind_ext_right μ); last first.
          { intros v. reflexivity. }
          rewrite dzero_dbind. apply Rcoupl_dzero_dzero. }
        destruct (bool_decide (j = i' ∧ qv = pv')) eqn:Hdec; revgoals.
        { destruct (sig_sample S j qv) as [d|] eqn:Hd; revgoals.
          { rewrite dmap_dzero dbind_dzero.
            erewrite (dbind_ext_right μ); last first.
            { intros v. reflexivity. }
            rewrite dzero_dbind. apply Rcoupl_dzero_dzero. }
          rewrite {1 2}/dmap.
          erewrite (dbind_ext_right μ); last first.
          { intros v. rewrite {1 2}/dmap. do 2 rewrite -dbind_assoc -/exec. reflexivity. }
          rewrite -/exec /=. rewrite -!dbind_assoc -/exec. rewrite dbind_comm.
          eapply Rcoupl_dbind; [|apply Rcoupl_eq]. intros ?? ->.
          do 2 rewrite dret_id_left.
          erewrite (distr_ext (μ ≫= _)); last first.
          { intros. apply dbind_pmf_ext; [|done..]. intros. rewrite !dret_id_left; done. }
          rewrite -dmap_dbind. eapply IH; done. }
        destruct xs' as [|x xs'].
        - destruct (sig_sample S j qv) as [d|] eqn:Hd; revgoals.
          { rewrite dmap_dzero dbind_dzero.
            erewrite (dbind_ext_right μ); last first.
            { intros v. reflexivity. }
            rewrite dzero_dbind. apply Rcoupl_dzero_dzero. }
          rewrite {1 2}/dmap.
          erewrite (dbind_ext_right μ); last first.
          { intros v. rewrite {1 2}/dmap. do 2 rewrite -dbind_assoc -/exec. reflexivity. }
          rewrite -/exec /=. rewrite -!dbind_assoc -/exec. rewrite dbind_comm.
          eapply Rcoupl_dbind; [|apply Rcoupl_eq]. intros ?? ->.
          do 2 rewrite dret_id_left.
          erewrite (distr_ext (μ ≫= _)); last first.
          { intros. apply dbind_pmf_ext; [|done..]. intros. rewrite !dret_id_left; done. }
          rewrite -dmap_dbind. eapply IH; done.
        - rewrite dmap_dret dret_id_left -/exec.
          setoid_rewrite (dmap_dret (fill_lift K)).
          erewrite (dbind_ext_right μ); last first.
          { intros v.
            rewrite dret_id_left -/exec.
            assert (state_upd_stapes <[β:=(i', pv', xs')]> (state_upd_stapes <[α:=(i, pv, xs ++ [v])]> σ)
                    = {| heap := heap σ;
                         stapes := <[β:=(i', pv', xs')]> (<[α:=(i, pv, xs ++ [v])]> (stapes σ)) |}) as Heq
                by reflexivity.
            rewrite -Heq.
            rewrite (upd_diff_tape_comm σ α β (i', pv', xs') (i, pv, xs ++ [v])); [|done].
            reflexivity. }
          rewrite -dmap_dbind.
          eapply (IH (fill K x) (state_upd_stapes <[β:=(i', pv', xs')]> σ) α i pv xs μ).
          { simpl. rewrite lookup_insert_ne; [done|done]. }
          done. }
      rewrite Hα. simpl.
      setoid_rewrite lookup_insert_eq.
      destruct (bool_decide (j = i ∧ qv = pv)) eqn:Hdec; revgoals.
      { destruct (sig_sample S j qv) as [d|] eqn:Hd; revgoals.
        { rewrite dmap_dzero dbind_dzero.
          erewrite (dbind_ext_right μ); last first.
          { intros v. reflexivity. }
          rewrite dzero_dbind. apply Rcoupl_dzero_dzero. }
        rewrite {1 2}/dmap.
        erewrite (dbind_ext_right μ); last first.
        { intros v. rewrite {1 2}/dmap. do 2 rewrite -dbind_assoc -/exec. reflexivity. }
        rewrite -/exec /=. rewrite -!dbind_assoc -/exec. rewrite dbind_comm.
        eapply Rcoupl_dbind; [|apply Rcoupl_eq]. intros ?? ->.
        do 2 rewrite dret_id_left.
        erewrite (distr_ext (μ ≫= _)); last first.
        { intros. apply dbind_pmf_ext; [|done..]. intros. rewrite !dret_id_left; done. }
        rewrite -dmap_dbind. eapply IH; done. }
      apply bool_decide_eq_true_1 in Hdec as [-> ->].
      destruct xs as [|x xs].
      - rewrite Hμ.
        rewrite {1 2}/dmap.
        rewrite -!dbind_assoc -/exec.
        eapply (Rcoupl_dbind _ _ _ _ (=)); [|apply Rcoupl_eq].
        intros ? b ->.
        do 2 rewrite dret_id_left. simpl.
        rewrite insert_insert_eq.
        rewrite (insert_id (stapes σ) α (i, pv, [])); [|done].
        rewrite dmap_dret dret_id_left -/exec.
        rewrite /dmap.
        destruct σ; simpl. apply Rcoupl_eq.
      - rewrite dmap_dret dret_id_left -/exec.
        setoid_rewrite (dmap_dret (fill_lift K)).
        erewrite (dbind_ext_right μ); last first.
        { intros v.
          rewrite -app_comm_cons.
          rewrite dret_id_left -/exec.
          assert (state_upd_stapes <[α:=(i, pv, xs ++ [v])]> (state_upd_stapes <[α:=(i, pv, xs)]> σ)
                  = {| heap := heap σ;
                       stapes := <[α:=(i, pv, xs ++ [v])]> (<[α:=(i, pv, (x :: xs) ++ [v])]> (stapes σ)) |}) as Heq.
          { rewrite /state_upd_stapes /=. f_equal. rewrite !insert_insert_eq //. }
          rewrite -Heq. reflexivity. }
        rewrite -dmap_dbind.
        eapply (IH (fill K x) (state_upd_stapes <[α:=(i, pv, xs)]> σ) α i pv xs μ).
        { simpl. rewrite lookup_insert_eq //. }
        done.
    Qed.

  End erasure_helpers.

  Lemma prim_coupl_upd_tapes_dom m e1 σ1 α i pv xs μ :
    σ1.(stapes) !! α = Some (i, pv, xs) →
    sig_sample S i pv = Some μ →
    Rcoupl
      (dmap (λ x, x.1) (pexec m (e1, σ1)))
      (μ ≫= (λ v, dmap (λ x, x.1) (pexec m (e1, state_upd_stapes <[α := (i, pv, xs ++ [v])]> σ1))))
      (=).
  Proof.
    intros Hα Hμ.
    rewrite -dmap_dbind.
    revert e1 σ1 α i pv xs μ Hα Hμ; induction m as [|m IHm]; intros e1 σ1 α i pv xs μ Hα Hμ.
    - rewrite /pexec /=.
      rewrite dmap_dret.
      rewrite dmap_dbind.
      erewrite (distr_ext (μ ≫= _)); last first.
      { intros. apply dbind_pmf_ext; [|done..].
        intros. rewrite dmap_dret. done. }
      rewrite (dret_const μ); [apply Rcoupl_eq | erewrite sig_sample_mass; [lra|eauto]].
    - rewrite pexec_Sn /step_or_final /=.
      destruct (to_val e1) eqn:He1.
      + rewrite dret_id_left.
        rewrite -/(pexec m (e1, σ1)).
        rewrite pexec_is_final; last by rewrite /is_final.
        rewrite dmap_dret. simpl.
        rewrite dmap_dbind.
        erewrite (distr_ext (μ ≫= _)); last first.
        { intros. apply dbind_pmf_ext; [|done..].
          intros. rewrite pexec_is_final; last by rewrite /is_final.
          rewrite dmap_dret. simpl. done. }
        rewrite dret_const; [apply Rcoupl_eq|].
        erewrite sig_sample_mass; [lra|eauto].
      + rewrite !dmap_dbind.
        erewrite (distr_ext (μ ≫= _)); last first.
        { intros. apply dbind_pmf_ext; [|done..].
          intros. setoid_rewrite pexec_Sn.
          rewrite /step_or_final/=He1/prim_step/=.
          rewrite dmap_dbind.
          done. }
        rewrite /prim_step/=.
        destruct (decomp e1) as [K ered] eqn:Hdecomp_e1.
        rewrite Hdecomp_e1.
        destruct (det_or_prob_or_dzero S ered σ1) as [HD | [HP | HZ]].
        * eapply (ind_case_det m IHm); [done|done|by apply is_det_head_step_true].
        * inversion HP; simplify_eq.
          -- eapply (ind_case_sample_no_tape m IHm); [done|done].
          -- eapply (ind_case_alloc_sample_tape m IHm); [done|done].
          -- eapply (ind_case_sample_tape m IHm); [done|done].
          -- eapply (ind_case_sample_tape m IHm); [done|done].
          -- eapply (ind_case_sample_tape m IHm); [done|done].
        * eapply (ind_case_dzero m); [done|done|done].
  Qed.

  Lemma pexec_coupl_step_pexec m e1 σ1 α t :
    σ1.(stapes) !! α = Some t →
    Rcoupl
      (dmap (λ ρ, ρ.1) (pexec m (e1, σ1)))
      (dmap (λ ρ, ρ.1) (state_step S σ1 α ≫= (λ σ2, pexec m (e1, σ2))))
      eq.
  Proof.
    intros Hα.
    destruct t as [[i pv] xs].
    destruct (sig_sample S i pv) as [μ|] eqn:Hμ.
    - eapply Rcoupl_eq_trans;
        first eapply (prim_coupl_upd_tapes_dom m e1 σ1 α i pv xs μ); [done|done|].
      rewrite <-dmap_dbind.
      apply Rcoupl_dmap.
      erewrite state_step_unfold; last done.
      rewrite Hμ.
      rewrite /dmap.
      rewrite -dbind_assoc.
      eapply Rcoupl_dbind; last apply Rcoupl_eq.
      intros ?? ->.
      rewrite dret_id_left.
      eapply Rcoupl_mono; first apply Rcoupl_eq.
      intros. naive_solver.
    - erewrite state_step_unfold; last done.
      rewrite Hμ.
      rewrite dret_id_left.
      apply Rcoupl_eq.
  Qed.

  Lemma prim_coupl_step_prim m e1 σ1 α t :
    σ1.(stapes) !! α = Some t →
    Rcoupl
      (exec m (e1, σ1))
      (state_step S σ1 α ≫= (λ σ2, exec m (e1, σ2)))
      eq.
  Proof.
    intros Hα.
    epose proof pexec_coupl_step_pexec _ _ _ _ _ Hα as H.
    setoid_rewrite exec_pexec_relate.
    simpl.
    erewrite (distr_ext _ (dmap (λ ρ, ρ.1) (pexec m (e1, σ1)) ≫=
                             λ e, match to_val e with | Some b => dret b | None => dzero end)); last first.
    { intros. rewrite /dmap.
      rewrite -dbind_assoc. simpl.
      apply dbind_pmf_ext; try done.
      intros. rewrite dret_id_left. done. }
    erewrite (distr_ext (state_step S σ1 α ≫= _) _).
    - eapply Rcoupl_dbind; last exact.
      intros. subst. apply Rcoupl_eq.
    - intros. rewrite /dmap.
      rewrite -!dbind_assoc. simpl.
      apply dbind_pmf_ext; try done.
      intros. apply dbind_pmf_ext; try done.
      intros.
      rewrite dret_id_left. done.
  Qed.

  Lemma state_step_erasable σ1 α t :
    σ1.(stapes) !! α = Some t →
    erasable (state_step S σ1 α) σ1.
  Proof.
    intros. rewrite /erasable.
    intros.
    symmetry.
    apply Rcoupl_eq_elim.
    by eapply prim_coupl_step_prim.
  Qed.

  Lemma iterM_state_step_erasable σ1 α t n :
    σ1.(stapes) !! α = Some t →
    erasable (iterM n (λ σ, state_step S σ α) σ1) σ1.
  Proof.
    revert σ1 t.
    induction n; intros σ1 t H.
    - simpl. apply dret_erasable.
    - simpl. apply erasable_dbind; first by eapply state_step_erasable.
      intros σ' H0.
      destruct t as [[i pv] xs].
      erewrite state_step_unfold in H0; last done.
      destruct (sig_sample S i pv) as [μ|] eqn:Hμ.
      + rewrite dmap_pos in H0. destruct H0 as (?&->&K).
        eapply IHn. simpl. apply lookup_insert_eq.
      + apply dret_pos in H0 as ->. by eapply IHn.
  Qed.

  (** DPcoupl erasure lemmas (used by adequacy).  These take ABSTRACT
      [erasable]/[rewritable] hypotheses, so they are language-generic; ported
      verbatim from [prob_lang/erasure.v] with [Λ := gen_lang S]. *)

  Lemma DPcoupl_erasure_erasable_exp_rhs_specialized δ1 μ1 μ1' (X2 : _ → R) R Φ (e1 e1' : expr) σ1 σ1' ε δ r n m :
    0 <= δ1 →
    DPcoupl μ1 (σ2' ← μ1'; pexec m (e1', σ2')) R 0 δ1 →
    δ1 + Expval (σ2' ← μ1'; pexec m (e1', σ2')) X2 <= δ →
    (∀ ρ, (0 <= X2 ρ <= r)%R) →
    erasable μ1 σ1 →
    erasable μ1' σ1' →
    (∀ σ2 e2' σ2', R σ2 (e2', σ2') →
                   DPcoupl (exec n (e1, σ2)) (lim_exec (e2', σ2')) Φ ε (X2 (e2', σ2'))) →
    DPcoupl (exec n (e1, σ1)) (lim_exec (e1', σ1')) Φ ε δ.
  Proof.
    intros Hδ1 Hcoupl Hineq Hbound Hμ1 Hμ2 Hcont.
    rewrite -Hμ1.
    rewrite -(erasable_pexec_lim_exec μ1' m) //.
    assert (0 + ε <= ε) by lra.
    eapply DPcoupl_mon_grading; [done|done|].
    eapply (DPcoupl_dbind_adv_rhs_specialized' _ _ _ _ _ _ ε δ1 _ X2) ; [done|eauto|done| |done].
    intros ? [] ?.
    by eapply Hcont.
  Qed.

  Lemma DPcoupl_erasure_erasable_rhs e1 e1' ε ε1 ε2 δ δ1 δ2 σ1 σ1' μ1 μ1' R φ k m
    (Hεsum : ε1 + ε2 <= ε)
    (Hδ1 : 0 <= δ1)
    (Hδ2 : 0 <= δ2)
    (Hδsum : δ1 + δ2 <= δ)
    (H : DPcoupl μ1 (μ1' ≫= λ σ2' : state, pexec k (e1', σ2')) R ε1 δ1)
    (Hμ1 : erasable μ1 σ1)
    (Hμ1' : erasable μ1' σ1')
    (Hcpl : (∀ (σ2 : state) ρ2',
                R σ2 ρ2'
                → DPcoupl (exec m (e1, σ2)) (lim_exec ρ2') φ ε2 δ2))
    : DPcoupl (exec m (e1, σ1)) (lim_exec (e1', σ1')) φ ε δ.
  Proof.
    rewrite -Hμ1. erewrite <-(erasable_pexec_lim_exec (Λ := gen_lang S) _ _ _ _ Hμ1') => /=.
    eapply DPcoupl_mon_grading; [apply Hεsum | apply Hδsum |].
    eapply DPcoupl_dbind ; try done.
  Qed.

  Lemma DPcoupl_erasure_rewritable_rhs (e1 e1': expr) ε ε1 ε2 δ δ1 δ2 σ1 σ1' μ1 μ1' R φ m
    (Hεsum : ε1 + ε2 <= ε)
    (Hδ1 : 0 <= δ1)
    (Hδ2 : 0 <= δ2)
    (Hδsum : δ1 + δ2 <= δ)
    (H : DPcoupl μ1 μ1' R ε1 δ1)
    (Hμ1 : erasable μ1 σ1)
    (Hμ1' : rewritable (e1', σ1') μ1')
    (Hcpl : (∀ (σ2 : state) ρ2',
                R σ2 ρ2'
                → DPcoupl (exec m (e1, σ2)) (lim_exec ρ2') φ ε2 δ2))
    : DPcoupl (exec m (e1, σ1)) (lim_exec (e1', σ1')) φ ε δ.
  Proof.
    rewrite -Hμ1.
    rewrite Hμ1'.
    eapply DPcoupl_mon_grading; [apply Hεsum | apply Hδsum |].
    eapply DPcoupl_dbind ; try done.
  Qed.

  Lemma DPcoupl_erasure_erasable_lhs' (e1 e1' : expr) ε ε1 ε2 δ δ1 δ2 σ1 σ1' μ1' R φ k m
    (Hred : reducible (e1, σ1))
    (Hεsum : ε1 + ε2 <= ε)
    (Hδ1 : 0 <= δ1)
    (Hδ2 : 0 <= δ2)
    (Hδsum : δ1 + δ2 <= δ)
    (H : DPcoupl (prim_step e1 σ1) (μ1' ≫= λ σ2' : state, pexec k (e1', σ2')) R ε1 δ1)
    (Hμ1' : erasable μ1' σ1')
    (Hcpl : (∀ (e2 : expr) (σ2 : state) (e2' : expr) (σ2' : state),
                R (e2, σ2) (e2', σ2')
                → DPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε2 δ2))
    : DPcoupl (prim_step e1 σ1 ≫= exec m) (lim_exec (e1', σ1')) φ ε δ.
  Proof.
    erewrite <-(erasable_pexec_lim_exec (Λ := gen_lang S) _ _ _ _ Hμ1') => /=.
    eapply DPcoupl_mon_grading; [apply Hεsum | apply Hδsum |].
    eapply DPcoupl_dbind ; try done.
    intros [] []. apply Hcpl.
  Qed.

  Lemma DPcoupl_erasure_erasable_lhs_choice (e1 e1' : expr) ε ε1 ε2 ε1' ε2' δ δ1 δ2 δ1' σ1 σ1' μ1' P R R' φ k m
    (Hred : reducible (e1, σ1))
    (Hεsum : ε1 + ε2 <= ε)
    (Hε'sum : ε1' + ε2' <= ε)
    (Hδ1 : 0 <= δ1)
    (Hδ2 : 0 <= δ2)
    (Hδ1' : 0 <= δ1')
    (Hδsum : δ1 + δ1' + δ2 <= δ)
    (Hindep : (forall a a' b, P a -> ¬ P a' -> ¬(R a b /\ R' a' b)))
    (H : DPcoupl (prim_step e1 σ1) (μ1' ≫= λ σ2' : state, pexec k (e1', σ2')) R ε1 δ1)
    (H' : DPcoupl (prim_step e1 σ1) (μ1' ≫= λ σ2' : state, pexec k (e1', σ2')) R' ε1' δ1')
    (Hμ1' : erasable μ1' σ1')
    (Hcpl1 : (∀ (e2 : expr) (σ2 : state) (e2' : expr) (σ2' : state),
                (P (e2, σ2) /\ R (e2, σ2) (e2', σ2'))
                → DPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε2 δ2))
    (Hcpl2 : (∀ (e2 : expr) (σ2 : state) (e2' : expr) (σ2' : state),
                (¬P (e2, σ2) /\ R' (e2, σ2) (e2', σ2'))
                → DPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε2' δ2))
    : DPcoupl (prim_step e1 σ1 ≫= exec m) (lim_exec (e1', σ1')) φ ε δ.
  Proof.
    erewrite <-(erasable_pexec_lim_exec (Λ := gen_lang S) _ _ _ _ Hμ1') => /=.
    eapply (DPcoupl_dbind_choice _ _ _ _ P _ _ _  ε1 ε2 δ1 δ2 ε1' ε2' δ1' ε δ); try done.
    - intros (e, σ) (e', σ') (HP & HR).
      by apply Hcpl1.
    - intros (e, σ) (e', σ') (HP & HR).
      by apply Hcpl2.
  Qed.

End gen_erasure.
