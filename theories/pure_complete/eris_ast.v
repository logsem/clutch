From clutch.eris Require Export eris error_rules. 
From clutch.pure_complete Require Import pure term.
Import Coquelicot.Lim_seq.

Local Open Scope R.

Lemma prob_comp_nn `{Countable A} (μ : distr A) (f : A -> bool) : 0 <= 1 - prob μ f.
Proof.
  pose proof (prob_le_1 μ f). lra.
Qed.

Definition prob_comp_nnr `{Countable A} (μ : distr A) (f : A -> bool) : nonnegreal := mknonnegreal (1 - prob μ f) (prob_comp_nn _ _).

Lemma tgl_gt_lim (e : expr) σ φ ε ε' : 
  ε < ε' ->
  tgl (lim_exec (e, σ)) φ ε -> 
  ∃ n, tgl (exec n (e, σ)) φ ε'.
Proof.
  rewrite /tgl //= /prob.  
  intros. 
  Check lim_exec_unfold.
  assert ((λ a : val, if bool_decide (φ a) then lim_exec (e, σ) a else 0) = (λ a : val, Rbar.real $ Sup_seq (λ n, Rbar.Finite $ if bool_decide (φ a) then exec n (e,σ) a else 0))). {
    apply functional_extensionality => a //=.
    case_bool_decide; last by rewrite sup_seq_const.
    by rewrite lim_exec_unfold.
  }
  rewrite H1 in H0.
  erewrite SeriesC_Sup_seq_swap in H0; first last; intros.
  
  2 : { eapply SeriesC_correct. eapply ex_seriesC_le; real_solver.  }
  { simpl. etrans; first eapply SeriesC_le; real_solver. }
  { exists 1. real_solver. }
  { case_bool_decide; try lra. apply exec_mono.  }
  { real_solver. }
  
  set s := Rbar.real $ Sup_seq (λ n : nat,  Rbar.Finite (SeriesC (λ a : val, if bool_decide (φ a) then exec n (e, σ) a else 0))).

  assert (Lim_seq.is_sup_seq (λ n : nat, Rbar.Finite (SeriesC (λ a : val, if bool_decide (φ a) then exec n (e, σ) a else 0)))  (Rbar.Finite $ s)). {
    rewrite rbar_finite_real_eq. 2 : {
      apply (Rbar_le_sandwich 0 1).
      { apply (Sup_seq_minor_le _ _ 0%nat). apply SeriesC_ge_0; try real_solver. eapply ex_seriesC_le; try real_solver.  }
      { apply upper_bound_ge_sup => n //=. etrans; first eapply SeriesC_le; real_solver. }
    }
    apply Lim_seq.Sup_seq_correct.
  }
  unfold is_sup_seq in H2.
  assert (0 < s - (1 - ε')); first by rewrite /s; lra.
  specialize H2 with (mkposreal _ H3) as [?[n?]].
  exists n. simpl in H4. ring_simplify in H4. ring_simplify. lra.
Qed.

Section Complete.

  Context `{!erisGS Σ}.

  Notation σ₀ := {| heap := ∅; tapes := ∅ |}.
  Notation almost_surely_terminates ρ := (SeriesC (lim_exec ρ) = 1%R).

  Lemma AST_complete_pure_pre (n: nat) (e : expr) (σ : state) E : 
    is_pure e = true -> 
    ↯ (pterm_comp n (e, σ)) -∗ WP e @ E [{ v, True }].
  Proof. 
    intros.
    iInduction n as [|n] "IH" forall (e H σ).
    - destruct ( language.to_val e) eqn: He.
      { iIntros. apply of_to_val in He as <-. by wp_pures. }
      iIntros "Herr". 
      rewrite /pterm_comp /pterm. simpl. rewrite He dzero_mass. 
      rewrite Rminus_0_r. iPoseProof (ec_contradict with "Herr") as "H"; 
      auto; try lra.
    - destruct (language.to_val e) eqn: He.
      { iIntros. apply of_to_val in He as <-. by wp_pures. }
      iIntros "Herr".
      iApply twp_lift_step_fupd_glm; auto.
      iIntros "%% [Hs Herra]". 
      iDestruct (ec_supply_ec_inv with "Herra Herr") as %(ε1' & ε3 & Hε_now & Hε1').
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "hclose".
      iApply glm_adv_comp. 
      iExists (fun s => step (e, σ1) s > 0), 0%NNR, (fun x => (ε3 + (pterm_comp n x))%NNR).
      destruct (Rlt_dec 0 (pterm (S n) (e, σ))).
      2 : {
        iExFalso.
        iApply (ec_contradict with "Herr").
        rewrite /pterm_comp. simpl. lra. 
      }
      iSplitR.
      { iPureIntro. apply (pterm_reducible (S n)); auto. rewrite (pure_pterm _ _ σ1 σ); auto. }
      iSplitR.
      { 
        iPureIntro. exists (ε3+1).
        intros. simpl.
        apply Rplus_le_compat_l, Rminus_le_0_compat, pmf_SeriesC_ge_0.
      }
      iSplitR.
      { 
        iPureIntro.
        simpl. rewrite Rplus_0_l. 
        rewrite (SeriesC_ext _ (λ r, (λ a, (prim_step e σ1 a) * (ε3 + 1)) r + (-1) * (λ a,  (prim_step e σ1 a) * (pterm n a)) r)).
        2: {
          intros.
          field_simplify. real_solver.
        }
        rewrite (SeriesC_plus).
        2 : {
          apply ex_seriesC_scal_r. apply pmf_ex_seriesC.
        }
        2 : {
          apply ex_seriesC_scal_l.
          apply pmf_ex_seriesC_mult_fn. 
          exists 1. intros. split.
          - apply pmf_SeriesC_ge_0.
          - apply pmf_SeriesC.
        }
        rewrite Hε_now. replace (nonneg (ε1' + ε3)%NNR) with (nonneg ε1' + ε3); auto.
        rewrite Hε1'.
        rewrite /pterm_comp. simpl. 
        rewrite SeriesC_scal_l SeriesC_scal_r.
        rewrite /step. simpl. field_simplify.
        rewrite <- Rplus_minus_swap. 
        rewrite !Rminus_def.
        apply Rplus_le_compat.
        {
          apply Rplus_le_compat.
          - simpl. rewrite <- Rmult_1_l.
            apply Rmult_le_compat_r; auto.
          - apply pmf_SeriesC.
        }
        apply Ropp_le_contravar, Req_le.
        rewrite (pure_pterm _ _ _ σ1); auto.
        by rewrite pterm_rec /Expval.
      }
      iSplitR.
      { 
        iPureIntro.
        simpl.
        apply (pgl_mon_pred _ (fun x => (fun _ => True) x ∧ (prim_step e σ1) x > 0)).
        - by intros a [_ Hp]. 
        - apply pgl_pos_R, pgl_trivial. lra.
      }
      iIntros. 
      iMod (ec_supply_decrease with "Herra Herr") as (????) "Herra".
      iModIntro.
      destruct (Rlt_decision (nonneg ε3 + nonneg (pterm_comp n (e2, σ2)))%R 1%R) as [Hdec|Hdec]; last first.
      { 
        apply Rnot_lt_ge, Rge_le in Hdec.
        iApply exec_stutter_spend.
        iPureIntro.
        simpl.
        simpl in Hdec. lra.
      }
      iApply exec_stutter_free.
      replace (nonneg ε3 + nonneg (pterm_comp n (e2, σ2)))%R with (nonneg (ε3 + (pterm_comp n (e2, σ2)))%NNR); [|by simpl].
      iMod (ec_supply_increase ε3 (pterm_comp n (e2, σ2)) with "[Herra]") as "[Herra Herr]"; try lra.
      { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
      simpl in H0. 
      apply (pure_state_step) in H0 as H'0; auto.
      subst σ2.
      iFrame.
      iMod "hclose".
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros.
      iApply "IH"; iFrame.
      { 
        iPureIntro. eapply pure_step_inv. 
        - apply H.
        - apply H0.
      }
  Qed.

   Lemma AST_complete_pure_pre' (n: nat) (e : expr) (σ : state) φ ε E : 
    is_pure e = true -> 
    tgl (exec n (e, σ)) φ ε ->
    ↯ ε -∗ WP e @ E [{ v, ⌜φ v⌝ }].
  Proof. 
    intros.
    iInduction n as [|n] "IH" forall (e H σ ε H0).
    - rewrite /exec //= in H0.
      destruct (to_val e) eqn: He.
      + iIntros "Herr". 
        rewrite /tgl in H0. apply of_to_val in He as <-.
        destruct (bool_decide (φ v)) eqn: Hv.
        -- rewrite prob_dret_true //= in H0.
           wp_pures. iModIntro. iPureIntro. by eapply bool_decide_eq_true_1.
        -- rewrite prob_dret_false //= in H0.
           iPoseProof (ec_contradict with "Herr") as "H"; auto; lra.
      + iIntros "Herr". 
        rewrite /tgl in H0. 
        assert (prob dzero (λ (a : val), bool_decide (φ a)) = 0). {
          rewrite /prob. erewrite SeriesC_ext; first by rewrite SeriesC_0.
          move => ? //=. by case_bool_decide.
        }
        rewrite H1 in H0.
        iPoseProof (ec_contradict with "Herr") as "H"; auto; lra.
        
    - destruct (language.to_val e) eqn: He.
      { iIntros "Herr". 
        rewrite /tgl in H0. apply of_to_val in He as <-.
        destruct (bool_decide (φ v)) eqn: Hv.
        -- rewrite prob_dret_true //= in H0.
           wp_pures. iModIntro. iPureIntro. by eapply bool_decide_eq_true_1.
        -- rewrite prob_dret_false //= in H0.
           iPoseProof (ec_contradict with "Herr") as "H"; auto; lra. }
      iIntros "Herr".
      iApply twp_lift_step_fupd_glm; auto.
      iIntros "%% [Hs Herra]". 
      iDestruct (ec_supply_ec_inv with "Herra Herr") as %(ε1' & ε3 & Hε_now & Hε1').
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros "hclose".
      iApply glm_adv_comp. 
      iExists (fun s => step (e, σ1) s > 0), 0%NNR, (fun x => (ε3 + prob_comp_nnr (exec n x) (λ a, bool_decide (φ a)))%NNR).
      destruct (Rlt_dec 0 (prob (exec (S n) (e, σ)) (λ x, bool_decide (φ x)))).
      2 : {
        iExFalso.
        iApply (ec_contradict with "Herr").
        rewrite /pterm_comp. simpl. 
        rewrite /tgl in H0. lra.
      }
      iSplitR.
      { 
        iPureIntro. 
        eapply pure_reducible => //=.
        apply mass_pos_reducible.
        destruct (decide (SeriesC (step (e, σ)) <= 0)); try real_solver.
        apply Rle_antisym in r0; auto. rewrite exec_Sn step_or_final_no_final in r; auto.
        symmetry in r0. apply SeriesC_zero_dzero in r0.
        rewrite r0 dbind_dzero in r. 
        assert (prob dzero (λ (a : val), bool_decide (φ a)) = 0). {
          rewrite /prob. erewrite SeriesC_ext; first by rewrite SeriesC_0.
          move => ? //=. by case_bool_decide.
        } 
        rewrite H1 in r. lra.
      }
      iSplitR. {
        iPureIntro. exists (ε3+1).
        intros. simpl.
        apply Rplus_le_compat_l, Rminus_le_0_compat, prob_ge_0.
      }
      iSplitR. {
        iPureIntro.
        simpl. rewrite Rplus_0_l. 
        rewrite (SeriesC_ext _ (λ r, (λ a, (prim_step e σ1 a) * (ε3 + 1)) r + (-1) * (λ a,  (prim_step e σ1 a) * prob (exec n a) (λ a : val, bool_decide (φ a))) r)).
        2: {
          intros.
          field_simplify. real_solver.
        }
        rewrite (SeriesC_plus).
        2 : {
          apply ex_seriesC_scal_r. apply pmf_ex_seriesC.
        }
        2 : {
          apply ex_seriesC_scal_l.
          apply pmf_ex_seriesC_mult_fn. 
          exists 1. intros. split.
          - apply prob_ge_0.
          - apply prob_le_1.
        }
        rewrite Hε_now. replace (nonneg (ε1' + ε3)%NNR) with (nonneg ε1' + ε3); auto.
        rewrite Hε1'.
        rewrite SeriesC_scal_l SeriesC_scal_r.
        rewrite /step. simpl. field_simplify.
        rewrite <- Rplus_minus_assoc.
        apply Rplus_le_compat.
        { rewrite <- Rmult_1_l. apply Rmult_le_compat_r; auto. }
        rewrite /tgl in H0.
        assert (1 - prob (exec (S n) (e, σ)) (λ a : mstate_ret (lang_markov prob_lang), bool_decide (φ a)) <= ε); try lra.
        etrans. 2 : apply H1.
        rewrite !Rminus_def.
        apply Rplus_le_compat; auto.
        apply Ropp_le_contravar. 
        rewrite <- prob_dbind. 
        assert ((dbind (exec n) (prim_step e σ1))= (exec (S n) (e, σ))) as <-; try real_solver.
        erewrite pure_exec_state; auto.
        simpl. by rewrite He.
      }
      iSplitR.
      { 
        iPureIntro.
        simpl.
        apply (pgl_mon_pred _ (fun x => (fun _ => True) x ∧ (prim_step e σ1) x > 0)).
        - by intros a [_ Hp]. 
        - apply pgl_pos_R, pgl_trivial. lra.
      }
      iIntros. 
      iMod (ec_supply_decrease with "Herra Herr") as (????) "Herra".
      iModIntro.
      destruct (Rlt_decision (nonneg ε3 + nonneg (prob_comp_nnr (exec n (e2, σ2)) (λ a : val, bool_decide (φ a))))%R 1%R) as [Hdec|Hdec]; last first.
      { 
        apply Rnot_lt_ge, Rge_le in Hdec.
        iApply exec_stutter_spend.
        iPureIntro.
        simpl.
        simpl in Hdec. lra.
      }
      iApply exec_stutter_free.
      iMod (ec_supply_increase ε3 (prob_comp_nnr (exec n (e2, σ2)) (λ a : val, bool_decide (φ a))) with "[Herra]") as "[Herra Herr]"; try lra.
      { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
      simpl in H0. 
      apply (pure_state_step) in H1 as H'1; auto.
      subst σ2.
      iFrame.
      iMod "hclose".
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros.
      iApply "IH"; iFrame.
      { 
        iPureIntro. eapply pure_step_inv. 
        - apply H.
        - apply H1.
      }
      iPureIntro. rewrite /tgl /prob_comp_nnr =>//=. 
      by field_simplify.
  Qed.

  Theorem AST_complete_pure (e : expr) ε: 
    is_pure e = true ->
    almost_surely_terminates (e, σ₀) ->
    0 < ε -> 
    ↯ ε -∗ WP e [{ v, True }].
  Proof.
    iIntros "%%% Herr".
    assert (0 <= ε). { lra. }
    apply (AST_pt_lim _ (1-ε)) in H0 as [n H']; auto; try lra.
    iPoseProof ((ec_weaken ε (1 - pterm n (e, σ₀))) with "[Herr]") as "Herr"; try iFrame.
    - pose proof (pmf_SeriesC (exec n (e, σ₀))).
      split; try lra. apply pterm_le1.
    - by iApply AST_complete_pure_pre.
  Qed.


  Theorem twp_complete_pure (e : expr) ε φ: 
    is_pure e = true ->
    tgl (lim_exec (e, σ₀)) φ ε ->
    ↯ ε -∗ WP e [{ v, ⌜φ v⌝ }].
  Proof.
    iIntros "%% Herr".
    destruct (to_val e) eqn: He.
    { 
      apply of_to_val in He; subst.
      rewrite /tgl /prob in H0. 
      destruct (decide (φ v)); first by wp_pures.
      rewrite SeriesC_0 in H0. 2 : {
        intros. case_bool_decide; auto.
        erewrite lim_exec_final; auto.
        eapply dret_0. destruct (decide (x = v)); subst; eauto.
      }
      iPoseProof (ec_contradict with "Herr") as "H"; auto; lra.
    }
    iApply twp_lift_step_fupd_glm; auto.
    iIntros "%% [Hs Herra]". 
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "hclose".
    iApply glm_err_incr_step.
    iIntros. 
    iMod "hclose".
    iDestruct (ec_supply_ec_inv with "Herra Herr") as %(ε1' & ε3 & Hε_now & Hε1'); subst.
    assert (∃ ε2, (ε1' + ε3 + ε2)%NNR = ε') as [??]. { 
      assert (0 <= ε' - (ε1' + ε3)); first by apply Rle_0_le_minus; real_solver.
      exists (mknonnegreal _ H2). 
      apply nnreal_ext => //=. real_solver.
    } 
    assert (0 < x). { 
      rewrite -H2 //= in H1. 
      apply (Rplus_lt_reg_l (ε1' + ε3)). 
      by field_simplify.
    }
    subst.
    destruct (decide (ε1' + ε3 + x < 1)) as [H2 | H2]. 2 : { 
      apply Rnot_lt_ge, Rge_le in H2.
      iApply exec_stutter_spend.
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros.
      by iPureIntro.
    }
    iMod (ec_supply_increase with "Herra") as "[Herra Herr']"; first by simpl; exact H2.
    iCombine "Herr" "Herr'" as "Herr".
    assert (ε1' < ε1' + x). { lra. }
    eapply tgl_gt_lim in H0 as [n H0]; [|exact H4].
    iPoseProof (AST_complete_pure_pre' with "Herr") as "hwp"; eauto.
    rewrite tgl_wp_unfold /tgl_wp_pre //= He.
    iPoseProof ("hwp" with "[Hs Herra]") as "hwp"; try iFrame.
    iMod "hwp". 
    iApply fupd_mask_intro. 
    { set_solver. }
    iIntros "Hclose'".
    iApply exec_stutter_free.
    iFrame.
  Qed.
End Complete.