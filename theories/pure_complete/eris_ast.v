From clutch.eris Require Export eris error_rules. 
From clutch.pure_complete Require Import pure term.

Local Open Scope R.

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

End Complete.