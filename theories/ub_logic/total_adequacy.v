From iris.proofmode Require Import base proofmode.
From Coquelicot Require Export Lim_seq Rbar.
From clutch.common Require Export language.
From clutch.ub_logic Require Import ub_total_weakestpre adequacy primitive_laws.
From clutch.prob Require Import distribution union_bounds.

Import uPred.

Lemma twp_step_fupd_ineq_prim_step (e : language.expr prob_lang) σ (ε ε1:nonnegreal) (ε2: language.cfg prob_lang -> nonnegreal) R:
  (∃ r, ∀ ρ : language.cfg prob_lang, ε2 ρ <= r) ->
  ε1 + SeriesC
         (λ ρ, prim_step e σ ρ * ε2 ρ) <= ε -> ub_lift (prim_step e σ) R ε1 ->
  (∀ e, R e → 1 - ε2 e <= SeriesC (lim_exec e)) ->
  1 - ε <= SeriesC (λ a, step (e, σ) a * SeriesC (lim_exec a)).
Proof.
Admitted.

Lemma twp_step_fupd_ineq_state_step (e : language.expr prob_lang) σ l (ε ε1:nonnegreal) (ε2: _ -> nonnegreal) R:
  (∃ r, ∀ ρ : language.cfg prob_lang, ε2 ρ <= r) ->
  ε1 + SeriesC
         (λ ρ, language.state_step σ l ρ * ε2 (e, ρ)) <= ε -> ub_lift (language.state_step σ l) R ε1 ->
  (∀ s, R s → 1 - ε2 (e, s) <= SeriesC (lim_exec (e, s))) ->
  1 - ε <= SeriesC (λ a, state_step σ l a * SeriesC (lim_exec (e, a))).
Proof.
Admitted.

Section adequacy.
  Context `{!ub_clutchGS Σ}.

  Theorem twp_step_fupd (e : expr) (σ : state) (ε : nonnegreal) φ  :
    state_interp σ ∗ err_interp (ε) ∗ WP e [{ v, ⌜φ v⌝ }] ⊢
    |={⊤,∅}=> ⌜(1 - ε <= SeriesC (lim_exec (e, σ)))%R⌝.
  Proof.
    iIntros "(Hstate & Herr & Htwp)".
    iRevert (σ ε) "Hstate Herr".
    pose proof (ub_twp_ind' ⊤ ()  (λ e _, ∀ (a : state) (a0 : nonnegreal),
                                  state_interp a -∗ err_interp a0 ={⊤,∅}=∗ ⌜1 - a0 <= SeriesC (lim_exec (e, a))⌝)%I) as H. iApply H.
    2: { destruct twp_default. done. }
    clear H e.
    iModIntro.
    iIntros (e Φ) "H".
    iIntros (σ ε) "Hs Hec".
    rewrite /ub_twp_pre.
    case_match.
    - iApply fupd_mask_intro; first done. iIntros "_".
      iPureIntro.
      etrans.
      2:{ eapply SeriesC_ge_elem; last done. intros. apply pmf_pos. }
      erewrite (lim_exec_term 0).
      { simpl. rewrite H. rewrite dret_1_1; last done. destruct ε. simpl. lra. }
      simpl. rewrite H. by rewrite dret_mass.
    - iSpecialize ("H" $! σ ε with "[$]").
      iMod "H".
      iRevert (H).
      iApply (exec_ub_strong_ind (λ ε e σ, ⌜language.to_val e = None⌝ ={∅}=∗ ⌜1 - ε <= SeriesC (lim_exec (e, σ))⌝)%I with "[][$H]").
      iModIntro. clear e σ ε. iIntros (e σ ε) "H %Hval".
      iDestruct "H" as "[H|[H|[H|H]]]".
      + iDestruct "H" as "(%R & %ε1 & %ε2 & %Hred & %Hineq & %Hub & H)".
        rewrite lim_exec_step step_or_final_no_final.
        2: { rewrite /is_final. rewrite -eq_None_not_Some. simpl. by eapply reducible_not_val. }
        rewrite dbind_mass.
        iAssert (∀ ρ2 : language.expr prob_lang * language.state prob_lang,
          ⌜R ρ2⌝ ={∅}=∗
          let
          '(e2, σ2) := ρ2 in
          |={∅}=> ⌜1 - ε2 <= SeriesC (lim_exec (e2, σ2))⌝)%I with "[H]" as "H".
        { iIntros (ρ2) "%Hρ2". iMod ("H" $! ρ2 Hρ2) as "H".
          destruct ρ2. iMod "H" as "(?&?&H)".
          iMod ("H" with "[$][$]"). iModIntro. iModIntro. done.
        }
        iApply (fupd_mono _ _ (⌜∀ e, R e -> 1 - ε2 <= SeriesC (lim_exec e)⌝)%I).
        { iIntros (H). iPureIntro.
          eapply (twp_step_fupd_ineq_prim_step _ _ _ _ (λ _, ε2)); try done.
          - exists ε. intros. trans (ε1 + ε2); last lra. destruct ε1, ε2. simpl. lra.
          - rewrite SeriesC_scal_r. etrans; last exact Hineq.
            pose proof (pmf_SeriesC (prim_step e σ)).
            cut (SeriesC (prim_step e σ) * ε2 <= ε2).
            + intros; lra.
            + rewrite <-Rmult_1_l. apply Rmult_le_compat_r.
              * apply cond_nonneg.
              * exact.
        }
        iIntros (a HR). iMod ("H" $! a (HR)) as "H".
        destruct a.
        iApply "H".
      + iDestruct "H" as "(%R & %ε1 & %ε2 & %Hred & %Hbound & %Hineq & %Hub & H)".
        rewrite lim_exec_step step_or_final_no_final.
        2: { rewrite /is_final. rewrite -eq_None_not_Some. simpl. by eapply reducible_not_val. }
        rewrite dbind_mass.
        iAssert (∀ ρ2 : language.expr prob_lang * language.state prob_lang,
          ⌜R ρ2⌝ ={∅}=∗
          let
          '(e2, σ2) := ρ2 in
          |={∅}=> ⌜1 - (ε2 ρ2) <= SeriesC (lim_exec (e2, σ2))⌝)%I with "[H]" as "H".
        { iIntros (ρ2) "%Hρ2". iMod ("H" $! ρ2 Hρ2) as "H".
          destruct ρ2. iMod "H" as "(?&?&H)".
          iMod ("H" with "[$][$]"). iModIntro. iModIntro. done.
        }
        iApply (fupd_mono _ _ (⌜∀ e, R e -> 1 - (ε2 e) <= SeriesC (lim_exec e)⌝)%I).
        { iIntros (H). iPureIntro. by eapply twp_step_fupd_ineq_prim_step. }
        iIntros (a HR). iMod ("H" $! a (HR)) as "H".
        destruct a.
        iApply "H".
      + remember (language.get_active σ) as l.
        assert (l ⊆ language.get_active σ) as Hsubseteq by set_solver.
        clear Heql.
        iInduction (l) as [| l] "IH".
        { rewrite big_orL_nil //. }
        rewrite !big_orL_cons.
        iDestruct "H" as "[H|H]".
        2:{ iApply "IH"; try done. iPureIntro. set_solver. }
        iDestruct "H" as "(%R & %ε1 & %ε2 & %Hineq & %Hub & H)".
        iAssert (∀ σ2 : language.state prob_lang,
                   ⌜R σ2⌝ ={∅}=∗ ⌜1 - ε2 <= SeriesC (lim_exec (e, σ2))⌝)%I with "[H]" as "H".
        { iIntros. iMod ("H" $! σ2 (H)) as "H". iDestruct "H" as "[H _]". iApply "H". done. }
        iApply (fupd_mono _ _ (⌜∀ s, R s -> 1 - ε2 <= SeriesC (lim_exec (e, s))⌝)%I).
        { iIntros (H). iPureIntro. rewrite (erasure.lim_exec_eq_erasure [l]); last set_solver.
          simpl. erewrite SeriesC_ext; last by (intros; rewrite dret_id_right).
          rewrite dbind_mass.
          erewrite SeriesC_ext.
          - eapply (twp_step_fupd_ineq_state_step _ _ _ _ _ (λ _, ε2)); try done.
            + exists ε. intros. trans (ε1 + ε2); last lra. destruct ε1, ε2. simpl. lra.
            + rewrite SeriesC_scal_r. etrans; last exact Hineq.
              pose proof (pmf_SeriesC (language.state_step σ l)).
              cut (SeriesC (language.state_step σ l) * ε2 <= ε2).
              -- intros; lra.
              -- rewrite <-Rmult_1_l. apply Rmult_le_compat_r.
                 ++ apply cond_nonneg.
                 ++ exact.
          - intros. by simpl. 
        }
        iIntros (a HR). iMod ("H" $! a (HR)) as "H".
        destruct a.
        iApply "H".
      + remember (language.get_active σ) as l.
        assert (l ⊆ language.get_active σ) as Hsubseteq by set_solver.
        clear Heql.
        iInduction l as [| l] "IH".
        { rewrite big_orL_nil //. }
        rewrite !big_orL_cons.
        iDestruct "H" as "[H|H]".
        2:{ iApply "IH"; try done. iPureIntro. set_solver. }
        iDestruct "H" as "(%R & %ε1 & %ε2  & %Hbound & %Hineq & %Hub & H)".
        iAssert (∀ σ2 : language.state prob_lang,
                   ⌜R σ2⌝ ={∅}=∗ ⌜1 - (ε2 (e, σ2)) <= SeriesC (lim_exec (e, σ2))⌝)%I with "[H]" as "H".
        { iIntros. iMod ("H" $! σ2 (H)) as "H". iDestruct "H" as "[H _]". iApply "H". done. }
        iApply (fupd_mono _ _ (⌜∀ s, R s -> 1 - ε2 (e, s) <= SeriesC (lim_exec (e, s))⌝)%I).
        { iIntros (H). iPureIntro. rewrite (erasure.lim_exec_eq_erasure [l]); last set_solver.
          simpl. erewrite SeriesC_ext; last by (intros; rewrite dret_id_right).
          rewrite dbind_mass.
          erewrite SeriesC_ext.
          - by eapply twp_step_fupd_ineq_state_step.
          - intros; simpl. done.
        }    
        iIntros (a HR). iMod ("H" $! a (HR)) as "H".
        destruct a.
        iApply "H".
  Qed.
  
End adequacy.
  

Theorem twp_mass_lim_exec Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, ⊢ € ε -∗ WP e [{ v, ⌜φ v⌝ }]) →
  (1 - ε <= SeriesC (lim_exec (e, σ)))%R.
Proof.
  intros Hwp.
  eapply (step_fupdN_soundness_no_lc _ 0 0) => Hinv.
  iIntros "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod ec_alloc as (?) "[? ?]".
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  epose proof (twp_step_fupd e σ ε φ).
  iApply fupd_wand_r. iSplitL.
  - iApply H1. iFrame. by iApply Hwp.
  - iIntros "%". iApply step_fupdN_intro; first done. done. 
Qed. 

Theorem twp_union_bound_lim Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, ⊢ € ε -∗ WP e [{ v, ⌜φ v⌝ }]) →
  ub_lift (lim_exec (e, σ)) φ ε.
Proof.
  intros.
  eapply wp_union_bound_lim; first done.
  intros H1.
  iIntros "Hε".
  iApply ub_twp_ub_wp.
  iAssert (WP e [{ v, ⌜φ v⌝ }])%I with "[Hε]" as "H".
  2:{ destruct twp_default. destruct wp_default. iExact "H". }
  by iApply H0.
Qed.

(** limit rules *)
Theorem twp_mass_lim_exec_limit Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, (∀ ε' : nonnegreal, ε' > ε -> ⊢ € ε' -∗ WP e [{ v, ⌜φ v⌝ }])) →
  (1 - ε <= SeriesC (lim_exec (e, σ)))%R.
Proof.
  intros H'.
  apply real_le_limit.
  intros ε0 H1.
  replace (1-_-_) with (1- (ε+ε0)) by lra.
  assert (0<=ε+ ε0) as Hε0.
  { trans ε; try lra. by destruct ε. }
  pose (mknonnegreal (ε+ε0) Hε0) as NNRε0.
  assert (ε+ε0 = (NNRbar_to_real (NNRbar.Finite (NNRε0)))) as Heq.
  { by simpl. }
  rewrite Heq.
  eapply twp_mass_lim_exec; first done.
  intros. iIntros "He".
  iApply H'; try iFrame.
  simpl. destruct ε; simpl in H1; simpl; lra.
Qed.

Theorem twp_union_bound_lim_limit Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, (∀ ε':nonnegreal, ε'>ε -> ⊢ € ε' -∗ WP e [{ v, ⌜φ v⌝ }])) →
  ub_lift (lim_exec (e, σ)) φ ε.
Proof.
  (* This lemma can be proven with the continuity of ub_lift lemma in the pull request *)
Admitted.
