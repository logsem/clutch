From iris.proofmode Require Import base proofmode.
From Coquelicot Require Export Lim_seq Rbar.
From clutch.common Require Export language.
From clutch.eris Require Import total_weakestpre adequacy primitive_laws.
From clutch.prob Require Import distribution graded_predicate_lifting.

Import uPred.

Lemma twp_step_fupd_tgl_prim_step (e : language.expr prob_lang) σ (ε ε1:nonnegreal) (ε2: language.cfg prob_lang -> nonnegreal) R P:
  reducible (e, σ) ->
  (∃ r, ∀ ρ : language.cfg prob_lang, ε2 ρ <= r) ->
  ε1 + SeriesC
         (λ ρ, prim_step e σ ρ * ε2 ρ) <= ε -> pgl (prim_step e σ) R ε1 ->
  (∀ e, R e → 1 - ε2 e <= prob (lim_exec e) P) ->
  1 - ε <= SeriesC (λ a, step (e, σ) a * prob (lim_exec a) P).
Proof.
  intros Hred Hbound Hsum Hub H.
  simpl.
  assert (1 - (ε1 + SeriesC (λ ρ, prim_step e σ ρ * ε2 ρ)) <=
            SeriesC (λ a, prim_step e σ a * prob (lim_exec a) P)) as Hint; last first.
  { etrans; last exact. apply Rminus_le. lra. }
  rewrite Rcomplements.Rle_minus_l Rplus_comm Rplus_assoc.
  rewrite <-SeriesC_plus; last first.
  { eapply ex_seriesC_le; last first.
    - instantiate (1 := prim_step e σ).
      apply pmf_ex_seriesC.
    -  intros. split.
       + apply Rmult_le_pos; try done. apply prob_ge_0.
       + rewrite <-Rmult_1_r. apply Rmult_le_compat_l; first done. apply prob_le_1.
  }
  { destruct Hbound as [r ?]. eapply ex_seriesC_le; last first.
    - instantiate (1 := λ ρ, prim_step e σ ρ * r).
      apply ex_seriesC_scal_r.
      apply pmf_ex_seriesC.
    -  intros. split.
       + apply Rmult_le_pos; first done. apply cond_nonneg.
       + by apply Rmult_le_compat_l.
  }
  erewrite SeriesC_ext; last first.
  { intros n. by rewrite <-Rmult_plus_distr_l. }
  simpl in Hub, H, R. simpl.
  rewrite (SeriesC_ext _
             (λ ρ, (if bool_decide(R ρ) then prim_step e σ ρ * (ε2 ρ + prob (lim_exec ρ) P) else 0)+
                     if bool_decide (~R ρ) then prim_step e σ ρ * (ε2 ρ + prob (lim_exec ρ) P) else 0
          )); last first.
  { intros. repeat case_bool_decide; try done.
    - by rewrite Rplus_0_r.
    - by rewrite Rplus_0_l.
  }
  rewrite SeriesC_plus; last first.
  { eapply ex_seriesC_filter_pos.
    - intros. apply Rmult_le_pos; first done.
      apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
    - destruct Hbound as [r?].
      eapply ex_seriesC_ext; last first.
      + eapply pmf_ex_seriesC_mult_fn. shelve.
      + intros. simpl. f_equal.
        Unshelve. exists (r+1).
        intros; split.
        * apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
        * apply Rplus_le_compat; try done. apply prob_le_1.
  }
  { eapply ex_seriesC_filter_pos.
    - intros. apply Rmult_le_pos; first done.
      apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
    - destruct Hbound as [r?].
      eapply ex_seriesC_ext; last first.
      + eapply pmf_ex_seriesC_mult_fn. shelve.
      + intros. simpl. f_equal.
        Unshelve. exists (r+1).
        intros; split.
        * apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
        * apply Rplus_le_compat; try done. apply prob_le_1.
  }
  trans (ε1 +
  (SeriesC
     (λ x : expr * state,
        if bool_decide (R x) then prim_step e σ x else 0) +
   SeriesC
     (λ x : expr * state,
        if bool_decide (¬ R x) then prim_step e σ x * (ε2 x + prob (lim_exec x) P) else 0))).
  2:{ apply Rplus_le_compat_l. apply Rplus_le_compat_r.
      apply SeriesC_le.
      - intros. case_bool_decide; last done.
        split; [apply pmf_pos|].
        rewrite -{1}(Rmult_1_r (prim_step _ _ _)). apply Rmult_le_compat_l; [apply pmf_pos|].
        pose proof (H n H0).
        rewrite Rplus_comm. by rewrite <-Rcomplements.Rle_minus_l.
      - apply ex_seriesC_filter_pos.
        + intros. apply Rmult_le_pos; [apply pmf_pos|].
          apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
        + apply pmf_ex_seriesC_mult_fn. destruct Hbound as [r?]. exists (r+1).
          intros; split.
          * apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
          * apply Rplus_le_compat; try done. apply prob_le_1.
  }
  trans (ε1 +
           (SeriesC (λ x : expr * state, if bool_decide (R x) then prim_step e σ x else 0))); last first.
  { rewrite -Rplus_assoc. rewrite -{1}(Rplus_0_r (_+_)).
    apply Rplus_le_compat_l. apply SeriesC_ge_0'.
    intros. case_bool_decide; try lra.
    apply Rmult_le_pos; [apply pmf_pos|].
    apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
  }
  rewrite /pgl in Hub.
  assert (prob (prim_step e σ) (∽(λ ρ, bool_decide(R ρ)))%P <= ε1).
  { etrans; last exact. apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
    intros; repeat case_bool_decide; try done. simpl. done. }
  etrans.
  2: { apply Rplus_le_compat_r. exact. }
  rewrite /prob. simpl.
  rewrite <-SeriesC_plus; last first.
  - apply ex_seriesC_filter_pos; [apply pmf_pos|apply pmf_ex_seriesC].
  - eapply ex_seriesC_ext.
    + intros. by rewrite <- bool_decide_not.
    + apply ex_seriesC_filter_pos; [apply pmf_pos|apply pmf_ex_seriesC].
  - rewrite (SeriesC_ext _ (λ ρ, prim_step e σ ρ)); last first.
    { intros. case_bool_decide; simpl.
      - apply Rplus_0_l.
      - apply Rplus_0_r.
    }
    simpl. apply Req_le_sym.
    epose proof (@prim_step_mass prob_lang) as K. simpl in K.
    apply K. apply Hred.
Qed.

Lemma twp_step_fupd_tgl_state_step (e : language.expr prob_lang) σ l (ε ε1:nonnegreal) (ε2: _ -> nonnegreal) R P:
  l ∈ language.get_active σ ->
  (∃ r, ∀ ρ : language.cfg prob_lang, ε2 ρ <= r) ->
  ε1 + SeriesC
         (λ ρ, language.state_step σ l ρ * ε2 (e, ρ)) <= ε -> pgl (language.state_step σ l) R ε1 ->
  (∀ s, R s → 1 - ε2 (e, s) <= prob (lim_exec (e, s)) P) ->
  1 - ε <= SeriesC (λ a, state_step σ l a * prob (lim_exec (e, a)) P).
Proof.
  intros Hred Hbound Hsum Hub H.
  simpl.
  assert (1 - (ε1 + SeriesC (λ ρ, state_step σ l ρ * ε2 (e, ρ))) <=
            SeriesC (λ a, state_step σ l a * prob (lim_exec (e, a)) P)) as Hint; last first.
  { etrans; last exact. rewrite -Ropp_minus_distr -(Ropp_minus_distr (_+_)).
    apply Ropp_le_cancel. rewrite !Ropp_involutive Rcomplements.Rle_minus_l.
    rewrite Rplus_assoc Rplus_opp_l Rplus_0_r. done.
  }
  rewrite Rcomplements.Rle_minus_l Rplus_comm Rplus_assoc.
  rewrite <-SeriesC_plus; last first.
  { eapply ex_seriesC_le; last first.
    - instantiate (1 := state_step σ l).
      apply pmf_ex_seriesC.
    -  intros. split.
       + apply Rmult_le_pos; try done. apply prob_ge_0.
       + rewrite <-Rmult_1_r. apply Rmult_le_compat_l; try done. apply prob_le_1.
  }
  { destruct Hbound as [r ?]. eapply ex_seriesC_le; last first.
    - instantiate (1 := λ ρ, state_step σ l ρ * r).
      apply ex_seriesC_scal_r.
      apply pmf_ex_seriesC.
    -  intros. split.
       + apply Rmult_le_pos; first done. apply cond_nonneg.
       + by apply Rmult_le_compat_l.
  }
  erewrite SeriesC_ext; last first.
  { intros n. by rewrite <-Rmult_plus_distr_l. }
  simpl in Hub, H, R. simpl.
  rewrite (SeriesC_ext _
             (λ ρ, (if bool_decide(R ρ) then state_step σ l ρ * (ε2 (e, ρ) + prob (lim_exec (e, ρ)) P) else 0)+
                     if bool_decide (~R ρ) then state_step σ l ρ * (ε2 (e, ρ) + prob (lim_exec (e, ρ)) P) else 0
          )); last first.
  { intros. repeat case_bool_decide; try done.
    - by rewrite Rplus_0_r.
    - by rewrite Rplus_0_l.
  }
  rewrite SeriesC_plus; last first.
  { eapply ex_seriesC_filter_pos.
    - intros. apply Rmult_le_pos; first done.
      apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
    - destruct Hbound as [r?].
      eapply ex_seriesC_ext; last first.
      + eapply pmf_ex_seriesC_mult_fn. shelve.
      + intros. simpl. f_equal.
        Unshelve. exists (r+1).
        intros; split.
        * apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
        * apply Rplus_le_compat; try done. apply prob_le_1.
  }
  { eapply ex_seriesC_filter_pos.
    - intros. apply Rmult_le_pos; first done.
      apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
    - destruct Hbound as [r?].
      eapply ex_seriesC_ext; last first.
      + eapply pmf_ex_seriesC_mult_fn. shelve.
      + intros. simpl. f_equal.
        Unshelve. exists (r+1).
        intros; split.
        * apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
        * apply Rplus_le_compat; try done. apply prob_le_1.
  }
  trans (ε1 +
  (SeriesC
     (λ x,
        if bool_decide (R x) then state_step σ l x else 0) +
   SeriesC
     (λ x,
        if bool_decide (¬ R x) then state_step σ l x * (ε2 (e, x) + prob (lim_exec (e, x)) P) else 0))).
  2:{ apply Rplus_le_compat_l. apply Rplus_le_compat_r.
      apply SeriesC_le.
      - intros. case_bool_decide; last done.
        split; [apply pmf_pos|].
        rewrite -{1}(Rmult_1_r (state_step _ _ _)). apply Rmult_le_compat_l; [apply pmf_pos|].
        pose proof (H n H0).
        rewrite Rplus_comm. by rewrite <-Rcomplements.Rle_minus_l.
      - apply ex_seriesC_filter_pos.
        + intros. apply Rmult_le_pos; [apply pmf_pos|].
          apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
        + apply pmf_ex_seriesC_mult_fn. destruct Hbound as [r?]. exists (r+1).
          intros; split.
          * apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
          * apply Rplus_le_compat; try done. apply prob_le_1.
  }
  trans (ε1 +
           (SeriesC (λ x, if bool_decide (R x) then state_step σ l x else 0))); last first.
  { rewrite -Rplus_assoc. rewrite -{1}(Rplus_0_r (_+_)).
    apply Rplus_le_compat_l. apply SeriesC_ge_0'.
    intros. case_bool_decide; try lra.
    apply Rmult_le_pos; [apply pmf_pos|].
    apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
  }
  rewrite /pgl in Hub.
  assert (prob (state_step σ l) (∽(λ ρ, bool_decide(R ρ)))%P <= ε1).
  { etrans; last exact. apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
    intros; repeat case_bool_decide; try done. simpl. done. }
  etrans.
  2: { apply Rplus_le_compat_r. exact. }
  rewrite /prob. simpl.
  rewrite <-SeriesC_plus; last first.
  - apply ex_seriesC_filter_pos; [apply pmf_pos|apply pmf_ex_seriesC].
  - eapply ex_seriesC_ext.
    + intros. by rewrite <- bool_decide_not.
    + apply ex_seriesC_filter_pos; [apply pmf_pos|apply pmf_ex_seriesC].
  - rewrite (SeriesC_ext _ (λ ρ, state_step σ l ρ)); last first.
    { intros. case_bool_decide; simpl.
      - apply Rplus_0_l.
      - apply Rplus_0_r.
    }
    simpl. apply Req_le_sym.
    epose proof (@state_step_mass) as K. simpl in K.
    apply K. simpl in Hred. rewrite /get_active in Hred.
    set_solver.
Qed.

Section adequacy.
  Context `{!erisGS Σ}.

  Lemma tgl_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε':
    ⌜ 0 <= ε ⌝ -∗
    ⌜ 0 <= ε'⌝ -∗
    ⌜tgl μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ -∗ |={∅}=> ⌜tgl (f a) T ε'⌝) -∗
    |={∅}=> ⌜tgl (dbind f μ) T (ε + ε')⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (fupd_mono _ _ (⌜(∀ a b, R a → tgl (f a) T ε')⌝)).
    { iIntros (?). iPureIntro. eapply tgl_dbind; eauto. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.


  Theorem twp_step_fupd_tgl (e : expr) (σ : state) (ε : nonnegreal) φ  :
    state_interp σ ∗ err_interp (ε) ∗ WP e [{ v, ⌜φ v⌝ }] ⊢
    |={⊤,∅}=> ⌜tgl (lim_exec (e, σ)) φ ε⌝.
  Proof.
    iIntros "(Hstate & Herr & Htwp)".
    iRevert (σ ε) "Hstate Herr".
    pose proof (tgl_wp_ind_simple ⊤ () (λ e, ∀ (a : state) (a0 : nonnegreal),
                                  state_interp a -∗ err_interp a0 ={⊤,∅}=∗ ⌜tgl (lim_exec (e, a)) φ a0⌝)%I) as H. iApply H.
    2: { destruct twp_default. done. }
    clear H e.
    iModIntro.
    iIntros (e) "H".
    iIntros (σ ε) "Hs Hec".
    rewrite /tgl_wp_pre.
    case_match.
    - iMod "H" as "%".
      iApply fupd_mask_intro; first done. iIntros "_".
      iPureIntro.
      rewrite /tgl/prob.
      etrans.
      2:{ eapply SeriesC_ge_elem; last apply ex_seriesC_filter_bool_pos; try done.
          intros. case_bool_decide; try lra. apply pmf_pos. }
      erewrite (lim_exec_term 0).
      { simpl. rewrite H. rewrite dret_1_1; last done. destruct ε. simpl.
        case_bool_decide; try lra. done. }
      simpl. rewrite H. by rewrite dret_mass.
    - iSpecialize ("H" $! σ ε with "[$]").
      iMod "H".
      iRevert (H).
      iApply (glm_strong_ind (λ e σ ε, ⌜language.to_val e = None⌝ ={∅}=∗  ⌜tgl (lim_exec (e, σ)) φ ε⌝)%I with "[][$H]").
      iModIntro. clear e σ ε. iIntros (e σ ε) "H %Hval".
      iDestruct "H" as "[H|[H | H]]".
      + iAssert (|={∅}=>  ⌜∀ ε' : nonnegreal,
                             (ε < ε') -> tgl (lim_exec (e, σ)) φ ε'⌝)%I with "[H]" as "H".
        {
          iIntros (ε') "%Hε'".
          iMod ("H" $! ε' (Hε')) as "H".
          iDestruct "H" as "(%R' & %ε1' & %ε2' & %Hineq' & %Hub' & H)".
          iApply fupd_mono.
          { iApply pure_mono. intros. eapply tgl_mon_grading; [eapply Hineq'|eauto]. }
          rewrite -{2}(dret_id_left' (fun _ : () => (lim_exec (e, σ))) tt).
          iApply tgl_dbind'.
          - iPureIntro; apply cond_nonneg.
          - iPureIntro; apply cond_nonneg.
          - iPureIntro; eapply Hub'.
          - iIntros. destruct a.
            iSpecialize ("H" with "[//]").
            iDestruct "H" as "[H _]".
            iApply ("H" with "[//]").
        }
        iApply fupd_mono; [|done].
        apply pure_mono.
        intro H.
        apply tgl_epsilon_limit; [apply Rle_ge, cond_nonneg|].
        intros ε' Hε'.
        eapply (H (mknonnegreal ε' _)); eauto.
        Unshelve.
        apply Rgt_lt in Hε'.
        etrans; [|left;eauto].
        apply cond_nonneg.
      + iDestruct "H" as "(%R & %ε1 & %ε2 & %Hred & %Hbound & %Hineq & %Hub & H)".
        rewrite lim_exec_step step_or_final_no_final.
        2: { by apply reducible_not_final. }
        iAssert (∀ ρ2 : language.expr prob_lang * language.state prob_lang,
          ⌜R ρ2⌝ ={∅}=∗
          let
          '(e2, σ2) := ρ2 in
          |={∅}=>  ⌜tgl (lim_exec (e2, σ2)) φ (ε2 ρ2)⌝)%I with "[H]" as "H".
        { iIntros (ρ2) "%Hρ2". destruct (ρ2) as (e2&σ2). iMod ("H" $! e2 σ2 Hρ2) as "H".
          rewrite /exec_stutter.
          iDestruct "H" as (R2 ε1' ε2' Hineq' Htotal_ub) "H".
          iModIntro.
          iApply (fupd_mono _ _ (⌜tgl (lim_exec (e2, σ2)) φ (ε1' + ε2')⌝)%I).
          { iPureIntro. apply tgl_mon_grading, Hineq'. }
          rewrite -(dret_id_left' (fun _ : () => (lim_exec (e2, σ2))) tt).
          iApply tgl_dbind'.
          (* Fix the weakening for the first two goals *)
          * iPureIntro. apply cond_nonneg.
          * iPureIntro. apply cond_nonneg.
          * iPureIntro. eapply Htotal_ub.
          * iIntros ([] ?).
            iMod ("H" with "[]") as "(Hσ&Herr&Hwand)". { iPureIntro; auto. }
            iMod ("Hwand" with "[$] [$]"); eauto.
        }
        rewrite {2}/tgl.
        setoid_rewrite prob_dbind.
        iApply (fupd_mono _ _ (⌜∀ e, R e -> 1 - (ε2 e) <= prob (lim_exec e) (λ x, bool_decide(φ x))⌝)%I).
        {
          iIntros (HR). iPureIntro.
          by eapply twp_step_fupd_tgl_prim_step.
        }
        iIntros (a HR). iMod ("H" $! a (HR)) as "H".
        destruct a.
        iMod "H" as "%".
        iPureIntro.
        by apply H.
      + remember (language.get_active σ) as l.
        assert (l ⊆ language.get_active σ) as Hsubseteq by set_solver.
        clear Heql.
        iInduction l as [| l] "IH".
        { rewrite big_orL_nil //. }
        rewrite !big_orL_cons.
        iDestruct "H" as "[H|H]".
        2:{ iApply "IH"; try done. iPureIntro. set_solver. }
        iDestruct "H" as "(%R & %ε1 & %ε2 & %Hbound & %Hineq & %Hub & H)".
        iAssert (∀ σ2 : language.state prob_lang,
                   ⌜R σ2⌝ ={∅}=∗ ⌜tgl (lim_exec (e, σ2)) φ (ε2 (e, σ2))⌝)%I with "[H]" as "H".
        { iClear "IH".
          iIntros. iMod ("H" $! σ2 (H)) as "H".
          iDestruct "H" as "(%R' & %ε1' & %ε2' & %Hineq' & %Hub' & H)".
          iApply fupd_mono.
          { iApply pure_mono. intros. eapply tgl_mon_grading; [eapply Hineq'|eauto]. }
          rewrite -{2}(dret_id_left' (fun _ : () => (lim_exec (e, σ2))) tt).
          iApply tgl_dbind'.
          - iPureIntro; apply cond_nonneg.
          - iPureIntro; apply cond_nonneg.
          - iPureIntro; eapply Hub'.
          - iIntros. destruct a.
            iSpecialize ("H" with "[//]").
            iDestruct "H" as "[H _]".
            iApply ("H" with "[//]").
        }
        rewrite {2}/tgl.
        iApply (fupd_mono _ _ (⌜∀ s, R s -> 1 - ε2 (e, s) <= prob (lim_exec (e, s)) (λ x, bool_decide (φ x))⌝)%I).
        {
          iIntros. iPureIntro.
          rewrite (erasure.lim_exec_eq_erasure [l]); last set_solver.
          simpl.
          rewrite /tgl prob_dbind.
          erewrite SeriesC_ext; last by rewrite dret_id_right.
          eapply twp_step_fupd_tgl_state_step; try done.
          set_solver.
        }
        iIntros (a HR). iMod ("H" $! a (HR)) as "%H".
        iPureIntro. by apply H.
    Qed.
End adequacy.


Theorem twp_tgl Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ}, ⊢ ↯ ε -∗ WP e [{ v, ⌜φ v⌝ }]) →
  tgl (lim_exec (e, σ)) φ ε.
Proof.
  intros Hε Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ 0 0) => Hinv.
  iIntros "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iClear "Hh Ht".
    iApply (fupd_mask_intro); [eauto|].
    iIntros "_".
    simpl.
    iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /tgl; intros.
    eapply Rle_trans; last eapply prob_ge_0.
    lra. }
  set ε' := mknonnegreal _ Hε.
  iMod (ec_alloc ε') as (?) "[? ?]"; [by simpl|].
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  epose proof (twp_step_fupd_tgl e σ ε' φ).
  iApply fupd_wand_r. iSplitL.
  - iApply H1. iFrame. by iApply Hwp.
  - iIntros "%". done.
Qed.

Theorem twp_mass_lim_exec Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ}, ⊢ ↯ ε -∗ WP e [{ v, ⌜φ v⌝ }]) →
  (1 - ε <= SeriesC (lim_exec (e, σ)))%R.
Proof.
  intros Hε Hwp.
  eapply tgl_termination_ineq.
  by eapply twp_tgl.
Qed.

Theorem twp_pgl_lim Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ}, ⊢ ↯ ε -∗ WP e [{ v, ⌜φ v⌝ }]) →
  pgl (lim_exec (e, σ)) φ ε.
Proof.
  intros ? Hwp.
  eapply (wp_pgl_lim Σ); [done|].
  intros HGS.
  iIntros "Hε".
  iApply tgl_wp_pgl_wp.
  iPoseProof (Hwp with "Hε") as "Hwp".
  by destruct twp_default, wp_default.
Qed.

(** limit rules *)

Theorem twp_tgl_limit Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ}, (∀ ε' : R, ε' > ε -> ⊢ ↯ ε' -∗ WP e [{ v, ⌜φ v⌝ }])) →
  tgl (lim_exec (e, σ)) φ ε.
Proof.
  intros ? Hwp. rewrite /tgl.
  apply real_le_limit.
  intros.
  replace (1-_-_) with (1 - (ε+ε0)) by lra.
  assert (0<=ε+ε0) as Hεsum.
  { trans ε; try lra. }
  eapply (twp_tgl Σ); [done|].
  iIntros (?) "He".
  iApply (Hwp with "He").
  lra.
Qed.

Theorem twp_mass_lim_exec_limit Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ}, (∀ ε' : R, ε' > ε -> ⊢ ↯ ε' -∗ WP e [{ v, ⌜φ v⌝ }])) →
  (1 - ε <= SeriesC (lim_exec (e, σ)))%R.
Proof.
  intros Hε H'.
  apply real_le_limit.
  intros ε0 H1.
  replace (1-_-_) with (1- (ε+ε0)) by lra.
  assert (0 <= ε + ε0) as Hε0.
  { trans ε; try lra. }
  eapply (twp_mass_lim_exec Σ); [done|].
  iIntros (?) "He".
  iApply (H' with "He").
  lra.
Qed.

Theorem twp_pgl_lim_limit Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ}, (∀ ε' : R, ε' > ε -> ⊢ ↯ ε' -∗ WP e [{ v, ⌜φ v⌝ }])) →
  pgl (lim_exec (e, σ)) φ ε.
Proof.
  intros ? Hwp. eapply (wp_pgl_epsilon_lim Σ); [done|].
  iIntros (???) "Herr".
  iApply tgl_wp_pgl_wp.
  iPoseProof (Hwp with "Herr") as "Hwp".
  { lra. }
  by destruct twp_default, wp_default.
Qed.
