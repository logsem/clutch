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

  (** Helper: lift a pure-monotone implication through [◇ ⌜·⌝]. *)
  Local Lemma except_0_pure_mono_iprop (P Q : Prop) :
    (P → Q) → ((◇ ⌜P⌝ : iProp Σ) ⊢ ◇ ⌜Q⌝).
  Proof. intros HPQ. apply bi.except_0_mono, bi.pure_mono, HPQ. Qed.

  Lemma tgl_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε':
    ⌜ 0 <= ε ⌝ -∗
    ⌜ 0 <= ε'⌝ -∗
    ⌜tgl μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ -∗ |={0; ∅|}=> ◇ ⌜tgl (f a) T ε'⌝) -∗
    |={0; ∅|}=> ◇ ⌜tgl (dbind f μ) T (ε + ε')⌝ : iProp Σ.
  Proof.
    iIntros (Hε Hε' HR) "H".
    iApply (hfupd_mono _ _ (◇ ⌜∀ a, R a → tgl (f a) T ε'⌝)%I).
    { apply except_0_pure_mono_iprop. intros Hall.
      eapply tgl_dbind; eauto. }
    iIntros (a HRa). iApply ("H" with "[//]").
  Qed.

  Theorem twp_step_fupd_tgl k (e : expr) (σ : state) (ε : nonnegreal) φ  :
    state_interp k σ ∗ err_interp (ε) ∗ WP e [{ v, ⌜φ v⌝ }] ⊢
    |={0; ⊤|}=> ◇ ⌜tgl (lim_exec (e, σ)) φ ε⌝.
  Proof.
    iIntros "(Hstate & Herr & Htwp)".
    iRevert (k σ ε) "Hstate Herr".
    pose proof (tgl_wp_ind_simple ⊤ () (λ e, ∀ (k : nat) (a : state) (a0 : nonnegreal),
                                  state_interp k a -∗ err_interp a0 -∗
                                  |={0; ⊤|}=> ◇ ⌜tgl (lim_exec (e, a)) φ a0⌝)%I) as H.
    iApply H.
    2: { destruct twp_default. done. }
    clear H e.
    iModIntro.
    iIntros (e) "H".
    iIntros (k σ ε) "Hs Hec".
    rewrite /tgl_wp_pre.
    case_match.
    - iApply (elim_fupd_hfupd_plain 0 0 ⊤ ⊤ ⌜φ v⌝
        ⌜tgl (lim_exec (e, σ)) φ ε⌝); [lia|].
      iSplitL "H"; [iApply "H"|].
      iIntros (l Hl) "%Hφ". assert (l = 0%nat) as -> by lia.
      iApply hfupd_intro. rewrite /bi_except_0. iRight. iPureIntro.
      rewrite /tgl/prob.
      etrans.
      2:{ eapply SeriesC_ge_elem; last apply ex_seriesC_filter_bool_pos; try done.
          intros. case_bool_decide; try lra. apply pmf_pos. }
      erewrite (lim_exec_term 0).
      { simpl. rewrite H. rewrite dret_1_1; last done. destruct ε. simpl.
        case_bool_decide; try lra. done. }
      simpl. rewrite H. by rewrite dret_mass.
    - iSpecialize ("H" $! k σ ε with "[$]").
      iApply (elim_fupd_hfupd_plain 0 0 ⊤ ∅ _
        ⌜tgl (lim_exec (e, σ)) φ ε⌝ with "[$H]"); first lia.
      iIntros (l Hl) "Hglm". assert (l = 0%nat) as -> by lia.
      iRevert (H).
      iApply (glm_strong_ind
        (λ e σ ε, ⌜language.to_val e = None⌝ -∗
                  |={0; ∅|}=> ◇ ⌜tgl (lim_exec (e, σ)) φ ε⌝)%I
        with "[][$Hglm]").
      iModIntro. clear e σ ε. iIntros (e σ ε) "H %Hval".
      iDestruct "H" as "[H|[H | H]]".
      + iApply (hfupd_mono _ _ (◇ ⌜∀ ε' : nonnegreal,
            (ε < ε') → tgl (lim_exec (e, σ)) φ ε'⌝)%I).
        { iIntros "Hgoal". iStopProof.
          apply except_0_pure_mono_iprop.
          intros Hall.
          apply tgl_epsilon_limit; [apply Rle_ge, cond_nonneg|].
          intros ε' Hε'.
          assert (0 <= ε')%R as Hε'nn.
          { apply Rgt_lt in Hε'. etrans; [|left; eauto]. apply cond_nonneg. }
          eapply (Hall (mknonnegreal ε' Hε'nn)). simpl. lra. }
        rewrite bi.pure_forall except_0_forall.
        iApply hfupd_forall_2. iIntros (ε').
        destruct (decide (ε < ε')%R) as [Hε'|Hε']; last first.
        { iApply hfupd_intro. rewrite /bi_except_0. iRight.
          iPureIntro. intros. done. }
        iSpecialize ("H" $! ε' with "[//]").
        iApply (elim_fupd_hfupd_plain 0 0 ∅ ∅
          (exec_stutter
             (λ ε'' : nonnegreal,
                ((⌜language.to_val e = None⌝ ={0; ∅|}=∗
                  ◇ ⌜tgl (lim_exec (e, σ)) φ ε''⌝) ∧
                 glm e σ ε''
                   (λ '(e2, σ2) (ε2 : nonnegreal),
                      |={∅,⊤}=> state_interp (S k) σ2 ∗ err_interp ε2 ∗
                        ∀ (k0 : nat) (a : state) (a0 : nonnegreal),
                          state_interp k0 a -∗ err_interp a0 ={0; ⊤|}=∗
                          ◇ ⌜tgl (lim_exec (e2, a)) φ a0⌝))%I)
             ε')
          ⌜ε < ε' → tgl (lim_exec (e, σ)) φ ε'⌝); [lia|].
        iSplitL "H"; [iApply "H"|].
        iIntros (l' Hl') "Hst". assert (l' = 0%nat) as -> by lia.
        iDestruct (exec_stutter_compat_1 _ _ with "[] Hst") as "[%H'|H2]".
        { iIntros (εa εb Hle) "H". iSplit.
          - iDestruct "H" as "[H _]". iIntros "%Hto". iSpecialize ("H" with "[//]").
            iApply (hfupd_mono _ _ _ with "H").
            apply except_0_pure_mono_iprop.
            intros Hge. eapply tgl_mon_grading; eauto.
          - iDestruct "H" as "[_ H]".
            iApply (glm_mono_grading with "[%] H"). exact Hle. }
        2: { iDestruct "H2" as "[H2 _]". iSpecialize ("H2" with "[//]").
          iApply (hfupd_mono _ _ _ with "H2").
          apply except_0_pure_mono_iprop. intros; auto. }
        iApply hfupd_intro. iApply laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        intros _. rewrite /tgl. intros.
        eapply Rle_trans; [|apply prob_ge_0]. lra.
      + iDestruct "H" as "(%R & %ε1 & %ε2 & %Hred & %Hbound & %Hineq & %Hub & H)".
        rewrite lim_exec_step step_or_final_no_final.
        2: { by apply reducible_not_final. }
        iAssert (∀ ρ2 : language.expr prob_lang * language.state prob_lang,
          ⌜R ρ2⌝ -∗
          |={0; ∅|}=> ◇ ⌜tgl (lim_exec ρ2) φ (ε2 ρ2)⌝)%I with "[H]" as "H".
        { iIntros (ρ2) "%Hρ2". destruct (ρ2) as (e2&σ2).
          iApply (elim_fupd_hfupd_plain 0 0 ∅ ∅
            (exec_stutter
               (λ ε' : nonnegreal,
                  (|={∅,⊤}=> state_interp (S k) σ2 ∗ err_interp ε' ∗
                    ∀ (k0 : nat) (a : state) (a0 : nonnegreal),
                      state_interp k0 a -∗ err_interp a0 ={0; ⊤|}=∗
                      ◇ ⌜tgl (lim_exec (e2, a)) φ a0⌝)%I)
               (ε2 (e2, σ2)))
            ⌜tgl (lim_exec (e2, σ2)) φ (ε2 (e2, σ2))⌝); [lia|].
          iSplitL "H"; [iApply ("H" $! e2 σ2 Hρ2)|].
          iIntros (l1 Hl1) "Hst". assert (l1 = 0%nat) as -> by lia.
          iDestruct "Hst" as "(%R' & %ε1' & %ε2' & %Hineq' & %Hlift' & H)".
          rewrite -(dret_id_left' (λ _ : (), lim_exec (e2, σ2)) tt).
          iApply (hfupd_mono _ _ (◇ ⌜tgl (dret tt ≫= λ _ : (), lim_exec (e2, σ2)) φ (ε1' + ε2')⌝)%I).
          { apply except_0_pure_mono_iprop.
            intros Htgl. eapply tgl_mon_grading; eauto. }
          iApply (tgl_dbind' (λ _ : (), lim_exec (e2, σ2)) (dret tt) R' (λ x, φ x) ε1' ε2').
          { iPureIntro. apply cond_nonneg. }
          { iPureIntro. apply cond_nonneg. }
          { iPureIntro. exact Hlift'. }
          iIntros (a HRa). destruct a.
          iSpecialize ("H" with "[//]").
          iApply (elim_fupd_hfupd_plain 0 0 ∅ ⊤
            (state_interp (S k) σ2 ∗ err_interp ε2' ∗
              (∀ (k0 : nat) (a : state) (a0 : nonnegreal),
                state_interp k0 a -∗ err_interp a0 ={0; ⊤|}=∗
                ◇ ⌜tgl (lim_exec (e2, a)) φ a0⌝))%I
            ⌜tgl (lim_exec (e2, σ2)) φ ε2'⌝); [lia|].
          iSplitL "H"; [iApply "H"|].
          iIntros (l' Hl') "(Hσ' & Hε' & Hwp')".
          assert (l' = 0%nat) as -> by lia.
          iSpecialize ("Hwp'" $! (S k) σ2 ε2' with "Hσ' Hε'").
          iApply (hfupd_mono _ _ _ with "Hwp'").
          apply except_0_pure_mono_iprop. intros Htgl. exact Htgl. }
        rewrite {2}/tgl.
        setoid_rewrite prob_dbind.
        iApply (hfupd_mono _ _ (◇ ⌜∀ e0, R e0 → 1 - (ε2 e0) <=
                          prob (lim_exec e0) (λ x, bool_decide (φ x))⌝)%I).
        { iIntros "Hgoal". iStopProof.
          apply except_0_pure_mono_iprop. intros HR.
          by eapply twp_step_fupd_tgl_prim_step. }
        iIntros (a HRa).
        iApply (hfupd_mono _ _ _ with "(H [//])").
        apply except_0_pure_mono_iprop.
        intros. by destruct a.
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
                   ⌜R σ2⌝ -∗
                   |={0; ∅|}=> ◇ ⌜tgl (lim_exec (e, σ2)) φ (ε2 (e, σ2))⌝)%I
          with "[H]" as "H".
        { iClear "IH".
          iIntros (σ2) "%HRs2".
          iApply (elim_fupd_hfupd_plain 0 0 ∅ ∅
            (exec_stutter
               (λ ε2' : nonnegreal,
                  ((⌜language.to_val e = None⌝ ={0; ∅|}=∗
                    ◇ ⌜tgl (lim_exec (e, σ2)) φ ε2'⌝) ∧
                   glm e σ2 ε2'
                     (λ '(e2, σ2') (ε2'' : nonnegreal),
                        |={∅,⊤}=> state_interp (S k) σ2' ∗ err_interp ε2'' ∗
                          ∀ (k0 : nat) (a : state) (a0 : nonnegreal),
                            state_interp k0 a -∗ err_interp a0 ={0; ⊤|}=∗
                            ◇ ⌜tgl (lim_exec (e2, a)) φ a0⌝))%I)
               (ε2 (e, σ2)))
            ⌜tgl (lim_exec (e, σ2)) φ (ε2 (e, σ2))⌝); [lia|].
          iSplitL "H"; [iApply ("H" $! σ2 HRs2)|].
          iIntros (l' Hl') "Hst". assert (l' = 0%nat) as -> by lia.
          iDestruct (exec_stutter_compat_1 _ _ with "[] Hst") as "[%H'|H2]".
          { iIntros (εa εb Hle) "H". iSplit.
            - iDestruct "H" as "[H _]". iIntros "%Hto". iSpecialize ("H" with "[//]").
              iApply (hfupd_mono _ _ _ with "H").
              apply except_0_pure_mono_iprop.
              intros Hge. eapply tgl_mon_grading; eauto.
            - iDestruct "H" as "[_ H]".
              iApply (glm_mono_grading with "[%] H"). exact Hle. }
          2: { iDestruct "H2" as "[H2 _]". iSpecialize ("H2" with "[//]").
            iApply (hfupd_mono _ _ _ with "H2").
            apply except_0_pure_mono_iprop. intros; auto. }
          iApply hfupd_intro. iApply laterN_intro.
          rewrite /bi_except_0. iRight. iPureIntro.
          rewrite /tgl. intros.
          eapply Rle_trans; [|apply prob_ge_0].
          destruct (ε2 (e, σ2)) as [? ?]. simpl in *. lra. }
        rewrite {2}/tgl.
        iApply (hfupd_mono _ _ (◇ ⌜∀ s, R s → 1 - ε2 (e, s) <=
              prob (lim_exec (e, s)) (λ x, bool_decide (φ x))⌝)%I).
        { iIntros "Hgoal". iStopProof.
          apply except_0_pure_mono_iprop. intros HR.
          rewrite (erasure.lim_exec_eq_erasure [l]); last set_solver.
          simpl.
          rewrite /tgl prob_dbind.
          erewrite SeriesC_ext; last by rewrite dret_id_right.
          eapply twp_step_fupd_tgl_state_step; try done.
          set_solver. }
        iIntros (s HRs).
        iApply (hfupd_mono _ _ _ with "(H [//])").
        apply except_0_pure_mono_iprop. intros; done.
  Qed.
End adequacy.


Theorem twp_tgl Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ}, ⊢ ↯ ε -∗ WP e [{ v, ⌜φ v⌝ }]) →
  tgl (lim_exec (e, σ)) φ ε.
Proof.
  intros Hε Hwp.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ 1).
  rewrite laterN_later -except_0_into_later.
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iApply laterN_intro. iApply except_0_intro. iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /tgl. intros.
    eapply Rle_trans; last eapply prob_ge_0.
    lra. }
  iMod (hfupd_soundness HasLc 0 ⊤) as (Hinv) "(_ & Hhfupd)".
  iApply "Hhfupd".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  set ε' := mknonnegreal _ Hε.
  iMod (ec_alloc ε') as (Hec) "[Hs Hf]"; [done|].
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  change ε with (nonneg ε').
  iPoseProof (twp_step_fupd_tgl O e σ ε' φ) as "H".
  iApply "H".
  iFrame "Hs". rewrite /state_interp /=. iFrame "Hh Ht".
  iApply Hwp. iApply "Hf".
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
