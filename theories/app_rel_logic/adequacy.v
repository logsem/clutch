From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Import language.
From clutch.ub_logic Require Import error_credits.
From clutch.app_rel_logic Require Import spec_ra.
From clutch.app_rel_logic Require Import app_weakestpre primitive_laws.
From clutch.prob Require Import distribution couplings_app.
Import uPred.

Section adequacy.
  Context `{!app_clutchGS Σ}.


  Lemma ARcoupl_dbind' `{Countable A, Countable A', Countable B, Countable B'}
    (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B) (R : A → B -> Prop) (T : A' → B' -> Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ 0 <= ε' ⌝ -∗
    ⌜ARcoupl μ1 μ2 R ε⌝ -∗
    (∀ a b, ⌜R a b⌝ ={∅}▷=∗^(S n) ⌜ARcoupl (f a) (g b) T ε'⌝) -∗
    |={∅}▷=>^(S n) ⌜ARcoupl (dbind f μ1) (dbind g μ2) T (ε + ε')⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a b → ARcoupl (f a) (g b) T ε')⌝)).
    { iIntros (?). iPureIntro. eapply ARcoupl_dbind; eauto. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.

  Lemma exec_coupl_erasure (e1 : expr) (σ1 : state) (e1' : expr) (σ1' : state) (n : nat) φ (ε : nonnegreal) :
    to_val e1 = None →
    exec_coupl e1 σ1 e1' σ1' (λ '(e2, σ2) '(e2', σ2') ε',
        |={∅}▷=>^(S n) ⌜ARcoupl (exec n (e2, σ2)) (lim_exec (e2', σ2')) φ ε'⌝) ε
    ⊢ |={∅}▷=>^(S n) ⌜ARcoupl (exec (S n) (e1, σ1)) (lim_exec (e1', σ1')) φ ε⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /exec_coupl /exec_coupl'.
    set (Φ := (λ '(((e1, σ1),(e1', σ1')),ε'),
                (⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                 ⌜ARcoupl (exec (S n) (e1, σ1)) (lim_exec (e1', σ1')) φ ε'⌝)%I) :
           prodO (prodO cfgO cfgO) NNRO  → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m (((?&?)&(?&?))&?) (((?&?)&(?&?))&?) [[[[=] [=]] [[=] [=]]] [=] ]. by simplify_eq. }
    set (F := (exec_coupl_pre (λ '(e2, σ2) '(e2', σ2') ε',
                   |={∅}▷=>^(S n) ⌜ARcoupl (exec n (e2, σ2)) (lim_exec (e2', σ2')) φ ε'⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iMod ("H" $! ((_, _)) with "Hfix [//]").
    }
    clear.
    iIntros "!#" ([[[e1 σ1] [e1' σ1']] ε'']). rewrite /exec_coupl_pre.
    iIntros "[(%R & %ε1 & %ε2 & %Hleq & % & %Hcpl & H) | [(%R & %ε1 & %ε2 & %Hleq & % & %Hcpl & H) | [(%R & %m & %ε1 & %ε2 & %Hleq & %Hcpl & H) | [H | [H | H]]]]] %Hv".
    - rewrite exec_Sn_not_final; [|eauto].
      rewrite lim_exec_step.
      iApply step_fupdN_mono.
      { apply pure_mono.
        eapply ARcoupl_mon_grading; eauto. }
      destruct (to_val e1') eqn:Hv'.
      + destruct (decide (prim_step e1 σ1 = dzero)) as [Hs|].
        * rewrite /= Hs dbind_dzero.
          do 3 iModIntro. iApply step_fupdN_intro; [done|].
          iModIntro. iPureIntro.
          apply ARcoupl_dzero.
          apply Rplus_le_le_0_compat; apply cond_nonneg.
        * assert (prim_step e1' σ1' = dzero) as Hz.
          { eapply (is_final_dzero (e1', σ1')). eauto. }
          simpl in *. rewrite Hz in Hcpl.
          iApply ARcoupl_dbind'.
          -- iPureIntro; apply cond_nonneg.
          -- iPureIntro; apply cond_nonneg.
          -- iPureIntro.
             pose proof (Rplus_0_r ε1) as h. simpl in h. rewrite -h. clear h.
             apply (ARcoupl_eq_trans_r _ dzero); [apply cond_nonneg | lra | eauto |].
             apply ARcoupl_dzero; lra.
          -- iIntros ([e3 σ3] [e3' σ3']) "HR".
             by iMod ("H" $! (e3,σ3) (e3',σ3') with "HR").
      + rewrite step_or_final_no_final; [|eauto].
        iApply (ARcoupl_dbind' _ _ _ _ R); auto.
        * iPureIntro; apply cond_nonneg.
        * iPureIntro; apply cond_nonneg.
        * iIntros ([] [] HR). by iMod ("H" with "[//]").
    - rewrite exec_Sn_not_final; [|eauto].
      iApply step_fupdN_mono.
      { apply pure_mono.
        eapply ARcoupl_mon_grading; eauto. }
      rewrite -(dret_id_left (lim_exec)).
      iApply ARcoupl_dbind'.
      * iPureIntro; apply cond_nonneg.
      * iPureIntro; apply cond_nonneg.
      * iPureIntro. by apply ARcoupl_pos_R in Hcpl.
      * iIntros ([] [] (?&?& [= -> ->]%dret_pos)).
        by iMod ("H"  with "[//]").
    - rewrite -(dret_id_left (exec _)).
      iApply step_fupdN_mono.
      { apply pure_mono.
        eapply ARcoupl_mon_grading; eauto. }
      rewrite (lim_exec_pexec m).
      iApply ARcoupl_dbind'.
      + iPureIntro; apply cond_nonneg.
      + iPureIntro; apply cond_nonneg.
      + by apply ARcoupl_pos_R in Hcpl.
      + iIntros ([] [] (?& [= -> ->]%dret_pos &?)).
          by iMod ("H"  with "[//] [//]").
    - iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜ARcoupl (exec (S n) (e1, σ1))
                                  (lim_exec (e1', σ1')) φ ε''⌝)%I
                  with "H") as "H".
      { iIntros (i α Hα%elem_of_list_lookup_2) "(% & %ε1 & %ε2 & %Hleq & % & %Hcpl & H)".
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ e2 σ2 σ2', R2 (e2, σ2) σ2' → ARcoupl (exec n (e2, σ2))
                                                             (lim_exec (e1', σ2')) φ ε2⌝)%I).
        - iIntros (?). iPureIntro.
          eapply ARcoupl_mon_grading; eauto.
          rewrite /= /get_active in Hα.
          apply elem_of_elements, elem_of_dom in Hα as [].
          eapply ARcoupl_erasure_r; eauto.
          + apply cond_nonneg.
          + apply cond_nonneg.
        - iIntros (????). by iMod ("H" with "[//]"). }
      iInduction (language.get_active σ1') as [| α'] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
    - iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜ARcoupl (exec (S n) (e1, σ1))
                                  (lim_exec (e1', σ1')) φ ε''⌝)%I
                  with "H") as "H".
      { iIntros (i α' Hα'%elem_of_list_lookup_2) "(% & %ε1 & %ε2 & %Hleq & %Hcpl & H)".
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 e2' σ2', R2 σ2 (e2', σ2') → ARcoupl (exec (S n) (e1, σ2))
                                                               (lim_exec (e2', σ2')) φ ε2⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα'.
          apply elem_of_elements, elem_of_dom in Hα' as [].
          eapply ARcoupl_mon_grading; eauto.
          eapply ARcoupl_erasure_l; eauto.
          + apply cond_nonneg.
          + apply cond_nonneg.
        - iIntros (????). by iMod ("H" with "[//] [//]"). }
      iInduction (language.get_active σ1) as [| α'] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
    - iDestruct "H" as "(%&%&%&%&%&%&%&%&%&%&%&%&H)".
      iApply (step_fupdN_mono _ _ _
                (⌜∀ σ2 σ2', R2 σ2 σ2' → ARcoupl (exec (S n) (e1, σ2))
                                          (lim_exec (e1', σ2')) φ (E2 σ2')⌝)%I).
      + iPureIntro.
        intros ?.
        eapply (ARcoupl_erasure_erasable_adv_rhs _ _ _ _ _ _ _ _ _ E2); [apply cond_nonneg|apply cond_nonneg| exact|..]; done.
      + iIntros (???). rewrite /Φ.
        by iMod ("H" with "[//] [//]").
  Qed.


  Theorem wp_ARcoupl_step_fupdN (e e' : expr) (σ σ' : state) n φ (ε : nonnegreal) :
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε ∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜ARcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ e' σ' ε); iIntros "([Hh Ht] & HspecI_auth & Herr & Hwp)".
    - rewrite /exec /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite wp_value_fupd.
        iMod "Hwp" as (v') "[Hspec_frag %]".
        iDestruct (spec_interp_auth_frag_agree_expr with "HspecI_auth Hspec_frag") as %->.
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        erewrite lim_exec_det_final; last first.
        { erewrite pexec_O. by eapply dret_1_1. }
        { done. }
        iPureIntro.
        rewrite /dmap.
        apply (ARcoupl_mon_grading _ _ _ 0); [apply cond_nonneg | ].
        by apply ARcoupl_dret.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro.
        apply ARcoupl_dzero, cond_nonneg.
    - rewrite exec_Sn /step_or_final /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite wp_value_fupd.
        iMod "Hwp" as (v') "[Hspec_frag %]".
        iDestruct (spec_interp_auth_frag_agree_expr with "HspecI_auth Hspec_frag") as %->.
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iApply step_fupdN_intro; [done|]. do 4 iModIntro.
        iPureIntro.
        rewrite exec_unfold dret_id_left /=.
        erewrite lim_exec_det_final; last first.
        { erewrite pexec_O. by eapply dret_1_1. }
        { done. }
        apply (ARcoupl_mon_grading _ _ _ 0); [apply cond_nonneg | ].
        by apply ARcoupl_dret.
      + rewrite wp_unfold /wp_pre /= Heq.
        iMod ("Hwp" with "[$]") as "Hcpl".
        iModIntro.
        assert ((prim_step e σ) = (step (e, σ))) as h => //. rewrite h. clear h.
        rewrite -exec_Sn_not_final ; [|auto].
        iPoseProof
          (exec_coupl_mono _ (λ '(e2, σ2) '(e2', σ2') ε', |={∅}▷=>^(S n)
             ⌜ARcoupl (exec n (e2, σ2)) (lim_exec (e2', σ2')) φ ε'⌝)%I
            with "[] Hcpl") as "H".
        { iIntros ([] [] ?) "H !> !>".
          iMod "H" as "(Hstate & HspecI_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        by iApply (exec_coupl_erasure with "H").
  Qed.

End adequacy.

Class app_clutchGpreS Σ :=
  App_ClutchGpreS{
      app_clutchGpreS_iris  :: invGpreS Σ;
      app_clutchGpreS_heap  :: ghost_mapG Σ loc val;
      app_clutchGpreS_tapes :: ghost_mapG Σ loc tape;
      app_clutchGpreS_spec_heap  :: ghost_mapG Σ loc val;
      app_clutchGpreS_spec_tapes :: ghost_mapG Σ loc tape;
      app_clutchGpreS_spec_prog :: inG Σ (authR progUR);
      app_clutchGpreS_prog  :: inG Σ (authR progUR);
      app_clutchGpreS_err   :: ecGpreS Σ;
    }.

Definition app_clutchΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    (* GFunctor (authUR cfgUR); *)
    GFunctor (authUR progUR);
    GFunctor (authR (realUR))].
Global Instance subG_app_clutchGPreS {Σ} : subG app_clutchΣ Σ → app_clutchGpreS Σ.
Proof. solve_inG. Qed.

Theorem wp_aRcoupl Σ `{app_clutchGpreS Σ} (e e' : expr) (σ σ' : state) n (ε : nonnegreal) φ :
  (∀ `{app_clutchGS Σ}, ⊢  ⤇ e' -∗ € ε -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  ARcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros Hwp.
  eapply pure_soundness.
  eapply (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (ghost_map_alloc σ'.(heap)) as "[%γHs [Hh_spec _]]".
  iMod (ghost_map_alloc σ'.(tapes)) as "[%γTs [Ht_spec _]]".
  iMod (own_alloc ((● (Excl' e')) ⋅ (◯ (Excl' e')))) as "(%γp & Hprog_auth & Hprog_frag)".
  { by apply auth_both_valid_discrete. }


  destruct (Rlt_decision (nonneg ε) 1) as [Hcr|Hcr]; last first.
  { iClear "Hh Ht".
    iApply (fupd_mask_intro); [eauto|].
    iIntros "_".
    iApply step_fupdN_intro; [eauto|].
    iApply laterN_intro.
    iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    (* FIXME: cleanup and move into ARcoupl file *)
    rewrite /ARcoupl. intros.
    apply (Rle_trans _ 1%R _).
    - eapply Rle_trans.
      + eapply SeriesC_le'.
        * intros n'.
          apply Rge_le; rewrite -(Rmult_1_r (_ n')); apply Rle_ge.
          apply Rmult_le_compat.
          -- apply pmf_pos.
          -- destruct (H0 n'); lra.
          -- eapply Rle_refl.
          -- destruct (H0 n'); lra.
        * eapply ex_seriesC_le.
          -- intros n'.
             split.
             --- apply Rmult_le_pos; [apply pmf_pos|destruct (H0 n'); lra].
             --- apply Rge_le; rewrite -(Rmult_1_r (_ n')); apply Rle_ge.
                apply Rmult_le_compat.
                ---- apply pmf_pos.
                ---- destruct (H0 n'); lra.
                ---- eapply Rle_refl.
                ---- destruct (H0 n'); lra.
          -- apply pmf_ex_seriesC.
        * apply pmf_ex_seriesC.
      + apply pmf_SeriesC.
    - eapply Rle_trans; first eapply Hcr.
      simpl.
      rewrite -{1}(Rplus_0_l (nonneg ε)).
      apply Rplus_le_compat_r.
      apply SeriesC_ge_0.
      + intros.
        apply Rmult_le_pos.
        * apply pmf_pos.
        * destruct (H1 x); lra.
      + eapply ex_seriesC_le.
        * intros n'.
          split.
          -- apply Rmult_le_pos; [apply pmf_pos|destruct (H1 n'); lra].
          -- apply Rge_le; rewrite -(Rmult_1_r (_ n')); apply Rle_ge.
             apply Rmult_le_compat.
              --- apply pmf_pos.
              --- destruct (H1 n'); lra.
              --- eapply Rle_refl.
              --- destruct (H1 n'); lra.
        * apply pmf_ex_seriesC.
  }
  iMod (ec_alloc with "[]") as (?) "[? ?]"; first eauto.
  set (HspecGS := CfgSG Σ _ γp _ _ γHs γTs).
  set (HclutchGS := HeapG Σ _ _ _ γH γT HspecGS _).
  iApply wp_ARcoupl_step_fupdN.
  iFrame. (* iFrame "Hctx". *)
  by iApply (Hwp with " [Hprog_frag]").
Qed.

Theorem wp_aRcoupl_lim Σ `{app_clutchGpreS Σ} (e e' : expr) (σ σ' : state) (ε : nonnegreal) φ :
  (∀ `{app_clutchGS Σ}, ⊢  ⤇ e' -∗ € ε -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  ARcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros Hwp.
  rewrite {1}/lim_exec/=.
  intros f g Hf Hg Hfg.
  assert (forall n,
    SeriesC (λ a, exec n (e, σ) a * f a) <=
         SeriesC (λ b, lim_exec (e', σ') b * g b) + ε) as Haux2.
  {
   intro. eapply wp_aRcoupl; eauto.
  }
  assert (forall a,
             Rbar.is_finite (Lim_seq.Sup_seq (λ n : nat, Rbar.Finite (exec n (e, σ) a)))) as Hfin.
  {
    intro a.
    apply (is_finite_bounded 0 1).
    - apply (Lim_seq.Sup_seq_minor_le _ _ 0); simpl.
      case_match; auto.
    - by apply upper_bound_ge_sup; intro; simpl.
  }
  setoid_rewrite lim_distr_pmf at 1.
  transitivity (Rbar.real (Lim_seq.Sup_seq (λ n : nat, Rbar.Finite (SeriesC (λ a : val, exec n (e, σ) a * f a))))).
  - right.
    setoid_rewrite (rbar_scal_r); auto.
    setoid_rewrite <- Sup_seq_scal_r; [ | apply Hf].
    simpl.
    eapply MCT_seriesC.
    + intros n a; auto. specialize (Hf a); real_solver.
    + intros n a. apply Rmult_le_compat_r; [apply Hf | apply (exec_mono (e,σ))].
    + intro a; exists 1; intro n. specialize (Hf a); real_solver.
    + intro n. apply SeriesC_correct.
      apply (ex_seriesC_le _ (exec n (e, σ))); auto.
      intro a; specialize (Hf a). split; [ real_solver |].
      rewrite <- Rmult_1_r. real_solver.
    + rewrite rbar_finite_real_eq; last first.
    {
      apply (is_finite_bounded 0 1).
      - apply (Lim_seq.Sup_seq_minor_le _ _ 0); simpl.
        apply SeriesC_ge_0'.
        intro a. specialize (Hf a).
        case_match; real_solver.
      - apply upper_bound_ge_sup; intro; simpl.
        etrans.
        + apply (SeriesC_le _ (exec n (e, σ))); auto.
          intro a; specialize (Hf a). split; [ real_solver |].
          rewrite <- Rmult_1_r. real_solver.
        + auto.
    }
    apply Lim_seq.Sup_seq_correct.
  - apply Rbar_le_fin'.
    {
      apply Rplus_le_le_0_compat; [ | apply cond_nonneg].
      apply SeriesC_ge_0'.
      intro b. specialize (Hg b); real_solver.
    }
    apply upper_bound_ge_sup.
    intro; simpl. auto.
Qed.

Theorem wp_ARcoupl_epsilon_lim Σ `{app_clutchGpreS Σ} (e e' : expr) (σ σ' : state) (ε : nonnegreal) φ :
  (∀ `{app_clutchGS Σ} (ε' : nonnegreal), ε<ε' -> ⊢ ⤇ e' -∗ € ε' -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  ARcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros H'.
  apply ARcoupl_limit.
  intros ε' Hineq.
  assert (0<=ε') as Hε'.
  { trans ε; try lra. by destruct ε. }
  pose (mknonnegreal ε' Hε') as NNRε'.
  assert (ε' = (NNRbar_to_real (NNRbar.Finite NNRε'))) as Heq.
  { by simpl. }
  rewrite Heq.
  eapply wp_aRcoupl_lim; first done.
  intros. iIntros "Hctx".
  iApply (H' with "[$Hctx]").
  lra.
Qed. 
