From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Export language erasable exec.
From clutch.base_logic Require Import error_credits.
From clutch.eris Require Import weakestpre primitive_laws.
From clutch.prob Require Import distribution.
Import uPred.

Section adequacy.
  Context `{!erisGS Σ}.

  Lemma step_fupd_fupdN_S n (P : iProp Σ) :  ((|={∅}▷=>^(S n) P) ⊣⊢ (|={∅}=> |={∅}▷=>^(S n) P))%I.
  Proof. iSplit; iIntros; simpl; iApply fupd_idemp; iFrame. Qed.

  Lemma pgl_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ 0 <= ε' ⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ ={∅}▷=∗^(S n) ⌜pgl (f a) T ε'⌝) -∗
    |={∅}▷=>^(S n) ⌜pgl (dbind f μ) T (ε + ε')⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → pgl (f a) T ε')⌝)).
    { iIntros (?). iPureIntro. eapply pgl_dbind; eauto. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.

  Lemma pgl_dbind_adv' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ exists r, forall a, 0 <= ε' a <= r ⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ ={∅}▷=∗^(S n) ⌜pgl (f a) T (ε' a)⌝) -∗
    |={∅}▷=>^(S n) ⌜pgl (dbind f μ) T (ε + SeriesC (λ a : A, (μ a * ε' a)%R))⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → pgl (f a) T (ε' a))⌝)).
    { iIntros (?). iPureIntro. eapply pgl_dbind_adv; eauto. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.


  Lemma glm_erasure (e : expr) (σ : state) (n : nat) φ (ε : nonnegreal) :
    to_val e = None →
    glm e σ ε (λ '(e2, σ2) ε',
        |={∅}▷=>^(S n) ⌜pgl (exec n (e2, σ2)) φ ε'⌝)
      ⊢ |={∅}▷=>^(S n) ⌜pgl (exec (S n) (e, σ)) φ ε⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /glm /glm'.
    set (Φ := (λ '((e1, σ1), ε''),
                (⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                                              ⌜pgl (exec (S n) (e1, σ1)) φ ε''⌝)%I) :
           prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    set (F := (glm_pre (λ '(e2, σ2) ε',
                   |={∅}▷=>^(S n) ⌜pgl (exec n (e2, σ2)) φ ε'⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iMod ("H" $! ((_, _)) with "Hfix [//]").
    }
    clear.
    iIntros "!#" ([[e1 σ1] ε'']). rewrite /Φ/F/glm_pre.
    iIntros " [H | [ (%R & %ε1 & %ε2 & %Hred & (%r & %Hr) & % & %Hlift & H)|H]] %Hv".

    - iApply step_fupdN_mono.
      {
        apply pure_mono.
        eapply pgl_epsilon_limit; auto.
        apply Rle_ge.
        apply cond_nonneg.
      }
      iIntros (ε' Hε').
      destruct (decide (ε' < 1)); last first.
      {
        iApply step_fupdN_mono.
        - apply pure_mono.
          intros ?.
          apply pgl_1.
          lra.
        - iApply step_fupdN_intro; auto.
      }
      iApply step_fupd_fupdN_S.
      iMod ("H" $! (mknonnegreal ε' _) with "[]") as "H".
      {
        iPureIntro.
        simpl in *. simpl.
        lra.
      }
      iDestruct "H" as "[%R' [%ε1' [%ε2' (%Hsum' & %Hlift' & Hwand')]]]".
      iModIntro.
      rewrite -(dret_id_left' (fun _ : () => (exec (S n) _)) tt).
      iApply (step_fupdN_mono _ _ _ ⌜(pgl _ _ (ε1' + ε2')) ⌝).
      { iIntros "%H'"; iPureIntro. eapply pgl_mon_grading; eauto. }
      iApply (pgl_dbind').
      * iPureIntro; apply cond_nonneg.
      * iPureIntro; apply cond_nonneg.
      * iPureIntro.
        apply tgl_implies_pgl in Hlift'.
        eapply Hlift'.
      * iIntros (? Hcont).
        replace tt with a; [| by destruct a].
        iSpecialize ("Hwand'" with "[]"); [iPureIntro; eauto|].
        rewrite (dret_id_left').
        iApply step_fupd_fupdN_S.
        iMod ("Hwand'" with "[//]"); iModIntro; iFrame.
        iModIntro; eauto.
      Unshelve.
      pose proof (cond_nonneg ε'').
      simpl in *.
      lra.
    - iApply step_fupdN_mono.
      { apply pure_mono.
        eapply pgl_mon_grading; eauto. }
      rewrite exec_Sn_not_final; [|eauto].
      iApply pgl_dbind_adv'.
      + iPureIntro; apply cond_nonneg.
      + iPureIntro. exists r. split; auto. 
      + done.
      + iIntros ([] ?).
        iApply step_fupd_fupdN_S.
        iMod ("H" $! e s with "[]") as "H";  [iPureIntro; eauto| iModIntro ].
        iDestruct "H" as "[%R' [%ε1' [%ε2' (%Hsum' & %Hlift' & Hwand')]]]".
        rewrite -(dret_id_left' (fun _ : () => (exec n (e, s))) tt).
        iApply (step_fupdN_mono _ _ _ ⌜(pgl _ _ (ε1' + ε2')) ⌝).
        { iIntros "%H'"; iPureIntro. eapply pgl_mon_grading; eauto. }
        iApply (pgl_dbind').
        * iPureIntro; apply cond_nonneg.
        * iPureIntro; apply cond_nonneg.
        * iPureIntro.
          apply tgl_implies_pgl in Hlift'.
          eapply Hlift'.
        * iIntros (? Hcont).
          replace tt with a; [| by destruct a].
          iSpecialize ("Hwand'" with "[]"); [iPureIntro; eauto|].
          rewrite (dret_id_left').
          iApply step_fupd_fupdN_S.
          iFrame.
          iModIntro.
          eauto.
    - rewrite exec_Sn_not_final; [|eauto].
      iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜pgl (prim_step e1 σ1 ≫= exec n) φ ε''⌝)%I
                  with "H") as "H".
      { iIntros (i α Hα%elem_of_list_lookup_2) "(% & %ε1 & %ε2 & %Hε'' & %Hleq & %Hlift & H)".
        replace (prim_step e1 σ1) with (step (e1, σ1)) => //.
        rewrite -exec_Sn_not_final; [|eauto].
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 , R2 σ2 → pgl (exec (S n) (e1, σ2)) φ (ε2 (e1, σ2))⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα.
          apply elem_of_elements, elem_of_dom in Hα as [bs Hα].
          erewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim _ _ _ _ _ Hα)); eauto.
          apply (pgl_mon_grading _ _
                   (ε1 + (SeriesC (λ ρ : language.state prob_lang, language.state_step σ1 α ρ * ε2 (e1, ρ))))) => //.
          eapply pgl_dbind_adv; eauto; [by destruct ε1|].
          destruct Hε'' as [r Hr]; exists r.
          intros a.
          split; [by destruct (ε2 _) | by apply Hr].
        - iIntros (e s).
          iApply step_fupd_fupdN_S.
          iMod ("H" with "[//]") as "H"; iModIntro.
          iDestruct "H" as "[%R' [%ε1' [%ε2' (%Hsum' & %Hlift' & Hwand')]]]".
          rewrite -(dret_id_left' (fun _ : () => (exec (S n) _)) tt).
          iApply (step_fupdN_mono _ _ _ ⌜(pgl _ _ (ε1' + ε2')) ⌝).
          { iIntros "%H'"; iPureIntro. eapply pgl_mon_grading; eauto. }
          iApply (pgl_dbind').
          * iPureIntro; apply cond_nonneg.
          * iPureIntro; apply cond_nonneg.
          * iPureIntro.
            apply tgl_implies_pgl in Hlift'.
            eapply Hlift'.
          * iIntros (? Hcont).
            replace tt with a; [| by destruct a].
            iSpecialize ("Hwand'" with "[]"); [iPureIntro; eauto|].
            rewrite (dret_id_left').
            iApply step_fupd_fupdN_S.
            iMod ("Hwand'" with "[//]"); iModIntro; iFrame.
            iModIntro; eauto. }
      iInduction (language.get_active σ1) as [| α] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
  Qed.

  Theorem wp_refRcoupl_step_fupdN (ε : nonnegreal) (e : expr) (σ : state) n φ :
    state_interp σ ∗ err_interp (ε) ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜pgl (exec n (e, σ)) φ ε⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ ε); iIntros "((Hσh & Hσt) & Hε & Hwp)".
    - rewrite /exec /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd.
        iMod "Hwp" as "%".
        iApply fupd_mask_intro; [set_solver|]; iIntros.
        iPureIntro.
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg | ].
        apply pgl_dret; auto.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro.
        apply pgl_dzero,
        Rle_ge,
        cond_nonneg.
    - rewrite exec_Sn /step_or_final /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd.
        iMod "Hwp" as "%".
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iApply step_fupdN_intro; [done|]. do 4 iModIntro.
        iPureIntro.
        rewrite exec_unfold dret_id_left /=.
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg | ].
        apply pgl_dret; auto.
      + rewrite pgl_wp_unfold /pgl_wp_pre /= Heq.
        iMod ("Hwp" with "[$]") as "Hlift".
        iModIntro.
        iPoseProof
          (glm_mono _ (λ '(e2, σ2) ε', |={∅}▷=>^(S n)
             ⌜pgl (exec n (e2, σ2)) φ ε'⌝)%I
            with "[%] [] Hlift") as "H".
        { apply Rle_refl. }
        { iIntros ([] ?) "H !> !>".
          iMod "H" as "(Hstate & Herr_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        assert ((prim_step e σ) = (step (e, σ))) as h => //.
        rewrite h. clear h.
        rewrite -exec_Sn_not_final; [|eauto].
        by iApply (glm_erasure with "H").
  Qed.

  (** safety *)
  Lemma glm_erasure_safety (e : expr) (σ : state) (n : nat) (ε : nonnegreal) :
    to_val e = None →
    glm e σ ε (λ '(e2, σ2) ε',
                     |={∅}▷=>^(S n) ⌜SeriesC (iterM n prim_step_or_val (e2, σ2)) >= 1 - ε'⌝)
    ⊢ |={∅}▷=>^(S n) ⌜SeriesC (iterM (S n) prim_step_or_val (e, σ)) >= 1 - ε⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /glm/glm'.
    set (Φ := (λ '((e1, σ1), ε''),
                (⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                 ⌜SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) >= 1 - ε''⌝)%I) :
           prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    set (F := (glm_pre (λ '(e2, σ2) ε',
                   |={∅}▷=>^(S n) ⌜SeriesC (iterM n prim_step_or_val (e2, σ2)) >= 1 - ε'⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      iMod ("H" $! ((_, _)) with "Hfix [//]"). done.
    }
    clear.
    iIntros "!#" ([[e1 σ1] ε'']). rewrite /Φ/F/glm_pre.
    iIntros " [ H | [ (%R & %ε1 & %ε2 & %Hred & (%r & %Hr) & % & %Hlift & H)|H]] %Hv".
    - iApply (step_fupdN_mono _ _ _ (⌜∀ ε', ε'' < ε'  -> SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) >= 1 - ε'⌝ )).
      {
        apply pure_mono.
        intros ?.
        apply Rle_ge.
        apply real_le_limit.
        intros ε Hε.
        apply Rge_le.
        replace (1 - ε'' - ε) with (1 - (ε'' + ε)) by lra.
        apply H.
        lra.
      }
      iIntros (ε' Hε').
      iMod ("H" $! (mknonnegreal ε' _) with "[]") as "H".
      {
        iPureIntro.
        simpl in *. simpl.
        lra.
      }
      iApply step_fupd_fupdN_S.
      iDestruct (exec_stutter_compat_1 with "[][$]") as "[%H'|H2]".
      { iIntros (???) "H %".
        iDestruct ("H" with "[//]") as "H".
        iApply step_fupdN_mono; last done.
        iPureIntro. intros. trans (1-ε); try lra.
        simpl. lra. }
        + iApply step_fupdN_intro; first done.
          iPureIntro.
          trans 0; last first.
          * simpl. apply Rle_ge. apply Rle_minus. done.
          * apply Rle_ge; auto.
        + iDestruct ("H2" with "[//]") as "H2". done.
    Unshelve.
    pose proof (cond_nonneg ε'').
    simpl in *.
    lra.
    - iApply (step_fupdN_mono _ _ _ (⌜∀ ρ, R ρ -> SeriesC (iterM n prim_step_or_val ρ) >= 1 - (ε2 ρ)⌝)).
      { apply pure_mono.
        intros H1.
        apply Rle_ge.
        simpl.
        rewrite /dbind/dbind_pmf{1}/pmf.
        setoid_rewrite prim_step_or_val_no_val; last done.
        rewrite /pgl in Hlift. rewrite /prob in Hlift.
        rewrite distr_double_swap. setoid_rewrite SeriesC_scal_l.
        trans (1 - SeriesC
            (λ a : language.expr prob_lang * language.state prob_lang,
               if Datatypes.negb (bool_decide (R a)) then language.prim_step e1 σ1 a else 0) - SeriesC
                            (λ ρ : language.expr prob_lang * language.state prob_lang, language.prim_step e1 σ1 ρ * ε2 ρ)).
          { simpl. simpl in *. lra. }
          simpl. simpl in *.
          rewrite !Rcomplements.Rle_minus_l.
          replace 1 with (SeriesC (prim_step e1 σ1)); last first.
          { eapply mixin_prim_step_mass; last auto.
            apply ectx_lang_mixin.
          }
          assert (ex_seriesC (λ a : language.cfg prob_lang, prim_step e1 σ1 a * SeriesC (iterM n prim_step_or_val a))).
          { apply pmf_ex_seriesC_mult_fn. naive_solver. }
          assert (ex_seriesC (λ ρ : expr * state, prim_step e1 σ1 ρ * ε2 ρ) ).
          { apply pmf_ex_seriesC_mult_fn. exists r. intros a. pose proof cond_nonneg (ε2 a). naive_solver. }
          eassert (ex_seriesC (λ a : expr * state, if Datatypes.negb (bool_decide (R a)) then prim_step e1 σ1 a else 0)).
          { apply ex_seriesC_filter_bool_pos; auto. }
          rewrite -!SeriesC_plus; auto; last first.
          { apply ex_seriesC_plus; auto. }
          apply SeriesC_le; last first.
          { repeat apply ex_seriesC_plus; auto. }
          intros x; split; first auto.
          case_bool_decide; simpl.
          + rewrite -Rmult_plus_distr_l.
            cut (prim_step e1 σ1 x *1 <= prim_step e1 σ1 x * (SeriesC (iterM n prim_step_or_val x) + ε2 x)).
            { rewrite Rmult_1_r. rewrite Rplus_0_r. intros; done. }
            apply Rmult_le_compat_l; auto.
            rewrite -Rcomplements.Rle_minus_l.
            apply Rge_le. naive_solver.
          + apply Rle_plus_r; first done.
            apply Rplus_le_le_0_compat; first real_solver.
            apply Rmult_le_pos; auto.
      }
      iIntros ([e s] ?).
      iMod ("H" with "[//]") as "H".
      iDestruct (exec_stutter_compat_1 with "[][$]") as "[%H'|H]".
      { iIntros.
        iApply step_fupdN_mono; last done.
        iPureIntro. intros. trans (1-ε); try lra.
        simpl. lra. }
      + iApply step_fupdN_intro; first done.
        iPureIntro.
        trans 0; last (simpl in *; lra).
        apply Rle_ge.
        auto.
      + done.
    - iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) >= 1 - ε''⌝)%I
                  with "H") as "H".
      { iIntros (i α Hα%elem_of_list_lookup_2) "(% & %ε1 & %ε2 & %Hε'' & %Hleq & %Hlift & H)".
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 , R2 σ2 → SeriesC (iterM (S n) prim_step_or_val (e1, σ2)) >= 1 - (ε2 (e1, σ2))⌝)%I).
        {
          iPureIntro.
          intros H.
          assert (SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) =
                  SeriesC (state_step σ1 α ≫= λ σ1', iterM (S n) prim_step_or_val (e1, σ1'))) as ->.
          { erewrite (SeriesC_ext _ (pexec (S n) (e1, σ1))); last first.
            { rewrite /pexec. done. }
            erewrite (SeriesC_ext (_≫=_) (_≫=λ σ1', pexec (S n) (e1, σ1'))); last first.
            { rewrite /pexec. done. }
            rewrite -!(dmap_mass _ (λ x, x.1)).
            eapply Rcoupl_mass_eq.
            rewrite /=/get_active elem_of_elements elem_of_dom in Hα.
            destruct Hα as [??].
            by eapply pexec_coupl_step_pexec.
          }
          simpl. apply Rle_ge.
          setoid_rewrite prim_step_or_val_no_val; last done.
          simpl. simpl in *.
          rewrite {1}/dbind/dbind_pmf{1}/pmf.
          rewrite /pgl in Hlift. rewrite /prob in Hlift.
          rewrite distr_double_swap. setoid_rewrite SeriesC_scal_l.
          trans (1 - SeriesC
                       (λ a ,
                          if Datatypes.negb (bool_decide (R2 a)) then language.state_step σ1 α a else 0) - SeriesC
                                                                                                                               (λ σ2 , language.state_step σ1 α σ2 * ε2 (e1, σ2))).
          { simpl. simpl in *. rewrite -Rminus_plus_distr.
            rewrite !Rminus_def. apply Rplus_le_compat_l.
            apply Ropp_le_contravar. etrans; last exact.
            apply Rplus_le_compat_r. auto. }
          simpl. simpl in *.
          rewrite !Rcomplements.Rle_minus_l.
          replace 1 with (SeriesC (state_step σ1 α)); last first.
          { apply state_step_mass. rewrite /get_active in Hα.
            rewrite elem_of_elements in Hα. done.
          }
          assert (ex_seriesC (λ a : state, state_step σ1 α a * SeriesC (prim_step e1 a ≫= iterM n prim_step_or_val)) ).
          { apply pmf_ex_seriesC_mult_fn. exists 1. intros; auto. }
          eassert (ex_seriesC (λ σ2 : state, state_step σ1 α σ2 * ε2 (e1, σ2))).
          { apply pmf_ex_seriesC_mult_fn. destruct Hε''. epose proof cond_nonneg. naive_solver. }
          eassert (ex_seriesC (λ a : state, if Datatypes.negb (bool_decide (R2 a)) then state_step σ1 α a else 0)).
          { apply ex_seriesC_filter_bool_pos; auto. }
          rewrite -!SeriesC_plus; auto; last first.
          { apply ex_seriesC_plus; auto. }
          apply SeriesC_le; last first.
          { repeat apply ex_seriesC_plus; auto. }
          intros x; split; first auto.
          case_bool_decide; simpl.
          - rewrite -Rmult_plus_distr_l.
            cut (state_step σ1 α x *1 <=
  state_step σ1 α x * (SeriesC (prim_step e1 x ≫= iterM n prim_step_or_val) + ε2 (e1, x))).
            { rewrite Rmult_1_r. rewrite Rplus_0_r. intros; done. }
            apply Rmult_le_compat_l; auto.
            rewrite -Rcomplements.Rle_minus_l.
            apply Rge_le. simpl.
            setoid_rewrite prim_step_or_val_no_val in H; last auto.
            apply H. naive_solver.
          - apply Rle_plus_r; first done.
            apply Rplus_le_le_0_compat; first real_solver.
            apply Rmult_le_pos; auto.
        }
        iIntros (e s).
        iApply step_fupd_fupdN_S.
        iMod ("H" with "[//]") as "H"; iModIntro.
        iDestruct (exec_stutter_compat_1 with "[][$]") as "[%H'|H]".
        { iIntros (???) "H %".
          iDestruct ("H" with "[//]") as "H".
          iApply step_fupdN_mono; last done.
          iPureIntro. intros. trans (1-ε); try lra.
          simpl. lra. }
        + iApply step_fupdN_intro; first done.
          iPureIntro.
          trans 0; last first.
          * simpl. apply Rle_ge. apply Rle_minus. done.
          * apply Rle_ge; auto.
        + iDestruct ("H" with "[//]") as "H". done.
      }
      iInduction (language.get_active σ1) as [| α] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
  Qed.

  Theorem wp_safety_fupdN (ε : nonnegreal) (e : expr) (σ : state) n φ  :
    state_interp σ ∗ err_interp (ε) ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜SeriesC (pexec n (e, σ)) >= 1 - ε⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ ε); iIntros "((Hσh & Hσt) & Hε & Hwp)".
    - rewrite /=.
      iApply fupd_mask_intro; [set_solver|]; iIntros.
      iPureIntro.
      trans 1; last first.
      { pose proof cond_nonneg ε. lra. }
      apply Rle_ge. rewrite dret_mass. done.
    - destruct (to_val e) eqn:Heq.
      + simpl.
        rewrite /dbind/dbind_pmf{2}/pmf/=.
        apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd.
        iMod "Hwp" as "%".
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iApply step_fupdN_intro; [done|]. do 4 iModIntro.
        iPureIntro.
        apply Rle_ge. trans 1.
        { pose proof cond_nonneg ε. lra. }
        erewrite SeriesC_ext; last first.
        { intros. setoid_rewrite prim_step_or_val_is_val; last done.
          done.
        }
        erewrite (SeriesC_ext _ (λ n0, if bool_decide (n0 = (of_val v, σ)) then 1 else 0)); last first.
        * intros []. case_bool_decide as H0.
          -- simplify_eq. etrans; last eapply (SeriesC_singleton' (of_val v, σ)).
             apply SeriesC_ext.
             intros. case_bool_decide.
             ++ subst. rewrite dret_1_1; last done.
                rewrite Rmult_1_l.
                induction n; simpl.
                ** rewrite dret_1_1; [lra|done].
                ** rewrite /dbind/dbind_pmf{1}/pmf/=.
                   etrans; last eapply (SeriesC_singleton' (of_val v, σ)).
                   apply SeriesC_ext.
                   intros. case_bool_decide; subst; simpl.
                   --- rewrite IHn. rewrite step_or_final_is_final; first rewrite dret_1_1; [lra|done|].
                       rewrite /is_final. simpl. done.
                   --- simpl. rewrite step_or_final_is_final; last by rewrite /is_final.
                       rewrite dret_0; last done. lra.
             ++ rewrite dret_0; last done. lra.
          -- apply SeriesC_0.
             intros.
             rewrite /dret/dret_pmf{1}/pmf.
             case_bool_decide; subst; last lra.
             rewrite Rmult_1_l.
             revert e s v σ H H0.
             induction n.
             ++ simpl. intros. rewrite dret_0; done.
             ++ intros. simpl. rewrite /dbind/dbind_pmf{1}/pmf/=.
                apply SeriesC_0.
                intros. destruct (decide (x = (of_val v, σ))).
                ** subst. rewrite IHn; try done. lra.
                ** rewrite step_or_final_is_final; last by rewrite /is_final.
                   rewrite dret_0; last done.
                   lra.
        * rewrite SeriesC_singleton. lra.
      + rewrite pgl_wp_unfold /pgl_wp_pre /= Heq.
        iMod ("Hwp" with "[$]") as "Hlift".
        iModIntro.
        iPoseProof
          (glm_mono _ (λ '(e2, σ2) ε', |={∅}▷=>^(S n)
             ⌜SeriesC (iterM n prim_step_or_val (e2, σ2)) >= 1 - ε'⌝)%I
            with "[%] [] Hlift") as "H".
        { apply Rle_refl. }
        { iIntros ([] ?) "H !> !>".
          iMod "H" as "(Hstate & Herr_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        by iApply (glm_erasure_safety with "H").
  Qed.

End adequacy.


Class erisGpreS Σ := ErisGpreS {
  erisGpreS_iris  :: invGpreS Σ;
  erisGpreS_heap  :: ghost_mapG Σ loc val;
  erisGpreS_tapes :: ghost_mapG Σ loc tape;
  erisGpreS_err   :: ecGpreS Σ;
}.

Definition erisΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    GFunctor (authR nonnegrealUR)].
Global Instance subG_erisGPreS {Σ} : subG erisΣ Σ → erisGpreS Σ.
Proof. solve_inG. Qed.

Theorem wp_pgl Σ `{erisGpreS Σ} (e : expr) (σ : state) n (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (exec n (e, σ)) φ ε.
Proof.
  intros Hε Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  (* Handle the trivial 1 <= ε case *)
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iClear "Hh Ht".
    iApply (fupd_mask_intro); [eauto|].
    iIntros "_".
    iApply step_fupdN_intro; [eauto|].
    iApply laterN_intro; iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /pgl; intros.
    eapply Rle_trans; [eapply prob_le_1|done]. }
  set ε' := mknonnegreal _ Hε.
  iMod (ec_alloc ε') as (?) "[? ?]"; [done|].
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  iApply (wp_refRcoupl_step_fupdN ε').
  iFrame.
  iApply Hwp.
  done.
Qed.

Lemma pgl_closed_lim (e : expr) (σ : state) (ε : R) φ :
  (∀ n, pgl (exec n (e, σ)) φ ε) →
  pgl (lim_exec (e, σ)) φ ε .
Proof. intros Hn. by apply lim_exec_continuous_prob. Qed.

Theorem wp_pgl_lim Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (lim_exec (e, σ)) φ ε.
Proof.
  intros.
  apply pgl_closed_lim.
  intro n.
  by apply (wp_pgl Σ).
Qed.

Theorem wp_pgl_epsilon_lim Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ :
  0 <= ε →
  (∀ `{erisGS Σ} (ε':nonnegreal), ε<ε' -> ⊢ ↯ ε' -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (lim_exec (e, σ)) φ ε.
Proof.
  intros ? H'.
  apply pgl_epsilon_limit; [lra|].
  intros ε0 H1.
  assert (0<=ε0) as Hε0 by lra.
  pose (mknonnegreal ε0 Hε0) as NNRε0.
  assert (ε0 = (NNRbar_to_real (NNRbar.Finite (NNRε0)))) as Heq.
  { by simpl. }
  rewrite Heq.
  eapply wp_pgl_lim; [done|done|].
  intros. iIntros "He".
  iApply H'; try iFrame.
  lra.
Qed.

Theorem wp_safety Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ n:
  0 <= ε →
  (∀ `{erisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  SeriesC (pexec n (e, σ)) >= 1 - ε.
Proof.
  intros Hε Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  (* Handle the trivial 1 <= ε case *)
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iClear "Hh Ht".
    iApply (fupd_mask_intro); [eauto|].
    iIntros "_".
    iApply step_fupdN_intro; [eauto|].
    iApply laterN_intro; iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    trans 0.
    - apply Rle_ge. apply SeriesC_ge_0'. intros. auto.
    - simpl. lra. }
  set ε' := mknonnegreal _ Hε.
  iMod (ec_alloc ε') as (?) "[? ?]"; [done|].
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  iApply (wp_safety_fupdN ε'). iFrame.
  iApply Hwp. done.
Qed.

Lemma pexec_safety_relate (e:expr) σ n:
  probp (pexec n (e, σ)) (λ ρ, (is_final ρ ∨ reducible ρ)) =
  SeriesC (pexec (S n) (e, σ)).
Proof.
  revert e σ.
  induction n; intros e σ.
  - simpl. rewrite pexec_O. rewrite pexec_1.
    rewrite /probp. rewrite /step_or_final.
    erewrite (SeriesC_ext _ (λ x, if bool_decide (is_final (e, σ) ∨ reducible (e, σ))
                                  then dret (e, σ) x else 0)); last first.
    { intros. destruct (decide (n=(e,σ))).
      - subst. done.
      - rewrite dret_0; last done. by repeat case_match.
    }
    case_bool_decide as H.
    + rewrite dret_mass. case_match; first by rewrite dret_mass.
      simpl. erewrite mixin_prim_step_mass; auto.
      * apply: ectx_lang_mixin.
      * destruct H; auto.
        exfalso.
        destruct H. naive_solver.
    + rewrite SeriesC_0; last done.
      case_match; first exfalso.
      * apply H. naive_solver.
      * symmetry. apply SeriesC_0.
        intros x. assert (0<=step (e, σ) x) as [|] by auto; auto.
        exfalso. apply H. right. rewrite /reducible. naive_solver.
  - rewrite /prob in IHn. rewrite /prob.
    rewrite (pexec_Sn_r _ (S n)).
    rewrite dbind_mass.
    apply SeriesC_ext.
    intros [].
    case_bool_decide as H.
    + replace (SeriesC _) with 1; first lra.
      symmetry.
      destruct H.
      * rewrite /step_or_final. case_match; first apply dret_mass.
        exfalso. destruct H. naive_solver.
      * rewrite /step_or_final. case_match; first apply dret_mass.
        simpl. erewrite mixin_prim_step_mass; auto.
        apply: ectx_lang_mixin.
    + replace (SeriesC _) with 0; first lra.
      symmetry.
      rewrite /step_or_final.
      case_match.
      * exfalso. naive_solver.
      * apply SeriesC_0.
        intros x. eassert (0<= step _ x) as [|<-] by auto; auto.
        exfalso. apply H. right. rewrite /reducible. naive_solver.
Qed.

Corollary wp_safety' Σ `{erisGpreS Σ} (e : expr) (σ : state) (ε : R) φ n:
  0 <= ε →
  (∀ `{erisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  probp (pexec n (e, σ)) (λ ρ, is_final ρ ∨ reducible ρ) >= 1 - ε.
Proof.
  intros Hε Hwp.
  rewrite pexec_safety_relate.
  by eapply (wp_safety Σ).
Qed.
