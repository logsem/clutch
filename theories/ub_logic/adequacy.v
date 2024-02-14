From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Export language.
From clutch.ub_logic Require Import error_credits ub_weakestpre primitive_laws.
From clutch.prob Require Import distribution.
Import uPred.

Section adequacy.
  Context `{!ub_clutchGS Σ}.


  Lemma ub_lift_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ 0 <= ε' ⌝ -∗
    ⌜ub_lift μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ ={∅}▷=∗^(S n) ⌜ub_lift (f a) T ε'⌝) -∗
    |={∅}▷=>^(S n) ⌜ub_lift (dbind f μ) T (ε + ε')⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → ub_lift (f a) T ε')⌝)).
    { iIntros (?). iPureIntro. eapply ub_lift_dbind; eauto. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.


  Lemma ub_lift_dbind_adv' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ exists r, forall a, 0 <= ε' a <= r ⌝ -∗
    ⌜ub_lift μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ ={∅}▷=∗^(S n) ⌜ub_lift (f a) T (ε' a)⌝) -∗
    |={∅}▷=>^(S n) ⌜ub_lift (dbind f μ) T (ε + SeriesC (λ a : A, (μ a * ε' a)%R))⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → ub_lift (f a) T (ε' a))⌝)).
    { iIntros (?). iPureIntro. eapply ub_lift_dbind_adv; eauto. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.

  Lemma exec_ub_erasure (e : expr) (σ : state) (n : nat) φ (ε : nonnegreal) :
    to_val e = None →
    exec_ub e σ ε (λ ε' '(e2, σ2),
        |={∅}▷=>^(S n) ⌜ub_lift (exec n (e2, σ2)) φ ε'⌝)
    ⊢ |={∅}▷=>^(S n) ⌜ub_lift (exec (S n) (e, σ)) φ ε⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /exec_ub /exec_ub'.
    set (Φ := (λ '(ε'', (e1, σ1)),
                (⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                 ⌜ub_lift (exec (S n) (e1, σ1)) φ ε''⌝)%I) :
           prodO NNRO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m (?&(?&?)) (?&(?&?)) [[=] [[=] [=]]]. by simplify_eq. }
    set (F := (exec_ub_pre (λ ε' '(e2, σ2),
                   |={∅}▷=>^(S n) ⌜ub_lift (exec n (e2, σ2)) φ ε'⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iMod ("H" $! ((_, _)) with "Hfix [//]").
    }
    clear.
    iIntros "!#" ([ε'' [e1 σ1]]). rewrite /Φ/F/exec_ub_pre.
    iIntros "[ (%R & %ε1 & %ε2 & %Hred & % & %Hlift & H)| [ (%R & %ε1 & %ε2 & %Hred & (%r & %Hr) & % & %Hlift & H)| [H| [H | H]]]] %Hv".
    - iApply step_fupdN_mono.
      { apply pure_mono.
        eapply UB_mon_grading. eauto. }
      rewrite exec_Sn_not_final; [|eauto].
      iApply ub_lift_dbind'.
      1,2 : iPureIntro; apply cond_nonneg.
      + done.
      + iIntros ([] ?).
        by iMod ("H"  with "[//]").
    - iApply step_fupdN_mono.
      { apply pure_mono.
        eapply UB_mon_grading; eauto. }
      rewrite exec_Sn_not_final; [|eauto].
      iApply ub_lift_dbind_adv'.
      + iPureIntro; apply cond_nonneg.
      + iPureIntro. exists r. split; auto. apply cond_nonneg.
      + done.
      + iIntros ([] ?).
        by iMod ("H"  with "[//]").
    - rewrite exec_Sn_not_final; [|eauto].
      iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜ub_lift (prim_step e1 σ1 ≫= exec n) φ ε''⌝)%I
                  with "H") as "H".
      { iIntros (i α Hα%elem_of_list_lookup_2) "(% & %ε1 & %ε2 & %Hleq & %Hlift & H)".
        replace (prim_step e1 σ1) with (step (e1, σ1)) => //.
        rewrite -exec_Sn_not_final; [|eauto].
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 , R2 σ2 → ub_lift (exec (S n) (e1, σ2)) φ ε2 ⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα.
          apply elem_of_elements, elem_of_dom in Hα as [bs Hα].
          apply (UB_mon_grading _ _ (ε1 + ε2)) => //.
          erewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim _ _ _ _ _ Hα)); eauto.
          eapply ub_lift_dbind; eauto; [apply cond_nonneg | ].
          apply cond_nonneg.
        - iIntros (??). by iMod ("H" with "[//] [//]"). }
      iInduction (language.get_active σ1) as [| α] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
   - rewrite exec_Sn_not_final; [|eauto].
      iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜ub_lift (prim_step e1 σ1 ≫= exec n) φ ε''⌝)%I
                  with "H") as "H".
      { iIntros (i α Hα%elem_of_list_lookup_2) "(% & %ε1 & %ε2 & %Hε'' & %Hleq & %Hlift & H)".
        replace (prim_step e1 σ1) with (step (e1, σ1)) => //.
        rewrite -exec_Sn_not_final; [|eauto].
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 , R2 σ2 → ub_lift (exec (S n) (e1, σ2)) φ (ε2 (e1, σ2))⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα.
          apply elem_of_elements, elem_of_dom in Hα as [bs Hα].
          erewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim _ _ _ _ _ Hα)); eauto.
          apply (UB_mon_grading _ _
                   (ε1 + (SeriesC (λ ρ : language.state prob_lang, language.state_step σ1 α ρ * ε2 (e1, ρ))))) => //.
          eapply ub_lift_dbind_adv; eauto; [by destruct ε1|].
          destruct Hε'' as [r Hr]; exists r.
          intros a.
          split; [by destruct (ε2 _) | by apply Hr].
        - iIntros (??). by iMod ("H" with "[//] [//]"). }
      iInduction (language.get_active σ1) as [| α] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
  - iDestruct "H" as "[%R [%ε1 [%ε2 (%Hsum & %Hlift & Hwand)]]]".
    iApply step_fupdN_mono. { apply pure_mono. eapply UB_mon_grading, Hsum. }
    rewrite -(dret_id_left' (fun _ : () => (exec (S n) (e1, σ1))) tt).
    iApply ub_lift_dbind'.
    + iPureIntro; apply cond_nonneg.
    + iPureIntro; apply cond_nonneg.
    + iPureIntro.
      apply total_ub_lift_implies_ub_lift in Hlift.
      eapply Hlift.
    + iIntros (? Hcont).
      replace tt with a; [| by destruct a].
      do 2 rewrite Nat.iter_succ.
      iSpecialize ("Hwand" with "[]"); [iPureIntro; eauto|].
      rewrite (dret_id_left').
      iMod ("Hwand" with "[//]") as "H".
      iFrame.
  Qed.

  Theorem wp_refRcoupl_step_fupdN (e : expr) (σ : state) (ε : nonnegreal) n φ  :
    state_interp σ ∗ err_interp (ε) ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜ub_lift (exec n (e, σ)) φ ε⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ ε); iIntros "((Hσh & Hσt) & Hε & Hwp)".
    - rewrite /exec /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite ub_wp_value_fupd.
        iMod "Hwp" as "%".
        iApply fupd_mask_intro; [set_solver|]; iIntros.
        iPureIntro.
        apply (UB_mon_grading _ _ 0); [apply cond_nonneg | ].
        apply ub_lift_dret; auto.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro.
        apply ub_lift_dzero,
        Rle_ge,
        cond_nonneg.
    - rewrite exec_Sn /step_or_final /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite ub_wp_value_fupd.
        iMod "Hwp" as "%".
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iApply step_fupdN_intro; [done|]. do 4 iModIntro.
        iPureIntro.
        rewrite exec_unfold dret_id_left /=.
        apply (UB_mon_grading _ _ 0); [apply cond_nonneg | ].
        apply ub_lift_dret; auto.
      + rewrite ub_wp_unfold /ub_wp_pre /= Heq.
        iMod ("Hwp" with "[$]") as "Hlift".
        iModIntro.
        iPoseProof
          (exec_ub_mono _ (λ ε' '(e2, σ2), |={∅}▷=>^(S n)
             ⌜ub_lift (exec n (e2, σ2)) φ ε'⌝)%I
            with "[%] [] Hlift") as "H".
        { apply Rle_refl. }
        { iIntros (? []) "H !> !>".
          iMod "H" as "(Hstate & Herr_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        assert ((prim_step e σ) = (step (e, σ))) as h => //.
        rewrite h. clear h.
        rewrite -exec_Sn_not_final; [|eauto].
        iAssert
          (|={∅}▷=> |={∅}▷=>^n ⌜ub_lift (exec (S n) (e, σ)) φ ε⌝)%I
          with "[H]" as "Haux"; last first.
        {  iMod "Haux".
           do 2 iModIntro.
           iMod "Haux".
           iModIntro.
           iApply (step_fupdN_wand with "Haux").
           iPureIntro; done.
         }
        by iApply (exec_ub_erasure with "H").
  Qed.

End adequacy.


Class ub_clutchGpreS Σ := UB_ClutchGpreS {
  ub_clutchGpreS_iris  :> invGpreS Σ;
  ub_clutchGpreS_heap  :> ghost_mapG Σ loc val;
  ub_clutchGpreS_tapes :> ghost_mapG Σ loc tape;
  ub_clutchGpreS_err   :> ecGpreS Σ;
}.

Definition ub_clutchΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    GFunctor (authR (realUR))].
Global Instance subG_ub_clutchGPreS {Σ} : subG ub_clutchΣ Σ → ub_clutchGpreS Σ.
Proof. solve_inG. Qed.

Theorem wp_union_bound Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) n (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, ⊢ € ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ub_lift (exec n (e, σ)) φ ε.
Proof.
  intros Hwp.
  eapply (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod ec_alloc as (?) "[? ?]".
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  iApply wp_refRcoupl_step_fupdN.
  iFrame.
  iApply Hwp.
  done.
Qed.

Lemma ub_lift_closed_lim (e : expr) (σ : state) (ε : nonnegreal) φ :
  (forall n, ub_lift (exec n (e, σ)) φ ε ) ->
  ub_lift (lim_exec (e, σ)) φ ε .
Proof.
  intros Hn P HP.
  apply lim_exec_continuous_prob; auto.
  intro n.
  apply Hn; auto.
Qed.

Theorem wp_union_bound_lim Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, ⊢ € ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ub_lift (lim_exec (e, σ)) φ ε.
Proof.
  intros.
  apply ub_lift_closed_lim.
  intro n.
  apply (wp_union_bound Σ); auto.
Qed.

Theorem wp_union_bound_epsilon_lim Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ} (ε':nonnegreal), ε<ε' -> ⊢ € ε' -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ub_lift (lim_exec (e, σ)) φ ε.
Proof.
  intros H'.
  apply ub_lift_epsilon_limit.
  { destruct ε. simpl. lra. }
  intros ε0 H1.
  assert (0<=ε0) as Hε0.
  { trans ε; try lra. by destruct ε. }
  pose (mknonnegreal ε0 Hε0) as NNRε0.
  assert (ε0 = (NNRbar_to_real (NNRbar.Finite (NNRε0)))) as Heq.
  { by simpl. }
  rewrite Heq.
  eapply wp_union_bound_lim; first done.
  intros. iIntros "He".
  iApply H'; try iFrame.
  simpl. destruct ε; simpl in H1; simpl; lra.
Qed.
