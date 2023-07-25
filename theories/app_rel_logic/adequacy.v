From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.program_logic Require Export language weakestpre.
From clutch.ub_logic Require Import error_credits.
From clutch.rel_logic Require Import spec_ra.
From clutch.app_rel_logic Require Import app_weakestpre primitive_laws.
From clutch.prob Require Import distribution couplings_app.
Import uPred.

Section adequacy.
  Context `{!clutchGS Σ}.


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

  Lemma exec_coupl_erasure (e1 : expr) (σ1 : state) (e1' : expr) (σ1' : state) (n : nat) φ (ε ε' : nonnegreal) :
    to_val e1 = None →
    reducible e1 σ1 ->
    exec_coupl e1 σ1 e1' σ1' (λ '(e2, σ2) '(e2', σ2'),
        |={∅}▷=>^(S n) ⌜ARcoupl (exec_val n (e2, σ2)) (lim_exec_val (e2', σ2')) φ ε⌝) ε'
    ⊢ |={∅}▷=>^(S n) ⌜ARcoupl (exec_val (S n) (e1, σ1)) (lim_exec_val (e1', σ1')) φ (ε + ε')%NNR⌝.
  Proof.
    iIntros (Hv Hred) "Hexec".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /exec_coupl /exec_coupl'.
    set (Φ := (λ '(ε'',((e1, σ1),(e1', σ1'))),
                (⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                 ⌜ARcoupl (exec_val (S n) (e1, σ1)) (lim_exec_val (e1', σ1')) φ (ε + ε'')%NNR⌝)%I) :
           prodO NNRO (prodO cfgO cfgO) → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m (?&((?&?)&(?&?))) (?&((?&?)&(?&?))) [[=] [[[=] [=]] [[=] [=]]]]. by simplify_eq. }
    set (F := (exec_coupl_pre (λ '(e2, σ2) '(e2', σ2'),
                   |={∅}▷=>^(S n) ⌜ARcoupl (exec_val n (e2, σ2)) (lim_exec_val (e2', σ2')) φ ε⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iMod ("H" $! ((_, _)) with "Hfix [//]").
    }
    clear.
    iIntros "!#" ([ε'' [[e1 σ1] [e1' σ1']]]). rewrite /exec_coupl_pre.
    iIntros "[(%R & % & %Hcpl & H) | [(%R & % & %Hcpl & H) | [(%R & %m & %ε1 & %ε2 & %Hleq & %Hcpl & H) | [H | [H | H]]]]] %Hv".
    - rewrite exec_val_Sn_not_val; [|done].
      rewrite lim_exec_val_prim_step.
      rewrite nnreal_plus_comm.
      destruct (to_val e1') eqn:Hv'.
      + destruct (decide (prim_step e1 σ1 = dzero)) as [Hs|].
        * rewrite /= Hs dbind_dzero.
          do 3 iModIntro. iApply step_fupdN_intro; [done|].
          iModIntro. iPureIntro.
          apply ARcoupl_dzero.
          apply Rplus_le_le_0_compat;
          apply cond_nonneg.
        * assert (prim_step e1' σ1' = dzero) as Hz by by apply val_stuck_dzero.
          rewrite /= (val_stuck_dzero e1') in Hcpl; [|eauto].
          iApply ARcoupl_dbind'.
          -- iPureIntro; apply cond_nonneg.
          -- iPureIntro; apply cond_nonneg.
          -- iPureIntro.
             rewrite -(Rplus_0_r ε'').
             apply (ARcoupl_eq_trans_r _ dzero); [apply cond_nonneg | lra | eauto |].
             apply ARcoupl_dzero; lra.
          -- iIntros ([e3 σ3] [e3' σ3']) "HR".
             by iMod ("H" $! (e3,σ3) (e3',σ3') with "HR").
      + rewrite prim_step_or_val_no_val; [|done].
        iApply (ARcoupl_dbind' _ _ _ _ R); auto.
        * iPureIntro; apply cond_nonneg.
        * iPureIntro; apply cond_nonneg.
        * iIntros ([] [] HR). by iMod ("H" with "[//]").
    - rewrite exec_val_Sn_not_val; [|done].
      rewrite nnreal_plus_comm.
      rewrite -(dret_id_left (lim_exec_val)).
      iApply ARcoupl_dbind'.
      * iPureIntro; apply cond_nonneg.
      * iPureIntro; apply cond_nonneg.
      * iPureIntro. by apply ARcoupl_pos_R in Hcpl.
      * iIntros ([] [] (?&?& [= -> ->]%dret_pos)).
        by iMod ("H"  with "[//]").
    - rewrite -(dret_id_left (exec_val _)).
      rewrite nnreal_plus_comm.
      rewrite (lim_exec_val_exec m).
      iAssert (|={∅}▷=>^(S n)
                 ⌜ARcoupl (dret (e1, σ1) ≫=
                             (λ a', exec_val (S n) a')) (exec m (e1', σ1') ≫= lim_exec_val) φ (ε1 + (ε + ε2))%NNR⌝)%I
      with "[H]" as "Haux".
      + iApply ARcoupl_dbind'.
        * iPureIntro; apply cond_nonneg.
        * iPureIntro; apply cond_nonneg.
        * by apply ARcoupl_pos_R in Hcpl.
        * iIntros ([] [] (?& [= -> ->]%dret_pos &?)).
          by iMod ("H"  with "[//] [//]").
      + iMod "Haux".
        do 2 iModIntro.
        iMod "Haux".
        iModIntro.
        iApply (step_fupdN_wand with "Haux").
        iPureIntro.
        apply ARcoupl_mon_grading; simpl.
        rewrite (Rplus_comm ε) -Rplus_assoc.
        by apply Rplus_le_compat.
    - iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜ARcoupl (exec_val (S n) (e1, σ1))
                                  (lim_exec_val (e1', σ1')) φ (ε'' + ε)⌝)%I
                  with "H") as "H".
      { iIntros (i α Hα%elem_of_list_lookup_2) "(% & % & %Hcpl & H)".
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ e2 σ2 σ2', R2 (e2, σ2) σ2' → ARcoupl (exec_val n (e2, σ2))
                                                             (lim_exec_val (e1', σ2')) φ ε⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα.
          apply elem_of_elements, elem_of_dom in Hα as [].
          eapply ARcoupl_erasure_r; eauto.
          + apply cond_nonneg.
          + apply cond_nonneg.
        - iIntros (????). by iMod ("H" with "[//]"). }
      iInduction (language.get_active σ1') as [| α'] "IH"; [done|].
      rewrite big_orL_cons nnreal_plus_comm.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
    - iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜ARcoupl (exec_val (S n) (e1, σ1))
                                  (lim_exec_val (e1', σ1')) φ (ε + ε'')⌝)%I
                  with "H") as "H".
      { iIntros (i α' Hα'%elem_of_list_lookup_2) "(% & %ε1 & %ε2 & %Hleq & %Hcpl & H)".
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 e2' σ2', R2 σ2 (e2', σ2') → ARcoupl (exec_val (S n) (e1, σ2))
                                                               (lim_exec_val (e2', σ2')) φ (ε + ε2)⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα'.
          apply elem_of_elements, elem_of_dom in Hα' as [].
          apply (ARcoupl_mon_grading _ _ _ (ε1 + (ε + ε2))); [lra | ].
          eapply ARcoupl_erasure_l; eauto.
          + apply cond_nonneg.
          + apply Rplus_le_le_0_compat; apply cond_nonneg.
        - iIntros (????). by iMod ("H" with "[//] [//]"). }
      iInduction (language.get_active σ1) as [| α'] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
    - rewrite exec_val_Sn_not_val; [|done].
      iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜ARcoupl (prim_step e1 σ1 ≫= exec_val n)
                                  (lim_exec_val (e1', σ1')) φ (ε + ε'')⌝)%I
                  with "H") as "H".
      { iIntros (i [α1 α2] [Hα1 Hα2]%elem_of_list_lookup_2%elem_of_list_prod_1) "(% & %ε1 & %ε2 & %Hleq & %Hcpl & H)".
        rewrite -exec_val_Sn_not_val; [|done].
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 σ2', R2 σ2 σ2' → ARcoupl (exec_val (S n) (e1, σ2))
                                                    (lim_exec_val (e1', σ2')) φ (ε + ε2)⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα1, Hα2.
          apply elem_of_elements, elem_of_dom in Hα1 as [], Hα2 as [].
          apply (ARcoupl_mon_grading _ _ _ (ε1 + (ε + ε2))); [lra | ].
          eapply ARcoupl_erasure; eauto.
          + apply cond_nonneg.
          + apply Rplus_le_le_0_compat; apply cond_nonneg.
        - iIntros (???). by iMod ("H" with "[//] [//]"). }
      iInduction (list_prod (language.get_active σ1) (language.get_active σ1'))
        as [| [α α']] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
  Qed.

End adequacy.

(*
Class clutchGpreS Σ := ClutchGpreS {
  clutchGpreS_iris  :> invGpreS Σ;
  clutchGpreS_heap  :> ghost_mapG Σ loc val;
  clutchGpreS_tapes :> ghost_mapG Σ loc tape;
  clutchGpreS_err   :> ecGpreS Σ;
}.

Definition clutchΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    GFunctor (authR (realUR))].
Global Instance subG_clutchGPreS {Σ} : subG clutchΣ Σ → clutchGpreS Σ.
Proof. solve_inG. Qed.

Theorem wp_union_bound Σ `{clutchGpreS Σ} (e : expr) (σ : state) n (ε : nonnegreal) φ :
  (∀ `{clutchGS Σ}, ⊢ € ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ub_lift (exec_val n (e, σ)) φ ε.
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
  (forall n, ub_lift (exec_val n (e, σ)) φ ε ) ->
  ub_lift (lim_exec_val (e, σ)) φ ε .
Proof.
  intros Hn P HP.
  apply lim_exec_continous_prob; auto.
  intro n.
  apply Hn; auto.
Qed.

Theorem wp_union_bound_lim Σ `{clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{clutchGS Σ}, ⊢ € ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ub_lift (lim_exec_val (e, σ)) φ ε.
Proof.
  intros.
  apply ub_lift_closed_lim.
  intro n.
  apply (wp_union_bound Σ); auto.
Qed.
*)

