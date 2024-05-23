From iris.proofmode Require Import base proofmode.
From iris.bi Require Export fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.bi Require Import weakestpre.
From clutch.prob_lang Require Import erasure.
From clutch.common Require Export language.
From clutch.ctx_logic Require Import weakestpre primitive_laws spec_ra.
From clutch.prob Require Import distribution.
Import uPred.

Section adequacy.
  Context `{!clutchGS Σ}.

  Lemma refRcoupl_dbind' `{Countable A, Countable A', Countable B, Countable B'}
    (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (T : A' → B' → Prop) n :
    ⌜refRcoupl μ1 μ2 R⌝ -∗
    (∀ a b, ⌜R a b⌝ ={∅}▷=∗^(S n) ⌜refRcoupl (f a) (g b) T⌝) -∗
    |={∅}▷=>^(S n) ⌜refRcoupl (dbind f μ1) (dbind g μ2) T⌝ : iProp Σ.
  Proof.
    iIntros (HR) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a b → refRcoupl (f a) (g b) T)⌝)).
    { iIntros (?). iPureIntro. by eapply refRcoupl_dbind. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.

  Lemma exec_coupl_erasure (e1 : expr) (σ1 : state) (e1' : expr) (σ1' : state) (n : nat) φ :
    to_val e1 = None →
    exec_coupl e1 σ1 e1' σ1' (λ '(e2, σ2) '(e2', σ2'),
        |={∅}▷=>^(S n) ⌜refRcoupl (exec n (e2, σ2)) (lim_exec (e2', σ2')) φ⌝)
    ⊢ |={∅}▷=>^(S n) ⌜refRcoupl (exec (S n) (e1, σ1)) (lim_exec (e1', σ1')) φ⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e1 = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /exec_coupl /exec_coupl'.
    set (Φ := (λ '((e1, σ1), (e1', σ1')),
                (⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                 ⌜refRcoupl (exec (S n) (e1, σ1))
                            (lim_exec (e1', σ1')) φ⌝)%I) :
           prodO cfgO cfgO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&(?&?)) ((?&?)&(?&?)) [[[=] [=]] [[=] [=]]]. by simplify_eq. }
    set (F := (exec_coupl_pre (λ '(e2, σ2) '(e2', σ2'),
                   |={∅}▷=>^(S n) ⌜refRcoupl (exec n (e2, σ2))
                     (lim_exec (e2', σ2')) φ⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %". by iMod ("H" $! ((_, _), (_, _)) with "Hfix [//]"). }
    clear.
    iIntros "!#" ([[e1 σ1] [e1' σ1']]). rewrite /exec_coupl_pre.
    iIntros "[(%R & % & %Hcpl & H) | [(%R & % & %Hcpl & H) | [(%R & %m & %Hcpl & H) | [H | [H | [H | H]]]]]] %Hv".
    - rewrite exec_Sn_not_final; [|eauto].
      rewrite lim_exec_step.
      destruct (to_val e1') eqn:Hv'.
      + destruct (decide (prim_step e1 σ1 = dzero)) as [Hs|].
        * rewrite /= Hs dbind_dzero.
          do 3 iModIntro. iApply step_fupdN_intro; [done|].
          iModIntro. iPureIntro.
          apply refRcoupl_dzero.
        * assert (prim_step e1' σ1' = dzero) as Hz.
          { apply (is_final_dzero (e1', σ1')). eauto. }
          simpl in *. rewrite Hz in Hcpl.
          by apply Rcoupl_dzero_r_inv in Hcpl.
      + rewrite step_or_final_no_final; [|eauto].
        iApply (refRcoupl_dbind' _ _ _ _ R).
        { iPureIntro. by apply Rcoupl_refRcoupl. }
        iIntros ([] [] HR). by iMod ("H" with "[//]").
    - rewrite exec_Sn_not_final; [|eauto].
      rewrite -(dret_id_left (lim_exec)).
      iApply refRcoupl_dbind'.
      { iPureIntro. apply Rcoupl_pos_R in Hcpl. by apply Rcoupl_refRcoupl. }
      iIntros ([] [] (?&?& [= -> ->]%dret_pos)).
      by iMod ("H"  with "[//]").
    - rewrite -(dret_id_left (exec _)).
      rewrite (lim_exec_pexec m).
      iApply refRcoupl_dbind'.
      { iPureIntro. apply Rcoupl_pos_R in Hcpl. by apply Rcoupl_refRcoupl. }
      iIntros ([] [] (?& [= -> ->]%dret_pos &?)).
      by iMod ("H"  with "[//] [//]").
    - iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜refRcoupl (exec (S n) (e1, σ1))
                                  (lim_exec (e1', σ1')) φ⌝)%I
                  with "H") as "H".
      { iIntros (i α Hα%elem_of_list_lookup_2) "(% & % & %Hcpl & H)".
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ e2 σ2 σ2', R2 (e2, σ2) σ2' → refRcoupl (exec n (e2, σ2))
                                                             (lim_exec (e1', σ2')) φ⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα.
          apply elem_of_elements, elem_of_dom in Hα as [].
          eapply refRcoupl_erasure_r; eauto.
        - iIntros (????). by iMod ("H" with "[//]"). }
      iInduction (language.get_active σ1') as [| α'] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
    - iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜refRcoupl (exec (S n) (e1, σ1))
                                  (lim_exec (e1', σ1')) φ⌝)%I
                  with "H") as "H".
      { iIntros (i α' Hα'%elem_of_list_lookup_2) "(% & %Hcpl & H)".
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 e2' σ2', R2 σ2 (e2', σ2') → refRcoupl (exec (S n) (e1, σ2))
                                                               (lim_exec (e2', σ2')) φ⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα'.
          apply elem_of_elements, elem_of_dom in Hα' as [].
          eapply refRcoupl_erasure_l; eauto.
        - iIntros (????). by iMod ("H" with "[//] [//]"). }
      iInduction (language.get_active σ1) as [| α'] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
    - rewrite exec_Sn_not_final; [|eauto].
      iDestruct (big_orL_mono _ (λ _ _,
                     |={∅}▷=>^(S n)
                       ⌜refRcoupl (prim_step e1 σ1 ≫= exec n)
                                  (lim_exec (e1', σ1')) φ⌝)%I
                  with "H") as "H".
      { iIntros (i [α1 α2] [Hα1 Hα2]%elem_of_list_lookup_2%elem_of_list_prod_1) "(% & %Hcpl & H)".
        rewrite -(exec_Sn_not_final (e1, σ1)); [|auto].
        iApply (step_fupdN_mono _ _ _
                  (⌜∀ σ2 σ2', R2 σ2 σ2' → refRcoupl (exec (S n) (e1, σ2))
                                                    (lim_exec (e1', σ2')) φ⌝)%I).
        - iIntros (?). iPureIntro.
          rewrite /= /get_active in Hα1, Hα2.
          apply elem_of_elements, elem_of_dom in Hα1 as [], Hα2 as [].
          eapply refRcoupl_erasure; eauto.
        - iIntros (???). by iMod ("H" with "[//] [//]"). }
      iInduction (list_prod (language.get_active σ1) (language.get_active σ1'))
        as [| [α α']] "IH"; [done|].
      rewrite big_orL_cons.
      iDestruct "H" as "[H | Ht]"; [done|].
      by iApply "IH".
    - iDestruct "H" as "(%&%&%&%&%&%&%&H)".
      iApply (step_fupdN_mono _ _ _
                (⌜∀ σ2 σ2', R2 σ2 σ2' → refRcoupl (exec (S n) (e1, σ2))
                                          (lim_exec (e1', σ2')) φ⌝)%I).
      + iPureIntro.
        intros ?.
        by eapply refRcoupl_erasure_erasable.
      + iIntros (???). by iMod ("H" with "[//] [//]").
  Qed.

  Theorem wp_refRcoupl_step_fupdN (e e' : expr) (σ σ' : state) n φ :
    state_interp σ ∗ spec_interp (e', σ') ∗ spec_ctx ∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜refRcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ e' σ'); iIntros "([Hh Ht] & HspecI_auth & #Hctx & Hwp)".
    - rewrite /exec /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite wp_value_fupd.
        iMod "Hwp" as (v') "[Hspec_frag %]".
        iInv specN as (ρ e0 σ0 n) ">(HspecI_frag & %Hexec & Hspec_auth & Hstate)" "_".
        iDestruct (spec_interp_auth_frag_agree with "HspecI_auth HspecI_frag") as %<-.
        iDestruct (spec_prog_auth_frag_agree with "Hspec_auth Hspec_frag") as %->.
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        erewrite lim_exec_det_final; [| |done]; [|done].
        iPureIntro.
        rewrite /dmap.
        by apply refRcoupl_dret.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iPureIntro.
        apply refRcoupl_dzero.
    - rewrite exec_Sn /step_or_final /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite wp_value_fupd.
        iMod "Hwp" as (v') "[Hspec_frag %]".
        iInv specN as (ξ ρ e0 σ0) ">(HspecI_frag & %Hexec & Hspec_auth & Hstate)" "_".
        iDestruct (spec_interp_auth_frag_agree with "HspecI_auth HspecI_frag") as %<-.
        iDestruct (spec_prog_auth_frag_agree with "Hspec_auth Hspec_frag") as %->.
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iApply step_fupdN_intro; [done|]. do 4 iModIntro.
        iPureIntro.
        rewrite exec_unfold dret_id_left /=.
        erewrite lim_exec_det_final; [| |done]; [|done].
        by apply refRcoupl_dret.
      + rewrite wp_unfold /wp_pre /= Heq.
        iMod ("Hwp" with "[$]") as "Hcpl".
        iModIntro.
        iPoseProof
          (exec_coupl_mono _ (λ '(e2, σ2) '(e2', σ2'), |={∅}▷=>^(S n)
             ⌜refRcoupl (exec n (e2, σ2)) (lim_exec (e2', σ2')) φ⌝)%I
            with "[] Hcpl") as "H".
        { iIntros ([] []) "H !> !>".
          iMod "H" as "(Hstate & HspecI_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        rewrite -(exec_Sn_not_final (_, _)); [|eauto].
        by iApply (exec_coupl_erasure with "H").
  Qed.

End adequacy.

Theorem wp_refRcoupl Σ `{clutchGpreS Σ} (e e' : expr) (σ σ' : state) n φ :
  (∀ `{clutchGS Σ}, ⊢ spec_ctx -∗ ⤇ e' -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
  refRcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ.
Proof.
  intros Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (ghost_map_alloc σ'.(heap)) as "[%γHs [Hh_spec _]]".
  iMod (ghost_map_alloc σ'.(tapes)) as "[%γTs [Ht_spec _]]".
  iMod (own_alloc ((● (Excl' (e', σ'))) ⋅ (◯ (Excl' (e', σ'))))) as "(%γsi & Hsi_auth & Hsi_frag)".
  { by apply auth_both_valid_discrete. }
  iMod (own_alloc ((● (Excl' e')) ⋅ (◯ (Excl' e')))) as "(%γp & Hprog_auth & Hprog_frag)".
  { by apply auth_both_valid_discrete. }
  set (HspecGS := CfgSG Σ _ γsi _ γp _ _ γHs γTs).
  set (HclutchGS := HeapG Σ _ _ _ γH γT HspecGS).
  iMod (inv_alloc specN ⊤ spec_inv with "[Hsi_frag Hprog_auth Hh_spec Ht_spec]") as "#Hctx".
  { iModIntro. iExists _, _, _, O. iFrame. rewrite pexec_O dret_1_1 //. }
  iApply wp_refRcoupl_step_fupdN.
  iFrame. iFrame "Hctx".
  by iApply (Hwp with "[Hctx] [Hprog_frag]").
Qed.

Corollary wp_refRcoupl_mass Σ `{clutchGpreS Σ} (e e' : expr) (σ σ' : state) φ :
  (∀ `{clutchGS Σ}, ⊢ spec_ctx -∗ ⤇ e' -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
  SeriesC (lim_exec (e, σ)) <= SeriesC (lim_exec (e', σ')).
Proof.
  intros Hwp.
  apply: lim_exec_leq_mass => n.
  eapply refRcoupl_mass_eq.
  by eapply wp_refRcoupl.
Qed.
