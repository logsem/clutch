From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
(*  From clutch.prob_lang Require Import erasure notation. *)
From clutch.base_logic Require Import error_credits.
From clutch.micrometer Require Import app_weakestpre primitive_laws.
From clutch.meas_lang Require Import erasure.
From mathcomp Require Import classical_sets.
From mathcomp.analysis Require Import ereal.

(*  From clutch.prob Require Import distribution couplings_app. *)
Import uPred.

Section adequacy.
  Context `{!micrometerGS Σ}.
  Local Open Scope classical_set_scope.

  Lemma wp_adequacy_spec_coupl n m (e1 : meas_lang.language.exprT meas_lang)
    (σ1 : meas_lang.language.stateT meas_lang) (e1' : meas_lang.language.exprT meas_lang)
    (σ1' : meas_lang.language.stateT meas_lang)  Z φ ε :
    meas_spec_coupl ∅ σ1 e1' σ1' ε Z -∗
    (∀ σ2 e2' σ2' ε', Z σ2 e2' σ2' ε' ={∅}=∗ |={∅}▷=>^n
        ⌜ARcoupl_meas (@exec (language.meas_lang_markov meas_lang) m (e1, σ2)) (@lim_exec (language.meas_lang_markov meas_lang) (e2', σ2')) φ (0)%R (EFin $ nonneg ε')⌝ ) -∗
    |={∅}=> |={∅}▷=>^n ⌜ARcoupl_meas (@exec (language.meas_lang_markov meas_lang) m (e1, σ1)) (@lim_exec (language.meas_lang_markov meas_lang) (e1', σ1')) φ (0)%R (EFin $ nonneg ε) ⌝.
  Proof.
    iRevert (σ1 e1' σ1' ε).
    simpl in *.
    iApply meas_spec_coupl_ind.
    iIntros "!>" (σ1 e1' σ1' ε)
      "[% | [H | (%T & %k & %μ1 & %μ1' & %ε' & %X2 & %r & % & % & % & %Hμ1 & %Hμ1' & H)]] HZ".
    - iApply step_fupdN_intro; [done|].
      do 2 iModIntro. iPureIntro.
      apply ARcoupl_meas_1.
      by repeat destroy_mathcomp.
    - by iMod ("HZ" with "[$]").
    - iApply (step_fupdN_mono _ _ _
                ⌜forall (σ2 : (stateT meas_lang))
                         (e2' : (meas_lang.language.exprT meas_lang))
                         (σ2' : (stateT meas_lang)),
                         T σ2 (e2', σ2') →
                         ARcoupl_meas
                           (@exec (meas_lang_markov meas_lang) m (e1, σ2))
                           (@lim_exec (meas_lang_markov meas_lang) (e2', σ2'))
                           φ (0)%R (EFin (nonneg (X2 (e2', σ2')))) ⌝).
      { iPureIntro. intros. eapply ARcoupl_erasure_erasable_exp_rhs.
        3:  { by apply H1. }
        { by apply cond_nonneg. }
        { by apply H. }
        { intro ρ. split; [by apply cond_nonneg | by apply H0 ]. }
        { done. }
        { done. }
        eauto.
      }
      iIntros (σ2 e2' σ2' HT).
      iMod ("H" with "[//]") as "[H _]".
      iApply "H".
      done.
  Qed.


  Lemma wp_adequacy_val_fupd (e e' : measure.Measurable.sort (meas_lang.language.expr meas_lang))
    (σ σ' : measure.Measurable.sort (meas_lang.language.state meas_lang)) n φ v ε :
    fill.to_val e = Some v ->
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε ∗
    WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤, ∅}=> ⌜ARcoupl_meas (@exec (language.meas_lang_markov meas_lang) n (e, σ)) (@lim_exec (language.meas_lang_markov meas_lang) (e', σ')) φ 0 (EFin $ nonneg $ ε)⌝.
  Proof.
    iIntros (He) "(Hσ & Hs & Hε & Hwp)".
    rewrite wp_unfold /wp_pre /= He.
    iSpecialize ("Hwp" $! σ e' σ' ε with "[Hσ Hs Hε]" ).
    { iSplitR "Hs Hε"; [iApply "Hσ"|]. iSplitL "Hs"; [iApply "Hs" | iApply "Hε"]. }
    iMod "Hwp".
    iApply (wp_adequacy_spec_coupl 0 with "Hwp").
    iIntros (σ1 e1' σ1' ε') "> (? & Hs & Hε & (% & Hv & %)) /=".
    iDestruct (spec_auth_prog_agree with "Hs Hv") as %->.
    erewrite exec_is_final; [|done].
    iApply fupd_mask_intro; [set_solver|]; iIntros "_".
    iPureIntro.
    erewrite ARcoupl_meas_proper.
    2: { reflexivity. }
    2: { rewrite lim_exec_final; [|done]. reflexivity. }
    eapply ARcoupl_meas_dret; [| | done].
    { by repeat destroy_mathcomp. }
    { repeat destroy_mathcomp. by apply cond_nonneg.  }
  Qed.

  Lemma wp_adequacy_step_fupdN ε (e e' : meas_lang.language.exprT meas_lang) (σ σ' :  meas_lang.language.stateT meas_lang) n φ :
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε ∗
    WP (e: meas_lang.language.exprT meas_lang) {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜ARcoupl_meas (@exec (language.meas_lang_markov meas_lang) n (e, σ)) (@lim_exec (language.meas_lang_markov meas_lang) (e', σ')) φ 0 (EFin $ nonneg $ ε)⌝.
  Proof.
    iIntros "(Hσ & HspecI_auth & Hε & Hwp)".
    iInduction n as [|n] "IH" forall (e σ e' σ' ε).
    { destruct (fill.to_val e) eqn:He.
      - iMod (wp_adequacy_val_fupd with "[Hσ HspecI_auth Hε Hwp]"); first by apply He.
        { iSplitL "Hσ"; first by iApply "Hσ".
          iSplitL "HspecI_auth"; first by iApply "HspecI_auth".
          iSplitL "Hε"; first by iApply "Hε".
          by iApply "Hwp". }
        by iApply step_fupdN_intro.
      - iApply fupd_mask_intro; [done|]; iIntros "_ /=".
        iPureIntro. rewrite He.
        admit.
        (* by apply ARcoupl_meas_dzero. *) }
    destruct (fill.to_val e) eqn:He.
    { iMod (wp_adequacy_val_fupd with "[Hσ HspecI_auth Hε Hwp]"); first by apply He.
      { iSplitL "Hσ"; first by iApply "Hσ".
        iSplitL "HspecI_auth"; first by iApply "HspecI_auth".
        iSplitL "Hε"; first by iApply "Hε".
        by iApply "Hwp". }
      iApply step_fupdN_intro; [done|].
      do 3 iModIntro. done. }
    iEval (rewrite wp_unfold /wp_pre /= He) in "Hwp".
    iMod ("Hwp" with "[Hσ HspecI_auth Hε]") as "Hwp".
    { iDestruct "Hσ" as "[A [B C]]".
      iSplitL "A B C".
      { iSplitL "A"; [by iApply "A" |].
        iSplitL "B"; [by iApply "B" |].
        by iApply "C". }
      iSplitL "HspecI_auth"; [by iApply "HspecI_auth"|].
      by iApply "Hε". }
    iApply (wp_adequacy_spec_coupl with "Hwp").
    iIntros (σ2 e2' σ2' ε') "(%R & %m & %μ1' & %ε1 & %X2 & %r & ? & % & % & % & % & Hcnt)".
    (*
    Opaque step. simpl.
    iEval (rewrite He).
    rewrite -step_fupdN_Sn.
    iApply (step_fupdN_mono _ _ _ ⌜_⌝).
    { iPureIntro. intros.
      (*
      eapply ARcoupl_erasure_erasable_exp_lhs.
      3: { simpl in *. apply H1.
      3: { done. }
      1: { done. }
      all: clear H3.
      3: { by apply H2. }
      3: { simpl. admit. }
*)

      all: admit.
      (* eapply ARcoupl_erasure_erasable_exp_lhs; [..|done]; eauto. *) } *)
  Admitted.
(*
    iIntros (e2 σ3 e3' σ3' HR).
    iMod ("Hcnt" with "[//]") as "Hcnt".
    clear.
    iIntros "!> !> !>".
    iApply (wp_adequacy_spec_coupl with "Hcnt").
    iIntros (σ4 e4' σ4' ε) ">(Hσ & Hs & Hε & Hcnt)".
    iApply ("IH" with "Hσ Hs Hε Hcnt").
  Qed.
  *)
End adequacy.

Lemma wp_adequacy_exec_n Σ `{!micrometerGpreS Σ} e e' σ σ' n φ (ε : R) :
  (0 <= ε)%R →
  (∀ `{micrometerGS Σ}, ⊢ ⤇ e' -∗ ↯ ε -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
  ARcoupl_meas (@exec (language.meas_lang_markov meas_lang) n (e, σ)) (@lim_exec (language.meas_lang_markov meas_lang) (e', σ')) φ 0 (EFin  ε).
Proof.
  intros Heps Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc (heap σ)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc (tapes σ)) as "[%γT [Ht _]]".
  iMod (ghost_map_alloc (utapes σ)) as "[%γU [Hu _]]".
  iMod spec_ra_init as (HspecGS) "(Hs & Hj & ?)".
  destruct (decide (ε < 1)%R) as [? | H%Rnot_lt_le].
  - set ε' := mknonnegreal _ Heps.
    iMod (ec_alloc ε') as (?) "[HE He]"; [done|].
    set (HmicrometerGS := HeapG Σ _ _ _ _ γH γT γU HspecGS _).
    iApply (wp_adequacy_step_fupdN ε').
    iFrame "Hh Ht Hs Hu HE".
    by iApply (Hwp with "[Hj] [He]").
  - iApply fupd_mask_intro; [done|]; iIntros "_".
    iApply step_fupdN_intro; [done|]; iModIntro.
    iPureIntro.
    apply ARcoupl_meas_1.
    by repeat destroy_mathcomp.
Qed.

Theorem wp_adequacy Σ `{micrometerGpreS Σ} e e' σ σ' (ε : R) φ :
  (0 <= ε)%R →
  (∀ `{micrometerGS Σ}, ⊢  ⤇ e' -∗ ↯ ε -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  ARcoupl_meas (@lim_exec (language.meas_lang_markov meas_lang) (e, σ)) (@lim_exec (language.meas_lang_markov meas_lang) (e', σ')) φ 0 (EFin ε).
Proof.
  intros ? Hwp.
  apply lim_exec_ARcoupl.
  { by repeat destroy_mathcomp. }
  { by repeat destroy_mathcomp. }
  intros n.
  by eapply wp_adequacy_exec_n.
Qed.

Corollary wp_adequacy_error_lim Σ `{micrometerGpreS Σ} e e' σ σ' (ε : R) δ φ :
  (0 <= ε)%R →
  (∀ `{micrometerGS Σ} (ε' : R),
      (ε < ε')%R → ⊢ ⤇ e' -∗ ↯ ε' -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  ARcoupl_meas (@lim_exec (language.meas_lang_markov meas_lang) (e, σ)) (@lim_exec (language.meas_lang_markov meas_lang) (e', σ')) φ ε δ.
Proof.
  intros ? Hwp.
Admitted.
(*
  apply ARcoupl_limit.
  intros ε' Hineq.
  assert (0 <= ε') as Hε'.
  { trans ε; [done|lra]. }
  pose (mknonnegreal ε' Hε') as NNRε'.
  assert (ε' = (NNRbar_to_real (NNRbar.Finite NNRε'))) as Heq; [done|].
  rewrite Heq.
  eapply wp_adequacy; [done|done|].
  iIntros (?).
  by iApply Hwp.
Qed.
*)

Corollary wp_adequacy_mass Σ `{!micrometerGpreS Σ} e e' σ σ' φ (ε : R) :
  (0 <= ε)%R →
  (∀ `{micrometerGS Σ}, ⊢  ⤇ e' -∗ ↯ ε -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  le_ereal
    (gEval setT (@lim_exec (language.meas_lang_markov meas_lang) (e, σ)))
    (gEval setT (@lim_exec (language.meas_lang_markov meas_lang) (e', σ'))).
Proof.
  intros ? Hwp.
Admitted.
(*
  eapply ARcoupl_mass_leq.
  by eapply wp_adequacy.
Qed.
*)
