From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_eff_lang.probblaze Require Import erasure notation primitive_laws.
From clutch.common Require Import language.
From clutch.base_logic Require Import error_credits.
From clutch.approxis Require Import app_weakestpre.
From clutch.prob Require Import distribution couplings_app.
From clutch.prob_eff_lang.probblaze Require Import syntax semantics.
Import uPred.

Section adequacy.
  Context `{!probblazeGS Σ}.

  Lemma wp_adequacy_spec_coupl n m e1 σ1 e1' σ1' Z φ ε :
    spec_coupl ∅ σ1 e1' σ1' ε Z -∗
    (∀ σ2 e2' σ2' ε', Z σ2 e2' σ2' ε' ={∅}=∗ |={∅}▷=>^n ⌜ARcoupl (exec m (e1, σ2)) (lim_exec (e2', σ2')) φ ε'⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜ARcoupl (exec m (e1, σ1)) (lim_exec (e1', σ1')) φ ε⌝.
  Proof.
    iRevert (σ1 e1' σ1' ε).
    iApply spec_coupl_ind.
    iIntros "!>" (σ1 e1' σ1' ε)
      "[% | [H | (%T & %k & %μ1 & %μ1' & %ε' & %X2 & %r & % & % & % & %Hμ1 & %Hμ1' & H)]] HZ".
    - iApply step_fupdN_intro; [done|].
      do 2 iModIntro. iPureIntro. by apply ARcoupl_1.
    - by iMod ("HZ" with "[$]").
    - iApply (step_fupdN_mono _ _ _ ⌜_⌝).
      { iPureIntro. intros. eapply ARcoupl_erasure_erasable_exp_rhs; [..|done]; eauto. }
      iIntros (σ2 e2' σ2' HT).
      iMod ("H" with "[//]") as "[H _]".
      by iApply "H".
  Qed.

  Lemma val_to_final e1 σ1 :
    semantics.to_val e1 = None →
    to_final (e1, σ1) = None.
  Proof.
    intros Hval.
    unfold to_final. simpl. done.
  Qed.  

  Lemma wp_adequacy_prog_coupl n m e1 σ1 e1' σ1' Z φ ε :
    to_val e1 = None ->
    prog_coupl e1 σ1 e1' σ1' ε Z -∗
    (∀ e2 σ2 e2' σ2' ε', Z e2 σ2 e2' σ2' ε' ={∅}=∗ |={∅}▷=>^n ⌜ARcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε'⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜ARcoupl (exec (S m) (e1, σ1)) (lim_exec (e1', σ1')) φ ε⌝.
  Proof.
    intros Hval.
    rewrite exec_Sn.
    rewrite /step_or_final val_to_final //. 
    iIntros "(%R & %k & %μ1' & %ε1 & %X2 & %r & % & % & % & % & % & Hcnt) Hcoupl ".
    iApply (step_fupdN_mono _ _ _ ⌜_⌝).
    { iPureIntro. intros. eapply ARcoupl_erasure_erasable_exp_lhs; [..|done]; eauto. }
    iIntros (e2 σ2 e2' σ2' ε2).
    iMod ("Hcnt" with "[//]") as "Hcnt".
    by iApply "Hcoupl".
  Qed.

  Lemma wp_adequacy_val_fupd (e e' : expr) (σ σ' : state) n φ v ε:
    to_val e = Some v →
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε ∗
    WP e {{ v, ∃ v' : val, ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤, ∅}=> ⌜ARcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε⌝.
  Proof.
    iIntros (He) "(Hσ & Hs & Hε & Hwp)".
    rewrite wp_unfold /wp_pre /= He.
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (wp_adequacy_spec_coupl 0 with "Hwp").
    iIntros (σ1 e1' σ1' ε') "> (? & Hs & Hε & (% & Hv & %)) /=".
    iDestruct (spec_auth_prog_agree with "Hs Hv") as %->.
    erewrite exec_is_final; [|done].
    erewrite lim_exec_final; [|done].
    iApply fupd_mask_intro; [set_solver|]; iIntros "_".
    iPureIntro. by eapply ARcoupl_dret.
  Qed.

  Lemma wp_adequacy_step_fupdN ε (e e' : expr) (σ σ' : state) n φ :
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε ∗
    WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜ARcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε⌝.
  Proof.
    iIntros "(Hσ & HspecI_auth & Hε & Hwp)".
    iInduction n as [|n] "IH" forall (e σ e' σ' ε).
    { destruct (to_val e) eqn:He.
      - iMod (wp_adequacy_val_fupd with "[$]") as %?; [done|].
        by iApply step_fupdN_intro.
      - iApply fupd_mask_intro; [done|]; iIntros "_ /=".
        iPureIntro. rewrite He. by apply ARcoupl_dzero. }
    destruct (to_val e) eqn:He.
    { iMod (wp_adequacy_val_fupd with "[$]") as %?; [done|].
      iApply step_fupdN_intro; [done|].
      do 3 iModIntro. done. }
    iEval (rewrite wp_unfold /wp_pre /= He) in "Hwp".
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (wp_adequacy_spec_coupl with "Hwp").
    iIntros (σ2 e2' σ2' ε') "Hprog".
    iApply (wp_adequacy_prog_coupl with "Hprog"); [done|].
    iIntros (e3 σ3 e3' σ3' ε3) "Hspec".
    iIntros "!> !> !>".
    iApply (wp_adequacy_spec_coupl with "Hspec").
    iIntros (σ4 e4' σ4' ε4) ">(Hσ & Hs & Hε & Hcnt)".
    iApply ("IH" with "Hσ Hs Hε Hcnt").
  Qed.

End adequacy.

Lemma wp_adequacy_exec_n Σ `{!probblazeGpreS Σ} (e e' : expr) (σ σ' : state) n φ (ε : R) :
  0 <= ε →
  (∀ `{probblazeGS Σ}, ⊢ ⤇ e' -∗ ↯ ε -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
  ARcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros Heps Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (ghost_map_alloc (to_labels σ.(next_label))) as (γlabels) "[Hlabels _]".
  iMod spec_ra_init as (HspecGS) "(Hs & Hj & ? & ?)".
  destruct (decide (ε < 1)) as [? | H%Rnot_lt_le].
  - set ε' := mknonnegreal _ Heps.
    iMod (ec_alloc ε') as (?) "[HE He]"; [done|].
    set (HprobblazeGS := HeapG Σ _ _ _ _ γH γT γlabels HspecGS _).
    iApply (wp_adequacy_step_fupdN ε').
    iFrame "Hh Ht Hs HE Hlabels".
    by iApply (Hwp with "[Hj] [He]").
  - iApply fupd_mask_intro; [done|]; iIntros "_".
    iApply step_fupdN_intro; [done|]; iModIntro.
    iPureIntro. by apply ARcoupl_1.
Qed.

Theorem wp_adequacy Σ `{probblazeGpreS Σ} (e e' : expr) (σ σ' : state) (ε : R) φ :
  0 <= ε →
  (∀ `{probblazeGS Σ}, ⊢  ⤇ e' -∗ ↯ ε -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  ARcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros ? Hwp.
  apply lim_exec_ARcoupl; [done|].
  intros n.
  by eapply wp_adequacy_exec_n.
Qed.

Corollary wp_adequacy_error_lim Σ `{probblazeGpreS Σ} (e e' : expr) (σ σ' : state) (ε : R) φ :
  0 <= ε →
  (∀ `{probblazeGS Σ} (ε' : R),
      ε < ε' → ⊢ ⤇ e' -∗ ↯ ε' -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  ARcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros ? Hwp.
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

Corollary wp_adequacy_mass Σ `{!probblazeGpreS Σ} (e e' : expr) (σ σ' : state) φ (ε : R) :
  0 <= ε →
  (∀ `{probblazeGS Σ}, ⊢  ⤇ e' -∗ ↯ ε -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  SeriesC (lim_exec (e, σ)) <= SeriesC (lim_exec (e', σ')) + ε.
Proof.
  intros ? Hwp.
  eapply ARcoupl_mass_leq.
  by eapply wp_adequacy.
Qed.
