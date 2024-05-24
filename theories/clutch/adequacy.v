From iris.proofmode Require Import base proofmode.
From iris.bi Require Export fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.bi Require Import weakestpre.
From clutch.prob_lang Require Import erasure.
From clutch.common Require Export language.
From clutch.clutch Require Import weakestpre primitive_laws.
From clutch.prob Require Import distribution.
Import uPred.

Section adequacy.
  Context `{!clutchGS Σ}.

  Lemma refRcoupl_step_fupdN_dbind `{Countable A, Countable A', Countable B, Countable B'}
    n (f : A → distr A') (g : B → distr B') (μ1 : distr A) (μ2 : distr B) (R : A → B → Prop) (T : A' → B' → Prop) :
    ⌜μ1 ≾ μ2 : R⌝ -∗
    (∀ a b, ⌜R a b⌝ ={∅}=∗ |={∅}▷=>^n ⌜f a ≾ g b : T⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜(μ1 ≫= f) ≾ (μ2 ≫= g) : T⌝ : iProp Σ.
  Proof.
    iIntros (HR) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a b → f a ≾ g b : T)⌝)).
    { iIntros (?). iPureIntro. by eapply refRcoupl_dbind. }
    iIntros (???) "/=".
    by iMod ("H" with "[//]") as "H".
  Qed.

  Lemma wp_adequacy_spec_coupl n m e1 σ1 e1' σ1' Z φ :
    spec_coupl ∅ σ1 e1' σ1' Z -∗
    (∀ σ2 e2' σ2', Z σ2 e2' σ2' ={∅}=∗ |={∅}▷=>^n ⌜exec m (e1, σ2) ≾ lim_exec (e2', σ2') : φ⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜exec m (e1, σ1) ≾ lim_exec (e1', σ1') : φ⌝.
  Proof.
    iRevert (σ1 e1' σ1').
    iApply spec_coupl_ind.
    iIntros "!>" (σ1 e1' σ1')
      "[H |(%R & %p & %μ1 & %μ1' & % & %Hμ1 & %Hμ1' & H)] HZ".
    - by iMod ("HZ" with "[$]").
    - iEval (rewrite -Hμ1 -(erasable_pexec_lim_exec μ1' p) //).
      iApply refRcoupl_step_fupdN_dbind; [iPureIntro|].
      { by eapply Rcoupl_refRcoupl. }
      iIntros  (σ2 [e2' σ2'] HR).
      iMod ("H" with "[//]") as "H".
      by iApply "H".
  Qed.

  Lemma wp_refRcoupl_val_fupd (e e' : expr) (σ σ' : state) n φ v :
    to_val e = Some v →
    state_interp σ ∗ spec_interp (e', σ') ∗ WP e {{ v, ∃ v' : val, ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤, ∅}=> ⌜exec n (e, σ) ≾ lim_exec (e', σ') : φ⌝.
  Proof.
    iIntros (He) "(Hσ & Hs & Hwp)".
    rewrite wp_unfold /wp_pre /= He.
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (wp_adequacy_spec_coupl 0 with "Hwp").
    iIntros (σ1 e1' σ1') "> (? & Hs & (% & Hv & %)) /=".
    iDestruct (spec_auth_prog_agree with "Hs Hv") as %->.
    erewrite exec_is_final; [|done].
    erewrite lim_exec_final; [|done].
    iApply fupd_mask_intro; [set_solver|]; iIntros "_".
    iPureIntro. by eapply refRcoupl_dret.
  Qed.

  Lemma wp_refRcoupl_step_fupdN (e e' : expr) (σ σ' : state) n φ :
    state_interp σ ∗ spec_interp (e', σ') ∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜exec n (e, σ) ≾ lim_exec (e', σ') : φ⌝.
  Proof.
    iIntros "(Hσ & HspecI_auth & Hwp)".
    iInduction n as [|n] "IH" forall (e σ e' σ').
    { destruct (to_val e) eqn:He.
      - iMod (wp_refRcoupl_val_fupd with "[$]") as %?; [done|].
        by iApply step_fupdN_intro.
      - iApply fupd_mask_intro; [done|]; iIntros "_ /=".
        iPureIntro. rewrite He. apply refRcoupl_dzero. }
    destruct (to_val e) eqn:He.
    { iMod (wp_refRcoupl_val_fupd with "[$]") as %?; [done|].
      by iApply step_fupdN_intro. }
    iEval (rewrite wp_unfold /wp_pre /= He) in "Hwp".
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (wp_adequacy_spec_coupl with "Hwp").
    iIntros (σ2 e2' σ2') "(%R' & %m & %μ2' & % & % & %Hμ2' & Hwp)".
    iEval (rewrite -(erasable_pexec_lim_exec μ2' m) //).
    iEval (rewrite exec_Sn /step_or_final /= He).
    rewrite -step_fupdN_Sn.
    iApply refRcoupl_step_fupdN_dbind; [iPureIntro|].
    { by apply Rcoupl_refRcoupl. }
    iIntros "/=" ([e3 σ3] [e3' σ3'] HR').
    iMod ("Hwp" with "[//]") as "Hwp".
    clear.
    iIntros "!> !> !>".
    iApply (wp_adequacy_spec_coupl with "Hwp").
    iIntros (σ4 e4' σ4') ">(Hσ & Hs & Hwp)".
    iApply ("IH" with "Hσ Hs Hwp").
  Qed.

End adequacy.

Theorem wp_refRcoupl Σ `{clutchGpreS Σ} (e e' : expr) (σ σ' : state) n φ :
  (∀ `{clutchGS Σ}, ⊢ ⤇ e' -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
  exec n (e, σ) ≾ lim_exec (e', σ') : φ.
Proof.
  intros Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod spec_ra_init as (HspecGS) "(Hs & Hj & ?)".
  set (HclutchGS := HeapG Σ _ _ _ γH γT HspecGS).
  iApply wp_refRcoupl_step_fupdN.
  iFrame "Hh Ht Hs". by iApply (Hwp with "[Hj]").
Qed.

Corollary wp_refRcoupl_mass Σ `{clutchGpreS Σ} (e e' : expr) (σ σ' : state) φ :
  (∀ `{clutchGS Σ}, ⊢ ⤇ e' -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
  SeriesC (lim_exec (e, σ)) <= SeriesC (lim_exec (e', σ')).
Proof.
  intros Hwp.
  apply: lim_exec_leq_mass => n.
  eapply refRcoupl_mass_eq.
  by eapply wp_refRcoupl.
Qed.
