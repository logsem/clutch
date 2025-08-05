From clutch.prob_lang.spec Require Export spec_ra.
From clutch.prob_lang Require Export class_instances.
From clutch.prob_lang Require Import tactics lang notation metatheory.


From iris.proofmode Require Import base proofmode.
From iris.bi Require Import weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Import language.
From clutch.base_logic Require Import error_credits.
From clutch.diffpriv_simple_pw_again Require Import weakestpre_simple weakestpre_simple_prob_lang_resources.
From clutch.prob Require Import differential_privacy distribution couplings_dp.
Import uPred.

Section adequacy.
  Context `{!diffprivGS Σ}.

  Lemma wp_adequacy_val_fupd (e e' : expr) (σ σ' : state) n φ v ε δ:
    to_val e = Some v →
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε δ ∗
    WP e {{ v, ∃ v' : val, ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤, ∅}=> ⌜DPcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε δ⌝.
  Proof.
    iIntros (He) "(Hσ & Hs & Hε & Hwp)".
    rewrite wp_unfold /wp_pre /= He.
    iMod ("Hwp") as "(% & Hv & %)".
    iDestruct (spec_auth_prog_agree with "Hs Hv") as %->.
    erewrite exec_is_final; [|done].
    erewrite lim_exec_final; [|done].
    iApply fupd_mask_intro; [set_solver|]; iIntros "_".
    iPureIntro. by eapply DPcoupl_dret.
  Qed.

  Lemma wp_adequacy_step_fupdN_pw n : ∀ ε δ (e e' : expr) (σ σ' : state) φ (φrefl : ∀ x, φ x x),
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε δ ∗
    WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜DPcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε δ⌝.
  Proof.
    iInduction n as [|n] "IH" ; iIntros (ε δ e e' σ σ' φ) ; try iIntros (φrefl) ;
      iIntros "(Hσ & HspecI_auth & Hε & Hwp)".
    { destruct (to_val e) eqn:He.
      - iMod (wp_adequacy_val_fupd with "[$]") as %?; [done|].
        by iApply step_fupdN_intro.
      - iApply fupd_mask_intro; [done|]; iIntros "_ /=".
        iPureIntro. rewrite He.
        by apply DPcoupl_dzero.
    }
    destruct (language.to_val e) eqn:He.
    { iMod (wp_adequacy_val_fupd with "[$]") as %?; [done|].
      iApply step_fupdN_intro; [done|].
      do 3 iModIntro. done. }
    iEval (rewrite wp_unfold) in "Hwp".

    iEval (rewrite /wp_pre He) in "Hwp".

    iMod ("Hwp" with "[$]") as "[(%red & %R & % & % & % & % & %k & %HCR & %hε & %hδ & Hrec)|pw]".
    -
      (* rewrite the execution in the goal into dbinds *)
      rewrite exec_Sn /step_or_final ; iSimpl ; rewrite He. rewrite (lim_exec_pexec k).
      (* bind the coupling HCR *)
      iApply (step_fupdN_mono _ _ _ ⌜∀ ρ ρ', R ρ ρ' → DPcoupl (exec n ρ) (lim_exec ρ') φ ε2 δ2⌝).
      { iPureIntro. intros. eapply DPcoupl_dbind'' ; eauto. }
      rewrite -step_fupdN_Sn. iIntros ([e2 σ2] [e2' σ2'] HR).
      iSpecialize ("Hrec" $! e2 σ2 e2' σ2').
      iMod ("Hrec" $! HR) as "Hrec" ; iSimpl ; iIntros "!>!>!>".
      iMod "Hrec" as "(HT & S & E & Hwp)". iApply ("IH" with "[] [$]").
      1: done.
    -
      iDestruct "pw" as "(%e2 & %e2' & %σ2' & %k & %hstep & %hexec & %δ2' & (%hpos & %hex & %hδ) & pw)".
      assert (∀ x y, eq x y → φ x y) as φpw. { clear -φrefl. intros ?? ->. apply φrefl. }

      set (pweq_res (RES : val) := (λ v v', v = RES → v' = RES)).

      rewrite exec_Sn /step_or_final ; iSimpl ; rewrite He. rewrite (lim_exec_pexec k).
      iApply (step_fupdN_mono _ _ _ ⌜DPcoupl (exec n (e2, σ)) (lim_exec (e2', σ2')) φ ε δ⌝).
      { iPureIntro. intros. eapply (DPcoupl_dbind'' 0 ε ε 0 δ) ; try real_solver. 1: apply cond_nonneg.
        2: apply DPcoupl_pos_R.
        2: apply DPcoupl_trivial => //.
        - simpl. intros ρ ρ' (_ & lhs & rhs).
          assert (ρ = (e2, σ)) as ->.
          2: assert (ρ' = (e2', σ2')) as -> => //.
          + admit.
          + admit.
        - destruct hstep as [? hstep]. simpl in *.
          rewrite /prim_step /=.
          opose proof head_step_mass.
          admit.
        - opose proof (dret_mass ((e2', σ2'))) as h. rewrite -h.
          f_equal. apply pmf_1_eq_dret in hexec. rewrite hexec. done.
      }

      iApply (step_fupdN_mono _ _ _ ⌜∀ RES, DPcoupl (exec n (e2, σ)) (lim_exec (e2', σ2')) (pweq_res RES) ε (δ2' RES)⌝).
      { iPureIntro. intros PWCPL.
        eapply DPcoupl_mono ; last first. 4: apply φpw.
        1: eapply DPcoupl_pweq ; last first. 1: eapply PWCPL.
        all: eauto. 1: apply cond_nonneg. 1: right ; eauto.
      }
      iIntros "!>!>!>".
      iIntros (RES).
      iMod "pw". iDestruct ("pw" $! RES) as "(HT & S & (ε & δ) & pw)".
      iApply ("IH" $! ε (δ2' RES) e2 e2' σ σ2' (pweq_res RES) with "[%] [-]").
      1: intros v hv. 1: exact hv.
      iFrame.

  Admitted.



End adequacy.

Lemma wp_adequacy_exec_n_refl Σ `{!diffprivGpreS Σ} (e e' : expr) (σ σ' : state) n φ (φrefl : ∀ x, φ x x) (ε δ : R) :
  0 <= ε → 0 <= δ ->
  (∀ `{diffprivGS Σ}, ⊢ ⤇ e' -∗ ↯m ε -∗ ↯ δ -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
  DPcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε δ.
Proof.
  intros Heps Hdel Hwp.
  eapply pure_soundness. eapply (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod spec_ra_init as (HspecGS) "(Hs & Hj & ?)".
  set ε' := mknonnegreal _ Heps.
  iMod (ecm_alloc ε') as (?) "[HE He]".
  destruct (decide (δ < 1)) as [? | Hnlt%Rnot_lt_le].
  - set δ' := mknonnegreal _ Hdel.
    iMod (ec_alloc δ') as (?) "[HD Hd]"; [done|].
    set (HdiffprivGS := HeapG Σ _ _ _ γH γT HspecGS _).
    iApply (wp_adequacy_step_fupdN_pw n ε' δ'). 1: assumption.
    iFrame "Hh Ht Hs HE HD".
    by iApply (Hwp with "[Hj] [He] [Hd]").
  - iApply fupd_mask_intro; [done|]; iIntros "_".
    iApply step_fupdN_intro; [done|]; iModIntro.
    iPureIntro. by apply DPcoupl_1.
Qed.

(* Lemma wp_adequacy_exec_n Σ `{!diffprivGpreS Σ} (e e' : expr) (σ σ' : state) n φ (ε δ : R) :
     0 <= ε → 0 <= δ ->
     (∀ `{diffprivGS Σ}, ⊢ ⤇ e' -∗ ↯m ε -∗ ↯ δ -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
     DPcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε δ.
   Proof.
     intros Heps Hdel Hwp.
     eapply pure_soundness. eapply (step_fupdN_soundness_no_lc _ n 0).
     iIntros (Hinv) "_".
     iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
     iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
     iMod spec_ra_init as (HspecGS) "(Hs & Hj & ?)".
     set ε' := mknonnegreal _ Heps.
     iMod (ecm_alloc ε') as (?) "[HE He]".
     destruct (decide (δ < 1)) as [? | Hnlt%Rnot_lt_le].
     - set δ' := mknonnegreal _ Hdel.
       iMod (ec_alloc δ') as (?) "[HD Hd]"; [done|].
       set (HdiffprivGS := HeapG Σ _ _ _ γH γT HspecGS _).
       iApply (wp_adequacy_step_fupdN ε' δ').
       iFrame "Hh Ht Hs HE HD".
       by iApply (Hwp with "[Hj] [He] [Hd]").
     - iApply fupd_mask_intro; [done|]; iIntros "_".
       iApply step_fupdN_intro; [done|]; iModIntro.
       iPureIntro. by apply DPcoupl_1.
   Qed. *)

Theorem wp_adequacy_refl Σ `{diffprivGpreS Σ} (e e' : expr) (σ σ' : state) (ε δ : R) φ (φrefl : ∀ x, φ x x) :
  0 <= ε → 0 <= δ ->
  (∀ `{diffprivGS Σ}, ⊢  ⤇ e' -∗ ↯m ε -∗ ↯ δ -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  DPcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε δ.
Proof.
  intros ? ? Hwp.
  apply lim_exec_DPcoupl; [done|done|].
  intros n.
  by eapply wp_adequacy_exec_n_refl.
Qed.

(* Theorem wp_adequacy Σ `{diffprivGpreS Σ} (e e' : expr) (σ σ' : state) (ε δ : R) φ :
     0 <= ε → 0 <= δ ->
     (∀ `{diffprivGS Σ}, ⊢  ⤇ e' -∗ ↯m ε -∗ ↯ δ -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
     DPcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε δ.
   Proof.
     intros ? ? Hwp.
     apply lim_exec_DPcoupl; [done|done|].
     intros n.
     by eapply wp_adequacy_exec_n.
   Qed. *)

(* Corollary wp_adequacy_error_lim Σ `{diffprivGpreS Σ} (e e' : expr) (σ σ' : state) (ε : R) φ :
     0 <= ε →
     (∀ `{diffprivGS Σ} (ε' : R),
         ε < ε' → ⊢ ⤇ e' -∗ ↯ ε' -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
     Mcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε.
   Proof.
     intros ? Hwp.
     apply Mcoupl_limit.
     intros ε' Hineq.
     assert (0 <= ε') as Hε'.
     { trans ε; [done|lra]. }
     pose (mknonnegreal ε' Hε') as NNRε'.
     assert (ε' = (NNRbar_to_real (NNRbar.Finite NNRε'))) as Heq; [done|].
     rewrite Heq.
     eapply wp_adequacy; [done|done|].
     iIntros (?).
     by iApply Hwp.
   Qed. *)

(* Corollary wp_adequacy_mass Σ `{!diffprivGpreS Σ} (e e' : expr) (σ σ' : state) φ (ε δ : R) :
     0 <= ε → 0 <= δ ->
     (∀ `{diffprivGS Σ}, ⊢  ⤇ e' -∗ ↯m ε -∗ ↯ δ -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
     SeriesC (lim_exec (e, σ)) <= exp ε * SeriesC (lim_exec (e', σ')) + δ.
   Proof.
     intros ? ? Hwp. eapply DPcoupl_mass_leq. by eapply wp_adequacy.
   Qed. *)

Corollary wp_diffpriv_Z Σ `{diffprivGpreS Σ} (e : expr) (σ σ' : state) (ε δ : R) :
  0 <= ε → 0 <= δ ->
  (∀ x y, (IZR (Z.abs (x - y)) <= 1) →
          ∀ `{diffprivGS Σ}, ⊢ ⤇ e #y -∗ ↯m ε -∗ ↯ δ -∗ WP e #x {{ v, ∃ v', ⤇ Val v' ∗ ⌜v = v'⌝ }})
  →
    diffpriv_approx (λ x y, IZR (Z.abs (x - y))) (λ x, (lim_exec (e #x, σ))) ε δ.
Proof.
  intros Hε Hδ Hwp. apply DPcoupl_diffpriv.
  intros. eapply wp_adequacy_refl.
  1,2: eauto. 1: apply Hε. 1: apply Hδ.
  intros. apply Hwp. done.
Qed.
