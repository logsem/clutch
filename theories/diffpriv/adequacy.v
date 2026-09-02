From iris.proofmode Require Import base proofmode.
From iris.bi Require Import lib.fixpoint_mono big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Import language.
From clutch.base_logic Require Import error_credits.
From clutch.diffpriv Require Import weakestpre primitive_laws distance diffpriv_rules.
From clutch.prob Require Import differential_privacy distribution couplings_dp.
Import uPred.


Section adequacy.
  Context `{!diffprivGS Σ}.

  Lemma wp_adequacy_spec_coupl n m e1 σ1 e1' σ1' Z φ ε δ :
    spec_coupl ∅ σ1 e1' σ1' ε δ Z -∗
    (∀ σ2 e2' σ2' ε' δ', Z σ2 e2' σ2' ε' δ' ={∅}=∗ |={∅}▷=>^n ⌜DPcoupl (exec m (e1, σ2)) (lim_exec (e2', σ2')) φ ε' δ'⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜DPcoupl (exec m (e1, σ1)) (lim_exec (e1', σ1')) φ ε δ⌝.
  Proof.
    iRevert (σ1 e1' σ1' ε δ).
    iApply spec_coupl_ind.
    iIntros "!>" (σ1 e1' σ1' ε δ)
      "[% | [boo | (%S & %μ1 & %μ1' & %E2 & %D2 & %Heras & %Hrwr & %Hbdd & %Hkanto & H)]] HZ";
      [ | by iMod ("HZ" with "[$]") |].
    - iApply step_fupdN_intro; [done|].
      do 2 iModIntro. iPureIntro. by apply DPcoupl_1.
    - iApply (step_fupdN_mono _ _ _ ⌜∀ σ2 e2' σ2',
        S σ2 (e2', σ2') →
        DPcoupl (exec m (e1, σ2)) (lim_exec (e2', σ2')) φ
          (E2 σ2 (e2', σ2')) (D2 σ2 (e2', σ2'))⌝).
      { iPureIntro. intros HΦ.
        rewrite -(Heras e1 m).
        rewrite Hrwr.
        eapply DPcoupl_dbind_adv_kanto_s_cond.
        - intros. apply cond_nonneg.
        - exact Hkanto.
        - intros a [e2' σ2'] HS. by apply HΦ. }
      iIntros (σ2 e2' σ2') "%HS".
      iMod ("H" with "[//]") as "[H _]".
      by iApply "H".
  Qed.

  Lemma wp_adequacy_prog_coupl n m e1 σ1 e1' σ1' Z φ ε δ :
    to_val e1 = None ->
    prog_coupl e1 σ1 e1' σ1' ε δ Z -∗
    (∀ e2 σ2 e2' σ2' ε' δ', Z e2 σ2 e2' σ2' ε' δ' ={∅}=∗ |={∅}▷=>^n ⌜DPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε' δ'⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜DPcoupl (exec (S m) (e1, σ1)) (lim_exec (e1', σ1')) φ ε δ⌝.
  Proof.
    iIntros (Hnone).
    rewrite exec_Sn.
    rewrite /step_or_final /= Hnone.
    rewrite /prog_coupl.
    iIntros "(%n0 & %μ1' & %E2 & %D2 & %S & %Hred & [%r %HD2r] & %Hkanto & %Heras & Hcnt) Hcoupl /=".
    iApply (step_fupdN_mono _ _ _ ⌜∀ e2 σ2 e2' σ2',
      S (e2, σ2) (e2', σ2') →
      DPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ
        (E2 (e2, σ2) (e2', σ2')) (D2 (e2, σ2) (e2', σ2'))⌝).
    { iPureIntro. intros HΦ.
      rewrite -(erasable_pexec_lim_exec μ1' n0).
      - eapply DPcoupl_dbind_adv_kanto_s_cond.
        + intros. apply cond_nonneg.
        + exact Hkanto.
        + intros [] [] HS. apply HΦ. exact HS.
      - exact Heras.
    }
    iIntros (e2 σ2 e2' σ2') "%HS".
    iMod ("Hcnt" $! e2 σ2 e2' σ2' with "[//]").
    by iApply "Hcoupl".
  Qed.

  Lemma wp_adequacy_val_fupd (e e' : expr) (σ σ' : state) n φ v ε δ:
    to_val e = Some v →
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε δ ∗
    WP e {{ v, ∃ v' : val, ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤, ∅}=> ⌜DPcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε δ⌝.
  Proof.
    iIntros (He) "(Hσ & Hs & Hε & Hwp)".
    rewrite wp_unfold /wp_pre /= He.
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (wp_adequacy_spec_coupl 0 with "Hwp").
    iIntros (σ1 e1' σ1' ε' δ') "> (? & Hs & (Hε & Hδ) & (% & Hv & %)) /=".
    iDestruct (spec_auth_prog_agree with "Hs Hv") as %->.
    erewrite exec_is_final; [|done].
    erewrite lim_exec_final; [|done].
    iApply fupd_mask_intro; [set_solver|]; iIntros "_".
    iPureIntro. by eapply DPcoupl_dret.
  Qed.

  Lemma wp_adequacy_step_fupdN ε δ (e e' : expr) (σ σ' : state) n φ :
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε δ ∗
    WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜DPcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε δ⌝.
  Proof.
    iIntros "(Hσ & HspecI_auth & Hε & Hwp)".
    iInduction n as [|n] "IH" forall (e σ e' σ' ε δ).
    { destruct (to_val e) eqn:He.
      - iMod (wp_adequacy_val_fupd with "[$]") as %?; [done|].
        by iApply step_fupdN_intro.
      - iApply fupd_mask_intro; [done|]; iIntros "_ /=".
        iPureIntro. rewrite He.
        by apply DPcoupl_dzero.
    }
    destruct (to_val e) eqn:He.
    { iMod (wp_adequacy_val_fupd with "[$]") as %?; [done|].
      iApply step_fupdN_intro; [done|].
      do 3 iModIntro. done. }
    iEval (rewrite wp_unfold /wp_pre /= He) in "Hwp".
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (wp_adequacy_spec_coupl with "Hwp").
    iIntros (σ2 e2' σ2' ε' δ') "Hprog". simpl in φ.
    iApply (wp_adequacy_prog_coupl with "Hprog"); [done|].
    iIntros (e3 σ3 e3' σ3' ε3 δ3) "Hspec".
    iIntros "!> !> !>".
    iApply (wp_adequacy_spec_coupl with "Hspec").
    iIntros (σ4 e4' σ4' ε4 δ4) ">(Hσ & Hs & Hε & Hcnt)".
    iApply ("IH" with "Hσ Hs Hε Hcnt").
  Qed.

End adequacy.

Lemma wp_adequacy_exec_n Σ `{!diffprivGpreS Σ} (e e' : expr) (σ σ' : state) n φ (ε δ : R) :
  0 <= ε → 0 <= δ ->
  (∀ `{diffprivGS Σ}, ⊢ ⤇ e' -∗ ↯m ε -∗ ↯ δ -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
  DPcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε δ.
Proof.
  intros Heps Hdel Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (ghost_map_alloc σ.(tapes_laplace)) as "[%γTL [Htl _]]".
  iMod spec_ra_init as (HspecGS) "(Hs & Hj & ?)".
  set ε' := mknonnegreal _ Heps.
  iMod (ecm_alloc ε') as (?) "[HE He]".
  destruct (decide (δ < 1)) as [? | Hnlt%Rnot_lt_le].
  - set δ' := mknonnegreal _ Hdel.
    iMod (ec_alloc δ') as (?) "[HD Hd]"; [done|].
    set (HdiffprivGS := HeapG Σ _ _ _ _ γH γT γTL HspecGS _).
    pose proof (wp_adequacy_step_fupdN ε' δ') as h. iApply h.
    iFrame "Hh Ht Htl Hs HE HD".
    by iApply (Hwp with "[Hj] [He] [Hd]").
  - iApply fupd_mask_intro; [done|]; iIntros "_".
    iApply step_fupdN_intro; [done|]; iModIntro.
    iPureIntro. by apply DPcoupl_1.
    Unshelve. apply _.
Qed.

Theorem wp_adequacy Σ `{diffprivGpreS Σ} (e e' : expr) (σ σ' : state) (ε δ : R) φ :
  0 <= ε → 0 <= δ ->
  (∀ `{diffprivGS Σ}, ⊢  ⤇ e' -∗ ↯m ε -∗ ↯ δ -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  DPcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε δ.
Proof.
  intros ? ? Hwp.
  apply lim_exec_DPcoupl; [done|done|].
  intros n.
  by eapply wp_adequacy_exec_n.
Qed.

Lemma DPcoupl_limit `{Countable A, Countable B} μ1 μ2 ε δ (ψ : A -> B -> Prop):
  (forall δ', δ' > δ -> DPcoupl μ1 μ2 ψ ε δ') -> DPcoupl μ1 μ2 ψ ε δ.
Proof.
  rewrite /DPcoupl.
  intros Hlimit. intros.
  apply real_le_limit.
  intros δ0 ?. rewrite Rcomplements.Rle_minus_l.
  rewrite Rplus_assoc.
  apply Hlimit; try done.
  lra.
Qed.

Corollary wp_adequacy_error_lim Σ `{diffprivGpreS Σ} (e e' : expr) (σ σ' : state) (ε δ : R) φ :
  0 <= ε →
  0 <= δ →
  (∀ `{diffprivGS Σ} (δ' : R),
      δ < δ' → ⊢ ⤇ e' -∗ ↯m ε -∗ ↯ δ' -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  DPcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε δ.
Proof.
  intros ?? Hwp.
  apply DPcoupl_limit.
  intros δ' Hineq.
  assert (0 <= δ') as Hδ'.
  { trans δ; [done|lra]. }
  pose (mknonnegreal δ' Hδ') as NNRδ'.
  assert (δ' = (NNRbar_to_real (NNRbar.Finite NNRδ'))) as Heq; [done|].
  rewrite Heq.
  eapply wp_adequacy; [done|done|done|..].
  iIntros (?).
  by iApply Hwp.
Qed.

Corollary wp_adequacy_mass Σ `{!diffprivGpreS Σ} (e e' : expr) (σ σ' : state) φ (ε δ : R) :
  0 <= ε → 0 <= δ ->
  (∀ `{diffprivGS Σ}, ⊢  ⤇ e' -∗ ↯m ε -∗ ↯ δ -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  SeriesC (lim_exec (e, σ)) <= exp ε * SeriesC (lim_exec (e', σ')) + δ.
Proof.
  intros ? ? Hwp. eapply DPcoupl_mass_leq. by eapply wp_adequacy.
Qed.

Corollary wp_diffpriv_list Σ `{diffprivGpreS Σ} (e : expr) (σ σ' : state) (ε δ : R) :
  0 <= ε → 0 <= δ ->
  (∀ x y, (IZR (list_dist x y) <= 1) →
          ∀ `{diffprivGS Σ}, ⊢ ⤇ e (list.inject_list y) -∗ ↯m ε -∗ ↯ δ -∗ WP e (list.inject_list x) {{ v, ∃ v', ⤇ Val v' ∗ ⌜v = v'⌝ }})
  →
    diffpriv_approx (λ x y, IZR (list_dist x y)) (λ x, (lim_exec (e (list.inject_list x), σ))) ε δ.
Proof.
  intros Hε Hδ Hwp. apply DPcoupl_diffpriv.
  intros. eapply wp_adequacy.
  1: eauto. 1: apply Hε. 1: apply Hδ.
  intros. apply Hwp. done.
Qed.

(* internal diffpriv implies external approximate diffpriv *)
Fact hoare_diffpriv_pure_list f ε δ (εpos : (0 <= ε)%R) (δpos : (0 <= δ)%R) :
  (∀ `{diffprivGS Σ}, ⊢ hoare_diffpriv_classic f ε δ (dlist _) _)
  →
    ∀ σ,
    diffpriv_approx
      (λ x y, IZR (list_dist x y))
      (λ x, lim_exec (f (list.inject_list x), σ))
      ε δ.
Proof.
  intros hwp ?.
  eapply (wp_diffpriv_list diffprivΣ) ; eauto ; try lra.
  iIntros (????) "f' ε δ".
  tp_bind (f _).
  iApply (hwp with "[] [$f' ε δ]").
  2: iFrame.
  1: rewrite /dlist //= //.
  iNext. iIntros (?) "$ //".
Qed.

Corollary wp_diffpriv_Z Σ `{diffprivGpreS Σ} (e : expr) (σ σ' : state) (ε δ : R) :
  0 <= ε → 0 <= δ ->
  (∀ x y, (IZR (Z.abs (x - y)) <= 1) →
          ∀ `{diffprivGS Σ}, ⊢ ⤇ e #y -∗ ↯m ε -∗ ↯ δ -∗ WP e #x {{ v, ∃ v', ⤇ Val v' ∗ ⌜v = v'⌝ }})
  →
    diffpriv_approx (λ x y, IZR (Z.abs (x - y))) (λ x, (lim_exec (e #x, σ))) ε δ.
Proof.
  intros Hε Hδ Hwp. apply DPcoupl_diffpriv.
  intros. eapply wp_adequacy.
  1: eauto. 1: apply Hε. 1: apply Hδ.
  intros. apply Hwp. done.
Qed.

(* hoare_diffpriv implies approximate diffpriv *)
Fact hoare_diffpriv_pure f ε δ (εpos : (0 <= ε)%R) (δpos : (0 <= δ)%R) :
  (∀ `{diffprivGS Σ}, ⊢ hoare_diffpriv f ε δ dZ Z)
  →
    ∀ σ,
    diffpriv_approx
      (λ x y, IZR (Z.abs (x - y)))
      (λ x, lim_exec (f #x, σ))
      ε δ.
Proof.
  intros hwp ?.
  eapply (wp_diffpriv_Z diffprivΣ) ; eauto ; try lra.
  iIntros (????) "f' ε δ".
  tp_bind (f _).
  iApply (hwp with "[] [$f' ε δ]").
  2: erewrite 2!Rmult_1_l ; iFrame.
  1: rewrite /dZ /= -abs_IZR //.
  iNext. iIntros (?) "$ //".
Qed.
