From iris.proofmode Require Import base proofmode.
From iris.bi Require Export lib.fixpoint_mono big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Export language erasable exec.
From clutch.base_logic Require Import error_credits.
From clutch.diffpriv Require Import weakestpre primitive_laws.
From clutch.diffpriv Require Import adequacy.
From clutch.prob Require Import distribution.
Import uPred.


Lemma uwp_adequacy_exec_n Σ `{!diffprivGpreS Σ} (e : expr) (σ : state) n φ (δ : R) :
  0 <= δ ->
  (∀ `{diffprivGS Σ}, ⊢ ↯ δ -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (exec n (e, σ)) φ δ.
Proof.
  intros Hδ Hwp.
  eapply DPcoupl_to_UB.
  eapply (wp_adequacy_exec_n Σ e (Val #()) σ σ n (λ v _, φ v) 0 δ); [lra|done|].
  intros ?. iIntros "Hspec _ Hd".
  iPoseProof (Hwp with "Hd") as "He".
  iApply (wp_wand with "He").
  iIntros (v) "%". iExists _. by iFrame.
Qed.

Theorem uwp_adequacy Σ `{diffprivGpreS Σ} (e : expr) (σ : state) (δ : R) φ :
  0 <= δ ->
  (∀ `{diffprivGS Σ}, ⊢  ↯ δ -∗ WP e {{ v, ⌜φ v⌝ }} ) →
  pgl (lim_exec (e, σ)) φ δ.
Proof.
  intros Hδ Hwp.
  eapply DPcoupl_to_UB.
  eapply (wp_adequacy Σ e (Val #()) σ σ 0 δ); [lra|done|].
  intros ?. iIntros "Hspec _ Hd".
  iPoseProof (Hwp with "Hd") as "He".
  iApply (wp_wand with "He").
  iIntros (v) "%". iExists _. by iFrame.
Qed.


(** * Expected-value adequacy

    A strengthening of [uwp_adequacy]: instead of a boolean predicate [φ] and
    a pure postcondition [⌜φ v⌝], here the postcondition is itself a δ-credit
    [↯ (D v)] whose amount depends on the returned value. The conclusion
    bounds the *expectation* of [D] under the final output distribution by
    the initial credit.

    Since the postcondition is a resource (not a pure fact), it cannot be
    reduced to the existing [DPcoupl]-based relational adequacy the way
    [uwp_adequacy]/[uwp_adequacy_exec_n] are: [DPcoupl] is universally
    quantified over *all* admissible [0,1]-valued test-function pairs, which
    is the wrong shape to pin down the expectation of one specific [D]
    (concretely, routing [D] through a trivial-right-side [DPcoupl] only
    ever yields the vacuous bound [Expval μ D <= 1 + δ]).

    Instead we redo the adequacy induction from [diffpriv/adequacy.v]
    (spec_coupl/prog_coupl composition, then induction on the step index),
    but target [Expval (exec n (e,σ)) D <= δ] directly at every level instead
    of a [DPcoupl] fact. Concretely, at each composition step we instantiate
    the ambient Kantorovich inequality with [h1 := λ a, Expval (exec m ⋅) D]
    and [h2 := λ _, 0] (we don't care about the right-hand/spec side at all),
    discharge the pointwise side-condition with the induction hypothesis,
    and use the erasability equation together with the [Expval] tower
    property ([Expval_dbind]) to fold the sum back up. Since [h2 ≡ 0]
    throughout, the multiplicative [exp ε] factor is always multiplied away
    — [ε] plays no role anywhere in this proof, mirroring what we found for
    [DPcoupl_to_UB]/[DPcoupl_to_exp_val_exp] on one-sided relations. At a
    value, [ec_supply_bound] turns the held [↯ (D v)] together with the
    ambient [err_interp] into the pure fact [D v <= δ']. *)
Section unary_expval_adequacy.
  Context `{!diffprivGS Σ}.

  Lemma Expval_bounded01 `{Countable A} (μ : distr A) (f : A -> R) :
    (forall x, 0 <= f x <= 1) -> Expval μ f <= 1.
  Proof.
    intros Hf.
    trans (Expval μ (fun _ => 1)).
    - apply Expval_le; [intros x; specialize (Hf x); lra | apply ex_expval_const].
    - rewrite /Expval (SeriesC_ext (fun n => μ n * 1) μ); [apply pmf_SeriesC | intros; lra].
  Qed.

  Lemma wp_adequacy_expval_spec_coupl n m (e1 : expr) σ1 e1' σ1' Z ε δ (D : val -> R) :
    (forall v, 0 <= D v <= 1) ->
    spec_coupl ∅ σ1 e1' σ1' ε δ Z -∗
    (∀ σ2 e2' σ2' ε' δ', Z σ2 e2' σ2' ε' δ' ={∅}=∗ |={∅}▷=>^n ⌜Expval (exec m (e1, σ2)) D <= δ'⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜Expval (exec m (e1, σ1)) D <= δ⌝.
  Proof.
    intros HD.
    iRevert (σ1 e1' σ1' ε δ).
    iApply spec_coupl_ind.
    iIntros "!>" (σ1 e1' σ1' ε δ)
      "[% | [boo | (%S & %μ1 & %μ1' & %E2 & %D2 & %Heras & %Hrwr & %Hbdd & %Hkanto & H)]] HZ";
      [ | by iMod ("HZ" with "[$]") |].
    - iApply step_fupdN_intro; [done|].
      do 2 iModIntro. iPureIntro.
      trans 1.
      + apply Expval_bounded01, HD.
      + exact H.
    - iApply (step_fupdN_mono _ _ _ ⌜∀ σ2 e2' σ2',
        S σ2 (e2', σ2') →
        Expval (exec m (e1, σ2)) D <= D2 σ2 (e2', σ2')⌝).
      { iPureIntro. intros HΦ.
        rewrite -(Heras e1 m).
        rewrite (Expval_dbind μ1 (fun a => exec m (e1, a)) D).
        - eapply Rle_trans.
          + apply (Hkanto (fun a => Expval (exec m (e1, a)) D) (fun _ => 0)).
            * intros a. split.
              -- apply Expval_ge_0'. intros v; specialize (HD v); lra.
              -- apply Expval_bounded01, HD.
            * intros b. lra.
            * intros a [e2' σ2'] HS. specialize (HΦ a e2' σ2' HS).
              rewrite Rmult_0_r Rplus_0_l. exact HΦ.
          + assert (Hz : Expval μ1' (fun _ => 0) = 0).
            { rewrite /Expval. apply SeriesC_0. intros; lra. }
            rewrite Hz. rewrite Rmult_0_r Rplus_0_l. apply Rle_refl.
        - intros b. specialize (HD b); lra.
        - apply (ex_expval_le _ _ (fun _ => 1)).
          + intros a; specialize (HD a); lra.
          + apply ex_expval_const. }
      iIntros (σ2 e2' σ2') "%HS".
      iMod ("H" with "[//]") as "[H _]".
      by iApply "H".
  Qed.

  Lemma wp_adequacy_expval_prog_coupl n m e1 σ1 e1' σ1' Z ε δ (D : val -> R) :
    (forall v, 0 <= D v <= 1) ->
    to_val e1 = None ->
    prog_coupl e1 σ1 e1' σ1' ε δ Z -∗
    (∀ e2 σ2 e2' σ2' ε' δ', Z e2 σ2 e2' σ2' ε' δ' ={∅}=∗ |={∅}▷=>^n ⌜Expval (exec m (e2, σ2)) D <= δ'⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜Expval (exec (S m) (e1, σ1)) D <= δ⌝.
  Proof.
    intros HD Hnone.
    rewrite exec_Sn.
    rewrite /step_or_final /= Hnone.
    rewrite /prog_coupl.
    iIntros "(%n0 & %μ1' & %E2 & %D2 & %S & %Hred & [%r %HD2r] & %Hkanto & %Heras & Hcnt) Hcoupl /=".
    iApply (step_fupdN_mono _ _ _ ⌜∀ e2 σ2 e2' σ2',
      S (e2, σ2) (e2', σ2') →
      Expval (exec m (e2, σ2)) D <= D2 (e2, σ2) (e2', σ2')⌝).
    { iPureIntro. intros HΦ.
      rewrite (Expval_dbind (prim_step e1 σ1) (fun ρ => exec m ρ) D).
      - eapply Rle_trans.
        + apply (Hkanto (fun ρ => Expval (exec m ρ) D) (fun _ => 0)).
          * intros ρ. split.
            -- apply Expval_ge_0'. intros v; specialize (HD v); lra.
            -- apply Expval_bounded01, HD.
          * intros ρ. lra.
          * intros [e2 σ2] [e2' σ2'] HS. specialize (HΦ e2 σ2 e2' σ2' HS).
            rewrite Rmult_0_r Rplus_0_l. exact HΦ.
        + transitivity (exp ε * 0 + δ); [|rewrite Rmult_0_r Rplus_0_l; apply Rle_refl].
          apply Rplus_le_compat_r.
          apply Rmult_le_compat_l; [left; apply exp_pos|].
          right. apply SeriesC_0. intros; lra.
      - intros v; specialize (HD v); lra.
      - apply (ex_expval_le _ _ (fun _ => 1)).
        + intros v; specialize (HD v); lra.
        + apply ex_expval_const. }
    iIntros (e2 σ2 e2' σ2') "%HS".
    iMod ("Hcnt" $! e2 σ2 e2' σ2' with "[//]").
    by iApply "Hcoupl".
  Qed.

  Lemma wp_adequacy_expval_val_fupd (e e' : expr) (σ σ' : state) n v ε δ (D : val -> R) :
    (forall v, 0 <= D v <= 1) ->
    to_val e = Some v →
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε δ ∗
    WP e {{ v, ↯ (D v) }} ⊢
    |={⊤, ∅}=> ⌜Expval (exec n (e, σ)) D <= δ⌝.
  Proof.
    intros HD He. iIntros "(Hσ & Hs & Hε & Hwp)".
    rewrite wp_unfold /wp_pre /= He.
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (wp_adequacy_expval_spec_coupl 0 with "Hwp"); [done|].
    iIntros (σ1 e1' σ1' ε' δ') "> (? & Hs & (Hε & Hδ) & Hd) /=".
    iDestruct (ec_supply_bound with "Hδ Hd") as %Hle.
    erewrite exec_is_final; [|done].
    iApply fupd_mask_intro; [set_solver|]; iIntros "_".
    iPureIntro. rewrite Expval_dret. done.
  Qed.

  Lemma wp_adequacy_expval_step_fupdN ε δ (e e' : expr) (σ σ' : state) n (D : val -> R) :
    (forall v, 0 <= D v <= 1) ->
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε δ ∗
    WP e {{ v, ↯ (D v) }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜Expval (exec n (e, σ)) D <= δ⌝.
  Proof.
    intros HD.
    iIntros "(Hσ & HspecI_auth & Hε & Hwp)".
    iInduction n as [|n] "IH" forall (e σ e' σ' ε δ).
    { destruct (to_val e) eqn:He.
      - iMod (wp_adequacy_expval_val_fupd with "[$]") as %?; [done|done|].
        by iApply step_fupdN_intro.
      - iApply fupd_mask_intro; [done|]; iIntros "_ /=".
        iPureIntro. rewrite He.
        rewrite /Expval (SeriesC_ext (fun a => dzero a * D a) (fun _ => 0)).
        + rewrite SeriesC_0; [apply cond_nonneg | done].
        + intros a. rewrite dzero_0. lra.
    }
    destruct (to_val e) eqn:He.
    { iMod (wp_adequacy_expval_val_fupd with "[$]") as %?; [done|done|].
      iApply step_fupdN_intro; [done|].
      do 3 iModIntro. done. }
    iEval (rewrite wp_unfold /wp_pre /= He) in "Hwp".
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (wp_adequacy_expval_spec_coupl with "Hwp"); [done|].
    iIntros (σ2 e2' σ2' ε' δ') "Hprog".
    iApply (wp_adequacy_expval_prog_coupl with "Hprog"); [done|done|].
    iIntros (e3 σ3 e3' σ3' ε3 δ3) "Hspec".
    iIntros "!> !> !>".
    iApply (wp_adequacy_expval_spec_coupl with "Hspec"); [done|].
    iIntros (σ4 e4' σ4' ε4 δ4) ">(Hσ & Hs & Hε & Hcnt)".
    iApply ("IH" with "Hσ Hs Hε Hcnt").
  Qed.

End unary_expval_adequacy.

Lemma uwp_expval_adequacy_exec_n Σ `{!diffprivGpreS Σ} (e : expr) (σ : state) n (δ : R) (D : val -> R) :
  0 <= δ -> (∀ v, 0 <= D v <= 1) ->
  (∀ `{diffprivGS Σ}, ⊢ ↯ δ -∗ WP e {{ v, ↯ (D v) }}) →
  Expval (exec n (e, σ)) D <= δ.
Proof.
  intros Hdel HD Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (ghost_map_alloc σ.(tapes_laplace)) as "[%γTL [Htl _]]".
  iMod spec_ra_init as (HspecGS) "(Hs & Hj & ?)".
  iMod (ecm_alloc 0%NNR) as (?) "[HE He]".
  destruct (decide (δ < 1)) as [? | Hnlt%Rnot_lt_le].
  - set δ' := mknonnegreal _ Hdel.
    iMod (ec_alloc δ') as (?) "[HD Hd]"; [done|].
    set (HdiffprivGS := HeapG Σ _ _ _ _ γH γT γTL HspecGS _).
    pose proof (wp_adequacy_expval_step_fupdN 0%NNR δ' e (Val #()) σ σ n D HD) as h.
    iApply h.
    iFrame "Hh Ht Htl Hs HE HD".
    by iApply (Hwp with "Hd").
  - iApply fupd_mask_intro; [done|]; iIntros "_".
    iApply step_fupdN_intro; [done|]; iModIntro.
    iPureIntro. trans 1; [apply Expval_bounded01, HD | lra].
    Unshelve. apply _.
Qed.

Lemma lim_exec_Expval (e : expr) (σ : state) (D : val -> R) (δ : R) :
  (∀ v, 0 <= D v <= 1) ->
  (∀ n, Expval (exec n (e, σ)) D <= δ) ->
  Expval (lim_exec (e, σ)) D <= δ.
Proof.
  intros HD Hn.
  assert (∀ a', Rbar.is_finite (Lim_seq.Sup_seq (λ n, Rbar.Finite (exec n (e,σ) a')))) as Hfin.
  { intro a'.
    apply (is_finite_bounded 0 1).
    - apply (Lim_seq.Sup_seq_minor_le _ _ 0); simpl.
      case_match; auto.
    - by apply upper_bound_ge_sup; intro; simpl. }
  rewrite /Expval {1}/lim_exec.
  setoid_rewrite lim_distr_pmf.
  transitivity (Rbar.real (Lim_seq.Sup_seq (λ n, Rbar.Finite (SeriesC (λ v, exec n (e,σ) v * D v))))).
  - right.
    setoid_rewrite (rbar_scal_r); [|done].
    setoid_rewrite <- Sup_seq_scal_r; [|apply HD].
    simpl.
    eapply MCT_seriesC.
    + intros n a; specialize (HD a); real_solver.
    + intros n a.
      apply Rmult_le_compat_r.
      * apply HD.
      * pose proof (exec_mono (e,σ) n a) as Hmono. exact Hmono.
    + intros a; exists 1; intros n; specialize (HD a); real_solver.
    + intro n.
      apply SeriesC_correct.
      apply (ex_seriesC_le _ (exec n (e,σ))); auto.
      intros v.
      specialize (HD v).
      pose proof (pmf_pos (exec n (e,σ)) v) as Hpos.
      split.
      * apply Rmult_le_pos; [exact Hpos | apply HD].
      * rewrite -{2}(Rmult_1_r (exec n (e,σ) v)).
        apply Rmult_le_compat_l; [exact Hpos | apply HD].
    + rewrite rbar_finite_real_eq.
      { apply Lim_seq.Sup_seq_correct. }
      apply (is_finite_bounded 0 1).
      * apply (Lim_seq.Sup_seq_minor_le _ _ 0); simpl.
        apply SeriesC_ge_0' => ?.
        case_match; real_solver.
      * apply upper_bound_ge_sup; intro n; simpl.
        etrans.
        { apply (SeriesC_le _ (exec n (e,σ))); [|done].
          intros v.
          specialize (HD v).
          pose proof (pmf_pos (exec n (e,σ)) v) as Hpos.
          split.
          - apply Rmult_le_pos; [exact Hpos | apply HD].
          - rewrite -{2}(Rmult_1_r (exec n (e,σ) v)).
            apply Rmult_le_compat_l; [exact Hpos | apply HD]. }
        apply pmf_SeriesC.
  - apply Rbar_le_fin'.
    + apply (Rle_trans _ (Expval (exec 0 (e,σ)) D)); [apply Expval_ge_0'; intros; apply HD | apply Hn].
    + apply upper_bound_ge_sup.
      intro n; simpl. apply Hn.
Qed.

Theorem uwp_expval_adequacy Σ `{diffprivGpreS Σ} (e : expr) (σ : state) (δ : R) (D : val -> R) :
  0 <= δ -> (∀ v, 0 <= D v <= 1) ->
  (∀ `{diffprivGS Σ}, ⊢  ↯ δ -∗ WP e {{ v, ↯ (D v) }} ) →
  Expval (lim_exec (e, σ)) D <= δ.
Proof.
  intros Hδ HD Hwp.
  apply lim_exec_Expval; [done|].
  intros n.
  by eapply uwp_expval_adequacy_exec_n.
Qed.
