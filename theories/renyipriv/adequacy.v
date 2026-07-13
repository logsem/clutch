From iris.proofmode Require Import base proofmode.
From iris.bi Require Import lib.fixpoint_mono big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Import language.
From clutch.renyipriv Require Import weakestpre primitive_laws.
From clutch.prob Require Import differential_privacy distribution couplings_rdp.
Import uPred.


Section adequacy.
  Context `{!renyiprivGS Σ}.

  (** ** Erasure lemmas for [RDPcoupl].

      These compose a state-level coupling with the continuation coupling,
      using [erasable] to absorb the (spec-side) execution steps. *)

  Lemma RDPcoupl_erasure_erasable
      (e1 e1' : expr) α ρ ρ1 ρ2 σ1 σ1' μ1 μ1' S φ n m :
    (1 <= α)%R →
    (0 <= ρ1)%R → (0 <= ρ2)%R → (ρ1 + ρ2 <= ρ)%R →
    RDPcoupl μ1 (σ2' ← μ1'; pexec n (e1', σ2')) S α ρ1 →
    erasable μ1 σ1 →
    erasable μ1' σ1' →
    (∀ σ2 e2' σ2', S σ2 (e2', σ2') →
       RDPcoupl (exec m (e1, σ2)) (lim_exec (e2', σ2')) φ α ρ2) →
    RDPcoupl (exec m (e1, σ1)) (lim_exec (e1', σ1')) φ α ρ.
  Proof.
    intros Hα Hρ1 Hρ2 Hρ Hcpl Hμ1 Hμ1' Hcont.
    rewrite -(Hμ1 e1 m).
    rewrite -(erasable_pexec_lim_exec μ1' n) //.
    eapply (RDPcoupl_mono _ _ _ _ _ _ _ (ρ1 + ρ2) ρ); [done..| |].
    { exact Hρ. }
    eapply (RDPcoupl_dbind _ _ _ _ S φ); [done|done|done| |exact Hcpl].
    intros σ2 [e2' σ2'] HS. by apply Hcont.
  Qed.

  Lemma RDPcoupl_erasure_prog
      (e1 e1' : expr) α ρ ρ1 ρ2 σ1 σ1' μ1' R φ n m :
    (1 <= α)%R →
    (0 <= ρ1)%R → (0 <= ρ2)%R → (ρ1 + ρ2 <= ρ)%R →
    RDPcoupl (prim_step e1 σ1) (σ2' ← μ1'; pexec n (e1', σ2')) R α ρ1 →
    erasable μ1' σ1' →
    (∀ e2 σ2 e2' σ2', R (e2, σ2) (e2', σ2') →
       RDPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ α ρ2) →
    RDPcoupl (prim_step e1 σ1 ≫= exec m) (lim_exec (e1', σ1')) φ α ρ.
  Proof.
    intros Hα Hρ1 Hρ2 Hρ Hcpl Hμ1' Hcont.
    rewrite -(erasable_pexec_lim_exec μ1' n) //.
    eapply (RDPcoupl_mono _ _ _ _ _ _ _ (ρ1 + ρ2) ρ); [done..| |].
    { exact Hρ. }
    eapply (RDPcoupl_dbind _ _ _ _ R φ); [done|done|done| |exact Hcpl].
    intros [e2 σ2] [e2' σ2'] HR. by apply Hcont.
  Qed.

  Lemma wp_adequacy_spec_coupl n m e1 σ1 e1' σ1' Z φ (α ρ : nonnegreal) :
    (1 <= α)%R →
    spec_coupl ∅ σ1 e1' σ1' α ρ Z -∗
    (∀ σ2 e2' σ2' ρ', Z σ2 e2' σ2' α ρ' ={∅}=∗ |={∅}▷=>^n ⌜RDPcoupl (exec m (e1, σ2)) (lim_exec (e2', σ2')) φ α ρ'⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜RDPcoupl (exec m (e1, σ1)) (lim_exec (e1', σ1')) φ α ρ⌝.
  Proof.
    iIntros (Hα) "Hcoupl HZ".
    iRevert (Hα). iRevert "HZ".
    iRevert (σ1 e1' σ1' α ρ) "Hcoupl".
    iApply spec_coupl_ind.
    iIntros "!>" (σ1 e1' σ1' α ρ)
      "[HZ' | (%S & %k & %μ1 & %μ1' & %ρ1 & %ρ2 & %Hcpl & %Hρ & %Hμ1 & %Hμ1' & H)] HZ %Hα".
    - by iMod ("HZ" with "HZ'").
    - iApply (step_fupdN_mono _ _ _ ⌜_⌝).
      { iPureIntro. intros Hcont.
        eapply (RDPcoupl_erasure_erasable e1 e1' α ρ ρ1 ρ2 σ1 σ1' μ1 μ1' S φ k m);
          last done;
            [done|apply cond_nonneg|apply cond_nonneg|done|done|done|done]. }
      iIntros (σ2 e2' σ2' HS).
      iMod ("H" with "[//]") as "[H _]".
      by iApply ("H" with "HZ").
  Qed.

  Lemma wp_adequacy_prog_coupl n m e1 σ1 e1' σ1' Z φ (α ρ : nonnegreal) :
    (1 <= α)%R →
    to_val e1 = None ->
    prog_coupl e1 σ1 e1' σ1' α ρ Z -∗
    (∀ e2 σ2 e2' σ2' ρ', Z e2 σ2 e2' σ2' α ρ' ={∅}=∗ |={∅}▷=>^n ⌜RDPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ α ρ'⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜RDPcoupl (exec (S m) (e1, σ1)) (lim_exec (e1', σ1')) φ α ρ⌝.
  Proof.
    iIntros (Hα Hnone).
    rewrite exec_Sn /step_or_final /= Hnone.
    rewrite /prog_coupl.
    iIntros "(%R & %k & %μ1' & %ρ1 & %ρ2 & %Hred & %Hcpl & %Hρ & %Hμ1' & Hcnt) Hcoupl /=".
    iApply (step_fupdN_mono _ _ _ ⌜_⌝).
    { iPureIntro. intros Hcont.
      eapply (RDPcoupl_erasure_prog e1 e1' α ρ ρ1 ρ2 σ1 σ1' μ1' R φ k m);
      last done;
        [done|apply cond_nonneg|apply cond_nonneg|done|done|done]. }
    iIntros (e2 σ2 e2' σ2' HR).
    iMod ("Hcnt" with "[//]") as "Hcnt".
    by iApply "Hcoupl".
  Qed.

  Lemma wp_adequacy_val_fupd (e e' : expr) (σ σ' : state) n φ v α ρ :
    to_val e = Some v →
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp α ρ ∗
    WP e {{ v, ∃ v' : val, ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤, ∅}=> ⌜RDPcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ α ρ⌝.
  Proof.
    iIntros (He) "(Hσ & Hs & Hε & Hwp)".
    iDestruct (rc_supply_valid with "Hε") as %Hα.
    rewrite wp_unfold /wp_pre /= He.
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (wp_adequacy_spec_coupl 0 with "Hwp"); [done|].
    iIntros (σ1 e1' σ1' ρ') "> (? & Hs & Hε & (% & Hv & %)) /=".
    iDestruct (spec_auth_prog_agree with "Hs Hv") as %->.
    erewrite exec_is_final; [|done].
    erewrite lim_exec_final; [|done].
    iApply fupd_mask_intro; [set_solver|]; iIntros "_".
    iDestruct (rc_supply_valid with "Hε") as %Hα'.
    iPureIntro. eapply RDPcoupl_dret; [done|apply cond_nonneg|done].
  Qed.

  Lemma wp_adequacy_step_fupdN α ρ (e e' : expr) (σ σ' : state) n φ :
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp α ρ ∗
    WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜RDPcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ α ρ⌝.
  Proof.
    iIntros "(Hσ & HspecI_auth & Hε & Hwp)".
    iInduction n as [|n] "IH" forall (e σ e' σ' α ρ).
    { destruct (to_val e) eqn:He.
      - iMod (wp_adequacy_val_fupd with "[$]") as %?; [done|].
        by iApply step_fupdN_intro.
      - iApply fupd_mask_intro; [done|]; iIntros "_ /=".
        iDestruct (rc_supply_valid with "Hε") as %Hα.
        iPureIntro. rewrite He.
        by apply RDPcoupl_dzero. }
    destruct (to_val e) eqn:He.
    { iMod (wp_adequacy_val_fupd with "[$]") as %?; [done|].
      iApply step_fupdN_intro; [done|].
      do 3 iModIntro. done. }
    iDestruct (rc_supply_valid with "Hε") as %Hα.
    iEval (rewrite wp_unfold /wp_pre /= He) in "Hwp".
    iMod ("Hwp" with "[$]") as "Hwp".
    iApply (wp_adequacy_spec_coupl with "Hwp"); [done|].
    iIntros (σ2 e2' σ2' ρ') "Hprog".
    iApply (wp_adequacy_prog_coupl with "Hprog"); [done|done|].
    iIntros (e3 σ3 e3' σ3' ρ3) "Hspec".
    iIntros "!> !> !>".
    iApply (wp_adequacy_spec_coupl with "Hspec"); [done|].
    iIntros (σ4 e4' σ4' ρ4) ">(Hσ & Hs & Hε & Hcnt)".
    iApply ("IH" with "Hσ Hs Hε Hcnt").
  Qed.

End adequacy.


Lemma wp_adequacy_exec_n Σ `{!renyiprivGpreS Σ} (e e' : expr) (σ σ' : state) n φ (α ρ : R) :
  1 <= α → 0 <= ρ ->
  (∀ `{renyiprivGS Σ}, ⊢ ⤇ e' -∗ ↯R (α, ρ) -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
  RDPcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ α ρ.
Proof.
  intros Halpha Hrho Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (ghost_map_alloc σ.(tapes_laplace)) as "[%γTL [Htl _]]".
  iMod spec_ra_init as (HspecGS) "(Hs & Hj & ?)".
  assert (Halpha' : 0 <= α) by lra.
  set α' := mknonnegreal _ Halpha'.
  set ρ' := mknonnegreal _ Hrho.
  iMod (rc_alloc α' ρ') as (?) "[HE He]"; [simpl; lra|].
  set (HrenyiprivGS := HeapG Σ _ _ _ γH γT HspecGS _).
  pose proof (wp_adequacy_step_fupdN α' ρ') as Hadeq. iApply Hadeq.
  iFrame "Hh Ht Hs HE".
  by iApply (Hwp with "[Hj] [He]").
  Unshelve. apply _.
Qed.

Theorem wp_adequacy Σ `{renyiprivGpreS Σ} (e e' : expr) (σ σ' : state) (α ρ : R) φ :
  1 <= α → 0 <= ρ ->
  (∀ `{renyiprivGS Σ}, ⊢  ⤇ e' -∗ ↯R (α , ρ) -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  RDPcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ α ρ.
Proof.
  intros ? ? Hwp.
  apply lim_exec_RDPcoupl; [done|done|].
  intros n.
  by eapply wp_adequacy_exec_n.
Qed.