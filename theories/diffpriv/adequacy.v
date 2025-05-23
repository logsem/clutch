From iris.proofmode Require Import base proofmode.
From iris.bi Require Import weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Import language.
From clutch.base_logic Require Import error_credits.
From clutch.diffpriv Require Import weakestpre primitive_laws diffpriv_rules.
From clutch.prob Require Import differential_privacy distribution couplings_exp.
Import uPred.


Section adequacy.
  Context `{!diffprivGS Σ}.

  Lemma wp_adequacy_spec_coupl n m e1 σ1 e1' σ1' Z φ ε :
    spec_coupl ∅ σ1 e1' σ1' ε Z -∗
    (∀ σ2 e2' σ2' ε', Z σ2 e2' σ2' ε' ={∅}=∗ |={∅}▷=>^n ⌜Mcoupl (exec m (e1, σ2)) (lim_exec (e2', σ2')) φ ε'⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜Mcoupl (exec m (e1, σ1)) (lim_exec (e1', σ1')) φ ε⌝.
  Proof.
    iRevert (σ1 e1' σ1' ε).
    iApply spec_coupl_ind.
    iIntros "!>" (σ1 e1' σ1' ε) "[boo|(%T & %k & %μ1 & %μ1' & %ε' & %X2 & % & % & %Hμ1 & %Hμ1' & H)] HZ" ;
      [by iMod ("HZ" with "[$]") |].
    iApply (step_fupdN_mono _ _ _ ⌜_⌝).
    { iPureIntro. intros h. eapply Mcoupl_erasure_erasable_rhs. 5: apply h. all: eauto. }
    iIntros (σ2 (e2', σ2') HT).
    iMod ("H" with "[//]") as "[H _]".
    by iApply "H".
  Qed.

  Lemma wp_adequacy_prog_coupl n m e1 σ1 e1' σ1' Z φ ε :
    to_val e1 = None ->
    prog_coupl e1 σ1 e1' σ1' ε Z -∗
    (∀ e2 σ2 e2' σ2' ε', Z e2 σ2 e2' σ2' ε' ={∅}=∗ |={∅}▷=>^n ⌜Mcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε'⌝) -∗
    |={∅}=> |={∅}▷=>^n ⌜Mcoupl (exec (S m) (e1, σ1)) (lim_exec (e1', σ1')) φ ε⌝.
  Proof.
    iIntros (Hnone).
    rewrite exec_Sn.
    rewrite /step_or_final /= Hnone.
    iIntros "(%R & %k & %μ1' & %ε1 & %X2 & % & % & % & % & Hcnt) Hcoupl /=".
    iApply (step_fupdN_mono _ _ _ ⌜_⌝).
    { iPureIntro. intros. eapply Mcoupl_erasure_erasable_lhs'. 5: by eauto. all: eauto. }
    iIntros (e2 σ2 e2' σ2' ε2).
    iMod ("Hcnt" with "[//]") as "Hcnt".
    by iApply "Hcoupl".
  Qed.

  Lemma wp_adequacy_val_fupd (e e' : expr) (σ σ' : state) n φ v ε:
    to_val e = Some v →
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε ∗
    WP e {{ v, ∃ v' : val, ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤, ∅}=> ⌜Mcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε⌝.
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
    iPureIntro. by eapply Mcoupl_dret.
  Qed.

  Lemma wp_adequacy_step_fupdN ε (e e' : expr) (σ σ' : state) n φ :
    state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε ∗
    WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜Mcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε⌝.
  Proof.
    iIntros "(Hσ & HspecI_auth & Hε & Hwp)".
    iInduction n as [|n] "IH" forall (e σ e' σ' ε).
    { destruct (to_val e) eqn:He.
      - iMod (wp_adequacy_val_fupd with "[$]") as %?; [done|].
        by iApply step_fupdN_intro.
      - iApply fupd_mask_intro; [done|]; iIntros "_ /=".
        iPureIntro. rewrite He.
        by apply Mcoupl_dzero.
    }
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

Lemma wp_adequacy_exec_n Σ `{!diffprivGpreS Σ} (e e' : expr) (σ σ' : state) n φ (ε : R) :
  0 <= ε →
  (∀ `{diffprivGS Σ}, ⊢ ⤇ e' -∗ ↯ ε -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }}) →
  Mcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros Heps Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod spec_ra_init as (HspecGS) "(Hs & Hj & ?)".
  set ε' := mknonnegreal _ Heps.
  iMod (ec_alloc ε') as (?) "[HE He]".
  set (HdiffprivGS := HeapG Σ _ _ _ γH γT HspecGS _).
  iApply (wp_adequacy_step_fupdN ε').
  iFrame "Hh Ht Hs HE".
  by iApply (Hwp with "[Hj] [He]").
Qed.

Theorem wp_adequacy Σ `{diffprivGpreS Σ} (e e' : expr) (σ σ' : state) (ε : R) φ :
  0 <= ε →
  (∀ `{diffprivGS Σ}, ⊢  ⤇ e' -∗ ↯ ε -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  Mcoupl (lim_exec (e, σ)) (lim_exec (e', σ')) φ ε.
Proof.
  intros ? Hwp.
  apply lim_exec_Mcoupl; [done|].
  intros n.
  by eapply wp_adequacy_exec_n.
Qed.

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

Corollary wp_adequacy_mass Σ `{!diffprivGpreS Σ} (e e' : expr) (σ σ' : state) φ (ε : R) :
  0 <= ε →
  (∀ `{diffprivGS Σ}, ⊢  ⤇ e' -∗ ↯ ε -∗ WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ) →
  SeriesC (lim_exec (e, σ)) <= exp ε * SeriesC (lim_exec (e', σ')).
Proof.
  intros ? Hwp. eapply Mcoupl_mass_leq. by eapply wp_adequacy.
Qed.

Corollary wp_diffpriv_Z Σ `{diffprivGpreS Σ} (e : expr) (σ σ' : state) (ε : R) :
  0 <= ε →
  (∀ x y, (IZR (Z.abs (x - y)) <= 1) →
          ∀ `{diffprivGS Σ}, ⊢ ⤇ e #y -∗ ↯ ε -∗ WP e #x {{ v, ∃ v', ⤇ Val v' ∗ ⌜v = v'⌝ }})
  →
    diffpriv_pure (λ x y, IZR (Z.abs (x - y))) (λ x, (lim_exec (e #x, σ))) ε.
Proof.
  intros Hε Hwp. apply Mcoupl_diffpriv.
  intros. eapply wp_adequacy.
  1: eauto. 1: apply Hε.
  intros. apply Hwp. done.
Qed.

(* hoare_diffpriv implies pure diffpriv *)
Fact hoare_diffpriv_pure f ε (εpos : (0 < ε)%R) :
  (∀ `{diffprivGS Σ}, ⊢ hoare_diffpriv f ε dZ)
  →
    ∀ σ,
    diffpriv_pure
      (λ x y, IZR (Z.abs (x - y)))
      (λ x, lim_exec (f #x, σ))
      ε.
Proof.
  intros hwp ?.
  eapply (wp_diffpriv_Z diffprivΣ) ; eauto ; try lra.
  iIntros (????) "f' ε".
  tp_bind (f _).
  iApply (hwp with "[] [$f' ε]").
  2: erewrite Rmult_1_l ; iFrame.
  1: rewrite /dZ /= -abs_IZR //.
  iNext. iIntros. iExists _. eauto.
Qed.
