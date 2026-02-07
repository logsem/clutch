From iris.proofmode Require Import base proofmode.
From iris.bi Require Import lib.fixpoint_mono big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Import language.
From clutch.base_logic Require Import error_credits.
From clutch.diffpriv Require Import weakestpre primitive_laws diffpriv_rules.
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
      "[boo|(%T & %μ1 & %μ1' & %ε1 & %δ1 & %ε2 & %δ2 & % & % & % & %Hμ1 & %Hμ1' & H)] HZ";
      [by iMod ("HZ" with "[$]") |].
    iApply (step_fupdN_mono _ _ _ ⌜_⌝).
    { iPureIntro. intros h. eapply DPcoupl_erasure_rewritable_rhs. 8: apply h. all: eauto. }
    iIntros (σ2 (e2', σ2') HT).
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
    iIntros "(%P & %R & %R' & %k & %μ1' & %ε1 & % & % & % & % & % & % & % & % & % & % & % & % & % & % & Hcnt) Hcoupl /=".


    (*
    set (Q := ∀ (e2 : expr) (σ2 : state) (e2' : expr) (σ2' : state),
            ⌜((P (e2, σ2) /\ R (e2, σ2) (e2', σ2')) → DPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε2 δ2)⌝ ∗
            ⌜((¬P (e2, σ2) /\ R' (e2, σ2) (e2', σ2')) → DPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε2' δ2') ⌝
        )%I.
    *)
    iApply (step_fupdN_mono _ _ _
              (∀ (e2 : expr) (σ2 : state) (e2' : expr) (σ2' : state),
                  ⌜((P (e2, σ2) /\ R (e2, σ2) (e2', σ2')) → DPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε2 δ2)⌝ ∗
                    ⌜((¬P (e2, σ2) /\ R' (e2, σ2) (e2', σ2')) → DPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε2' δ2) ⌝)
           ).
    { iPureIntro. simpl. intros.
      eapply (DPcoupl_erasure_erasable_lhs_choice _ _ _ _ _ _ _ _ _ _ _ _ _ _ P).
      9: apply H1.
      9: apply H2.
      all: eauto.
      - intros.
        destruct (H7 e2 σ2 e2' σ2').
        by apply H9.
      - intros.
        destruct (H7 e2 σ2 e2' σ2').
        by apply H10.
    }
    iIntros (e2 σ2 e2' σ2').
    iDestruct ("Hcnt" $! e2 σ2 e2' σ2') as "[Hcnt1  Hcnt2]".
    destruct (decide (P (e2, σ2))).
    - iApply (step_fupdN_mono _ _ _
                  ⌜((P (e2, σ2) /\ R (e2, σ2) (e2', σ2')) → DPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε2 δ2)⌝).
      {
        iIntros (?).
        iSplit; auto.
        iIntros ((?&?)).
        done.
      }
      iIntros ((?&?)).
      iMod ("Hcnt1" with "[//]") as "Hcnt1".
      by iApply "Hcoupl".
    - iApply (step_fupdN_mono _ _ _
                  ⌜((¬P (e2, σ2) /\ R' (e2, σ2) (e2', σ2')) → DPcoupl (exec m (e2, σ2)) (lim_exec (e2', σ2')) φ ε2' δ2)⌝).
      {
        iIntros (?).
        iSplit; auto.
        iIntros ((?&?)).
        done.
      }
      iIntros ((?&?)).
      iMod ("Hcnt2" with "[//]") as "Hcnt2".
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
    iApply (wp_adequacy_step_fupdN ε' δ').
    iFrame "Hh Ht Htl Hs HE HD".
    by iApply (Hwp with "[Hj] [He] [Hd]").
  - iApply fupd_mask_intro; [done|]; iIntros "_".
    iApply step_fupdN_intro; [done|]; iModIntro.
    iPureIntro. by apply DPcoupl_1.
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
