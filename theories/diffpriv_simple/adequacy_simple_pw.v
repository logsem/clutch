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
From clutch.diffpriv_simple Require Import weakestpre_simple_pw_again weakestpre_simple_prob_lang_resources_pw.
From clutch.prob Require Import differential_privacy distribution couplings_dp.
Import uPred.

(* Local Open Scope R.


      Definition wp_pre'
        `{!spec_updateGS (lang_markov prob_lang) Σ, !diffprivWpGS prob_lang Σ, !specG_prob_lang Σ}
        (* `{!diffprivGS Σ} *)
          (wp : coPset -d> expr -d> (val -d> iPropO Σ) -d> iPropO Σ) :
           coPset -d> expr -d> (val -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
        (match to_val e1 with
         | Some v => |={E}=> Φ v
         | None =>
             ∀ σ1 e1' σ1' ε δ,
               state_interp σ1 ∗ spec_interp (e1', σ1') ∗ err_interp ε δ ={E,∅}=∗
               ⌜reducible (e1, σ1)⌝ ∗
               (* do good things happen if we require S to be reflexive? *)
               ∃ (S : cfg → cfg → Prop) (ε1 ε2 δ1 δ2 : nonnegreal) (k : nat),
                 ⌜DPcoupl (prim_step e1 σ1) (pexec k (e1', σ1')) S ε1 δ1⌝ ∗
                  ⌜ε1 + ε2 <= ε⌝ ∗ ⌜δ1 + δ2 <= δ⌝ ∗
                  (∀ e2 σ2 e2' σ2',

                      (* (⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗
                          ▷ |={∅,E}=>  (state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 δ2 ∗ wp E e2 Φ))) *)


                      (⌜S (e2, σ2) (e2', σ2')⌝ ={∅}=∗
                       (▷ (|={∅,⊤}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 δ2 ∗ wp E e2 Φ))
                       ∨
                         (∃ δ2' : val → nonnegreal, (⌜(∀ RES, 0 <= δ2' RES) ∧ ex_seriesC δ2' ∧ nonneg δ2 = SeriesC δ2'⌝ ∗ ▷ |={∅,⊤}=>
                            ∀ RES : val, state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 (δ2' RES) ∗
                            wp E e2 (λ v, ∃ v' : val, ⤇ (of_val v') ∗ ⌜v = RES → v' = RES⌝)))
                       (* ∨
                            (▷ |={∅,⊤}=>
                               state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 δ2 ∗
                               ∀ RES : val, WP e2 {{ v, ∃ v' : val, ⤇ (of_val v') ∗ ⌜v = RES → v' = RES⌝ }}) *)
                      ))

            end)%I.


   Local Instance wp_pre_contractive `{!spec_updateGS (lang_markov prob_lang) Σ, !diffprivWpGS prob_lang Σ, !specG_prob_lang Σ} :
     Contractive wp_pre'.
   Proof.
     rewrite /wp_pre' /= => n wp wp' Hwp E e1 Φ.
     do 40 f_equiv. 2: do 3 f_equiv. all: f_contractive. all: repeat f_equiv ; apply Hwp.
   Qed.

   Local Definition wp_def' `{!spec_updateGS (lang_markov prob_lang) Σ, !diffprivWpGS prob_lang Σ, !specG_prob_lang Σ} :
     Wp (iProp Σ) (expr) (val) () :=
     {| wp := λ _ : (), fixpoint (wp_pre'); wp_default := () |}.
   Local Definition wp_aux : seal (@wp_def'). Proof. eexists. simpl. Qed.
   Definition wp' := wp_aux.(unseal).
   Global Arguments wp' {Λ Σ _}.
   Global Existing Instance wp'.
   Local Lemma wp_unseal `{!spec_updateGS (lang_markov Λ) Σ, !diffprivWpGS Λ Σ} : wp =
     (@wp_def Λ Σ _ _).(wp).
   Proof. rewrite -wp_aux.(seal_eq) //. Qed.

   Section wp.
   Context `{!spec_updateGS (lang_markov Λ) Σ, !diffprivWpGS Λ Σ}.
   Implicit Types P : iProp Σ.
   Implicit Types Φ : val Λ → iProp Σ.
   Implicit Types v : val Λ.
   Implicit Types e : expr Λ.
   Implicit Types σ : state Λ.
   Implicit Types ρ : cfg Λ.

   (* Weakest pre *)
   Lemma wp_unfold E e Φ s :
     WP e @ s; E {{ Φ }} ⊣⊢ wp_pre (wp (PROP:=iProp Σ) s) E e Φ.
   Proof. rewrite wp_unseal. apply (fixpoint_unfold wp_pre). Qed.

   Global Instance wp_ne E e n s :
     Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
   Proof.
     revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
     rewrite !wp_unfold /wp_pre /=.
     do 39 f_equiv.
     f_contractive_fin.
     do 2 f_equiv. rewrite IH ; [done | lia |].
     intros ?. apply dist_S, HΦ.
   Qed.
   Global Instance wp_proper E e s :
     Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
   Proof.
     by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
   Qed.
   Global Instance wp_contractive E e n s :
     TCEq (to_val e) None →
     Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
   Proof.
     intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
     do 38 f_equiv.
     f_contractive.
     repeat f_equiv.
   Qed. *)


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

  (* Lemma wp_adequacy_step_fupdN n : ∀ ε δ (e e' : expr) (σ σ' : state) φ,
       state_interp σ ∗ spec_interp (e', σ') ∗ err_interp ε δ ∗
       WP e {{ v, ∃ v', ⤇ Val v' ∗ ⌜φ v v'⌝ }} ⊢
       |={⊤,∅}=> |={∅}▷=>^n ⌜DPcoupl (exec n (e, σ)) (lim_exec (e', σ')) φ ε δ⌝.
     Proof.
       iInduction n as [|n] "IH" ; iIntros (ε δ e e' σ σ' φ) ;
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
       iEval (rewrite wp_unfold /wp_pre He) in "Hwp".
       (* from the assumption Hwp (and the State/Spec/Err interp) we get that... *)
       (* - there is a R-coupling HCR for the next prim_step and k rhs-steps *)
       (* - the recursive WP holds later after stepping *)
       iMod ("Hwp" with "[$]") as "(%red & %R & % & % & % & % & %k & %HCR & %hε & %hδ & Hrec)".
       (* rewrite the execution in the goal into dbinds *)
       rewrite exec_Sn /step_or_final ; iSimpl ; rewrite He. rewrite (lim_exec_pexec k).
       (* bind the coupling HCR *)
       iApply (step_fupdN_mono _ _ _ ⌜∀ ρ ρ', R ρ ρ' → DPcoupl (exec n ρ) (lim_exec ρ') φ ε2 δ2⌝).
       { iPureIntro. intros. eapply DPcoupl_dbind'' ; eauto. }
       rewrite -step_fupdN_Sn. iIntros ([e2 σ2] [e2' σ2'] HR).
       iSpecialize ("Hrec" $! _ _ _ _ HR).
       iMod "Hrec". iSimpl ; iIntros "!> !> !>".
       (* we get the coupling for the remaining n steps from IH with Hrec. *)
       iMod "Hrec" as "(HT & S & E & Hwp)". iApply ("IH" with "[$]").
     Qed. *)


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

    (* eassert ((@wp_pre prob_lang Σ _ _) = (@wp_pre' Σ _ _ _)) as h by admit.
       iEval (rewrite h /wp_pre') in "Hwp". *)

    iEval (rewrite /wp_pre He) in "Hwp".

    (* from the assumption Hwp (and the State/Spec/Err interp) we get that...
       - there is a R-coupling HCR for the next prim_step and k rhs-steps
       - the recursive WP holds later after stepping *)
    iMod ("Hwp" with "[$]") as "(%red & %R & % & % & % & % & %k & %HCR & %hε & %hδ & Hrec)".
    (* rewrite the execution in the goal into dbinds *)
    rewrite exec_Sn /step_or_final ; iSimpl ; rewrite He. rewrite (lim_exec_pexec k).
    (* bind the coupling HCR *)
    iApply (step_fupdN_mono _ _ _ ⌜∀ ρ ρ', R ρ ρ' → DPcoupl (exec n ρ) (lim_exec ρ') φ ε2 δ2⌝).
    { iPureIntro. intros. eapply DPcoupl_dbind'' ; eauto. }
    rewrite -step_fupdN_Sn. iIntros ([e2 σ2] [e2' σ2'] HR).
    iSpecialize ("Hrec" $! e2 σ2 e2' σ2').
    assert (∀ x y, eq x y → φ x y) as φpw. { clear -φrefl. intros ?? ->. apply φrefl. }

    set (pweq_res (RES : val) := (λ v v', v = RES → v' = RES)).


    (* iAssert (⌜R (e2, σ2) (e2', σ2')⌝ ={∅}=∗
                (▷ (|={∅,⊤}=> state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 δ2 ∗ WP e2 {{ v, ∃ v' : val, ⤇ v' ∗ ⌜φ v v'⌝ }}))
                ∨
                  (▷ |={∅,⊤}=>
                     state_interp σ2 ∗ spec_interp (e2', σ2') ∗ err_interp ε2 δ2 ∗
                     ∀ RES : val, WP e2 {{ v, ∃ v' : val, ⤇ v' ∗ ⌜pweq_res RES v v'⌝ }}))%I with "[-]" as "-#Hrec" ; [admit|]. *)

    iMod ("Hrec" $! HR) as "[Hrec | pw]" ; iSimpl ; iIntros "!>!>!>".
    - iMod "Hrec" as "(HT & S & E & Hwp)". iApply ("IH" with "[] [$]").
      1: done.
    -
      iDestruct "pw" as "(%δ2' & (%hpos & %hex & %hδ2) & pw)".
      iApply (step_fupdN_mono _ _ _ ⌜∀ RES, DPcoupl (exec n (e2, σ2)) (lim_exec (e2', σ2')) (pweq_res RES) ε2 (δ2' RES)⌝).
      { iPureIntro. rewrite hδ2. intros PWCPL.
        eapply DPcoupl_mono ; last first. 4: apply φpw.
        1: eapply DPcoupl_pweq ; last first. 1: eapply PWCPL.
        all: eauto. 1: apply cond_nonneg. 1,2: right ; reflexivity.
      }
      iIntros (RES).
      iMod "pw". iDestruct ("pw" $! RES) as "(HT & S & (ε & δ) & pw)".
      iApply ("IH" $! ε2 (δ2' RES) e2 e2' σ2 σ2' (pweq_res RES) with "[%] [$]").
      intros v hv. exact hv.
  Qed.



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
