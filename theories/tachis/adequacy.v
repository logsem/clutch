From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Export language.
From clutch.tachis Require Import expected_time_credits ert_weakestpre problang_wp.
From clutch.prob Require Import distribution.
Import uPred.

From Coquelicot Require Import Rcomplements Rbar Lim_seq.
Set Default Proof Using "Type*".

Section ERT.
  Context `{!Costfun prob_lang}.

  Fixpoint ERT k (ρ : cfg) : R :=
    let '(e, σ) := ρ in
    match k with
    | O => 0
    | S n =>
        match to_val e with
        | Some v => 0
        | None => cost e + SeriesC (λ ρ, prim_step e σ ρ * ERT n ρ)
        end
    end.

  Lemma ERT_Sn n e σ :
    to_val e = None →
    ERT (S n) (e, σ) = cost e + SeriesC (λ ρ, step (e, σ) ρ * ERT n ρ)%R.
  Proof. simpl. by intros ->. Qed.

  Lemma ERT_nonneg k eσ: 0<=ERT k eσ.
  Proof.
    revert eσ.
    induction k; simpl; intros []; first lra.
    case_match; first lra.
    apply Rplus_le_le_0_compat.
    - apply cost_nonneg.
    - apply SeriesC_ge_0'. intros. apply Rmult_le_pos; last done.
      auto.
  Qed.

  Definition lim_ERT (eσ:cfg) : Rbar:= Sup_seq (λ n, ERT n eσ).

  Lemma lim_ERT_bounded eσ k:
    (∀ n, ERT n eσ <= k) -> lim_ERT eσ <= k.
  Proof.
    intros Hbound.
    rewrite /lim_ERT.
    apply Rbar_le_fin.
    - etrans; last eapply (Hbound 0%nat). apply ERT_nonneg.
    - apply upper_bound_ge_sup. done.
  Qed.
  
End ERT.

Section adequacy.
  Context `{!tachisGS Σ f_cost}.

  Lemma step_fupd_fupdN_S n (P : iProp Σ) :  ((|={∅}▷=>^(S n) P) ⊣⊢ (|={∅}=> |={∅}▷=>^(S n) P))%I.
  Proof. iSplit; iIntros; simpl; iApply fupd_idemp; iFrame. Qed.

  Lemma ERM_erasure (e : expr) (σ : state) (n : nat) (x : nonnegreal) :
    to_val e = None →
    ERM e σ x
          (λ '(e2, σ2) (x' : nonnegreal),
             |={∅}▷=>^(S n) ⌜ERT n (e2, σ2) <= x'⌝)
    ⊢ |={∅}▷=>^(S n) ⌜ERT (S n) (e, σ) <= x⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /ERM /ERM'.
    set (Φ := (λ '((e1, σ1), x''),
                (⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                 ⌜ERT (S n) (e1, σ1) <= x''⌝)%I) :
           prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    set (F := (ERM_pre (λ '(e2, σ2) x',
                   |={∅}▷=>^(S n) ⌜ERT n (e2, σ2) <= x'⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iMod ("H" $! ((_, _)) with "Hfix [//]").
    }
    clear.
    iIntros "!#" ([[e1 σ1] x'']). rewrite /Φ/F/ERM_pre.
    iIntros " (%x2 & %Hred & (%r & %Hr) & %Hx'' & H) %Hv".
    - iApply step_fupdN_mono.
      { apply pure_mono.
        intros ψ. etrans. 2: apply Hx''.
        exact ψ. }
      clear Hx'' x''.
      rewrite ERT_Sn => //.
        simpl. fold cfg.
        iApply step_fupd_fupdN_S.
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".

       iApply (step_fupdN_mono _ _ _ (⌜(∀ e2 σ2, prim_step e1 σ1 (e2, σ2) > 0 → ERT n (e2, σ2) <= x2 (e2, σ2))⌝)).
       2: { iIntros (???) "/=".
            iMod ("H" with "[//]"); auto. }
       simpl. iIntros (?). iPureIntro.

       apply Rplus_le_compat_l.
       apply SeriesC_le.
       2:{ apply pmf_ex_seriesC_mult_fn. exists r. split; last naive_solver.
           apply cond_nonneg. }
       intros [e2 σ2].
       split.
       + apply Rmult_le_pos.
         1: auto.
         clear. revert e2 σ2. induction n.
         ++ done.
         ++ simpl. intros. destruct (to_val e2). 1: lra.
            assert (0 <= SeriesC (λ ρ : expr * state, prim_step e2 σ2 ρ * ERT n ρ)).
            2: {
              etrans. 1: eauto.
              rewrite -{1}(Rplus_0_l (SeriesC (λ ρ : expr * state, prim_step e2 σ2 ρ * ERT n ρ))).
              apply Rplus_le_compat_r. apply cost_nonneg. }
            apply SeriesC_ge_0'.
            intros.
            apply Rmult_le_pos.
            2: destruct x ; apply IHn.
            auto.
       + clear -H.
         destruct (decide (0 < prim_step e1 σ1 (e2, σ2))%R) as [Hgt | Hngt].
         * apply Rmult_le_compat_l => //.
           apply H. done.
         * destruct (decide (0 = prim_step e1 σ1 (e2, σ2))%R) as [Heq | Hneg].
           1: { rewrite -Heq. lra. }
           exfalso.
           opose proof (pmf_pos (prim_step e1 σ1) (e2, σ2)).
           lra.
  Qed.


  Lemma ERM_erasure_ast (e : expr) (σ : state) (n : nat) (* φ *) (x : nonnegreal) :
    to_val e = None →
    (∀ e, cost e = 1) →
    ERM e σ x
          (λ '(e2, σ2) (x' : nonnegreal),
            |={∅}▷=>^(S n) ⌜n <= x' + n * SeriesC (exec n (e2, σ2))⌝)
          ⊢ |={∅}▷=>^(S n) ⌜S n <= x + (S n) * SeriesC (exec (S n) (e, σ))⌝.
  Proof.
    iIntros (Hv Hcost) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /ERM /ERM'.
    set (Φ := (λ '((e1, σ1), x''),
                (⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                ⌜S n  <= x'' + (S n) * SeriesC (λ ρ, exec (S n) (e1, σ1) ρ)⌝)%I) :
           prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    set (F := (ERM_pre (λ '(e2, σ2) x',
                   |={∅}▷=>^(S n) ⌜n <= x' + n * SeriesC (λ ρ, exec n (e2, σ2) ρ)⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iMod ("H" $! ((_, _)) with "Hfix [//]").
    }
    clear e σ x Hv.
    iIntros "!#" ([[e1 σ1] x'']). rewrite /Φ/F/ERM_pre.
    (* iIntros " [ (%R & %x1 & %x2 & %Hred & (%r & %Hr) & % & %Hlift & H)|H] %Hv". *)
    iIntros " (%x2 & %Hred & (%r & %Hr) & %H0 & H) %Hv".
    iApply step_fupdN_mono.
    { apply pure_mono.
      intros ψ. etrans.
      2: apply Rplus_le_compat_r, H0.
      exact ψ. }
    clear H H0 x''.
    iApply (step_fupdN_mono _ _ _ (⌜(∀ e2 σ2, prim_step e1 σ1 (e2, σ2) > 0 → n <= x2 (e2, σ2) + n * SeriesC (exec n (e2, σ2)))⌝)).
    2: { iIntros (???) "/=".
         iMod ("H" with "[//]"); auto. }
    iIntros (H). iPureIntro.
    rewrite S_INR (Rplus_comm n) Rplus_assoc.
    rewrite Hcost.
    apply Rplus_le_compat_l.
    rewrite exec_Sn dbind_mass.
    rewrite -SeriesC_scal_l -SeriesC_plus /=.
    - transitivity (SeriesC (λ x : expr * state, prim_step e1 σ1 x * x2 x + n * (step_or_final (e1, σ1) x * SeriesC (exec n x))));
        last first.
      {
       apply SeriesC_le.
       + intros (e2 & σ2); split.
         * apply Rplus_le_le_0_compat.
           ** apply Rmult_le_pos; auto.
              apply cond_nonneg.
           ** apply Rmult_le_pos; [apply pos_INR | real_solver].
         * apply Rplus_le_compat_l.
           apply Rmult_le_compat_r; real_solver.
       + apply ex_seriesC_plus.
         * apply (ex_seriesC_le _ (λ x : expr * state, prim_step e1 σ1 x * r)).
           ** intro n0. pose proof (cond_nonneg (x2 n0)). split; real_solver.
           ** apply ex_seriesC_scal_r; auto.
         * apply ex_seriesC_scal_l.
           apply (ex_seriesC_le _ (λ x : expr * state, (step_or_final (e1, σ1) x) * 1)).
           ** intro. split; real_solver.
           ** apply ex_seriesC_scal_r; auto.
      }
      transitivity (SeriesC (λ x : expr * state, prim_step e1 σ1 x * (x2 x + n * SeriesC (exec n x)))); last first.
      { right.
        apply SeriesC_ext.
        intros (e2 & σ2).
        assert ((prim_step e1 σ1) = (step (e1, σ1))) as -> => //.
        assert ((step_or_final (e1, σ1)) = (step (e1, σ1))) as -> => //.
        - rewrite /step_or_final.
          rewrite to_final_None_1; auto.
        - rewrite Rmult_plus_distr_l.
          f_equal.
          rewrite -Rmult_assoc.
          rewrite (Rmult_comm _ n).
          rewrite Rmult_assoc //.
      }
      transitivity (SeriesC (λ x : expr * state, prim_step e1 σ1 x * n)); last first.
      {
        apply SeriesC_le.
        - intros (e2 & σ2); split.
          + apply Rmult_le_pos; auto.
            apply pos_INR.
          + destruct (decide (prim_step e1 σ1 (e2, σ2) > 0)) eqn:Haux.
            * apply Rmult_le_compat_l; auto.
            * assert (prim_step e1 σ1 (e2, σ2) = 0) as ->.
              ** pose proof (pmf_pos (prim_step e1 σ1) (e2, σ2)). lra.
              ** do 2 rewrite Rmult_0_l //.
        - eapply ex_seriesC_ext; [ intros; by rewrite Rmult_plus_distr_l | ].
          eapply ex_seriesC_plus.
          * apply (ex_seriesC_le _ (λ x : expr * state, prim_step e1 σ1 x * r)).
            ** intro n0. pose proof (cond_nonneg (x2 n0)). split; real_solver.
            ** apply ex_seriesC_scal_r; auto.
          * apply (ex_seriesC_le _ (λ x : expr * state, prim_step e1 σ1 x * n)).
            ** intros. pose proof (pos_INR n). real_solver.
            ** apply ex_seriesC_scal_r; auto.
       }
       rewrite SeriesC_scal_r.
       rewrite <- (Rmult_1_l n) at 1.
       right.
       f_equal.
       symmetry.
       clear - Hred.
       destruct Hred as ( (e2 & σ2) & Hρ).
       destruct (prim_step_iff e1 e2 σ1 σ2) as (Haux & ?).
       apply prim_step_mass; eauto.
    - apply (ex_seriesC_le _ (λ ρ : expr * state, prim_step e1 σ1 ρ * r)).
      + intro ρ'.
        pose proof (pmf_pos (prim_step e1 σ1) ρ').
        pose proof (cond_nonneg (x2 ρ')). real_solver.
      + apply ex_seriesC_scal_r; auto.
   - apply ex_seriesC_scal_l.
     apply (ex_seriesC_le _ (λ x : expr * state, step_or_final (e1, σ1) x * 1)); [ | apply ex_seriesC_scal_r; auto ].
     real_solver.
   Qed.

  Lemma ERM_erasure_correct (e : expr) (σ : state) (n : nat)  φ  (x : nonnegreal) :
    to_val e = None →
    ERM e σ x
          (λ '(e2, σ2) (x' : nonnegreal),
            |={∅}▷=>^(S n) ⌜∀ v, exec n (e2,σ2) v > 0 → φ v⌝)
    ⊢ |={∅}▷=>^(S n) ⌜∀ v, exec (S n) (e,σ) v > 0 → φ v⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /ERM /ERM'.
    set (Φ := (λ '((e1, σ1), x''),
                (⌜to_val e1 = None⌝ ={∅}▷=∗^(S n)
                 ⌜∀ v, exec (S n) (e1,σ1) v > 0 → φ v⌝)%I) :
           prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    set (F := (ERM_pre (λ '(e2, σ2) x',
                   |={∅}▷=>^(S n) ⌜∀ v, exec n (e2,σ2) v > 0 → φ v⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iMod ("H" $! ((_, _)) with "Hfix [//]").
    }
    clear.
    iIntros "!#" ([[e1 σ1] x'']). rewrite /Φ/F/ERM_pre.
    iIntros " (%x2 & %Hred & (%r & %Hr) & %Hx'' & H) %Hv".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ e2 σ2, prim_step e1 σ1 (e2, σ2) > 0 → ∀ v, exec n (e2, σ2) v> 0 → φ v)⌝)).
    2:{ iIntros (???). iMod ("H" with "[//]"); auto. }
    iPureIntro. simpl. rewrite Hv.
    intros H v Hexec. rewrite dbind_pos in Hexec.
    destruct Hexec as [[e σ] [Hexec Hprimstep]].
    naive_solver.
  Qed.

  Theorem wp_refRcoupl_step_fupdN (e : expr) (σ : state) (x : nonnegreal) n φ  :
    state_interp σ ∗ etc_supply x ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n ⌜ERT n (e, σ) <= x⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ x); iIntros "((Hσh & Hσt) & Hx & Hwp)".
    - simpl.
      iApply fupd_mask_intro; [set_solver|]; iIntros.
      iPureIntro. apply cond_nonneg.
    - iSimpl.
      destruct (to_val e) eqn:Heq.
      + iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iApply step_fupdN_intro; [done|]. do 4 iModIntro.
        iPureIntro.
        apply cond_nonneg.
      + rename n into m.
        assert ((prim_step e σ) = (step (e, σ))) as -> => //.
        rewrite -ERT_Sn => //.
        rewrite ert_wp_unfold /ert_wp_pre /= Heq -ERT_Sn => //.
        iMod ("Hwp" with "[$]") as "Hlift".
        iModIntro.
        iPoseProof
          (ERM_mono _
             (λ '(e2, σ2) x', |={∅}▷=>^(S m) ⌜ERT m (e2, σ2) <= x'⌝)%I
             _ _ _ x
            with "[] Hlift") as "H" ; first reflexivity.
        { iIntros ([] ?) "H !> !>".
          iMod "H" as "(Hstate & Herr_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        by iApply (ERM_erasure with "H").
  Qed.

  Theorem wp_refRcoupl_step_fupdN_ast (e : expr) (σ : state) (x : nonnegreal) n φ  :
    (∀ e, cost e = 1) →
    state_interp σ ∗ etc_supply x ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
      |={⊤,∅}=> |={∅}▷=>^n ⌜n <= x + n * SeriesC (exec n (e, σ))⌝.
  Proof.
    intro Hcost.
    iInduction n as [|n] "IH" forall (e σ x); iIntros "((Hσh & Hσt) & Hx & Hwp)".
    - simpl.
      iApply fupd_mask_intro; [set_solver|]; iIntros.
      iPureIntro. rewrite Rmult_0_l Rplus_0_r. apply cond_nonneg.
    - destruct (to_val e) eqn:Heq.
      + iSimpl.
        iApply fupd_mask_intro; [set_solver|]; iIntros "_".
        iApply step_fupdN_intro; [done|]. do 4 iModIntro.
        iPureIntro.
        rewrite Heq dret_mass Rmult_1_r.
        rewrite <- Rplus_0_l at 1.
        apply Rplus_le_compat_r.
        apply cond_nonneg.
      + rewrite ert_wp_unfold /ert_wp_pre.
        assert (language.to_val e = None) as ->; auto.
        iMod ("Hwp" with "[$]") as "Hlift".
        iModIntro.
        iPoseProof
          (ERM_mono _
             (λ '(e2, σ2) x', |={∅}▷=>^(S n) ⌜n <= x' + n * SeriesC (exec n (e2, σ2)) ⌝)%I
            with "[] Hlift") as "H".
        { reflexivity. }
        { iIntros ([] ?) "H !> !>".
          iMod "H" as "(Hstate & Herr_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        by iApply (ERM_erasure_ast).
  Qed.

  Theorem wp_refRcoupl_step_fupdN_correct (e : expr) (σ : state) (x : nonnegreal) n φ  :
    state_interp σ ∗ etc_supply x ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
      |={⊤,∅}=> |={∅}▷=>^n ⌜∀ v, exec n (e,σ) v > 0 → φ v⌝.
  Proof.
    iInduction n as [|n] "IH" forall (e σ x); iIntros "((Hσh & Hσt) & Hx & Hwp)".
    - simpl.
      destruct (to_val e) eqn:Hv.
      + apply of_to_val in Hv. subst.
        rewrite ert_wp_unfold /ert_wp_pre /=.
        iMod "Hwp" as "%H1".
        iApply fupd_mask_intro; [set_solver|]; iIntros.
        iPureIntro.
        intros ? H. apply dret_pos in H. naive_solver.
      + iApply fupd_mask_intro; [set_solver|]; iIntros.
        iPureIntro. intros ? H. rewrite /dzero /pmf in H. lra.
    - iSimpl.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq. subst.
        rewrite ert_wp_unfold /ert_wp_pre /=.
        iMod "Hwp" as "%H1".
        iApply fupd_mask_intro; [set_solver|]; iIntros.
        repeat iModIntro.
        iApply step_fupdN_intro; first done.
        iApply laterN_intro.
        iPureIntro.
        intros ? H. apply dret_pos in H. naive_solver.
      + rewrite ert_wp_unfold /ert_wp_pre /= Heq.
        iMod ("Hwp" with "[$]") as "Hlift".
        iPoseProof
          (ERM_mono _
             (λ '(e2, σ2) x', |={∅}▷=>^(S n) ⌜∀ v : val, exec n (e2,σ2) v > 0 → φ v⌝)%I
            with "[] Hlift") as "H".
        { reflexivity. }
        { simpl. iIntros ([] ?) "H !> !>".
          iMod "H" as "(Hstate & Herr_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        iPoseProof (ERM_erasure_correct with "[$H]") as "K"; first done.
        iModIntro. rewrite -step_fupdN_Sn.
        iApply (step_fupdN_mono with "[$]").
        iPureIntro. intros H v H'.
        apply (H v). simpl. rewrite Heq. done.
  Qed.

End adequacy.

Class tachisGpreS Σ := TachisGpreS {
  tachisGpreS_iris  :: invGpreS Σ;
  tachisGpreS_heap  :: ghost_mapG Σ loc val;
  tachisGpreS_tapes :: ghost_mapG Σ loc tape;
  tachisGpreS_etc   :: etcGpreS Σ;
}.

Definition tachisΣ (cost : Costfun prob_lang) : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    GFunctor (authR (nonnegrealUR))].
Global Instance subG_tachisGPreS (cost : Costfun prob_lang) {Σ} : subG (tachisΣ cost) Σ → tachisGpreS Σ.
Proof. solve_inG. Qed.

Section wp_ERT.
Context (costfun : Costfun prob_lang).

Theorem wp_ERT Σ `{tachisGpreS Σ} (e : expr) (σ : state) n (x : nonnegreal) φ :
  (∀ `{tachisGS Σ}, ⊢ ⧖ x -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ERT n (e, σ) <= x.
Proof.
  intros Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (etc_alloc) as (?) "[??]".
  set (HclutchGS := HeapG Σ _ _ _ _ γH γT _).
  iApply (wp_refRcoupl_step_fupdN).
  iFrame.
  iApply Hwp.
  done.
Qed.

Theorem wp_ERT_lim Σ `{tachisGpreS Σ} (e : expr) (σ : state) (x : nonnegreal) φ :
  (∀ `{tachisGS Σ}, ⊢ ⧖ x -∗ WP e {{ v, ⌜φ v⌝ }}) →
  lim_ERT (e, σ) <= x.
Proof.
  intros Hwp.
  apply lim_ERT_bounded. intros.
  by eapply wp_ERT.
Qed.

Theorem wp_ERT_ast Σ `{tachisGpreS Σ} (e : expr) (σ : state) (n : nat) (x : nonnegreal) φ :
  (∀ e, cost e = 1) →
  (∀ `{tachisGS Σ}, ⊢ ⧖ x -∗ WP e {{ v, ⌜φ v⌝ }}) →
  n <= x + n * SeriesC (exec n (e, σ)).
Proof.
  intros Hcost Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (etc_alloc) as (?) "[??]".
  set (HclutchGS := HeapG Σ _ _ _ _ γH γT _).
  iApply wp_refRcoupl_step_fupdN_ast; auto.
  iFrame.
  iApply Hwp.
  done.
Qed.

(** Finite expected mean => Almost sure termination *)

Theorem ERT_implies_AST e σ (x : nonnegreal) :
  (∀ (n : nat), n <= x + n * SeriesC (exec n (e, σ))) →
  SeriesC (lim_exec (e, σ)) = 1.
Proof.
  intro H.
  destruct x as (r & Hr); simpl in H.
  rewrite lim_exec_Sup_seq.
  apply eq_rbar_finite'.
  apply Lim_seq.is_sup_seq_unique.
  intro eps; split.
  - intro n; simpl.
    apply (Rle_lt_trans _ 1); auto.
    destruct eps; simpl.
    lra.
  - simpl.
    assert (exists m:nat, 1 - eps < 1 - (r / (m + 1))) as (m & Hm); last first.
    + exists (m + 1)%nat.
      eapply Rlt_le_trans; [apply Hm |].
      specialize (H (m+1)%nat).
      (* Should follow from H *)
      rewrite plus_INR /= in H.
      pose proof (pos_INR m).
      apply (Rmult_le_reg_l (m+1)); [lra |].
      rewrite Rmult_minus_distr_l Rmult_1_r.
      replace ((m + 1) * (r / (m + 1))) with r; first by lra.
      rewrite /Rdiv.
      rewrite Rmult_comm Rmult_assoc.
      rewrite Rinv_l; lra.
    + (* Pick m to be the ceil of r/eps *)
      destruct eps as (eps & Heps); simpl.
      assert (exists m : nat, (m + 1) > r / eps) as (m & Hm).
      {
        destruct (INR_unbounded (r / eps)) as (k & Hk).
        exists k; lra.
      }
      exists m.
      apply Rgt_lt in Hm.
      assert (r / (m + 1) < eps); last by lra.
      apply Rcomplements.Rlt_div_l in Hm; last by lra.
      apply Rcomplements.Rlt_div_l; last by lra.
      pose proof (pos_INR m). lra.
Qed.

Theorem wp_ERT_ast' Σ `{tachisGpreS Σ} (e : expr) (σ : state) (n : nat) (x : nonnegreal) φ :
  (∀ e, cost e = 1) →
  (∀ `{tachisGS Σ}, ⊢ ⧖ x -∗ WP e {{ v, ⌜φ v⌝ }}) →
  SeriesC (lim_exec (e, σ)) = 1.
Proof.
  intros. eapply ERT_implies_AST.
  intros. eapply wp_ERT_ast; done.
Qed.

(** wp correct*)
Theorem wp_correct Σ `{tachisGpreS Σ} (e : expr) (σ : state) (n : nat) (x : nonnegreal) φ :
  (∀ `{tachisGS Σ}, ⊢ ⧖ x -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ∀ v, exec n (e, σ) v > 0 → φ v.
Proof using costfun.
  intros Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (etc_alloc) as (?) "[??]".
  set (HclutchGS := HeapG Σ _ _ _ _ γH γT _).
  iApply wp_refRcoupl_step_fupdN_correct; auto.
  iFrame.
  iApply Hwp.
  done.
Qed.

Local Lemma exec_lim_exec_pos (e : expr) (σ : state) (φ : val → Prop) :
  (∀ v n, exec n (e, σ) v > 0 → φ v) →
  ∀ v, lim_exec (e, σ) v > 0 → φ v.
Proof. intros H v [n Hexec]%lim_exec_pos. naive_solver. Qed.

Theorem wp_correct_lim Σ `{tachisGpreS Σ} (e : expr) (σ : state) (n : nat) (x : nonnegreal) φ :
  (∀ `{tachisGS Σ}, ⊢ ⧖ x -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ∀ v, lim_exec (e, σ) v > 0 → φ v.
Proof using costfun.
  intros H'. apply exec_lim_exec_pos.
  intros.
  eapply wp_correct; done.
Qed.

End wp_ERT.
