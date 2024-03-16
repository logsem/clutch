From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.prob_lang Require Import erasure notation.
From clutch.common Require Export language.
From clutch.ert_logic Require Import expected_time_credits ert_weakestpre problang_wp.
From clutch.prob Require Import distribution.
Import uPred.

Fixpoint ERT k (eσ : lang.cfg) : R :=
  match k with
  | O => 0
  | S n =>
      match to_val eσ.1 with
      | Some v => nnreal_zero
      | None => 1 + SeriesC (λ ρ, prim_step eσ.1 eσ.2 ρ * ERT n ρ)
      end
  end.

Lemma ERT_Sn n e σ :
  to_val e = None →
  ERT (S n) (e, σ) = 1 + SeriesC (λ ρ, step (e, σ) ρ * ERT n ρ)%R.
Proof. simpl. by intros ->. Qed.

Section adequacy.
  Context `{!ert_clutchGS Σ}.

  Lemma step_fupd_fupdN_S n (P : iProp Σ) :  ((|={∅}▷=>^(S n) P) ⊣⊢ (|={∅}=> |={∅}▷=>^(S n) P))%I.
  Proof. iSplit; iIntros; simpl; iApply fupd_idemp; iFrame. Qed.

(*
  Lemma ub_lift_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜ 0 <= ε ⌝ -∗
    ⌜ 0 <= ε' ⌝ -∗
    ⌜ub_lift μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ ={∅}▷=∗^(S n) ⌜ub_lift (f a) T ε'⌝) -∗
    |={∅}▷=>^(S n) ⌜ub_lift (dbind f μ) T (ε + ε')⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → ub_lift (f a) T ε')⌝)).
    { iIntros (?). iPureIntro. eapply ub_lift_dbind; eauto. }
    iIntros (???) "/=".
    iMod ("H" with "[//]"); auto.
  Qed.
*)


  (* Lemma foo (e1 : expr) (σ1 : state) (n : nat) (x2 : (language.cfg prob_lang) -> nonnegreal)
     (r : R)
     (Hr : ∀ ρ : language.cfg prob_lang, x2 ρ <= r)
     (Hv : to_val e1 = None)
     :
     ((∀ (e2 : expr) (σ2 : state),
          ⌜prim_step e1 σ1 (e2, σ2) > 0⌝ ={∅}=∗
          |={∅}▷=> |={∅}▷=>^n ⌜ERT n (e2, σ2) <= x2 (e2, σ2)⌝)
      ⊢
        |={∅}▷=>^(S n)
          ⌜1 + SeriesC (λ ρ : cfg, (prim_step e1 σ1 ρ * ERT n ρ)%R) <=
             1 + SeriesC (λ ρ : cfg, (prim_step e1 σ1 ρ * x2 ρ)%R)⌝)%I. *)



  (* Lemma ub_lift_dbind_adv' `{Countable A, Countable A'}
       (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
       ⌜ 0 <= ε ⌝ -∗
       ⌜ exists r, forall a, 0 <= ε' a <= r ⌝ -∗
       ⌜ub_lift μ R ε⌝ -∗
       (∀ a , ⌜R a⌝ ={∅}▷=∗^(S n) ⌜ub_lift (f a) T (ε' a)⌝) -∗
       |={∅}▷=>^(S n) ⌜ub_lift (dbind f μ) T (ε + SeriesC (λ a : A, (μ a * ε' a)%R))⌝ : iProp Σ.
     Proof.
       iIntros (???) "H".
       iApply (step_fupdN_mono _ _ _ (⌜(∀ a b, R a → ub_lift (f a) T (ε' a))⌝)).
       { iIntros (?). iPureIntro. eapply ub_lift_dbind_adv; eauto. }
       iIntros (???) "/=".
       iMod ("H" with "[//]"); auto.
     Qed. *)

  Lemma ERM_erasure (e : expr) (σ : state) (n : nat) (* φ *) (x : nonnegreal) :
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
    (* iIntros " [ (%R & %x1 & %x2 & %Hred & (%r & %Hr) & % & %Hlift & H)|H] %Hv". *)
    iIntros " (%x2 & %Hred & (%r & %Hr) & % & H) %Hv".
    - iApply step_fupdN_mono.
      { apply pure_mono.
        intros ψ. etrans. 2: apply H.
        exact ψ. }
      clear H x''.
      rewrite ERT_Sn => //.
      (* iApply ub_lift_dbind_adv'.
         + iPureIntro; apply cond_nonneg.
         + iPureIntro. exists r. split; auto. apply cond_nonneg.
         + done.
         + iIntros ([] ?). *)
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
              apply Rplus_le_compat_r. lra.
            }
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
      + rewrite ert_wp_unfold /ert_wp_pre /= Heq.
        iMod ("Hwp" with "[$]") as "Hlift".
        iModIntro.
        iPoseProof
          (ERM_mono _
             (λ '(e2, σ2) x', |={∅}▷=>^(S n) ⌜ERT n (e2, σ2) <= x'⌝)%I
            with "[] Hlift") as "H".
        { reflexivity. }
        { iIntros ([] ?) "H !> !>".
          iMod "H" as "(Hstate & Herr_auth & Hwp)".
          iMod ("IH" with "[$]") as "H".
          iModIntro. done. }
        assert ((prim_step e σ) = (step (e, σ))) as -> => //.
        rewrite -ERT_Sn => //.
        by iApply (ERM_erasure with "H").
  Qed.

End adequacy.

Class ert_clutchGpreS Σ := ERT_ClutchGpreS {
  ert_clutchGpreS_iris  :: invGpreS Σ;
  ert_clutchGpreS_heap  :: ghost_mapG Σ loc val;
  ert_clutchGpreS_tapes :: ghost_mapG Σ loc tape;
  ert_clutchGpreS_etc   :: etcGpreS Σ;
}.

Definition ert_clutchΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc tape;
    GFunctor (authR (nonnegrealUR))].
Global Instance subG_ert_clutchGPreS {Σ} : subG ert_clutchΣ Σ → ert_clutchGpreS Σ.
Proof. solve_inG. Qed.

Theorem wp_ERT Σ `{ert_clutchGpreS Σ} (e : expr) (σ : state) n (x : nonnegreal) φ :
  (∀ `{ert_clutchGS Σ}, ⊢ ⧖ x -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ERT n (e, σ) <= x.
Proof.
  intros Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht _]]".
  iMod (etc_alloc) as (?) "[??]".
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  iApply wp_refRcoupl_step_fupdN.
  iFrame.
  iApply Hwp.
  done.
Qed.

(** Finite expected mean => Almost sure termination *)

Theorem mass_le_1_implies_growing_ert e σ (n:nat) ε:
  0<ε<=1->
  SeriesC(λ x, lim_exec (e, σ) x) = 1 - ε ->
  (n*ε)%R <= ERT n (e, σ).
Proof.
  intros Hε Hlim.
  assert (SeriesC (λ x, exec n (e,σ) x) <= 1 - ε) as Hexec.
  { rewrite -Hlim. apply SeriesC_le; last auto.
    intros; split; auto.
    rewrite /lim_exec/lim_distr{2}/pmf.
    apply rbar_le_finite; first apply is_finite_Sup_seq_exec.
    etrans; last first.
    - apply sup_is_upper_bound.
    - done.
  }
  clear Hlim.
  induction n.
  - simpl.
    lra.
  - replace (S n * ε) with (ε + n * ε); last first.
    { rewrite S_INR. lra. } 
    trans (ε + ERT n (e, σ)).
    { apply Rplus_le_compat_l. apply IHn.
      etrans; last apply Hexec. apply SeriesC_le; auto.
      intros; split; auto.
      apply exec_mono.
    }
Admitted.

Theorem finite_ert_implies_ast r e σ:
  (∀ n, ERT n (e, σ) <= r) ->
  SeriesC(λ x, lim_exec (e, σ) x) = 1.
Proof.
  intros H.
  epose proof pmf_SeriesC (lim_exec (e, σ)).
  pose proof Rle_or_lt 1 (SeriesC(λ x, lim_exec (e, σ) x)) as [|].
  { by apply Rle_antisym. }
  exfalso.
  set (ε := 1 - SeriesC (lim_exec (e, σ)) ).
  assert (0<ε<=1) as Hε.
  { epose proof pmf_SeriesC_ge_0 (lim_exec(e, σ)).
    split; rewrite /ε.
    - rewrite -Rcomplements.Rminus_lt_0. done.
    - rewrite Rcomplements.Rle_minus_l.
      assert (1=1+0) as K by lra.
      rewrite {1}K.
      apply Rplus_le_compat_l. done.
  }
  assert (∃ n:nat, r<n*ε) as [n?].
  { exists (S(Z.to_nat (up(r/ε)))).
    rewrite -Rcomplements.Rlt_div_l; last lra.
    rewrite S_INR.
    rewrite -{1}(Rplus_0_r (r/ε)).
    apply Rplus_le_lt_compat; try lra.
    admit.
  }
  epose proof mass_le_1_implies_growing_ert e σ n ε Hε _.
  specialize (H n).
  eapply Rle_not_gt; first exact H.
  apply Rlt_gt.
  eapply Rlt_le_trans; exact.
  Unshelve.
  rewrite /ε. rewrite Rminus_def. rewrite Ropp_minus_distr.
  rewrite Rplus_minus. done.
Admitted.
  
Theorem wp_ast Σ `{ert_clutchGpreS Σ} (e : expr) (σ : state) (x : nonnegreal) φ :
  (∀ `{ert_clutchGS Σ}, ⊢ ⧖ x -∗ WP e {{ v, ⌜φ v⌝ }}) →
  SeriesC(λ x, lim_exec (e, σ) x) = 1.
Proof.
  intros. eapply finite_ert_implies_ast with x.
  intros n. by eapply wp_ERT.
Qed.
  
