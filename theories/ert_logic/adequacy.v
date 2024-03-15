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
      | None => 1 + SeriesC (λ ρ, (prim_step eσ.1 eσ.2 ρ) * (ERT n ρ))
      end
  end.

Lemma ERT_Sn n e σ :
  to_val e = None ->
  ERT (S n) (e, σ) = 1 + SeriesC (λ ρ : cfg, ((step (e, σ) ρ) * (ERT n ρ))%R).
Proof.
  simpl. by intros ->.
Qed.


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
    (* exec_ub e σ ε (λ '(e2, σ2) ε',
           |={∅}▷=>^(S n) ⌜ub_lift (exec n (e2, σ2)) φ ε'⌝)
       ⊢ |={∅}▷=>^(S n) ⌜ub_lift (exec (S n) (e, σ)) φ ε⌝. *)
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
       2:{ admit. }
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
  Admitted.


  (*       iApply (step_fupdN_mono _ _ _ ⌜(ERT _ _ <= (1 + r)) ⌝).
           iApply fupd_mask_intro; [set_solver|]; iIntros.

           iMod ("H" $! e s with "[]") as "H";  [iPureIntro; eauto| iModIntro ].
           iDestruct "H" as "[%R' [%x1' [%x2' (%Hsum' & %Hlift' & Hwand')]]]".
           rewrite -(dret_id_left' (fun _ : () => (exec n (e, s))) tt).
           iApply (step_fupdN_mono _ _ _ ⌜(ub_lift _ _ (x1' + x2')) ⌝).
           { iIntros "%H'"; iPureIntro. eapply UB_mon_grading; eauto. }
           iApply (ub_lift_dbind').
           * iPureIntro; apply cond_nonneg.
           * iPureIntro; apply cond_nonneg.
           * iPureIntro.
             apply total_ub_lift_implies_ub_lift in Hlift'.
             eapply Hlift'.
           * iIntros (? Hcont).
             replace tt with a; [| by destruct a].
             iSpecialize ("Hwand'" with "[]"); [iPureIntro; eauto|].
             rewrite (dret_id_left').
             iApply step_fupd_fupdN_S.
             iFrame.
             iModIntro.
             eauto.
       - rewrite exec_Sn_not_final; [|eauto].
         iDestruct (big_orL_mono _ (λ _ _,
                        |={∅}▷=>^(S n)
                          ⌜ub_lift (prim_step e1 σ1 ≫= exec n) φ x''⌝)%I
                     with "H") as "H".
         { iIntros (i α Hα%elem_of_list_lookup_2) "(% & %x1 & %x2 & %Hx'' & %Hleq & %Hlift & H)".
           replace (prim_step e1 σ1) with (step (e1, σ1)) => //.
           rewrite -exec_Sn_not_final; [|eauto].
           iApply (step_fupdN_mono _ _ _
                     (⌜∀ σ2 , R2 σ2 → ub_lift (exec (S n) (e1, σ2)) φ (x2 (e1, σ2))⌝)%I).
           - iIntros (?). iPureIntro.
             rewrite /= /get_active in Hα.
             apply elem_of_elements, elem_of_dom in Hα as [bs Hα].
             erewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim _ _ _ _ _ Hα)); eauto.
             apply (UB_mon_grading _ _
                      (x1 + (SeriesC (λ ρ : language.state prob_lang, language.state_step σ1 α ρ * x2 (e1, ρ))))) => //.
             eapply ub_lift_dbind_adv; eauto; [by destruct x1|].
             destruct Hx'' as [r Hr]; exists r.
             intros a.
             split; [by destruct (x2 _) | by apply Hr].
           - iIntros (e s).
             iApply step_fupd_fupdN_S.
             iMod ("H" with "[//]") as "H"; iModIntro.
             iDestruct "H" as "[%R' [%x1' [%x2' (%Hsum' & %Hlift' & Hwand')]]]".
             rewrite -(dret_id_left' (fun _ : () => (exec (S n) _)) tt).
             iApply (step_fupdN_mono _ _ _ ⌜(ub_lift _ _ (x1' + x2')) ⌝).
             { iIntros "%H'"; iPureIntro. eapply UB_mon_grading; eauto. }
             iApply (ub_lift_dbind').
             * iPureIntro; apply cond_nonneg.
             * iPureIntro; apply cond_nonneg.
             * iPureIntro.
               apply total_ub_lift_implies_ub_lift in Hlift'.
               eapply Hlift'.
             * iIntros (? Hcont).
               replace tt with a; [| by destruct a].
               iSpecialize ("Hwand'" with "[]"); [iPureIntro; eauto|].
               rewrite (dret_id_left').
               iApply step_fupd_fupdN_S.
               iMod ("Hwand'" with "[//]"); iModIntro; iFrame.
               iModIntro; eauto. }
         iInduction (language.get_active σ1) as [| α] "IH"; [done|].
         rewrite big_orL_cons.
         iDestruct "H" as "[H | Ht]"; [done|].
         by iApply "IH".
     Qed. *)

  Theorem wp_refRcoupl_step_fupdN (e : expr) (σ : state) (x : nonnegreal) n φ  :
    state_interp σ ∗ etc_interp (x) ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
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
          (ERM_mono _ (λ '(e2, σ2) x', |={∅}▷=>^(S n)
             ⌜ERT n (e2, σ2) <= x'⌝)%I
            with "[%] [] Hlift") as "H".
        { apply Rle_refl. }
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
  (* Handle the trivial 1 <= ε case *)
  (* destruct (Rlt_decision (nonneg ε) 1) as [Hcr|Hcr]; last first.
     { iClear "Hh Ht".
       iApply (fupd_mask_intro); [eauto|].
       iIntros "_".
       iApply step_fupdN_intro; [eauto|].
       iApply laterN_intro; iPureIntro.
       apply not_Rlt, Rge_le in Hcr.
       rewrite /ub_lift; intros.
       eapply Rle_trans; [eapply prob_le_1|done]. } *)
  iMod (etc_alloc) as (?) "[??]".
  set (HclutchGS := HeapG Σ _ _ _ γH γT _).
  iApply wp_refRcoupl_step_fupdN.
  iFrame.
  iApply Hwp.
  done.
Qed.

(*
Lemma ub_lift_closed_lim (e : expr) (σ : state) (ε : nonnegreal) φ :
  (forall n, ub_lift (exec n (e, σ)) φ ε ) ->
  ub_lift (lim_exec (e, σ)) φ ε .
Proof.
  intros Hn.
  apply lim_exec_continuous_prob; auto.
Qed.

Theorem wp_union_bound_lim Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ}, ⊢ € ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ub_lift (lim_exec (e, σ)) φ ε.
Proof.
  intros.
  apply ub_lift_closed_lim.
  intro n.
  apply (wp_union_bound Σ); auto.
Qed.

Theorem wp_union_bound_epsilon_lim Σ `{ub_clutchGpreS Σ} (e : expr) (σ : state) (ε : nonnegreal) φ :
  (∀ `{ub_clutchGS Σ} (ε':nonnegreal), ε<ε' -> ⊢ € ε' -∗ WP e {{ v, ⌜φ v⌝ }}) →
  ub_lift (lim_exec (e, σ)) φ ε.
Proof.
  intros H'.
  apply ub_lift_epsilon_limit.
  { destruct ε. simpl. lra. }
  intros ε0 H1.
  assert (0<=ε0) as Hε0.
  { trans ε; try lra. by destruct ε. }
  pose (mknonnegreal ε0 Hε0) as NNRε0.
  assert (ε0 = (NNRbar_to_real (NNRbar.Finite (NNRε0)))) as Heq.
  { by simpl. }
  rewrite Heq.
  eapply wp_union_bound_lim; first done.
  intros. iIntros "He".
  iApply H'; try iFrame.
  simpl. destruct ε; simpl in H1; simpl; lra.
Qed.
*)
