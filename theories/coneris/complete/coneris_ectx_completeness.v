(* From clutch.coneris.complete Require Export coneris_completeness_prelims. *)
From clutch.coneris.complete Require Export coneris_completeness.
From clutch.base_logic Require Import error_credits.
From clutch.common Require Export con_ectx_language.
From clutch.con_prob_lang Require Import lang.
From clutch.coneris Require Import weakestpre proofmode.
From iris.prelude Require Export prelude options.
From iris.bi Require Export bi fractional.
From iris.proofmode Require Import base proofmode classes.

Local Open Scope R.
Section ectx_complete.

Class coneris_ectx_lang_completeness_gen (Σ : gFunctors) 
        `{!coneristpinvGS Σ con_prob_ectx_lang,
          !ecGS Σ,
          !conerisWpGS con_prob_lang Σ}:=
  ConerisEctxCompleteness {

  heap_inv : list (expr con_prob_lang) → state con_prob_lang → iProp Σ;
  heap_inv_timeless :> ∀ C σ, Timeless (heap_inv C σ);

  coneris_head_completeness :
    ∀ n (C : list (expr con_prob_lang)) (e1 : expr con_prob_lang)
      (σ : state con_prob_lang) (K : ectx con_prob_ectx_lang) E,
      head_reducible e1 σ →
      n ↪cthread (fill K e1) -∗
      heap_inv C σ ∗ con_tp_inv C ={E}=∗

      (* ─── ATOMIC CASE ─── *)
      (⌜Atomic StronglyAtomic e1⌝ ∗
        ∀ Φ (ε1 : cfg con_prob_lang → R),
          ⌜∃ r : R, ∀ ρ, ε1 ρ <= r⌝ →
          ⌜∀ C' σ' n' e',
              C' !! n' = Some e' → reducible e' σ' →
              Expval (prim_step e' σ')
                     (λ '(e'', σ'', efs), ε1 (<[n' := e'']> C' ++ efs, σ'')) <= ε1 (C', σ')⌝ →
          ⌜∀ ρ, 0 <= ε1 ρ⌝ →
          ⌜∀ C' σ' n' e', C' !! n' = Some e' → stuck e' σ' → ε1 (C', σ') = 1⌝ →
          (▷ ∀ v2 σ' efs,
            ⌜head_step e1 σ (of_val v2, σ', efs) > 0⌝ -∗
            n ↪cthread (fill K e1) -∗
            con_tp_inv C ==∗
            (heap_inv (<[n := fill K (of_val v2)]> C ++ efs) σ'
               -∗ ↯ (ε1 ((<[n := fill K (of_val v2)]> C ++ efs), σ'))
               -∗ Φ v2) ∗
            [∗ list] m↦etp ∈ efs, WP etp @ ⊤ {{_, True}}) -∗
          ↯ (ε1 (C, σ)) -∗
          WP e1 @ E {{Φ}}) ∨

      (* ─── NON-ATOMIC CASE ─── *)
      (heap_inv C σ ∗ con_tp_inv C ∗
        ∀ Ψ E2,
          (▷ |={E2,E}=> ∃ σ1 C1,
            heap_inv C1 σ1 ∗ con_tp_inv C1 ∗
            ∀ e2,
              ⌜pure_step e1 e2⌝ -∗
              n ↪cthread (fill K e1) -∗
              con_tp_inv C1 ==∗
              (heap_inv (<[n := fill K e2]> C1) σ1
                 ={E,E2}=∗ WP e2 @ E2 {{Ψ}})) -∗
          WP e1 @ E2 {{Ψ}})
}.

Global Existing Instance heap_inv_timeless.

End ectx_complete.

Section ectx_to_lang.

Context {Σ : gFunctors}.
Context `{!coneristpinvGS Σ con_prob_ectx_lang,
          !ecGS Σ,
          !conerisWpGS con_prob_lang Σ,
          !coneris_ectx_lang_completeness_gen Σ}.

Lemma pure_step_fill (K : ectx con_prob_ectx_lang) e1 e2 :
  pure_step e1 e2 → pure_step (fill K e1) (fill K e2).
Proof.
  apply pure_step_ctx. apply con_ectx_lang_ctx.
Qed.

Lemma wp_ectx_to_prim_completeness
    n (C : list (expr con_prob_lang)) (e1 : expr con_prob_lang)
    (σ : state con_prob_lang) E :
  reducible e1 σ →
  n ↪cthread e1 -∗
  heap_inv C σ ∗ con_tp_inv C ={E}=∗

  (∃ (K : ectx con_prob_ectx_lang) (e1' : expr con_prob_lang),
    ⌜e1 = fill K e1'⌝ ∗
    ⌜Atomic StronglyAtomic e1'⌝ ∗
    ⌜∃ σ', head_reducible e1' σ'⌝ ∗
    ∀ Φ (ε1 : cfg con_prob_lang → R),
      ⌜∃ r : R, ∀ ρ, ε1 ρ <= r⌝ →
      ⌜∀ C' σ' n' e',
          C' !! n' = Some e' → reducible e' σ' →
          Expval (prim_step e' σ')
                 (λ '(e'', σ'', efs), ε1 (<[n' := e'']> C' ++ efs, σ'')) 
            <= ε1 (C', σ')⌝ →
      ⌜∀ ρ, 0 <= ε1 ρ⌝ →
      ⌜∀ C' σ' n' e', C' !! n' = Some e' → stuck e' σ' → ε1 (C', σ') = 1⌝ →
      (▷ ∀ v2 σ' efs,
        ⌜head_step e1' σ (of_val v2, σ', efs) > 0⌝ -∗
        n ↪cthread e1 -∗
        con_tp_inv C ==∗
        (heap_inv (<[n := fill K (of_val v2)]> C ++ efs) σ'
          -∗ ↯ (ε1 ((<[n := fill K (of_val v2)]> C ++ efs), σ'))
          -∗ Φ v2) ∗
        [∗ list] m↦etp ∈ efs, WP etp @ ⊤ {{_, True}}) -∗
      ↯ (ε1 (C, σ)) -∗
      WP e1' @ E {{Φ}}) ∨

  (* NON-ATOMIC: [e1] takes a pure step *)
  (heap_inv C σ ∗ con_tp_inv C ∗
    ∀ Ψ E2,
      (▷ |={E2,E}=> ∃ σ1 C1,
        heap_inv C1 σ1 ∗ con_tp_inv C1 ∗ 
        ∀ e2,
          ⌜pure_step e1 e2⌝ -∗
          n ↪cthread e1 -∗
          con_tp_inv C1 ==∗
          (heap_inv (<[n := e2]> C1) σ1
             ={E,E2}=∗ WP e2 @ E2 {{Ψ}})) -∗
      WP e1 @ E2 {{Ψ}}).
Proof.
  intros ([[ e2_0 σ2_0] efs_0] & Hstep).
  rewrite prim_step_iff in Hstep.
  destruct Hstep as (K & e1' & e2' & <- & <- & Hhs). 
  iIntros "He (Hheap & Htp)".
  iMod (coneris_head_completeness n C e1' σ K E
          with "He [$Hheap $Htp]") as "[HATOMIC | HNONAT]".
  { eexists. done. }
  - iModIntro. iLeft.
    iDestruct "HATOMIC" as "(%Hatomic & HH)".
    iExists K, e1'. iSplitR; [done|]. iSplitR; [done|].
    iSplitR; first by (iPureIntro; exists σ; eexists; exact Hhs).
    iExact "HH".
  - iModIntro. iRight.
    iDestruct "HNONAT" as "(Hheap & Htp & HNA)".
    iFrame "Hheap Htp".
    iIntros (Ψ E2) "Hcb".
    iApply pgl_wp_bind.
    iApply ("HNA" $! (λ v : val con_prob_lang, WP fill K (of_val v) @ E2 {{Ψ}})%I E2).
    iNext. iMod "Hcb" as (σ1 C1) "(Hh1 & Htp1 & Hcb)".
    iModIntro. iExists σ1, C1. iFrame. 
    iIntros (e2 Hps) "Hthread Htp1".
    iMod ("Hcb" $! (fill K e2) with "[%] Hthread Htp1") as "Hfupd".
    { exact (pure_step_fill K e1' e2 Hps). }
    iModIntro.
    iIntros "Hheap".
    iMod ("Hfupd" with "Hheap") as "WPfull".
    iModIntro.
    iApply pgl_wp_bind_inv.
    iExact "WPfull".
Qed. 

End ectx_to_lang.

Global Program Instance coneris_ectx_to_lang
    {Σ : gFunctors}
    `{!coneristpinvGS Σ con_prob_ectx_lang,
      !ecGS Σ,
      !conerisWpGS con_prob_lang Σ,
      !coneris_ectx_lang_completeness_gen Σ} :
  coneris_lang_completeness_gen Σ := {
  heap_inv := heap_inv;
  heap_inv_timeless := heap_inv_timeless;
}.
Next Obligation.
  intros ???????????.
  by apply wp_ectx_to_prim_completeness.
Defined. 

From clutch.coneris Require Import primitive_laws derived_laws error_rules.

Section completeness.
Context {Σ : gFunctors}.

Global Instance pair_atomic s v1 v2 : Atomic s (Pair (Val v1) (Val v2)).
Proof. 
  apply strongly_atomic_atomic.
  intros σ e' σ' efs.
  setoid_rewrite head_prim_step_eq; last by eexists; simpl; solve_distr. 
  rewrite head_step_support_equiv_rel.
  intros H. by inversion H.
Qed.

Context `{!coneristpinvGS Σ con_prob_ectx_lang,
          !conerisGS Σ}.

Lemma wp_fork_fupd s E e Φ :
  ▷ (|={E}=> WP e @ s; ⊤ {{ _, True }} ∗ Φ (LitV LitUnit)) ⊢ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "H".
  iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1) "(Hh & Ht)". iModIntro.
  iSplitR; first by (iPureIntro; eauto with head_step).
  iNext. iIntros (e2 σ2 efs Hs).
  inv_head_step.
  iMod "H" as "[He HΦ]". iModIntro.
  iFrame.
Qed.

Definition con_heap_inv (C : list (expr)) (σ : con_prob_lang.state) : iProp Σ :=
    ⌜Forall no_allocN_expr C⌝
  ∗ ⌜map_Forall (λ _ v, no_allocN_val v) σ.(heap)⌝
  ∗ ([∗ map] l↦v ∈ σ.(heap),  l ↦ v)
  ∗ ([∗ map] ι↦α ∈ σ.(tapes), ι ↪ α).

Lemma atomic_pure_det_case (φ : Prop) n (C : list expr) (e1 : expr) (v2 : val)
    (σ : state) (K : ectx con_prob_ectx_lang) E
    `{!Atomic StronglyAtomic e1}
    `{!PureExec φ 1 e1 (of_val v2)}
    (Hnv : to_val e1 = None)
    (Hφ : φ)
    (Hdet : head_step e1 σ = dret (of_val v2, σ, [])) :
  n ↪cthread (fill K e1) -∗
  con_heap_inv C σ ∗ con_tp_inv C ={E}=∗
  ⌜Atomic StronglyAtomic e1⌝ ∗
  ∀ Φ (ε1 : cfg → R),
    ⌜∃ r : R, ∀ ρ, Rle (ε1 ρ) r⌝ →
    ⌜∀ C' σ' n' e',
        C' !! n' = Some e' → reducible e' σ' →
        Rle (Expval (prim_step e' σ')
               (λ '(e'', σ'', efs), ε1 (<[n' := e'']> C' ++ efs, σ''))) (ε1 (C', σ'))⌝ →
    ⌜∀ ρ, Rle 0 (ε1 ρ)⌝ →
    ⌜∀ C' σ' n' e', C' !! n' = Some e' → stuck e' σ' → ε1 (C', σ') = 1⌝ →
    (▷ ∀ v2' σ'' (efs : list expr),
      ⌜Rlt 0 (head_step e1 σ (of_val v2', σ'', efs))⌝ -∗
      n ↪cthread (fill K e1) -∗
      con_tp_inv C ==∗
      (con_heap_inv (<[n := fill K (of_val v2')]> C ++ efs) σ''
         -∗ ↯ (ε1 ((<[n := fill K (of_val v2')]> C ++ efs), σ''))
         -∗ Φ v2') ∗
      [∗ list] m↦etp ∈ efs, WP etp @ ⊤ {{_, True}}) -∗
    ↯ (ε1 (C, σ)) -∗
    WP e1 @ E {{Φ}}.
Proof.
  iIntros "He ((%HnoallocC & %HnoallocH & Hheap_pts & Htapes) & Htp)".
  iModIntro. iSplitR; first by iPureIntro; apply _.
  iIntros (Φ ε1 Hboundε Hstepε Hnnε Hstuckε) "Hind Herr".
  wp_pure.
  iPoseProof (con_tp_inv_lookup with "Htp He") as "%HCn".
  (* Derive no_allocN for the result value *)
  have HfillKe1 : no_allocN_expr (fill K e1)
    := proj1 (Forall_lookup _ _) HnoallocC _ _ HCn.
  have He1 : no_allocN_expr e1 := no_allocN_fill_inv K e1 HfillKe1.
  have Hv2 : no_allocN_val v2.
  { apply (no_allocN_head_step_val e1 v2 σ HnoallocH He1).
    rewrite -head_step_support_equiv_rel.
    rewrite Hdet. rewrite dret_1_1 //=. lra. }
  have HfillKv2 : no_allocN_expr (fill K (of_val v2))
    := no_allocN_fill_compat K e1 (of_val v2) HfillKe1 Hv2.
  iSpecialize ("Hind" $! v2 σ []).
  iMod ("Hind" with "[] He Htp") as "[Hind Hnext]".
  { iPureIntro. rewrite Hdet dret_1_1 //=. lra. }
  iModIntro.
  (* Construct con_heap_inv for the updated thread pool *)
  iAssert (con_heap_inv (<[n := fill K (of_val v2)]> C ++ []) σ)
      with "[Hheap_pts Htapes]" as "Hnew".
  { unfold con_heap_inv. rewrite app_nil_r.
    iSplitR; [iPureIntro; eapply no_allocN_Forall_insert; eauto |].
    iSplitR; [iPureIntro; exact HnoallocH | iFrame]. }
  iApply ("Hind" with "Hnew").
  iApply (ec_weaken with "Herr").
  split; first by apply Hnnε.
  etrans; last eapply Hstepε; eauto.
  - setoid_rewrite fill_prim_step_dbind => //=.
    setoid_rewrite head_prim_step_eq => //=; last by rewrite /head_reducible //= Hdet; eexists; rewrite dret_1_1 //=; lra.
    rewrite Hdet dmap_dret Expval_dret /fill_lift //=.
  - apply fill_reducible, head_prim_reducible. eexists.
    setoid_rewrite Hdet. rewrite dret_1_1 //=; lra.
Qed.

Lemma pure_step_head_step e1 e2: 
  (∀ σ, head_step e1 σ (e2, σ, []) = 1) →
  pure_step e1 e2.
Proof.
  intros.
  apply pure_head_step_pure_step.
  econstructor; auto.
  intros. rewrite /head_reducible //=.
  eexists. erewrite H. real_solver.
Qed.

Local Ltac atomic_start :=
  iLeft; iSplitL ""; [by iPureIntro; apply _ | idtac];
  iModIntro;
  iPoseProof (con_tp_inv_lookup with "Htp He") as "%HCn";
  iIntros (Φ ε1 Hboundε Hstepε Hnnε Hstuckε) "Hind Herr".

Local Ltac no_alloc_fill_head hnoallocC hCn :=
  pose proof (proj1 (Forall_lookup _ _) hnoallocC _ _ hCn) as Hfill_head.

Local Ltac no_alloc_arg_val hfill :=
  apply no_allocN_fill_inv in hfill; simpl in hfill; tauto.

Local Ltac no_alloc_heap_upd hloc hnoallocH :=
  intros k ? Hk;
  destruct (decide (k = hloc)) as [->|?];
  [ rewrite lookup_insert in Hk; simplify_eq; simpl; eauto
  | rewrite lookup_insert_ne in Hk; [|done]; by eapply hnoallocH ].

Local Ltac simple_heap_inv :=
  unfold con_heap_inv; rewrite app_nil_r /=;
  iSplitR; [iPureIntro; eapply no_allocN_Forall_insert; eauto |];
  iSplitR; [by iPureIntro | iFrame].

Local Ltac det_step_ec_weaken nn_hyp step_hyp ctx lookup :=
  iApply (ec_weaken with "Herr");
  split; [by apply nn_hyp |];
  etrans; [| eapply step_hyp; eauto];
  [ setoid_rewrite (fill_prim_step_dbind ctx) => //=;
    setoid_rewrite head_prim_step_eq => //=;
    rewrite lookup dmap_dret Expval_dret /fill_lift //=
  | apply fill_reducible, head_prim_reducible; eexists;
    rewrite /= lookup dret_1_1 //; lra ].

Global Program Instance coneris_ectx_lang_completeness
    : coneris_ectx_lang_completeness_gen Σ := {
      heap_inv := con_heap_inv
    }.
Next Obligation.
  Local Opaque INR.
  intros n C e1 σ K E Hred.
  iIntros "He (Hheap & Htp)".
  pose proof Hred as Hred'.
  destruct Hred' as ([[e2_w σ2_w] efs_w] & Hhs).
  rewrite head_step_support_equiv_rel in Hhs.
  inversion Hhs; subst; clear Hhs.
  (* pure atomic *)
  1-4, 10-11, 22 : iLeft; iApply (atomic_pure_det_case True with "He [$Hheap $Htp]"); [done | by rewrite /head_step //= | done]. 
  2 : { iLeft; iApply (atomic_pure_det_case (un_op_eval _ _ = Some _) with "He [$Hheap $Htp]");
        [done | eassumption | by (rewrite /head_step /=; case_match; congruence)]. }
  2 : { iLeft; iApply (atomic_pure_det_case (bin_op_eval _ _ _ = Some _) with "He [$Hheap $Htp]");
        [done | eassumption | by (rewrite /head_step /=; case_match; congruence)]. }
  (* pure nonatomic *)
  1-5 : 
    iRight; iModIntro; 
    iFrame "Hheap Htp"; iIntros (Ψ E2) "Hcb"; 
    wp_pure; iApply fupd_pgl_wp; 
    iMod "Hcb" as (σ1 C1) "((%Hnae&%Hnas&Hh&Ht) & Htp1 & Hcb)"; 
    iPoseProof (con_tp_inv_lookup with "Htp1 He") as "%HCn";
    iMod ("Hcb" $! _ with "[%] He Htp1 [Hh Ht]") as "Hfupd"; auto; [by apply pure_step_head_step => ?; rewrite dret_1_1|];
    unfold con_heap_inv; iSplitR; [iPureIntro | iSplitR; [iPureIntro; exact Hnas | iFrame]]; apply (no_allocN_Forall_insert _ _ _ _ Hnae HCn); 
    have Hfill := proj1 (Forall_lookup _ _) Hnae _ _ HCn; eapply no_allocN_fill_compat; [exact Hfill |];
    apply no_allocN_fill_inv in Hfill; simpl in *;
    try tauto;
    try (apply no_allocN_subst'; [tauto |];
    apply no_allocN_subst'; tauto). 
  1, 5:
    (* allocN & allocTape (skip) *)
    iPoseProof (con_tp_inv_lookup with "Htp He") as "%HCn";
    iDestruct "Hheap" as "(%HnoallocC&%HnoallocH&Hheap&Htapes)";
    pose proof (proj1 (Forall_lookup _ _) HnoallocC _ _ HCn) as H;
    apply no_allocN_fill_inv in H; contradiction.
  {
    (* load *)
    atomic_start.
    rewrite {1}/con_heap_inv big_sepM_delete; eauto.
    iDestruct "Hheap" as "(%HnoallocC & %HnoallocH &(Hl&Hheap')&Htapes)".
    wp_load.
    iCombine "Hl Hheap'" as "Hheap".
    rewrite <-(big_sepM_delete (λ l v, l ↦ v)%I _ _  _ H).
    iPoseProof ("Hind" $! v σ2_w [] with "[%] He Htp") as ">[Hv Hnext]";
    first by rewrite /head_step /= H dret_1_1 //=; lra.
    have HfillKFork : no_allocN_expr (fill K (Load (Val $ LitV $ LitLoc l)))
      := proj1 (Forall_lookup _ _) HnoallocC _ _ HCn.
    have He_noalloc : no_allocN_val v
      := map_Forall_lookup_1 _ _ _ _ HnoallocH H.
    have HfillKUnit : no_allocN_expr (fill K (of_val v))
      := no_allocN_fill_compat K _ _ HfillKFork _.
    iAssert (con_heap_inv (<[n := fill K (of_val v)]> C ++ []) σ2_w)
      with "[Hheap Htapes]" as "Hnew_heap"; [simple_heap_inv|].
    iApply ("Hv" with "Hnew_heap [Herr]").
    det_step_ec_weaken Hnnε Hstepε K H.
  }
  {
    (* store *)
    atomic_start.
    rewrite {1}/con_heap_inv big_sepM_delete; eauto.
    iDestruct "Hheap" as "(%HnoallocC & %HnoallocH &(Hl&Hheap')&Htapes)".
    wp_store.
    have HfillKStore : no_allocN_expr (fill K (Store (Val $ LitV $ LitLoc l) (Val w)))
      := proj1 (Forall_lookup _ _) HnoallocC _ _ HCn.
    have Hw_noalloc : no_allocN_val w. { no_alloc_arg_val HfillKStore. }
    have HfillKUnit : no_allocN_expr (fill K (of_val (LitV LitUnit))).
    { apply (no_allocN_fill_compat K _ _ HfillKStore). done. }
    have HnoallocH' : map_Forall (λ _ (v' : val), no_allocN_val v') (<[l:=w]> σ.(heap)).
    { no_alloc_heap_upd l HnoallocH. }
    iPoseProof ("Hind" $! (LitV LitUnit) (state_upd_heap <[l:=w]> σ) [] with "[%] He Htp") as ">[Hv Hnext]";
    first by rewrite /head_step /= H dret_1_1 //=; lra.
    iAssert (con_heap_inv (<[n := fill K (of_val (LitV LitUnit))]> C ++ []) (state_upd_heap <[l:=w]> σ))
      with "[Hl Hheap' Htapes]" as "Hnew_heap".
    { unfold con_heap_inv. rewrite app_nil_r /=.
      iSplitR; [iPureIntro; eapply no_allocN_Forall_insert; eauto |].
      iSplitR; [iPureIntro; exact HnoallocH' |].
      iSplitL "Hl Hheap'".
      - rewrite (big_sepM_delete _ _ _ _ (lookup_insert (heap σ) l w)).
        rewrite delete_insert_delete. iFrame.
      - iFrame. }
    iApply ("Hv" with "Hnew_heap [Herr]").
    det_step_ec_weaken Hnnε Hstepε K H.
  }
  {
    (* pure rand *)
    iLeft. 
    iSplitL ""; first by iPureIntro; apply _.
    iModIntro.
    iPoseProof (con_tp_inv_lookup with "Htp He") as "%HCn".
    iIntros (Φ ε1 Hboundε Hstepε Hnnε Hstuckε) "Hind Herr". 
    iApply (pgl_wp_strong_mono' E _ _ (λ v, |={E}=> Φ v)%I with "[-] []"); [done | |iIntros (???) "(?&?&H)"; iMod "H"; by iFrame].
    iDestruct "Hheap" as "(%HnoallocC & %HnoallocH &Hheap&Htapes)".
    iPoseProof (ec_weaken with "Herr") as "Herr"; last first. 
    - wp_apply (wp_couple_rand_adv_comp _ _ _ _ (λ n0 : fin (S (Z.to_nat z)), ε1 (<[n:=fill K (Val $ LitV $ LitInt n0)]> C, σ2_w)) with "Herr");
        [by intros; apply Hnnε | done|].
      iIntros (?) "Herr".
      iPoseProof ("Hind" $! (LitV (LitInt n1)) σ2_w [] with "[%] He Htp") as ">[Hv Hnext]"; 
      first by simpl; solve_distr. 
      have HfillKStore : no_allocN_expr (fill K (Rand (Val $ LitV $ LitInt z) (Val $ LitV $ LitUnit)))
      := proj1 (Forall_lookup _ _) HnoallocC _ _ HCn.
      have HfillKUnit : no_allocN_expr (fill K (of_val (LitV $ LitInt n1))).
      { apply (no_allocN_fill_compat K _ _ HfillKStore). done. }
      iAssert (con_heap_inv (<[n := fill K (of_val (LitV $ LitInt n1))]> C ++ []) σ2_w)
        with "[Hheap Htapes]" as "Hnew_heap"; [simple_heap_inv|].
      iModIntro. iApply ("Hv" with "Hnew_heap [Herr]").
      by rewrite app_nil_r.
    - split; first by apply SeriesC_ge_0; [real_solver | apply ex_seriesC_finite].
      etrans; last eapply Hstepε; eauto.
      + setoid_rewrite (fill_prim_step_dbind K) => //=.
        setoid_rewrite head_prim_step_eq => //=.
        rewrite Expval_dmap //=; [ | intros (?&?); real_solver| 
          destruct Hboundε as [r Hr]; apply (ex_expval_bounded _ _ r);
          intros x; split; simpl; destruct (fill_lift' K x) as [[??]?]; [ apply Hnnε | apply Hr] ].  
        rewrite Expval_dmap //=; [ | intros; simpl ; destruct (fill_lift' K b) as [[??]?] eqn : H'; apply Hnnε |
        destruct Hboundε as [r Hr]; apply (ex_expval_bounded _ _ r);
        intros x; split; [apply Hnnε | apply Hr]].  
        rewrite /Expval //=. setoid_rewrite app_nil_r => /=.
        setoid_rewrite dunif_pmf. by setoid_rewrite Rdiv_1_l. 
      + apply fill_reducible, head_prim_reducible. 
        eexists; simpl; solve_distr. 
  }
  {
    (* successful rand on tape *)
    iLeft. 
    iSplitL ""; first by iPureIntro; apply _.
    iModIntro.
    iPoseProof (con_tp_inv_lookup with "Htp He") as "%HCn".
    iIntros (Φ ε1 Hboundε Hstepε Hnnε Hstuckε) "Hind Herr".
    iApply (pgl_wp_strong_mono' E _ _ (λ v, |={E}=> Φ v)%I with "[-] []"); [done | |iIntros (???) "(?&?&H)"; iMod "H"; by iFrame].
    rewrite {1}/con_heap_inv (big_sepM_delete (λ i l, i ↪[conerisGS_tapes_name]l)%I); eauto.
    iDestruct "Hheap" as "(%HnoallocC & %HnoallocH &Hheap&(Hl&Htapes'))". 
    wp_apply (wp_rand_tape with "[Hl]"); first by iNext; iFrame.
    iIntros "[Hl' %]".
    have HfillKStore : no_allocN_expr (fill K (Rand (Val $ LitV $ LitInt z) (Val $ LitV $ LitLbl l)))
    := proj1 (Forall_lookup _ _) HnoallocC _ _ HCn. 
    have HfillKUnit : no_allocN_expr (fill K (of_val (LitV $ LitInt n0))).
    { apply (no_allocN_fill_compat K _ _ HfillKStore). done. } 
    iPoseProof ("Hind" $! (LitV (LitInt n0)) _ [] with "[%] He Htp") as ">[Hv Hnext]";
      first by rewrite /head_step /= H0; case_bool_decide; [solve_distr|tauto].   
    iAssert (con_heap_inv (<[n := fill K (of_val (LitV $ LitInt n0))]> C ++ []) (state_upd_tapes <[l:=_]> σ))
    with "[Hheap Hl' Htapes']" as "Hnew_heap"; last first.
    {
      iApply ("Hv" with "Hnew_heap [Herr]"). 
      iApply (ec_weaken with "Herr").
      split; first by apply Hnnε.
      etrans; last eapply Hstepε; eauto.
      - setoid_rewrite (fill_prim_step_dbind K) => //=.
        setoid_rewrite head_prim_step_eq => //=.
        rewrite H0. case_bool_decide; last tauto. 
        rewrite dmap_dret Expval_dret /fill_lift //=. 
      - apply fill_reducible, head_prim_reducible. eexists.
        rewrite /= H0. case_bool_decide; last tauto. 
        rewrite dret_1_1 //; lra.
    }
    unfold con_heap_inv. rewrite app_nil_r /=.
    iSplitR; [iPureIntro; eapply no_allocN_Forall_insert; eauto |].
    iSplitR; [by iPureIntro| iFrame]. 
    rewrite (big_sepM_delete _ _ _ _ (lookup_insert (tapes σ) l _)). 
    rewrite delete_insert_delete. iFrame. 
    simpl in *. 
    clear.
    iDestruct "Hl'" as (??) "H". 
    eassert ((Z.to_nat z; ns) = _) as ->; last iFrame.
    f_equal. 
    eapply fmap_inj; first apply fin_to_nat_inj.
    done.
  }
  {
    (* rand on empty tape *)
    iLeft. 
    iSplitL ""; first by iPureIntro; apply _.
    iModIntro.
    iPoseProof (con_tp_inv_lookup with "Htp He") as "%HCn".
    iIntros (Φ ε1 Hboundε Hstepε Hnnε Hstuckε) "Hind Herr".
    iApply (pgl_wp_strong_mono' E _ _ (λ v, |={E}=> Φ v)%I with "[-] []"); [done | |iIntros (???) "(?&?&H)"; iMod "H"; by iFrame].
    rewrite {1}/con_heap_inv (big_sepM_delete (λ i l, i ↪[conerisGS_tapes_name]l)%I); eauto.
    iDestruct "Hheap" as "(%HnoallocC & %HnoallocH &Hheap&(Hl&Htapes'))". 
    wp_apply (wp_couple_empty_tape_adv_comp' _ _ _ _ _  (λ m : nat, ε1 (<[n:=fill K (Val $ LitV $ LitInt m)]> C, σ2_w)) with "[Hl Herr]"); first by intro m; apply Hnnε.
    - (* series bound: SeriesC ≤ ε1 (C, σ), from Hstepε *)
      transitivity (Expval (prim_step (fill K (Rand (Val $ LitV $ LitInt z) (Val $ LitV $ LitLbl l))) σ2_w)
        (λ '(e'', σ'', efs), ε1 (<[n:=e'']> C ++ efs, σ''))).
      2: { 
        simpl in *.
        apply Hstepε; [exact HCn |
             apply fill_reducible, head_prim_reducible; eexists; simpl;
             rewrite H0; case_bool_decide; [| tauto]; solve_distr]. 
      }
      setoid_rewrite fill_prim_step_dbind; last done.
      setoid_rewrite (head_prim_step_eq _ _ Hred). 
      rewrite /= H0 /= Expval_dmap //=; [| intros (?&?); real_solver |
        destruct Hboundε as [r Hr]; apply (ex_expval_bounded _ _ r);
        intros x; split; simpl; destruct (fill_lift' K x) as [[??]?] eqn : H; rewrite H /=; [ apply Hnnε | apply Hr]].
      case_bool_decide; last tauto.
      rewrite Expval_dmap //=; [| intros; simpl ; destruct (fill_lift' K b) as [[??]?] eqn : H'; rewrite H' /=; apply Hnnε |
        destruct Hboundε as [r Hr]; apply (ex_expval_bounded _ _ r);
        intros x; split; [apply Hnnε | apply Hr]].
      rewrite /Expval /=.
      setoid_rewrite app_nil_r.
      rewrite SeriesC_nat_bounded_fin.
      setoid_rewrite dunif_pmf. by setoid_rewrite Rdiv_1_l. 
    - by iFrame; iPureIntro.
    - iIntros (n1) "(Hl & Herr & %Hn1)".
      iPoseProof ("Hind" $! (LitV (LitInt n1)) σ2_w [] with "[%] He Htp") as ">[Hv Hnext]".
      { simpl. rewrite H0. case_bool_decide; [| lia].
        have Hlt : n1 < S (Z.to_nat z) by lia.
        apply dmap_pos. exists (nat_to_fin Hlt).
        split; [by rewrite /= fin_to_nat_to_fin | apply dunifP_pos]. }
      have HfillKStore : no_allocN_expr (fill K (Rand (Val $ LitV $ LitInt z) (Val $ LitV $ LitLbl l)))
      := proj1 (Forall_lookup _ _) HnoallocC _ _ HCn.
      have HfillKUnit : no_allocN_expr (fill K (of_val (LitV $ LitInt n1))).
      { apply (no_allocN_fill_compat K _ _ HfillKStore). done. }
      iAssert (con_heap_inv (<[n := fill K (of_val (LitV $ LitInt n1))]> C ++ []) σ2_w)
        with "[Hheap Hl Htapes']" as "Hnew_heap".
      { unfold con_heap_inv. rewrite app_nil_r /=. 
        iSplitR; [iPureIntro; eapply no_allocN_Forall_insert; eauto |].
        iSplitR; [by iPureIntro| iFrame]. 
        iFrame. 
        rewrite ((big_sepM_delete _ _ _ _ H0)). iFrame. 
        iDestruct "Hl" as (??) "H". 
        destruct fs; [auto | simpl in *; inversion H]. 
      }
      iModIntro. iApply ("Hv" with "Hnew_heap [Herr]").
      by rewrite app_nil_r.
  }
  {
    (* rand on tape with mismatching bounds *)
    iLeft.
    iSplitL ""; first by iPureIntro; apply _.
    iModIntro.
    iPoseProof (con_tp_inv_lookup with "Htp He") as "%HCn".
    iIntros (Φ ε1 Hboundε Hstepε Hnnε Hstuckε) "Hind Herr".
    iApply (pgl_wp_strong_mono' E _ _ (λ v, |={E}=> Φ v)%I with "[-] []"); [done | |iIntros (???) "(?&?&H)"; iMod "H"; by iFrame].
    rewrite {1}/con_heap_inv (big_sepM_delete (λ i l, i ↪[conerisGS_tapes_name]l)%I); eauto.
    iDestruct "Hheap" as "(%HnoallocC & %HnoallocH &Hheap&(Hl&Htapes'))".
    iAssert (l ↪N (M; fin_to_nat <$> ms))%I with "[Hl]" as "HlN".
    { iExists ms. iSplitR; [done | iExact "Hl"]. }
    wp_apply (wp_couple_rand_adv_comp1_wrong_bound (Z.to_nat z) z E _
        (λ n0 : fin (S (Z.to_nat z)), ε1 (<[n:=fill K (Val $ LitV $ LitInt n0)]> C, σ2_w))
        l M (fin_to_nat <$> ms) with "[$]").
    { done. }
    { by intros; apply Hnnε. }
    { (* series bound *)
      etrans; last eapply Hstepε; eauto.
      + setoid_rewrite (fill_prim_step_dbind K) => //=.
        setoid_rewrite head_prim_step_eq => //=.
        rewrite H0 /=.
        case_bool_decide; first lia.
        rewrite Expval_dmap //=; [ | intros (?&?); real_solver|
          destruct Hboundε as [r Hr]; apply (ex_expval_bounded _ _ r);
          intros x; split; simpl; destruct (fill_lift' K x) as [[??]?]; [ apply Hnnε | apply Hr] ].
        rewrite Expval_dmap //=; [ | intros; simpl ; destruct (fill_lift' K b) as [[??]?] eqn : H'; apply Hnnε |
          destruct Hboundε as [r Hr]; apply (ex_expval_bounded _ _ r);
          intros x; split; [apply Hnnε | apply Hr]].
        rewrite /Expval //=. setoid_rewrite app_nil_r => /=.
        setoid_rewrite dunif_pmf. by setoid_rewrite Rdiv_1_l.
      + apply fill_reducible, head_prim_reducible.
        eexists. rewrite /= H0. case_bool_decide; [real_solver | solve_distr]. 
    }
    iIntros (n1) "(Herr & Hl')".
    iPoseProof ("Hind" $! (LitV (LitInt n1)) σ2_w [] with "[%] He Htp") as ">[Hv Hnext]"; 
      first by rewrite /= H0; case_bool_decide; first real_solver; solve_distr. 
    have HfillKRand : no_allocN_expr (fill K (Rand (Val $ LitV $ LitInt z) (Val $ LitV $ LitLbl l)))
      := proj1 (Forall_lookup _ _) HnoallocC _ _ HCn.
    have HfillKInt : no_allocN_expr (fill K (of_val (LitV $ LitInt n1))).
    { apply (no_allocN_fill_compat K _ _ HfillKRand). done. }
    iDestruct "Hl'" as "((%fs_out&%Heq_out & Hl_out) & %)".
    eassert (ms = fs_out) as Hms_eq.
    { eapply fmap_inj; first apply fin_to_nat_inj. exact (eq_sym Heq_out). }
    subst fs_out.
    iAssert (con_heap_inv (<[n := fill K (of_val (LitV $ LitInt n1))]> C ++ []) σ2_w)
      with "[Hheap Hl_out Htapes']" as "Hnew_heap".
    { unfold con_heap_inv. rewrite app_nil_r /=.
      iSplitR; [iPureIntro; eapply no_allocN_Forall_insert; eauto |].
      iSplitR; [by iPureIntro|].
      iSplitL "Hheap"; [iFrame |].
      rewrite (big_sepM_delete _ _ _ _ H0). iFrame. }
    iModIntro. iApply ("Hv" with "Hnew_heap [Herr]").
    by rewrite app_nil_r.
  }
  {
    (* fork e *)
    iLeft. iModIntro.
    iSplitL ""; first by iPureIntro; apply _.
    iIntros (Φ ε1 Hboundε Hstepε Hnnε Hstuckε) "Hind Herr".
    iApply (wp_fork_fupd with "[Hind Herr He Htp Hheap]").
    iPoseProof (con_tp_inv_lookup with "Htp He") as "%HCn".
    iNext.
    iMod ("Hind" $! (LitV LitUnit) σ2_w [e] with "[] He Htp") as "[Hv Hnext]";
      first by iPureIntro; rewrite dret_1_1 //=; lra.
    iSplitL "Hnext"; first by iModIntro; rewrite big_sepL_singleton.
    iModIntro.
    iDestruct "Hheap" as "(%HnoallocC & %HnoallocH & Hheap_pts & Htapes)".
    have HfillKFork : no_allocN_expr (fill K (Fork e))
      := proj1 (Forall_lookup _ _) HnoallocC _ _ HCn.
    have He_noalloc : no_allocN_expr e
      := no_allocN_fill_inv K (Fork e) HfillKFork.
    have HfillKUnit : no_allocN_expr (fill K (of_val (LitV LitUnit)))
      := no_allocN_fill_compat K (Fork e) _ HfillKFork _. 
    iAssert (con_heap_inv (<[n := fill K (of_val (LitV LitUnit))]> C ++ [e]) σ2_w)
        with "[Hheap_pts Htapes]" as "Hnew_heap".
    { unfold con_heap_inv.
      iSplitR.
      { iPureIntro. apply no_allocN_Forall_app.
        - by refine (no_allocN_Forall_insert _ _ _ _ HnoallocC HCn (HfillKUnit _)).  
        - by constructor. }
      iSplitR; [iPureIntro; exact HnoallocH | iFrame]. }
    iApply ("Hv" with "Hnew_heap [Herr]").
    iApply (ec_weaken with "Herr").
    split; first by apply Hnnε.
    etrans; last eapply Hstepε; eauto.
    - setoid_rewrite (fill_prim_step_dbind K) => //=.
      setoid_rewrite head_prim_step_eq => //=.
      rewrite dmap_dret Expval_dret /fill_lift //=.
    - apply fill_reducible, head_prim_reducible. eexists.
      rewrite dret_1_1 //=; lra.
  }
  {
    (* cmpxchg *)
    iLeft.
    iSplitL ""; first by iPureIntro; apply _.
    iModIntro.
    iPoseProof (con_tp_inv_lookup with "Htp He") as "%HCn".
    iIntros (Φ ε1 Hboundε Hstepε Hnnε Hstuckε) "Hind Herr".
    iApply (pgl_wp_strong_mono' E _ _ (λ v, |={E}=> Φ v)%I with "[-] []"); [done | |iIntros (???) "(?&?&H)"; iMod "H"; by iFrame].
    rewrite {1}/con_heap_inv big_sepM_delete; eauto.
    iDestruct "Hheap" as "(%HnoallocC & %HnoallocH &(Hl&Hheap')&Htapes)".
    have HfillKCmpXchg : no_allocN_expr (fill K (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)))
      := proj1 (Forall_lookup _ _) HnoallocC _ _ HCn.
    have Hvl_noalloc : no_allocN_val vl
      := map_Forall_lookup_1 _ _ _ _ HnoallocH H.
    have Hv2_noalloc : no_allocN_val v2. { no_alloc_arg_val HfillKCmpXchg. }
    destruct (decide (vl = v1)) as [-> | Hne].
    - (* success: vl = v1 *)
      have HnoallocH' : map_Forall (λ _ v', no_allocN_val v') (<[l:=v2]> σ.(heap)).
      { no_alloc_heap_upd l HnoallocH. }
      have HfillKResult : no_allocN_expr (fill K (of_val (PairV v1 (LitV (LitBool true))))).
      { apply (no_allocN_fill_compat K _ _ HfillKCmpXchg). simpl. exact (conj Hvl_noalloc I). }
      
      wp_apply (wp_cmpxchg_suc with "Hl"); [done | done |].
      iIntros "Hl".
      iPoseProof ("Hind" $! (PairV v1 (LitV (LitBool true))) (state_upd_heap <[l:=v2]> σ) []
        with "[%] [$] [$]") as ">[Hv Hnext]"; first by rewrite /head_step /= H; case_decide; [| done];
        rewrite bool_decide_true // /= dret_1_1 //=; lra. 
      iAssert (con_heap_inv (<[n := fill K (of_val (PairV v1 (LitV (LitBool true))))]> C ++ [])
        (state_upd_heap <[l:=v2]> σ))
        with "[Hl Hheap' Htapes]" as "Hnew_heap".
      { unfold con_heap_inv. rewrite app_nil_r /=.
        iSplitR; [iPureIntro; eapply no_allocN_Forall_insert; eauto |].
        iSplitR; [iPureIntro; exact HnoallocH' |].
        iSplitL "Hl Hheap'".
        - rewrite (big_sepM_delete _ _ _ _ (lookup_insert (heap σ) l v2)).
          rewrite delete_insert_delete. iFrame.
        - iFrame. }
      iApply ("Hv" with "Hnew_heap [Herr]").
      iApply (ec_weaken with "Herr").
      split; first by apply Hnnε.
      etrans; last eapply Hstepε; eauto.
      + setoid_rewrite (fill_prim_step_dbind K) => //=.
        setoid_rewrite head_prim_step_eq => //=.
        rewrite H; case_decide; [| done];
          rewrite bool_decide_true // /= dmap_dret Expval_dret /fill_lift //=.
      + apply fill_reducible, head_prim_reducible. eexists.
        rewrite /= H; case_decide; [| done];
          rewrite bool_decide_true // /= dret_1_1 //=; lra. 
    - (* failure: vl ≠ v1 *)
      have HfillKResult : no_allocN_expr (fill K (of_val (PairV vl (LitV (LitBool false))))).
      { apply (no_allocN_fill_compat K _ _ HfillKCmpXchg). simpl. exact (conj Hvl_noalloc I). }
      wp_apply (wp_cmpxchg_fail with "Hl"); [done | done |].
      iIntros "Hl".
      iPoseProof ("Hind" $! (PairV vl (LitV (LitBool false))) σ []
        with "[%] He Htp") as ">[Hv Hnext]";
      first by rewrite /head_step /= H; case_decide; [| done];
        rewrite (bool_decide_false _ Hne) /= dret_1_1 //=; lra.
      iAssert (con_heap_inv (<[n := fill K (of_val (PairV vl (LitV (LitBool false))))]> C ++ []) σ)
        with "[Hl Hheap' Htapes]" as "Hnew_heap".
      { unfold con_heap_inv. rewrite app_nil_r /=.
        iSplitR; [iPureIntro; eapply no_allocN_Forall_insert; eauto |].
        iSplitR; [iPureIntro; exact HnoallocH |].
        iSplitL "Hl Hheap'".
        - iCombine "Hl Hheap'" as "Hheap".
          rewrite <-(big_sepM_delete (λ l v, l ↦ v)%I _ _ _ H). iFrame.
        - iFrame. }
      iApply ("Hv" with "Hnew_heap [Herr]").
      iApply (ec_weaken with "Herr").
      split; first by apply Hnnε.
      etrans; last eapply Hstepε; eauto.
      + setoid_rewrite (fill_prim_step_dbind K) => //=.
        setoid_rewrite head_prim_step_eq => //=.
        rewrite H; case_decide; [| done];
          rewrite (bool_decide_false _ Hne) /= dmap_dret Expval_dret /fill_lift //=.
      + apply fill_reducible, head_prim_reducible. eexists.
        rewrite /= H; case_decide; [| done];
          rewrite (bool_decide_false _ Hne) /= dret_1_1 //=; lra.
  }
  {
    (* xchg *)
    atomic_start.
    iApply (pgl_wp_strong_mono' E _ _ (λ v, |={E}=> Φ v)%I with "[-] []"); [done | |iIntros (???) "(?&?&H)"; iMod "H"; by iFrame].
    rewrite {1}/con_heap_inv big_sepM_delete; eauto.
    iDestruct "Hheap" as "(%HnoallocC & %HnoallocH &(Hl&Hheap')&Htapes)".
    wp_apply (wp_xchg with "Hl").
    iIntros "Hl".
    have HfillKXchg : no_allocN_expr (fill K (Xchg (Val $ LitV $ LitLoc l) (Val v2)))
      := proj1 (Forall_lookup _ _) HnoallocC _ _ HCn.
    have Hv1_noalloc : no_allocN_val v1
      := map_Forall_lookup_1 _ _ _ _ HnoallocH H.
    have Hv2_noalloc : no_allocN_val v2. { no_alloc_arg_val HfillKXchg. }
    have HfillKResult : no_allocN_expr (fill K (of_val v1)).
    { apply (no_allocN_fill_compat K _ _ HfillKXchg). exact Hv1_noalloc. }
    have HnoallocH' : map_Forall (λ _ v', no_allocN_val v') (<[l:=v2]> σ.(heap)).
    { no_alloc_heap_upd l HnoallocH. }
    iPoseProof ("Hind" $! v1 (state_upd_heap <[l:=v2]> σ) [] with "[%] He Htp") as ">[Hv Hnext]";
    first by rewrite /head_step /= H dret_1_1 //=; lra.
    iAssert (con_heap_inv (<[n := fill K (of_val v1)]> C ++ []) (state_upd_heap <[l:=v2]> σ))
      with "[Hl Hheap' Htapes]" as "Hnew_heap".
    { unfold con_heap_inv. rewrite app_nil_r /=.
      iSplitR; [iPureIntro; eapply no_allocN_Forall_insert; eauto |].
      iSplitR; [iPureIntro; exact HnoallocH' |].
      iSplitL "Hl Hheap'".
      - rewrite (big_sepM_delete _ _ _ _ (lookup_insert (heap σ) l v2)).
        rewrite delete_insert_delete. iFrame.
      - iFrame. }
    iApply ("Hv" with "Hnew_heap [Herr]").
    det_step_ec_weaken Hnnε Hstepε K H.
  }
  {
    (* faa *)
    atomic_start.
    iApply (pgl_wp_strong_mono' E _ _ (λ v, |={E}=> Φ v)%I with "[-] []"); [done | |iIntros (???) "(?&?&H)"; iMod "H"; by iFrame].
    rewrite {1}/con_heap_inv big_sepM_delete; eauto.
    iDestruct "Hheap" as "(%HnoallocC & %HnoallocH &(Hl&Hheap')&Htapes)".
    wp_apply (wp_faa with "Hl").
    iIntros "Hl".
    have HfillKFAA : no_allocN_expr (fill K (FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2)))
      := proj1 (Forall_lookup _ _) HnoallocC _ _ HCn.
    have HfillKResult : no_allocN_expr (fill K (of_val (LitV (LitInt i1)))).
    { apply (no_allocN_fill_compat K _ _ HfillKFAA). done. }
    have HnoallocH' : map_Forall (λ _ v', no_allocN_val v') (<[l:= LitV (LitInt (i1+i2))]> σ.(heap)).
    { no_alloc_heap_upd l HnoallocH. }
    iPoseProof ("Hind" $! (LitV (LitInt i1)) (state_upd_heap <[l:= LitV (LitInt (i1+i2))]> σ) []
      with "[%] He Htp") as ">[Hv Hnext]";
    first by rewrite /head_step /= H dret_1_1 //=; lra.
    iAssert (con_heap_inv (<[n := fill K (of_val (LitV (LitInt i1)))]> C ++ [])
      (state_upd_heap <[l:= LitV (LitInt (i1+i2))]> σ))
      with "[Hl Hheap' Htapes]" as "Hnew_heap".
    { unfold con_heap_inv. rewrite app_nil_r /=.
      iSplitR; [iPureIntro; eapply no_allocN_Forall_insert; eauto |].
      iSplitR; [iPureIntro; exact HnoallocH' |].
      iSplitL "Hl Hheap'".
      - rewrite (big_sepM_delete _ _ _ _ (lookup_insert (heap σ) l (LitV (LitInt (i1+i2))))).
        rewrite delete_insert_delete. iFrame.
      - iFrame. }
    iApply ("Hv" with "Hnew_heap [Herr]").
    det_step_ec_weaken Hnnε Hstepε K H.
  }
  Unshelve.
  all: auto.
Qed.

End completeness.