From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.
From Coquelicot Require Import Rbar Lim_seq.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.delay_prob_lang Require Import notation metatheory urn_subst commute.
From clutch.common Require Export language.
From clutch.base_logic Require Import error_credits.
From clutch.elton Require Import weakestpre primitive_laws rupd.
From clutch.prob Require Import distribution.
Import uPred.

Set Default Proof Using "Type".
  
Section adequacy.
  Context `{!eltonGS Σ}.
  Lemma step_fupd_fupdN_S n (P : iProp Σ) :  ((|={∅}▷=>^(S n) P) ⊣⊢ (|={∅}=> |={∅}▷=>^(S n) P))%I.
  Proof. iSplit; iIntros; simpl; iApply fupd_idemp; iFrame. Qed.
  
  Lemma pgl_dbind_adv' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (T : A' → Prop) ε' n :
    ⌜ exists r, forall a, 0 <= ε' a <= r ⌝ -∗
    (∀ a , |={∅}=> |={∅}▷=>^(n) ⌜pgl (f a) T (ε' a)⌝) -∗
    |={∅}=> |={∅}▷=>^(n) ⌜pgl (dbind f μ) T ( Expval μ ε')⌝ : iProp Σ.
  Proof.
    iIntros (?) "H".
    iApply (step_fupdN_mono _ _ _ (⌜(∀ a, pgl (f a) T (ε' a))⌝)).
    { iIntros (?). iPureIntro. rewrite <-Rplus_0_l. eapply pgl_dbind_adv; try done.
      by apply pgl_trivial.
    }
    by iIntros (?) "/=".
  Qed.

  
  Theorem wp_elton_adequacy_val (ε: nonnegreal) e σ ϕ n m (v:val):
    to_val e = Some v ->
    is_well_constructed_expr e = true ->
    expr_support_set e ⊆ urns_support_set (urns σ) ->
    map_Forall (λ _ v, is_well_constructed_val v = true) (heap σ) ->
    map_Forall (λ _ v, val_support_set v ⊆ urns_support_set (urns σ)) (heap σ) ->
    state_interp σ ∗ err_interp (ε) ∗ WP e {{ v, |={⊤, ∅}=> rupd ϕ v }} ⊢
    |={⊤,∅}=>|={∅}▷=>^n ⌜pgl (urns_f_distr (σ.(urns)) ≫= λ f,
                       d_proj_Some (urn_subst_expr f e) ≫= λ e',
                         d_proj_Some (urn_subst_heap f (σ.(heap))) ≫= λ hm, 
                           exec n (e', {|heap:=hm; urns:=m|})) ϕ ε⌝.
  Proof.
    iIntros (<-%of_to_val He Hset Hforall1 Hforall2) "(?&?&Hwp)".
    rewrite pgl_wp_unfold/pgl_wp_pre.
    iMod ("Hwp" with "[$]") as "H"; simpl.
    iRevert (Hset Hforall1 Hforall2).
    iRevert "H".
    iRevert (σ ε).
    iApply state_step_coupl_ind.
    iModIntro.
    iIntros (??) "[%|[H|[H|H]]] %Hset %Hforall1 %Hforall2".
    - iApply step_fupdN_intro; first done.
      iPureIntro. by apply pgl_1.
    - iMod "H" as "(?&?&H)".
      rewrite rupd_unseal/rupd_def.
      iMod ("H" with "[$]") as "%Hsubst".
      iApply step_fupdN_intro; first done.
      iPureIntro.
      apply pgl_dbind'; first done; intros ? H1.
      apply pgl_dbind'; first done; intros ? H2.
      apply pgl_dbind'; first done; intros ? H3.
      inv_distr.
      unshelve epose proof Hsubst _ _ as (?&?&?); [|by apply urns_f_distr_pos|].
      rewrite bind_Some in H2. destruct!/=.
      erewrite exec_is_final; last done.
      eapply pgl_mon_grading; last apply pgl_dret; done.
    - iApply (step_fupdN_mono _ _ _ (⌜_⌝)%I).
      { iPureIntro.
        intros H'.
        apply pgl_epsilon_limit; last exact.
        by apply Rle_ge. 
      }
      iIntros (ε' ?).
      unshelve iDestruct ("H" $! (mknonnegreal ε' _) with "[]") as "[H _]"; last first. 
      + by iApply "H".
      + done.
      + pose proof cond_nonneg ε. lra.
    - iDestruct "H" as "(%&%&%&%&%&%&%&%Hineq&H)".
      erewrite urns_f_distr_split; [|done..].
      rewrite -dbind_assoc'.
      iApply (step_fupdN_mono _ _ _ (⌜_⌝)%I).
      { iPureIntro.
        intros H'.
        eapply pgl_mon_grading; first apply Hineq.
        exact H'.
      }
      iMod (pgl_dbind_adv'  with "[][-]"); [iPureIntro| |done]; first naive_solver.
      simpl.
      iIntros (x).
      iDestruct ("H"$! x) as "H".
      case_match; last done.
      rewrite dret_id_left.
      iMod ("H") as "[H _]".
      iApply "H".
      + iPureIntro.
        simpl in *.
        etrans; first exact.
        by apply urns_support_set_insert_subset.
      + done.
      + iPureIntro.
        eapply map_Forall_impl; first done.
        simpl.
        intros ?? H'.
        etrans; first exact.
        by apply urns_support_set_insert_subset.
  Qed. 

  
  Lemma state_step_coupl_erasure (ε:nonnegreal) e σ ϕ n m Z:
    is_well_constructed_expr e = true ->
    expr_support_set e ⊆ urns_support_set (urns σ) ->
    map_Forall (λ _ v, is_well_constructed_val v = true) (heap σ) ->
    map_Forall (λ _ v, val_support_set v ⊆ urns_support_set (urns σ)) (heap σ) ->
    state_step_coupl σ ε Z -∗
    (∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}▷=>^(n)
                               ⌜pgl (urns_f_distr (σ2.(urns)) ≫= λ f,
                                       d_proj_Some (urn_subst_expr f e) ≫= λ e',
                                         d_proj_Some (urn_subst_heap f (σ2.(heap))) ≫= λ hm, 
                                           exec (n) (e', {|heap:=hm; urns:=m|})) ϕ ε2⌝) -∗
    |={∅}=> |={∅}▷=>^(n)
             ⌜pgl (urns_f_distr (σ.(urns)) ≫= λ f,
                                       d_proj_Some (urn_subst_expr f e) ≫= λ e',
                                         d_proj_Some (urn_subst_heap f (σ.(heap))) ≫= λ hm, 
                                           exec (n) (e', {|heap:=hm; urns:=m|})) ϕ ε⌝.
  Proof.
    iIntros (He Hset Hforall1 Hforall2) "H HZ".
    iRevert (Hset Hforall1 Hforall2).
    iRevert "H HZ".
    iRevert (σ ε).
    iApply state_step_coupl_ind.
    iModIntro.
    iIntros (??) "[%|[H|[H|H]]] HZ %Hset %Hforall1 %Hforall2".
    - iApply step_fupdN_intro; first done.
      iPureIntro. by apply pgl_1.
    - by iMod ("HZ" with "[$]").  
    - iApply (step_fupdN_mono _ _ _ (⌜_⌝)%I).
      { iPureIntro.
        intros H'.
        apply pgl_epsilon_limit; last exact.
        apply Rle_ge.
        apply cond_nonneg.
      }
      iIntros (ε' ?).
      unshelve iDestruct ("H" $! (mknonnegreal ε' _) with "[]") as "[H _]"; last first. 
      + iApply ("H" with "[-]"); [|done..].
        iIntros (??) "?".
        iMod ("HZ" with "[$]").
        by iApply (step_fupdN_mono _ _ _ (⌜_⌝)%I).
      + done.
      + pose proof cond_nonneg ε.
        simpl in *. lra. 
    - iDestruct "H" as "(%&%&%&%&%&%&%&%Hineq&H)".
      erewrite urns_f_distr_split; [|done..].
      rewrite -dbind_assoc'.
      iApply (step_fupdN_mono _ _ _ (⌜_⌝)%I).
      { iPureIntro.
        intros H'.
        eapply pgl_mon_grading; first apply Hineq.
        exact H'.
      }
      iMod (pgl_dbind_adv'  with "[][-]"); [iPureIntro| |done]; first naive_solver.
      simpl.
      iIntros (x).
      iDestruct ("H"$! x) as "H".
      case_match; last done.
      rewrite dret_id_left.
      iMod ("H") as "[H _]".
      iApply ("H" with "[-]").
      + iIntros (??) "?".
        by iMod ("HZ" with "[$]").
      + iPureIntro. 
        etrans; first exact.
        by apply urns_support_set_insert_subset.
      + done.
      + iPureIntro.
        eapply map_Forall_impl; first done.
        simpl.
        intros ?? H'.
        etrans; first exact.
        by apply urns_support_set_insert_subset.
  Qed. 
  

  Lemma prog_coupl_erasure (ε:nonnegreal) e σ ϕ n m Z:
    is_well_constructed_expr e = true ->
    expr_support_set e ⊆ urns_support_set (urns σ) ->
    map_Forall (λ _ v, is_well_constructed_val v = true) (heap σ) ->
    map_Forall (λ _ v, val_support_set v ⊆ urns_support_set (urns σ)) (heap σ) ->
    prog_coupl e σ ε Z -∗
    (∀ e2 σ2 ε2, Z e2 σ2 ε2 ={∅}=∗ |={∅}▷=>^(S n)
                               ⌜pgl (urns_f_distr (σ2.(urns)) ≫= λ f,
                                       d_proj_Some (urn_subst_expr f e2) ≫= λ e',
                                         d_proj_Some (urn_subst_heap f (σ2.(heap))) ≫= λ hm, 
                                           exec (n) (e', {|heap:=hm; urns:=m|})) ϕ ε2⌝) -∗
    |={∅}=> |={∅}▷=>^(S n)
             ⌜pgl (urns_f_distr (σ.(urns)) ≫= λ f,
                                       d_proj_Some (urn_subst_expr f e) ≫= λ e',
                                         d_proj_Some (urn_subst_heap f (σ.(heap))) ≫= λ hm, 
                                           exec (S n) (e', {|heap:=hm; urns:=m|})) ϕ ε⌝.
  Proof.
    rewrite /prog_coupl.
    iIntros (He1 He2 Hforall1 Hforall2) "(%ε2&%Hred&%Hbound&%Hineq&H) Hrest".
    iApply (step_fupdN_mono _ _ _ (⌜_⌝)%I).
    { iPureIntro.
      intros H'.
      eapply pgl_mon_grading; first apply Hineq.
      simpl.
      erewrite dbind_ext_right_strong; first apply H'.
      intros.
      apply dbind_ext_right_strong.
      intros.
      apply dbind_ext_right_strong.
      intros.
      inv_distr.
      erewrite urn_subst_expr_not_val; first done; last done.
      apply reducible_not_final in Hred.
      rewrite /is_final in Hred.
      simpl in *.
      destruct (to_val _); naive_solver.
    }
    rewrite /reducible in Hred.
    (* annoying rewrites *)
    erewrite (dbind_ext_right); last first.
    { intros. apply dbind_ext_right.
      intros. by rewrite dbind_assoc-/exec.
    }
    erewrite dbind_ext_right'; last done; last first.
    { intros.
      by apply dbind_assoc'.
    }
    rewrite dbind_assoc'.
    rewrite (delay_prob_lang_commute e σ m); [|done..].
    rewrite -!dbind_assoc'.
    iApply pgl_dbind_adv'; first (iPureIntro; naive_solver).
    iIntros ([??]).
    iMod ("H" $! _ _).
    erewrite (distr_ext (dbind _ _)); first iApply ("Hrest" with "[$]").
    intros.
    rewrite -dbind_assoc'.
    f_equal.
    apply dbind_ext_right.
    intros.
    rewrite -dbind_assoc'.
    apply dbind_ext_right.
    intros.
    rewrite -!dbind_assoc'.
    apply dbind_ext_right.
    intros.
    by rewrite dret_id_left'.
  Qed. 
  
  Theorem wp_elton_adequacy (ε: nonnegreal) e σ ϕ n m :
    is_well_constructed_expr e = true ->
    expr_support_set e ⊆ urns_support_set (urns σ) ->
    map_Forall (λ _ v, is_well_constructed_val v = true) (heap σ) ->
    map_Forall (λ _ v, val_support_set v ⊆ urns_support_set (urns σ)) (heap σ) ->
    state_interp σ ∗ err_interp (ε) ∗ WP e {{ v, |={⊤, ∅}=> rupd ϕ v }} ⊢
    |={⊤,∅}=> |={∅}▷=>^n
               ⌜pgl (urns_f_distr (σ.(urns)) ≫= λ f,
                       d_proj_Some (urn_subst_expr f e) ≫= λ e',
                         d_proj_Some (urn_subst_heap f (σ.(heap))) ≫= λ hm, 
                           exec n (e', {|heap:=hm; urns:=m|})) ϕ ε⌝.
  Proof.
    iIntros (He Hsubset Hforall1 Hforall2).
    iInduction n as [|n] "IH" forall (e σ ε He Hsubset Hforall1 Hforall2);
      iIntros "((Hσh & Hσt) & Hε & Hwp)".
    - destruct (to_val e) eqn:Heqn.
      + apply of_to_val in Heqn as <-.
        iApply wp_elton_adequacy_val; [done..|iFrame].
      + iApply fupd_mask_intro; first set_solver.
        iIntros.
        iPureIntro.
        replace (dbind _ _) with (dzero: distr val); first (apply pgl_dzero, Rle_ge, cond_nonneg).
        symmetry.
        apply dbind_dzero_strong.
        intros ? H1.
        apply dbind_dzero_strong.
        intros ? H2.
        apply dbind_dzero_strong.
        intros ? H3.
        simpl.
        inv_distr.
        by erewrite urn_subst_expr_not_val.
    - destruct (to_val e) eqn:Heqn.
      + apply of_to_val in Heqn as <-.
        iApply wp_elton_adequacy_val; [done..|iFrame].
      + rewrite pgl_wp_unfold/pgl_wp_pre.
        iMod ("Hwp" with "[$]") as "Hwp".
        iSimpl in "Hwp".
        rewrite Heqn.
        iDestruct (state_step_coupl_preserve with "[$]") as "Hwp"; [done..|].
        iApply (state_step_coupl_erasure _ _ _ _ (S n) with "[-]"); [done..|].
        clear Hsubset Hforall1 Hforall2.
        iIntros (σ2 ε2) "(%Hsubset&%Hforall1&%Hforall2&Hwp)". 
        iDestruct (prog_coupl_preserve with "[][$]") as "Hwp"; [done..| |].
        { iModIntro. iIntros. iNext. by iApply state_step_coupl_ret_err_ge_1. }
        iApply (prog_coupl_erasure with "[$]"); [done..|].
        clear He Hsubset Hforall1 Hforall2.
        iIntros (e3 σ3 ε3) "([(%He&%Hsubset&%Hforall1&%Hforall2)|%Hineq]&Hwp)"; last first.
        { iApply step_fupdN_intro; first done.
          iPureIntro. by apply pgl_1. }
        iModIntro.
        simpl.
        iModIntro. iNext.
        iDestruct (state_step_coupl_preserve with "[$]") as "Hwp"; [done..|].
        iApply (state_step_coupl_erasure with "[$]"); [done..|].
        clear Hsubset Hforall1 Hforall2.
        iIntros (σ4 ε4) "(%Hsubset&%Hforall1&%Hforall2&Hwp)".
        iMod "Hwp" as "?".
        by iApply ("IH" with "[][][][]").
  Qed. 
  
End adequacy.

Class eltonGpreS Σ := EltonGpreS {
  eltonGpreS_iris  :: invGpreS Σ;
  eltonGpreS_heap  :: ghost_mapG Σ loc val;
  eltonGpreS_urns :: ghost_mapG Σ loc urn;
  eltonGpreS_err   :: ecGpreS Σ;
                        }.

Definition eltonΣ : gFunctors :=
  #[invΣ; ghost_mapΣ loc val;
    ghost_mapΣ loc urn;
    GFunctor (authR nonnegrealUR)].
Global Instance subG_eltonGPreS {Σ} : subG eltonΣ Σ → eltonGpreS Σ.
Proof. solve_inG. Qed.

Theorem elton_adequacy_stratified Σ `{eltonGpreS Σ} (e:expr) (σ:state) (ε:R) m ϕ n:
  is_well_constructed_expr e = true ->
  expr_support_set e ⊆ urns_support_set (urns σ) ->
  map_Forall (λ _ v, is_well_constructed_val v = true) (heap σ) ->
  map_Forall (λ _ v, val_support_set v ⊆ urns_support_set (urns σ)) (heap σ) ->
  (0<=ε)%R ->
  (∀ `{eltonGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, |={⊤, ∅}=> rupd ϕ v }}) ->
  pgl (urns_f_distr (σ.(urns)) ≫= λ f,
         d_proj_Some (urn_subst_expr f e) ≫= λ e',
           d_proj_Some (urn_subst_heap f (σ.(heap))) ≫= λ hm, 
            exec n (e', {|heap:=hm; urns:=m|})) ϕ ε
.
Proof.
  intros Htrue Hsubset Hforall1 Hforall2 Hε Hwp.
  eapply pure_soundness, (step_fupdN_soundness_no_lc _ n 0).
  iIntros (Hinv) "_".
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh _]]".
  iMod (ghost_map_alloc σ.(urns)) as "[%γU [Hu _]]".
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iClear "Hh Hu".
    iApply (fupd_mask_intro); [eauto|].
    iIntros "_".
    iApply step_fupdN_intro; [eauto|].
    iApply laterN_intro; iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /pgl; intros.
    eapply Rle_trans; [eapply prob_le_1|done]. }
  set ε' := mknonnegreal _ Hε.
  iMod (ec_alloc ε') as (?) "[? ?]"; [done|].
  set (HeltonGS := HeapG Σ _ _ _ γH γU _).
  iApply (wp_elton_adequacy ε'); try done.
  iFrame.
  by iApply Hwp.
Qed. 

Theorem elton_adequacy_with_conditions Σ `{eltonGpreS Σ} (e:expr) (σ:state) (ε:R) m ϕ:
  is_well_constructed_expr e = true ->
  expr_support_set e ⊆ urns_support_set (urns σ) ->
  map_Forall (λ _ v, is_well_constructed_val v = true) (heap σ) ->
  map_Forall (λ _ v, val_support_set v ⊆ urns_support_set (urns σ)) (heap σ) ->
  (0<=ε)%R ->
  (∀ `{eltonGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, |={⊤, ∅}=> rupd ϕ v }}) ->
  pgl (urns_f_distr (σ.(urns)) ≫= λ f,
         d_proj_Some (urn_subst_expr f e) ≫= λ e',
           d_proj_Some (urn_subst_heap f (σ.(heap))) ≫= λ hm, 
            lim_exec (e', {|heap:=hm; urns:=m|})) ϕ ε
.
Proof.
  intros.
  rewrite /pgl.
  erewrite (prob_Sup_seq _ (λ n, (urns_f_distr (σ.(urns)) ≫= λ f,
         d_proj_Some (urn_subst_expr f e) ≫= λ e',
           d_proj_Some (urn_subst_heap f (σ.(heap))) ≫= λ hm, 
             exec n (e', {|heap:=hm; urns:=m|})))).
  - rewrite -rbar_le_rle.
    rewrite rbar_finite_real_eq.
    + apply upper_bound_ge_sup.
      intros.
      by eapply elton_adequacy_stratified. 
    + apply (is_finite_bounded 0 1).
      * eapply (Sup_seq_minor_le _ _ 0).
        apply prob_ge_0.
      * apply upper_bound_ge_sup.
        intros. apply prob_le_1.
  - intros.
    eassert (dbind _ _ a = Sup_seq (λ n : nat,
       (urns_f_distr (urns σ)
        ≫= λ f : gmap loc nat,
             d_proj_Some (urn_subst_expr f e)
             ≫= λ e' : language.expr d_prob_lang,
                  d_proj_Some (urn_subst_heap f (heap σ))
                    ≫= λ hm : gmap loc val, exec n (e', {| heap := hm; urns := m |})) a)) as ->; last first.
    { rewrite rbar_finite_real_eq; [apply Sup_seq_correct|apply is_finite_Sup_seq_distr]. }
    apply dbind_Sup_seq; last first.
    { intros. apply: SeriesC_le; last (apply pmf_ex_seriesC_mult_fn; exists 1; naive_solver).
      intros. split; first real_solver.
      apply Rmult_le_compat_l; first done.
      apply: SeriesC_le; last (apply pmf_ex_seriesC_mult_fn; exists 1; naive_solver).
      intros. split; first real_solver.
      apply Rmult_le_compat_l; first done.
      apply exec_mono.
    }
    intros.
    eassert (dbind _ _ a = Sup_seq (λ n : nat,
       (d_proj_Some (urn_subst_expr a0 e)
        ≫= λ e' : language.expr d_prob_lang,
             d_proj_Some (urn_subst_heap a0 (heap σ))
               ≫= λ hm : gmap loc val, exec n (e', {| heap := hm; urns := m |})) a)) as ->; last first.
    { rewrite rbar_finite_real_eq; [apply Sup_seq_correct|apply is_finite_Sup_seq_distr]. }
    apply dbind_Sup_seq; last first.
    { intros. apply: SeriesC_le; last (apply pmf_ex_seriesC_mult_fn; exists 1; naive_solver).
      intros. split; first real_solver.
      apply Rmult_le_compat_l; first done.
      apply exec_mono.
    }
    intros.
    eassert (dbind _ _ a = Sup_seq (λ n : nat,
       (d_proj_Some (urn_subst_heap a0 (heap σ))
        ≫= λ hm : gmap loc val, exec n (a1, {| heap := hm; urns := m |})) a)) as ->; last first.
    { rewrite rbar_finite_real_eq; [apply Sup_seq_correct|apply is_finite_Sup_seq_distr]. }
    apply dbind_Sup_seq; last first.
    { intros.
      apply: exec_mono.
    }
    intros.
    rewrite lim_exec_unfold.
    rewrite rbar_finite_real_eq; [apply Sup_seq_correct|apply is_finite_Sup_seq_distr].
  - intros. apply: SeriesC_le; last (apply pmf_ex_seriesC_mult_fn; exists 1; naive_solver).
    intros. split; first real_solver.
    apply Rmult_le_compat_l; first done.
    apply: SeriesC_le; last (apply pmf_ex_seriesC_mult_fn; exists 1; naive_solver).
    intros. split; first real_solver.
    apply Rmult_le_compat_l; first done.
    apply: SeriesC_le; last (apply pmf_ex_seriesC_mult_fn; exists 1; naive_solver).
    intros. split; first real_solver.
    apply Rmult_le_compat_l; first done.
    apply exec_mono.
Qed. 

Theorem elton_adequacy_without_conditions Σ `{eltonGpreS Σ} (e:expr) (σ:state) (ε:R) m ϕ:
  (0<=ε)%R ->
  (∀ `{eltonGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, |={⊤, ∅}=> rupd ϕ v }}) ->
  pgl (urns_f_distr (σ.(urns)) ≫= λ f,
         d_proj_Some (urn_subst_expr f e) ≫= λ e',
           d_proj_Some (urn_subst_heap f (σ.(heap))) ≫= λ hm, 
            lim_exec (e', {|heap:=hm; urns:=m|})) ϕ ε
.
Proof.
  intros.
  destruct (is_well_constructed_expr e) eqn:?; last first.
  { erewrite (distr_ext _ _); first (apply pgl_dzero; lra).
    simpl.
    intros ?.
    rewrite dzero_0.
    rewrite {1}/dbind{1}/dbind_pmf{1}/pmf.
    setoid_rewrite is_well_constructed_expr_false; last done.
    setoid_rewrite d_proj_Some_None.
    apply SeriesC_0.
    intros.
    rewrite dbind_dzero dzero_0. lra.
  }
  destruct (decide (expr_support_set e ⊆ urns_support_set (urns σ))); last first.
  { erewrite (distr_ext _ _); first (apply pgl_dzero; lra).
    simpl.
    intros ?.
    rewrite dzero_0.
    erewrite dbind_eq; [by erewrite dzero_dbind| |done].
    simpl. intros f.
    rewrite urns_f_distr_pos.
    intros H'%urns_f_valid_support.
    rewrite expr_support_set_not_support.
    - rewrite d_proj_Some_None. by rewrite dbind_dzero.
    - by rewrite -H'.
  }
  destruct (decide (map_Forall (λ _ v, is_well_constructed_val v = true) (heap σ))); last first.
  {
    erewrite (distr_ext _ _); first (apply pgl_dzero; lra).
    simpl.
    intros ?.
    rewrite dzero_0.
    erewrite dbind_eq; [by erewrite dzero_dbind| |done].
    simpl. intros f.
    rewrite urns_f_distr_pos.
    intros H'%urns_f_valid_support.
    erewrite dbind_eq; [by erewrite dzero_dbind| |done].
    intros ?.
    intros.
    simpl.
    rewrite heap_not_well_constructed; last done. 
    rewrite d_proj_Some_None. by rewrite dbind_dzero.
  }
  destruct (decide (  map_Forall (λ _ v, val_support_set v ⊆ urns_support_set (urns σ)) (heap σ))); first by eapply elton_adequacy_with_conditions.
  erewrite (distr_ext _ _); first (apply pgl_dzero; lra).
  simpl.
  intros ?.
  rewrite dzero_0.
  erewrite dbind_eq; [by erewrite dzero_dbind| |done].
  simpl. intros f.
  rewrite urns_f_distr_pos.
  intros H'%urns_f_valid_support.
  erewrite dbind_eq; [by erewrite dzero_dbind| |done].
  intros ?.
  intros.
  simpl.
  rewrite heap_support_set_not_support.
  - rewrite d_proj_Some_None. by rewrite dbind_dzero.
  - by rewrite -H'.
Qed. 


