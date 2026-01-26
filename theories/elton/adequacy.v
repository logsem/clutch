From iris.proofmode Require Import base proofmode.
From iris.bi Require Export weakestpre fixpoint big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.
From Coquelicot Require Import Rbar Lim_seq.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.delay_prob_lang Require Import notation metatheory urn_subst.
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
  map_Forall (λ _ v, val_support_set v ⊆ urns_support_set (urns σ)) (heap σ) ->
  (0<=ε)%R ->
  (∀ `{eltonGS Σ}, ⊢ ↯ ε -∗ WP e {{ rupd ⊤ ∅ ϕ }}) ->
  pgl (urns_f_distr (σ.(urns)) ≫= λ f,
         d_proj_Some (urn_subst_expr f e) ≫= λ e',
           d_proj_Some (urn_subst_heap f (σ.(heap))) ≫= λ hm, 
            exec n (e', {|heap:=hm; urns:=m|})) ϕ ε
.
Proof.
Admitted. 

Theorem elton_adequacy_with_conditions Σ `{eltonGpreS Σ} (e:expr) (σ:state) (ε:R) m ϕ:
  is_well_constructed_expr e = true ->
  expr_support_set e ⊆ urns_support_set (urns σ) ->
  map_Forall (λ _ v, val_support_set v ⊆ urns_support_set (urns σ)) (heap σ) ->
  (0<=ε)%R ->
  (∀ `{eltonGS Σ}, ⊢ ↯ ε -∗ WP e {{ rupd ⊤ ∅ ϕ }}) ->
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
  (∀ `{eltonGS Σ}, ⊢ ↯ ε -∗ WP e {{ rupd ⊤ ∅ ϕ }}) ->
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
