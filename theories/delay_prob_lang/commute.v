From Coq Require Import Reals Psatz.
From stdpp Require Import functions gmap stringmap fin_sets.
From clutch.prelude Require Import stdpp_ext NNRbar fin uniform_list.
From clutch.prob Require Import distribution couplings couplings_app.
From clutch.common Require Import ectx_language.
From clutch.delay_prob_lang Require Import tactics notation urn_subst metatheory.
From clutch.delay_prob_lang Require Export lang.
From clutch.prob Require Import distribution couplings.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".

Local Ltac smash := repeat (rewrite urn_subst_expr_fill|| rewrite dmap_dret||rewrite  dret_id_left' ||rewrite d_proj_Some_bind || rewrite -dbind_assoc' || rewrite dret_id_left' ||simpl);
                    try (apply dbind_ext_right_strong; intros ??; simpl).

Lemma delay_prob_lang_commute e σ m: 
  is_well_constructed_expr e = true ->
  expr_support_set e ⊆ urns_support_set (urns σ) ->
  map_Forall (λ _ v, is_well_constructed_val v = true) (heap σ) ->
  map_Forall (λ _ v, val_support_set v ⊆ urns_support_set (urns σ)) (heap σ) ->
  (∃ x, prim_step e σ x > 0) ->
  (urns_f_distr (urns σ)
     ≫= λ a, d_proj_Some (urn_subst_expr a e)
               ≫= λ a0, d_proj_Some (urn_subst_heap a (heap σ))
                          ≫= λ a1, prim_step a0 {| heap := a1; urns := m |}) =
  prim_step e σ ≫= λ '(e', σ'), 
        urns_f_distr (urns σ')
          ≫= λ f, d_proj_Some (urn_subst_expr f e')
                    ≫= λ e'', d_proj_Some (urn_subst_heap f (heap σ'))
                                ≫= λ σh, dret (e'', {|heap:=σh; urns := m |}).
Proof.
  intros He1 He2 Hforall1 Hforall2 Hstep.
  apply prim_step_iff' in Hstep as Hstep'.
  destruct Hstep' as (K&e1'&<-&Hstep'&->).
  simpl in *.
  assert (head_step_pred e1' σ) as Hpred.
  { by rewrite head_step_pred_head_reducible. }
  inversion Hpred; subst.
  - (** rec *)
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    by smash.
  - (** pair *)
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    by smash.
  - (** injL *)
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    by smash.
  - (** injR *)
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    by smash.
  - (** Application *)
    repeat smash.
    admit.
  - (** un op *)
    repeat smash.
    case_match; simplify_eq.
    repeat smash.
    admit.
  - (** bin op *)
    repeat smash.
    case_match; simplify_eq.
    repeat smash.
    admit.
  - (** if true *)
    repeat smash.
    rewrite bool_decide_eq_true_2; last done.
    repeat smash.
    admit. 
  - (** if false *)
    repeat smash.
    rewrite bool_decide_eq_false_2.
Admitted. 

