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

Local Ltac unfolder :=
  repeat 
  (match goal with
  | H : context[is_well_constructed_expr (fill _ _)] |- _ => rewrite is_well_constructed_fill in H; simpl in *; andb_solver; simpl in *
  | H: _ ∪ _ ⊆ _ |- _ => apply union_subseteq in H as [??]; simpl in *
  | H: context[expr_support_set(fill _ _)] |- _ => rewrite support_set_fill in H; simpl in *
   end).

Local Ltac expr_exists_solver :=
  eapply urn_subst_expr_exists; first done;
      erewrite <-urns_f_valid_support; first done;
      by apply urns_f_distr_pos.
      
Local Ltac val_exists_solver :=
  eapply urn_subst_val_exists; first done;
      erewrite <-urns_f_valid_support; first done;
  by apply urns_f_distr_pos.

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
  inversion Hpred as [| | | |f x e1 v2|op v ? v'|op v1 v2 ? v'| bl e1 e2 |bl e1 e2|v1 v2 |v1 v2 |v e1 e2 | v e1 e2| z N v ? l|l v|l v w|N ? z bl|N ? z bl]; subst.
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
    unfolder.
    rename select (gmap _ _) into a.
    assert (∃ v', urn_subst_val a v2 = Some v') as [? Hrewrite] by val_exists_solver.
    assert (∃ e', urn_subst_expr a e1 = Some e') as [? Hrewrite'] by expr_exists_solver.
    erewrite urn_subst_expr_subst'; last first.
    + done.
    + erewrite urn_subst_expr_subst'; try done.
      simpl. apply bind_Some. naive_solver.
    + rewrite Hrewrite' Hrewrite. 
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    by repeat smash.
  - (** un op *)
    repeat smash.
    case_match; simplify_eq.
    repeat smash.
    unfolder.
    assert (∃ v', urn_subst_val a v = Some v') as [? Hrewrite] by val_exists_solver.
    rewrite Hrewrite.
    repeat smash.
    rename select (un_op_eval _ _ = _) into Hop.
    unshelve eapply urn_subst_val_un_op in Hop as Hop'; last done.
    destruct Hop' as [?[Hrewrite' Hrewrite'']].
    rewrite Hrewrite'. repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    simpl. rewrite Hrewrite''. by repeat smash.
  - (** bin op *)
    repeat smash.
    case_match; simplify_eq.
    repeat smash.
    unfolder.
    assert (∃ v', urn_subst_val a v1 = Some v') as [? Hrewrite1] by val_exists_solver.
    assert (∃ v', urn_subst_val a v2 = Some v') as [? Hrewrite2] by val_exists_solver.
    rewrite Hrewrite1 Hrewrite2.
    repeat smash.
    rename select (bin_op_eval _ _ _=_) into Hop.
    unshelve eapply urn_subst_val_bin_op in Hop as Hop'; [..|done|done].
    destruct Hop' as [?[Hrewrite' Hrewrite'']].
    rewrite Hrewrite'. repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    simpl. rewrite Hrewrite''. by repeat smash. 
  - (** if true *)
    repeat smash.
    rewrite bool_decide_eq_true_2; last done.
    repeat smash.
    rename select (urn_subst_equal _ _ _) into H.
    inv_distr.
    rewrite H; last by apply urns_f_distr_pos.
    repeat smash.
    unfolder.
    assert (∃ e', urn_subst_expr a e2 = Some e') as [? Hrewrite] by expr_exists_solver.
    rewrite Hrewrite.
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    simpl. rewrite bool_decide_eq_true_2.
    + by rewrite dmap_dret.
    + by apply urn_subst_equal_obv.
  - (** if false *)
    repeat smash.
    rename select (urn_subst_equal _ _ _) into H.
    rewrite bool_decide_eq_false_2; last first.
    { intros H'.
      eapply urn_subst_equal_unique in H; last done.
      simplify_eq. 
    }
    rewrite bool_decide_eq_true_2; last done.
    repeat smash.
    unfolder.
    rewrite H; last by apply urns_f_distr_pos.
    repeat smash.
    unfolder.
    assert (∃ e', urn_subst_expr a e1 = Some e') as [? Hrewrite] by expr_exists_solver.
    rewrite Hrewrite.
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    simpl. rewrite bool_decide_eq_false_2.
    + rewrite bool_decide_eq_true_2.
      * by rewrite dmap_dret.
      * by apply urn_subst_equal_obv.
    + intros Hcontra.
      eapply urn_subst_equal_not_unique; first done.
      * by apply urn_subst_equal_obv.
      * done.
  - (** fst *)
    repeat smash.
    inv_distr.
    unfolder.
    assert (∃ v', urn_subst_val a v2 = Some v') as [? Hrewrite] by val_exists_solver.
    rewrite Hrewrite/=.
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    rewrite dmap_dret//.
  - (** snd *)
    repeat smash.
    inv_distr.
    unfolder.
    assert (∃ v', urn_subst_val a v1 = Some v') as [? Hrewrite] by val_exists_solver.
    rewrite Hrewrite/=.
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    rewrite dmap_dret//.
  - (** case inl *)
    repeat smash.
    inv_distr.
    unfolder.
    assert (∃ v', urn_subst_val a v = Some v') as [? Hrewrite] by val_exists_solver.
    rewrite Hrewrite/=.
    repeat smash.
    assert (∃ e2', urn_subst_expr a e2 = Some e2') as [? Hrewrite1] by expr_exists_solver.
    rewrite Hrewrite1/=.
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    rewrite dmap_dret//.
  - (** case inr *)
    repeat smash.
    inv_distr.
    unfolder.
    assert (∃ v', urn_subst_val a v = Some v') as [? Hrewrite] by val_exists_solver.
    rewrite Hrewrite/=.
    repeat smash.
    assert (∃ e1', urn_subst_expr a e1 = Some e1') as [? Hrewrite1] by expr_exists_solver.
    rewrite Hrewrite1/=.
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    rewrite dmap_dret//.
  - (** allocN *)
    repeat smash.
    case_bool_decide; last lia.
    repeat smash.
    inv_distr.
    unfolder.
    assert (∃ v', urn_subst_val a v = Some v') as [? Hrewrite] by val_exists_solver.
    rewrite Hrewrite/=.
    repeat smash.
    admit.
  - (** load *)
    repeat smash.
    case_match; simplify_eq.
    repeat smash.
    inv_distr.
    unfolder.
    case_match; simplify_eq.
    destruct Hstep'; inv_distr.
    assert (∃ v', urn_subst_val a v = Some v') as [? Hrewrite].
    { eapply urn_subst_val_exists.
      - rewrite map_Forall_lookup in Hforall1.
        naive_solver.
      - rewrite map_Forall_lookup in Hforall2.
        erewrite <-urns_f_valid_support; last by apply urns_f_distr_pos.
        naive_solver.
    }
    rewrite Hrewrite/=.
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    inv_distr.
    rename select (mapM _ _ = Some _) into H'.
    apply mapM_Some in H'.
    rename select (list _) into ml.
    eassert (∃ i, map_to_list (heap σ) !! i = Some (_,_)) as [].
    { rename select (_!!_=Some _) into K'.
      rewrite -elem_of_map_to_list in K'.
      by apply elem_of_list_lookup in K'. }
    eassert (list_to_map ml !! l = Some _) as Hrewrite'.
    {
      eapply elem_of_list_to_map.
      - replace (ml.*1) with ((map_to_list (heap σ)).*1); first apply NoDup_fst_map_to_list.
        apply list_eq_Forall2.
        apply Forall2_fmap_2.
        eapply Forall2_impl; first done.
        simpl.
        intros [] [].
        rewrite bind_Some.
        intros.
        by destruct!/=.
      - rewrite elem_of_list_lookup.
        eapply Forall2_lookup_l in H'; last done.
        destruct H' as [[][? H']].
        rewrite bind_Some in H'.
        destruct!/=.
        naive_solver.
    }
    erewrite head_prim_step_eq; last first.
    { rewrite /head_reducible/=.
      rewrite Hrewrite'.
      eexists _; solve_distr. 
    }
    simpl.
    rewrite Hrewrite'.
    rewrite dmap_dret//.
  - (** store *)
    repeat smash.
    case_match; simplify_eq.
    repeat smash.
    admit.
  - (** rand *)
    repeat smash.
    case_match; last first.
    { exfalso. naive_solver. }
    repeat smash.
    erewrite urn_subst_equal_epsilon_unique; last done.
    erewrite (distr_ext (dbind _ (dunifP _))); last first.
    { intros.
      apply dbind_pmf_ext; [|done..].
      intros. by rewrite !dret_id_left'/=.
    }
    rewrite dbind_comm.
    apply dbind_ext_right_strong.
    intros.
    repeat smash.
    setoid_rewrite urn_subst_expr_fill.
    repeat smash.
    setoid_rewrite d_proj_Some_bind.
    rewrite (dbind_assoc' _ _ (dunifP _)).
    rewrite (dbind_comm _ (dunifP _)).
    repeat smash.
    rewrite H; last by apply urns_f_distr_pos.
    repeat smash.
    erewrite (distr_ext (dbind _ (dunifP _))); last first.
    { intros.
      apply dbind_pmf_ext; [|done..].
      intros. by rewrite !dret_id_left'/=.
    }
    rewrite dbind_comm.
    repeat smash.
    rewrite fill_prim_step_dbind; last done.
    rewrite head_prim_step_eq.
    simpl.
    case_match; last (exfalso; naive_solver).
    rewrite dmap_comp.
    rewrite /dmap.
    erewrite urn_subst_equal_epsilon_unique; last by apply urn_subst_equal_obv.
    by repeat smash.
  - (** drand *)
    repeat smash.
    case_match; last first.
    { exfalso. naive_solver. }
    repeat smash.
    admit. 
Admitted. 
