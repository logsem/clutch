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

Local Ltac heap_exists_solver :=
  eapply urn_subst_heap_exists; first done;
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
    rewrite !dret_id_left'/=.
    repeat smash.
    inv_distr.
    unfolder.
    assert (∃ v', urn_subst_val a v = Some v') as [? Hrewrite] by val_exists_solver.
    rewrite Hrewrite/=.
    rewrite !dret_id_left'.
    rewrite -d_proj_Some_fmap.
    rewrite dbind_assoc'.
    rewrite -d_proj_Some_fmap.
    rewrite -!/(urn_subst_heap _ _).
    assert (∃ h, urn_subst_heap a (heap σ) = Some h) as [? Hrewrite'] by heap_exists_solver.
    assert (∃ h, urn_subst_heap a (heap_array (fresh_loc (heap σ)) (replicate (Z.to_nat z) v) ) = Some h) as [? Hrewrite''].
    { eapply urn_subst_heap_exists.
      - apply map_Forall_lookup_2.
        intros ??. rewrite heap_array_lookup.
        intros [?[K1 [K2 K3]]]. subst.
        apply lookup_replicate in K3. by destruct!/=.
      - apply map_Forall_lookup_2.
        intros ??. rewrite heap_array_lookup.
        intros [?[K1 [K2 K3]]]. subst.
        apply lookup_replicate in K3.
        destruct!/=.
        etrans; first exact.
        erewrite urns_f_valid_support; last by apply urns_f_distr_pos. done. }
    erewrite urn_subst_heap_union; [..|done|done]; last first.
    + apply heap_array_disjoint.
    + rewrite Hrewrite'. smash.
      rewrite fill_prim_step_dbind; last done.
      rewrite head_prim_step_eq.
      simpl.
      rewrite bool_decide_eq_true_2; last done.
      smash.
      do 2 f_equal.
      * do 4 f_equal.
        apply fresh_loc_eq_dom.
        symmetry. by eapply urn_subst_heap_dom.
      * rewrite /state_upd_heap_N. simpl.
        do 2 f_equal.
        eapply urn_subst_heap_replicate; try done.
        replace (fresh_loc _) with (fresh_loc (heap σ)); first done.
        apply fresh_loc_eq_dom.
        by eapply urn_subst_heap_dom.
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
    unfolder.
    assert (∃ v', urn_subst_val a w = Some v') as [? Hrewrite] by val_exists_solver.
    rewrite Hrewrite.
    smash.
    rewrite dbind_assoc'.
    rewrite -d_proj_Some_fmap.
    rewrite dbind_assoc'.
    rewrite -d_proj_Some_fmap.
    rewrite -!/(urn_subst_heap _ _).
    assert (∃ h, urn_subst_heap a (heap σ) = Some h) as [h Hrewrite'] by heap_exists_solver.
    assert (is_Some(h!!l) ) as [? K'].
    { rewrite <-elem_of_dom. erewrite <-urn_subst_heap_dom; last done.
      rewrite elem_of_dom. naive_solver.
    }
    destruct!/=.
    rewrite Hrewrite'.
    erewrite urn_subst_heap_insert'; [| |done|done]; last first.
    { rewrite elem_of_dom. naive_solver. }
    smash.
    rewrite fill_prim_step_dbind; last done.
    erewrite head_prim_step_eq; last first.
    { rewrite -head_step_pred_head_reducible.
      by eapply StoreHSP. }
    smash.
    rewrite K'.
    by smash.
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
    erewrite urn_subst_equal_epsilon_unique; last done.
    erewrite urns_f_distr_insert; last first.
    { rewrite size_list_to_set; last apply NoDup_seq.
      rewrite seq_length.
      instantiate (1:=Z.to_nat z). lia.
    }
    { apply fresh_loc_is_fresh. }
    unfolder.
    repeat smash.
    assert (exists K', mapM (urn_subst_ectx_item a) K = Some K') as [? Hrewrite].
    { apply mapM_is_Some_2.
      rewrite Forall_forall.
      setoid_rewrite elem_of_list_lookup.
      intros. simpl. destruct!/=.
      eapply urn_subst_ectx_item_exists.
      - rewrite forallb_forall in H2.
        apply H2.
        rewrite -elem_of_list_In elem_of_list_lookup. naive_solver.
      - erewrite <-urns_f_valid_support; last by apply urns_f_distr_pos.
        etrans; last apply H3.
        set_unfold.
        setoid_rewrite elem_of_union_list.
        intros ??.
        eexists _; split; last done.
        rewrite elem_of_list_fmap.
        eexists _; split; first done.
        rewrite elem_of_list_lookup. naive_solver.
    }
    rewrite Hrewrite.
    smash.
    rewrite H; last by apply urns_f_distr_pos.
    smash.
    rewrite dbind_assoc'.
    rewrite -d_proj_Some_fmap.
    rewrite -!/(urn_subst_heap _ _).
    assert (∃ h, urn_subst_heap a (heap σ) = Some h) as [h Hrewrite'] by heap_exists_solver.
    rewrite Hrewrite'.
    smash.
    rewrite fill_prim_step_dbind; last done.
    unshelve epose proof H a _ as H'; first by apply urns_f_distr_pos. 
    erewrite head_prim_step_eq; last first.
    { rewrite -head_step_pred_head_reducible.
      eapply RandHSP; first by eapply urn_subst_equal_obv.
      done.
    }
    simpl.
    case_match; last done.
    case_match; last done.
    case_match; last (exfalso; naive_solver).
    erewrite urn_subst_equal_epsilon_unique; last done.
    rewrite dmap_comp.
    rewrite /dmap.
    assert (∀ (x:fin(S (Z.to_nat z))), ∃ y, elements ((list_to_set (seq 0 (Z.to_nat z + 1))):gset _) !! y = Some (fin_to_nat x)) as Hf.
    { clear.
      intros x.
      pose proof fin_to_nat_lt x.
      rewrite -elem_of_list_lookup.
      rewrite elem_of_elements.
      rewrite elem_of_list_to_set elem_of_seq. lia. }
    assert (∀ x, epsilon (Hf x)< S (Z.to_nat z))%nat as Hf'.
    { clear -Hf.
      intros a0.
      epose proof epsilon_correct _ (Hf a0) as Hcorrect.
      simpl in *.
      apply lookup_lt_Some in Hcorrect.
      rewrite -length_elements_size_gset in Hcorrect.
      rewrite size_list_to_set in Hcorrect; last apply NoDup_seq.
      rewrite seq_length in Hcorrect. lia. }
    pose (f:=λ x, nat_to_fin (Hf' x)).
    assert (Bij f) as Hbij.
    { clear. split.
      - intros x y. rewrite /f.
        intros H.
        apply (f_equal fin_to_nat) in H.
        rewrite !fin_to_nat_to_fin in H.
        epose proof epsilon_correct _ (Hf x) as Hcorrect.
        epose proof epsilon_correct _ (Hf y) as Hcorrect'.
        simpl in *.
        rewrite H in Hcorrect.
        rewrite Hcorrect' in Hcorrect. naive_solver.
      - intros x.
        rewrite /f.
        assert (∃ (n:fin (S (Z.to_nat z))), elements (list_to_set (seq 0 (Z.to_nat z + 1)) : gset nat) !! (fin_to_nat x) = Some (fin_to_nat n)) as Hfound.
        + assert (∃ n, elements (list_to_set (seq 0 (Z.to_nat z + 1)) : gset nat) !! (fin_to_nat x) = Some n /\ n < S $ Z.to_nat z)%nat as H; last first.
          { destruct H as [?[? Hineq]].
            exists (nat_to_fin Hineq).
            by rewrite fin_to_nat_to_fin. }
          assert (∃ n, elements (list_to_set (seq 0 (Z.to_nat z + 1)) : gset nat) !! (fin_to_nat x) = Some n)%nat as H.
          * apply lookup_lt_is_Some_2.
            rewrite -length_elements_size_gset size_list_to_set; last apply NoDup_seq.
            pose proof fin_to_nat_lt x.
            rewrite seq_length. lia.
          * destruct!/=.
            eexists _; split; first done.
            apply elem_of_list_lookup_2 in H.
            rewrite elem_of_elements elem_of_list_to_set elem_of_seq in H.
            lia.
        + destruct Hfound as [n H].
          exists n.
          apply fin_to_nat_inj.
          rewrite fin_to_nat_to_fin. 
          epose proof epsilon_correct _ (Hf (n)) as Hcorrect.
          simpl in *.
          eapply NoDup_alt in H; last apply Hcorrect; first done.
          apply NoDup_elements.
    } 
    apply Rcoupl_eq_elim.
    eapply Rcoupl_dbind; last first.
    { apply (Rcoupl_dunif ). apply Hbij. }
    simpl.
    intros a0 ? ->.
    rewrite /f.
    rewrite fin_to_nat_to_fin.
    epose proof epsilon_correct _ (Hf a0) as Hcorrect.
    simpl in *.
    rewrite Hcorrect.
    rewrite dret_id_left'.
    smash.
    assert (a ⊆ <[fresh_loc (urns σ):=(fin_to_nat a0)]> a).
    { apply insert_subseteq.
      rewrite -not_elem_of_dom.
      erewrite <-urns_f_valid_support; last by apply urns_f_distr_pos.
      rewrite /urns_support_set.
      rewrite elem_of_filter.
      intros [].
      pose proof fresh_loc_is_fresh (urns σ). naive_solver.
    }
    erewrite urn_subst_ectx_subset; [|done..].
    smash.
    rewrite lookup_insert.
    smash.
    rewrite dbind_assoc'.
    rewrite -d_proj_Some_fmap.
    rewrite -!/(urn_subst_heap _ _).
    erewrite urn_subst_heap_subset; [|done..].
    smash.
    apply Rcoupl_eq.
Qed. 
