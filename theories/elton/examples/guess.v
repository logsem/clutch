From clutch.elton Require Import elton. 

Section encr.
  Variable N:nat.
  
  Definition prog : expr :=
    λ: "f",
    let: "secret" := rand #N in
    let: "guess" := "f" #() in
    "secret" ≠ "guess".

  Definition prog' : expr :=
    λ: "f",
    let: "secret" := drand #N in
    let: "guess" := "f" #() in
    "secret" ≠ "guess".

  Local Opaque INR.
  
  Lemma prog_correct f:
    ∅ ⊢ₜ f : (TUnit → TNat) ->
             pgl (lim_exec ((prog f), {|heap:=∅; urns:= ∅|})) (λ v, v=#true) (1/(S N)).
  Proof.
    intros Htyped.
    eapply (elton_adequacy_remove_drand eltonΣ (prog' f)).
    - simpl. by erewrite typed_remove_drand_expr.
    - apply Rdiv_INR_ge_0.
    - rewrite /prog'.
      iIntros (?) "Herr".
      iPoseProof (typed_safe _ [] _ Htyped) as "H".
      wp_bind (f).
      iApply (pgl_wp_wand); first done.
      iIntros (?) "#Hinterp".
      simpl.
      wp_pures.
      wp_apply (wp_drand_thunk _ _ _ _ _ (True)).
      + rewrite rupd_unseal/rupd_def.
        iIntros (?) "$".
        iPureIntro.
        intros.
        simpl.
        eexists _; split; first done.
        f_equal.
        f_equal. 
        instantiate (1:=N).
        lia.
      + iIntros (?) "[_ Hl]".
        rewrite Nat2Z.id.
        rewrite -Nat.add_1_r.
        wp_pures.
        rewrite refines_eq /refines_def.
        wp_bind (v _)%E.
        iApply (pgl_wp_wand); first by iApply "Hinterp".
        simpl.
        iIntros (?) "[%n ->]".
        destruct (decide (n<S N))%nat as [K|K].
        * (* maybe guessed right*)
          pose (ε2' := λ x, if bool_decide (x=Z.of_nat n) then 1%R else 0%R).
          assert (∀ x, 0<=ε2' x)%R as Hε2.
          { intros. rewrite /ε2'. case_bool_decide; lra. }
          iMod (pupd_resolve_urn _ _ (λ x, mknonnegreal _ (Hε2 x)) with "[$][$]") as "(%x&Herr&Hl&%Helem)".
          { apply (non_empty_inhabited_L 0%Z).
            rewrite elem_of_list_to_set elem_of_list_fmap.
            setoid_rewrite elem_of_seq.
            exists 0%nat. lia.
          }
          {
            rewrite size_list_to_set; last (apply NoDup_fmap; first apply _; apply NoDup_seq).
            rewrite length_fmap length_seq.
            simpl.
            right.
            f_equal.
            erewrite (SeriesC_ext _ (λ x, if bool_decide (x = Z.of_nat n) then 1 else 0));
              first by rewrite SeriesC_singleton_dependent.
            intros.
            symmetry.
            case_bool_decide; subst.
            - rewrite bool_decide_eq_true_2 /ε2'; first by rewrite bool_decide_eq_true_2.
              rewrite elem_of_elements elem_of_list_to_set elem_of_list_fmap.
              eexists _; split; first done.
              rewrite elem_of_seq. lia.
            - case_bool_decide as H'; last done.
              rewrite elem_of_elements elem_of_list_to_set elem_of_list_fmap in H'.
              setoid_rewrite elem_of_seq in H'.
              destruct!/=. rewrite /ε2'. by case_bool_decide.
          }
          { simpl.
            rewrite /ε2'.
            exists 1%R.
            intros.
            case_bool_decide; lra.
          }
          rewrite /ε2'.
          simpl.
          case_bool_decide.
          { iDestruct (ec_contradict with "[$]") as "[]". lra. }
          wp_pures.
          iApply fupd_mask_intro; first set_solver.
          iIntros.
          rewrite rupd_unseal/rupd_def.
          iIntros (?) "[? Hu]".
          iDestruct (ghost_map_lookup with "Hu Hl") as "%".
          iFrame.
          iPureIntro.
          intros ? Hf.
          replace (urns σ1) with (<[l:=(urn_unif {[x]})]> (delete l (urns σ1))) in Hf; last first.
          { apply map_eq.
            intros i. destruct (decide (l=i)); subst; by simplify_map_eq. }
          rewrite urns_f_distr_insert in Hf; last first.
          -- simpl.
             eapply (non_empty_inhabited_L x).
             set_solver.
          -- by simplify_map_eq.
          -- inv_distr.
             simpl. simplify_map_eq.
             rename select (urns_f_distr_compute_distr _ _>0)%R into Heq.
             rewrite /urns_f_distr_compute_distr/urns_f_distr_compute/pmf in Heq.
             rewrite size_singleton in Heq.
             replace (INR _) with 1%R in Heq by done.
             replace (/ _) with 1%R in Heq by lra.
             case_bool_decide as H2; last lra.
             set_unfold in H2.
             subst.
             case_bool_decide; first naive_solver.
             naive_solver.
        * (* guess is out of bound *)
          wp_pures.
          iApply fupd_mask_intro; first set_solver.
          iIntros.
          rewrite rupd_unseal/rupd_def.
          iIntros (?) "[? Hu]".
          iDestruct (ghost_map_lookup with "Hu Hl") as "%".
          iFrame.
          iPureIntro.
          intros ? Hf.
          apply urns_f_distr_pos in Hf as Hf'.
          simpl.
          pose proof Hf' l as H1.
          rewrite H in H1.
          case_match; destruct!/=; last first.
          { exfalso.
            apply H1.
            eapply (non_empty_inhabited_L 0%Z).
            rewrite elem_of_list_to_set elem_of_list_fmap.
            setoid_rewrite elem_of_seq.
            exists 0%nat; lia.
          }
          eexists _; split; last done.
          rewrite bool_decide_eq_false_2; first done.
          intros ?.
          simplify_eq.
          rewrite /urns_f_valid in Hf.
          replace (urns σ1) with (<[l:=(urn_unif (list_to_set (Z.of_nat <$> seq 0 (N + 1))))]> (delete l (urns σ1))) in Hf; last first.
          { apply map_eq.
            intros i. destruct (decide (l=i)); subst; by simplify_map_eq. }
          rewrite urns_f_distr_insert in Hf; last first.
          -- simpl.
            eapply (non_empty_inhabited_L 0%Z).
            rewrite elem_of_list_to_set elem_of_list_fmap.
            setoid_rewrite elem_of_seq.
            exists 0%nat; lia.
          -- by simplify_map_eq.
          -- inv_distr.
             simplify_map_eq.
             rename select (urns_f_distr_compute_distr _ _>0)%R into Hcontra.
             rewrite /urns_f_distr_compute_distr/urns_f_distr_compute/pmf in Hcontra.
             case_bool_decide as Hcontra'; last lra.
             rewrite elem_of_list_to_set elem_of_list_fmap in Hcontra'.
             setoid_rewrite elem_of_seq in Hcontra'.
             destruct!/=. lia.
  Qed. 
End encr.
