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
          pose (ε2' := λ x, if bool_decide (x=n) then 1%R else 0%R).
          assert (∀ x, 0<=ε2' x)%R as Hε2.
          { intros. rewrite /ε2'. case_bool_decide; lra. }
          iMod (pupd_resolve_urn _ _ _ _ N (λ x, mknonnegreal _ (Hε2 x)) with "[$][$]") as "Hres".
          { apply NoDup_seq. }
          { rewrite length_seq. lia. }
          { simpl.
            rewrite /Expval.
            erewrite (SeriesC_ext _ (λ (x:fin (S N)), if bool_decide (x=nat_to_fin K) then _ else 0)); last first.
            - intros.
              rewrite /ε2'.
              case_bool_decide.
              + subst. rewrite Rmult_1_r.
                rewrite /pmf/=. 
                rewrite bool_decide_eq_true_2; first done.
                apply fin_to_nat_inj. by rewrite fin_to_nat_to_fin.
              + rewrite bool_decide_eq_false_2; first real_solver.
                intros ->. by rewrite fin_to_nat_to_fin in H.
            - rewrite SeriesC_singleton.
              right.
              rewrite Rdiv_1_l.
              f_equal. f_equal. lia.
          }
          { exists 1%R. simpl.
            rewrite /ε2'.
            intros.
            case_bool_decide; lra.
          }
          simpl.
          iDestruct "Hres" as "(%&%&%Hlookup&Hl&Herr)".
          rewrite /ε2'.
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
          simpl.
          pose proof Hf l.
          case_match; destruct!/=.
          set_unfold. subst.
          rewrite lookup_seq in Hlookup.
          destruct!/=.
          case_bool_decide; naive_solver.
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
          simpl.
          pose proof Hf l.
          case_match; destruct!/=; last first.
          { rename select (∅=_) into K'.
            apply (f_equal size) in K'.
            rewrite size_empty in K'.
            rewrite size_list_to_set in K'; last apply NoDup_seq.
            rewrite length_seq in K'. lia.
          }
          eexists _; split; last done.
          rewrite bool_decide_eq_false_2; first done.
          rename select (_∈_) into K'.
          rewrite elem_of_list_to_set elem_of_seq in K'. intros ?. simplify_eq. lia.
  Qed.
  


End encr.
