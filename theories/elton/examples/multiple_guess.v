From clutch.elton Require Import elton. 
Set Default Proof Using "Type*".

Section proofs.
  Context `{eltonGS Σ}.  

  Local Lemma ind_case (M N:nat) s (v:val) l:
    N≠0->
    M<N->
    size s = N ->
    {{{ □ (∀ v1 : val, ()%lrel v1 -∗ REL v v1 : lrel_nat) ∗
        ↯ (M / N) ∗
        l↪urn_unif s }}}
      (rec: "f" "x" :=
         if: "x" = #0 then #false
         else let: "guess" := v (Val (LitV LitUnit)) in if: "guess" = #lbl:l then #true else "f" ("x" - #1))%V
      #M
      {{{ RET #false; True }}}.
  Proof.
    iIntros (Hneq Hineq Hsize Φ) "(#Hinterp&Herr&Hl) HΦ".
    iLöb as "IH" forall (M N s Hneq Hineq Hsize) "Herr Hl".
    wp_pures.
    case_bool_decide.
    { wp_pures. by iApply "HΦ". }
    wp_pures.
    rewrite refines_eq/refines_def.
    wp_bind (v _)%E.
    iApply (pgl_wp_wand); first by iApply "Hinterp".
    iIntros (?) "[%guess ->]".
    assert (Z.of_nat M ≠ 0) as Hneq'; first (intros Hrewrite; destruct!/=).
    wp_pures.
    assert (∃ x (s':gset Z), x∉s'/\{[x]}∪s' = s /\ (Z.of_nat guess) ∉ s') as (x & s' &H1 &H2&H3).
    { destruct (decide (Z.of_nat guess ∈ s)).
      - exists (Z.of_nat guess), (s∖{[Z.of_nat guess]}).
        repeat split.
        + set_solver.
        + rewrite -union_difference_L; set_solver.
        + set_solver.
      - assert (∃ x, x ∈ s) as [x ].
        + apply size_pos_elem_of. lia.
        + exists x, (s∖{[x]}).
          split; first set_solver.
          split; first (rewrite -union_difference_L; set_solver).
          set_solver.
    }
    pose (ε2 := (λ s, if bool_decide (s = s') then (M-1)/(N-1) else if bool_decide (s = {[x]}) then 1 else 0)%R).
    assert (∀ x, 0<= ε2 x)%R as Hε2.
    { intros.
      rewrite /ε2.
      repeat case_bool_decide; try lra.
      apply Rcomplements.Rdiv_le_0_compat.
      - cut (INR 1<=M)%R; first (simpl; lra).
        apply le_INR.
        simplify_eq.
        lia.
      - assert (INR 1 < N)%R; last (simpl in *; lra).
        apply lt_INR. lia.
    }
    iMod (pupd_partial_resolve_urn _ _ (λ x, mknonnegreal _ (Hε2 x)) _ _ ({[x]}:: s'::[]) with "[$][$]") as "H"; try done.
    - set_solver.
    - set_solver.
    - apply NoDup_cons; split; last apply NoDup_cons; last split; last by apply NoDup_nil.
      + rewrite elem_of_list_singleton. set_solver.
      + set_solver.
    - repeat setoid_rewrite elem_of_cons.
      intros. destruct!/=; set_solver.
    - rewrite SeriesC_list; last first.
      + apply NoDup_cons; split; last apply NoDup_cons; last split; last by apply NoDup_nil.
        * rewrite elem_of_list_singleton. set_solver.
        * set_solver.
      + Local Opaque size. simpl. rewrite size_singleton.
        rewrite /ε2.
        rewrite bool_decide_eq_false_2; last set_solver.
        rewrite bool_decide_eq_true_2; last done.
        rewrite bool_decide_eq_true_2; last done.
        subst.
        rewrite size_union; last set_solver.
        rewrite size_singleton.
        replace 1%R with (INR 1) by done.
        rewrite -!minus_INR; try lia.
        replace (_+_-_)%nat with (size s') by lia.
        right.
        f_equal.
        rewrite -Rmult_div_swap.
        rewrite Rmult_div_l; last first.
        { apply not_0_INR.
          rewrite size_union in Hineq; last set_solver.
          rewrite size_singleton in Hineq. lia.
        }
        replace (_*_)%R with (INR 1); last first.
        { simpl. lra. }
        rewrite Rplus_0_r.
        rewrite -plus_INR.
        f_equal. lia.
    - exists 1.
      intros.
      rewrite /ε2.
      simpl.
      repeat case_bool_decide; try lra.
      rewrite -Rcomplements.Rdiv_le_1.
      + assert (M<=N)%R; last lra.
        apply le_INR. lia.
      + assert (INR 1 < N)%R; last (simpl in *; lra).
        apply lt_INR.
        lia.
    - iDestruct ("H") as "(%s''&Herr&Hunif&%Hcase)".
      set_unfold in Hcase.
      destruct!/=.
      + rewrite /ε2.
        rewrite bool_decide_eq_false_2; last set_solver.
        rewrite bool_decide_eq_true_2; last done.
        by iDestruct (ec_contradict with "[$]") as "[]".
      + rewrite /ε2.
        rewrite bool_decide_eq_true_2; last done.
        rewrite size_union; last set_solver.
        rewrite size_singleton.
        replace 1%R with (INR 1) by done.
        rewrite -(minus_INR (_+_)); last lia.
        replace ((_+_-_)%nat) with (size s') by lia.
        wp_bind (Val # (_ =ᵥ _))%V.
        iApply (wp_value_promotion _ false (l ↪ urn_unif s')%I with "[Hunif]").
        * admit.
        * iIntros "Hunif".
          wp_pures.
          wp_pure.
          wp_pure.
          replace (_-_)%Z with (Z.of_nat (M-1)) by lia.
          rewrite -minus_INR; last lia.
          iApply ("IH" with "[][][//][$HΦ][$Herr][$]").
          -- iPureIntro.
             apply size_non_empty_iff.
             rewrite leibniz_equiv_iff.
             intros ->.
             rewrite union_empty_r size_singleton in Hineq.
             lia.
          -- iPureIntro. rewrite size_union in Hineq; last set_solver.
             rewrite size_singleton in Hineq.
             lia. 
  Admitted.
    
End proofs.


Section result.
  Variable N:nat.
  Variable M:nat.
  Context (Hineq: (M<=S N)%nat).
  
  Definition prog : expr :=
    λ: "A",
      let: "secret" := rand #N in
      (rec: "f" "x":=
         if: "x"=#0 then #false
         else let: "guess" := "A" #() in
              if: "guess" = "secret" then #true else "f" ("x"-#1)
      ) #M
  .

  Definition prog' : expr :=
    λ: "A",
      let: "secret" := drand #N in
      (rec: "f" "x":=
         if: "x"=#0 then #false
         else let: "guess" := "A" #() in
              if: "guess" = "secret" then #true else "f" ("x"-#1)
      ) #M
  .
  Local Opaque INR.
  
  Lemma prog_correct A:
    ∅ ⊢ₜ A : (TUnit → TNat) ->
             pgl (lim_exec ((prog A), {|heap:=∅; urns:= ∅|})) (λ v, v=#false) (M/S N).
  Proof.
    intros Htyped.
    eapply (elton_adequacy_remove_drand eltonΣ (prog' A)).
    - simpl. by erewrite typed_remove_drand_expr.
    - apply Rcomplements.Rdiv_le_0_compat; first apply pos_INR.
      apply pos_INR_S.
    - rewrite /prog'.
      iIntros (? Φ).
      iModIntro. iIntros "Herr HΦ".
      iPoseProof (typed_safe _ [] _ Htyped) as "H".
      wp_bind (A).
      iApply (pgl_wp_wand); first done.
      iIntros (?) "#Hinterp".
      simpl.
      wp_pures.
      wp_apply (wp_drand_thunk _ _ _ _ _ (True)).
      { rewrite rupd_unseal/rupd_def.
        iIntros (?) "$".
        iPureIntro.
        intros.
        simpl.
        eexists _; split; first done.
        f_equal.
        f_equal. 
        instantiate (1:=N).
        lia. }
      iIntros (l) "[_ Hl]".
      rewrite Nat2Z.id.
      rewrite -Nat.add_1_r.
      iAssert (∃s, l↪urn_unif s ∗ ⌜size s = S N⌝)%I with "[$Hl]" as "H'".
      { iPureIntro.
        rewrite size_list_to_set.
        - rewrite length_fmap length_seq. lia.
        - apply NoDup_fmap; last apply NoDup_seq.
          apply Nat2Z.inj'.
      }
      iDestruct ("H'") as "(%s&Hl&%Hsize)".
      do 3 wp_pure.
      inversion Hineq.
      { iDestruct (ec_contradict with "[$]") as "[]".
        right. symmetry.
        apply Rdiv_diag_eq.
        - apply not_0_INR. lia.
        - f_equal. lia.
      }
      iApply (ind_case with "[$Herr $Hl]").
      + lia.
      + lia.
      + lia.
      + done.
      + iNext.
        iIntros.
        by iApply "HΦ".
  Qed. 
End result.

    
