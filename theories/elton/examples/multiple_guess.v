From clutch.elton Require Import elton. 
Set Default Proof Using "Type*".

Section proofs.
  Context `{eltonGS Σ}.  

  Local Lemma ind_case_zero v l:
    {{{ True }}}
      (rec: "f" "x" :=
         if: "x" = #0 then #false
         else let: "guess" := v (Val (LitV LitUnit)) in if: "guess" = #lbl:l then #true else "f" ("x" - #1))%V
      #0
      {{{ RET #false; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_pures. by iApply "HΦ".
  Qed. 

  Local Lemma ind_case (M N:nat) s (v:val) l:
    N≠0->
    M<=N->
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
      destruct M.
      + replace #0%nat with #0%Z by done.
        wp_apply (ind_case_zero with "[//][-]").
        iNext.
        iIntros.
        by iApply "HΦ".
      + iApply (ind_case with "[$Herr $Hl]").
        * lia.
        * lia.
        * lia.
        * done.
        * iNext.
          iIntros.
          by iApply "HΦ".
  Qed. 
End result.

    
