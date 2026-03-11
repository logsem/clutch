From iris.base_logic.lib Require Import token.
From clutch.elton Require Import elton hash. 
Set Default Proof Using "Type*".

Section prog.
  Variable secret_range:nat.
  Variable val_size: nat.
  Variable tries: nat.

  Definition prog : expr :=
    λ: "A",
      let: "hashf" := init_hash val_size #() in
      let: "secret" := rand #secret_range in
      let: "h" := "hashf" "secret" in
      let: "i" := ref #tries in
      let: "hashf'" :=
        (λ: "x", if: ! "i" = #0
                 then NONE
                 else "i" <- ! "i" - #1;; SOME ("hashf" "x") ) in
      let: "g" := "A" "hashf'" "h" in
      "hashf" "g" = "h".

  
  Definition prog' : expr :=
    λ: "A",
      let: "hashf" := init_hash val_size #() in
      let: "secret" := drand #secret_range in
      let: "h" := "hashf" "secret" in
      let: "i" := ref #tries in
      let: "hashf'" :=
        (λ: "x", if: ! "i" = #0
                 then NONE
                 else "i" <- ! "i" - #1;; SOME ("hashf" "x") ) in
      let: "g" := "A" "hashf'" "h" in
      "hashf" "g" = "h".
  
  (* Context `{eltonGS Σ}. *)

  Lemma guess_hash A:
    ∅ ⊢ₜ A : ((TNat → (TUnit+TNat)) → TNat → TNat) ->
             pgl (lim_exec ((prog A), {|heap:=∅; urns:= ∅|})) (λ v, v=#false)
               ((tries+1)%nat * (/(secret_range +1)%nat + /(val_size + 1)%nat) ).
  Proof. 
    intros Htyped.
    destruct (decide (tries+1<secret_range+1)) as [initial_ineq|]; last first.
    {
      apply pgl_1.
      rewrite Rmult_plus_distr_l.
      trans ((tries+1)%nat*/(secret_range+1)%nat)%R.
      - rewrite -Rdiv_def.
        apply Rcomplements.Rle_div_r.
        + apply Rlt_gt.
          apply lt_0_INR; lia.
        + rewrite Rmult_1_l.
          apply le_INR.
          lia.
      - assert (0<=(tries+1)%nat */(val_size +1)%nat)%R; last lra.
        rewrite -Rdiv_def.
        apply Rcomplements.Rle_div_r.
        + apply Rlt_gt.
          apply lt_0_INR; lia.
        + rewrite Rmult_0_l.
          replace 0%R with (INR 0) by done.
          apply le_INR.
          lia.
    }
    eapply (elton_adequacy_remove_drand (#[eltonΣ; tokenΣ]) (prog' A)).
    - simpl. by erewrite typed_remove_drand_expr.
    - apply Rmult_le_pos; first apply pos_INR.
      rewrite -!Rdiv_1_l.
      apply Rplus_le_le_0_compat;
        apply Rcomplements.Rdiv_le_0_compat; try lra.
      all: apply lt_0_INR; lia. 
    - rewrite /prog'.
      iIntros (? Φ).
      iModIntro. iIntros "Herr HΦ".
      iPoseProof (typed_safe _ [] _ Htyped) as "H".
      wp_bind (A).
      iApply (pgl_wp_wand); first done.
      iIntros (?) "#Hinterp".
      simpl.
      wp_pures.
      rewrite Rmult_plus_distr_l.
      iDestruct (ec_split with "[$]") as "[Herr1 Herr2]".
      { apply Rmult_le_pos; first apply pos_INR.
        rewrite -!Rdiv_1_l.
        apply Rcomplements.Rdiv_le_0_compat; try lra.
        apply lt_0_INR; lia.  }
      { apply Rmult_le_pos; first apply pos_INR.
        rewrite -!Rdiv_1_l.
        apply Rcomplements.Rdiv_le_0_compat; try lra.
        apply lt_0_INR; lia.  }
            
      wp_apply (wp_init_hash); first done.
      iIntros (f) ">Hf".
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
        instantiate (1:=secret_range).
        lia. }
      iIntros (l) "[_ Hl]".
      rewrite Nat2Z.id.
      wp_pures.
      iMod (ec_zero) as "Hzero".
      wp_apply (wp_insert_new _ _ _ _ _ _ (λ _, 0)%R True with "[$Hf $Hzero]").
      { done. }
      { by intros. }
      { right. apply SeriesC_0. intros. lra. }
      { iModIntro. rewrite dom_empty_L. by rewrite big_sepS_empty. }
      iIntros (secret) "(Hf&_)".
      wp_pures.
      wp_alloc lt as "Hr".
      wp_pures.
      iAssert (∃s, l↪urn_unif s ∗ ⌜size s = S secret_range⌝)%I with "[$Hl]" as "H'".
      { iPureIntro.
        rewrite size_list_to_set.
        - rewrite length_fmap length_seq. lia.
        - apply NoDup_fmap; last apply NoDup_seq.
          apply Nat2Z.inj'.
      }
      iDestruct "H'" as "(%s&Hl&%Hsize)".
      iMod (token_alloc) as (γ) "Htoken".
    iMod (inv_alloc (nroot) _
            ( ∃ (tries':nat) (m:gmap nat _),
                hashfun val_size f (<[LitLbl l:=fin_to_nat secret]> (kmap (λ x, LitInt (Z.of_nat x)) m))∗
                lt ↦ #tries' ∗ (⌜(tries'<=tries)%nat ⌝) ∗
                ∃ (s':gset Z),
                  ⌜s' ## (set_map Z.of_nat (dom m):gset _)⌝ ∗
                  ⌜s≠∅⌝ ∗
                  l↪ urn_unif (s')∗
                ((
                     (⌜∀ x y, m!!x=Some y -> y≠ fin_to_nat secret⌝) ∗
                     ↯ ((tries'+1)/(val_size +1)%nat) ∗
                     ↯ ((tries'+1)%nat / size s') ∗
                     ⌜secret_range + 1  + tries' - tries <=size s'⌝ 
                 )∨ (token γ))
            )%I
           with "[Herr1 Herr2 Hf Hr Hl]") as "#Hinv".
    { iNext. iFrame "Hr".
      iExists ∅.
      rewrite kmap_empty.
      iFrame.
      iSplit; first done.
      repeat iSplit; last iLeft; iFrame.
      - iPureIntro. rewrite dom_empty. rewrite set_map_empty. set_solver.
      - iPureIntro.
        intros ->.
        rewrite size_empty in Hsize. lia.
      - rewrite Hsize. rewrite S_INR plus_INR.
        replace 1%R with (INR 1) by done.
        rewrite Rdiv_def. rewrite plus_INR. simpl.
        iFrame. 
        repeat iSplit.
        + iPureIntro.
          intros. simplify_map_eq.
        + iPureIntro. lia.
    }
    
    wp_bind (v _)%E.
    rewrite refines_eq /refines_def.
    simpl.
    iApply (pgl_wp_wand); first iApply "Hinterp".
    { iModIntro.
      iIntros (?) "[%guess ->]".
      rewrite refines_eq/refines_def.
      wp_pures.
      iInv "Hinv" as ">(%tries'&%m&Hf&Hl&%& (%s'&%Hdisjoint&%Hnonempty&Hurn &Hor))" "Hclose".
      wp_load.
      wp_pures.
      case_bool_decide.
      - wp_pures.
        iMod ("Hclose" with "[-]"); first by iFrame.
        iModIntro.
        iExists _. iLeft. by iSplit.
      - wp_pures.
        wp_load. 
        wp_pures.
        wp_store.
        iDestruct "Hor" as "[Hor|Hor]".
        + (** normal case *)
          admit.
        + (** token case, its a weird case *)
          admit. 
          (* iDestruct "Hor" as "(%x&Hu&%Hnotin&Htoken)". *)
          (* destruct (decide (Z.of_nat guess =x)). *)
          (* * subst. *)
          (*   wp_apply (wp_hashfun_prev _ _ _ _ _ _ _ (l↪ _) with "[$Hu $Hf]"). *)
          (*   -- done. *)
          (*   -- by erewrite lookup_insert. *)
          (*   -- iSplit. *)
          (*      ++ iModIntro. *)
          (*         iIntros. *)
          (*         rewrite rupd_unseal/rupd_def. *)
          (*         iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
          (*         iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
          (*         iPureIntro. *)
          (*         intros. *)
          (*         eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
          (*         destruct Hlookup as (?&Hsome&Hin). *)
          (*         eexists _; split; last done. *)
          (*         simpl. *)
          (*         rewrite Hsome. *)
          (*         simpl. rewrite bool_decide_eq_true_2; first done. *)
          (*         set_solver. *)
          (*      ++ iModIntro. *)
          (*         iApply big_sepS_intro. *)
          (*         iModIntro. *)
          (*         iIntros (?). *)
          (*         rewrite elem_of_difference. *)
          (*         iIntros ([H2 H3]) "?". *)
          (*         rewrite rupd_unseal/rupd_def. *)
          (*         iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
          (*         iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
          (*         iPureIntro. *)
          (*         intros. *)
          (*         eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
          (*         destruct Hlookup as (?&Hsome&Hin). *)
          (*         eexists _; split; last done. *)
          (*         simpl. *)
          (*         rewrite elem_of_dom in H2. *)
          (*         destruct H2. *)
          (*         set_unfold. subst. simplify_map_eq. *)
          (*         apply lookup_kmap_Some in H2; last (intros ???; by simplify_eq). *)
          (*         destruct!/=. rewrite bool_decide_eq_false_2; first done. *)
          (*         intros ?. simplify_eq. *)
          (*         apply Hnotin. *)
          (*         eexists _; split; first done. *)
          (*         rewrite elem_of_dom. naive_solver. *)
          (*   -- iIntros "[Hf Hu]". *)
          (*      wp_pures. *)
          (*      iMod ("Hclose" with "[-]"); last first. *)
          (*      ++ iModIntro. iExists _. iRight. *)
          (*         iSplit; first done. *)
          (*         by iExists _. *)
          (*      ++ iNext. *)
          (*         iExists _, _. *)
          (*         replace (_-_)%Z with (Z.of_nat (tries' - 1)); last first.  *)
          (*         { rewrite Nat2Z.inj_sub; first lia. *)
          (*           destruct tries'; last lia. *)
          (*           done. } *)
          (*         iFrame "Hf Hl". *)
          (*         iSplit; last iRight. *)
          (*         ** iPureIntro. lia. *)
          (*         ** by iFrame. *)
          (* * destruct (decide (guess ∈ dom m)) as [H'|H']. *)
          (*   -- rewrite elem_of_dom in H'. *)
          (*      destruct H'. *)
          (*      wp_apply (wp_hashfun_prev _ _ _ _ _ _ (Z.of_nat guess) (l↪ _) with "[$Hu $Hf]"). *)
          (*      ++ done. *)
          (*      ++ simplify_map_eq. *)
          (*         apply lookup_kmap_Some; last naive_solver. *)
          (*         intros ???. by simplify_eq. *)
          (*      ++ iSplit. *)
          (*         ** iModIntro. *)
          (*            iIntros. *)
          (*            rewrite rupd_unseal/rupd_def. *)
          (*            iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
          (*            iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
          (*            iPureIntro. *)
          (*            intros. *)
          (*            eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
          (*            destruct Hlookup as (?&Hsome&Hin). *)
          (*            eexists _; split; last done. *)
          (*            simpl. by rewrite bool_decide_eq_true_2. *)
          (*         ** iModIntro. *)
          (*            iApply big_sepS_intro. *)
          (*            iModIntro.  *)
          (*            iIntros (?). *)
          (*            rewrite elem_of_difference. *)
          (*            iIntros ([K1 K2]) "?". *)
          (*            rewrite rupd_unseal/rupd_def. *)
          (*            iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
          (*            iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
          (*            iPureIntro. *)
          (*            intros. *)
          (*            eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
          (*            destruct Hlookup as (?&Hsome&Hin). *)
          (*            eexists _; split; last done. *)
          (*            simpl. *)
          (*            rewrite elem_of_dom in K1. *)
          (*            destruct K1 as [? K1]. *)
          (*            set_unfold. subst. simplify_map_eq. *)
          (*            rewrite lookup_insert_Some in K1. *)
          (*            destruct!/=. *)
          (*            --- rewrite Hsome. simpl. *)
          (*                rewrite bool_decide_eq_false_2; first done. *)
          (*                intros ?. simplify_eq. *)
          (*            --- rename select (kmap _ _ !! _ = _) into K1. *)
          (*                apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq). *)
          (*                destruct!/=. rewrite bool_decide_eq_false_2; first done. *)
          (*                intros ?. simplify_eq. *)
          (*      ++ iIntros "[Hf Hu]". *)
          (*      wp_pures. *)
          (*      iMod ("Hclose" with "[-]"); last first. *)
          (*         ** iModIntro. iExists _. iRight. *)
          (*            iSplit; first done. *)
          (*            by iExists _. *)
          (*         **  iNext. *)
          (*             iExists _, _. *)
          (*             replace (_-_)%Z with (Z.of_nat (tries' - 1)); last first.  *)
          (*             { rewrite Nat2Z.inj_sub; first lia. *)
          (*               destruct tries'; last lia. *)
          (*               done. } *)
          (*             iFrame "Hf Hl". *)
          (*             iSplit; last iRight. *)
          (*             --- iPureIntro. lia. *)
          (*             --- by iFrame. *)
          (*   -- iMod (ec_zero) as "Hzero". *)
          (*      wp_apply (wp_insert_new _ _ _ _ _ _ (λ _, 0)%R (l↪ _) with "[$Hu $Hf $Hzero]"). *)
          (*      ++ done. *)
          (*      ++ done. *)
          (*      ++ right. apply SeriesC_0. intros; lra. *)
          (*      ++ iModIntro. *)
          (*         iApply big_sepS_intro. *)
          (*         iModIntro. *)
          (*         iIntros (?) "%Hlookup'". *)
          (*         iIntros "?". *)
          (*         rewrite rupd_unseal/rupd_def. *)
          (*         iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
          (*         iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
          (*         iPureIntro. *)
          (*         intros. *)
          (*         eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
          (*         destruct Hlookup as (?&Hsome&Hin). *)
          (*         eexists _; split; last done. *)
          (*         simpl. *)
          (*         rewrite elem_of_dom in Hlookup'. *)
          (*         destruct Hlookup' as [? Hlookup']. *)
          (*         rewrite lookup_insert_Some in Hlookup'. *)
          (*         destruct!/=. *)
          (*         --- rewrite Hsome/=. rewrite bool_decide_eq_false_2; first done. *)
          (*             intros ?. simplify_eq. *)
          (*             set_unfold. naive_solver. *)
          (*         --- rename select (kmap _ _ !! _ = _) into K1. *)
          (*             apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq). *)
          (*             destruct!/=. rewrite bool_decide_eq_false_2; first done. *)
          (*             intros ?. simplify_eq. *)
          (*             set_unfold. simplify_eq. *)
          (*             rewrite elem_of_dom in H'. naive_solver. *)
          (*      ++ iIntros (?) "(Hf&Hurn&_)". *)
          (*         rewrite insert_commute; last done. *)
          (*         wp_pures. *)
          (*         iMod ("Hclose" with "[-]"); last first. *)
          (*         ** iModIntro. iExists _. iRight. *)
          (*            iSplit; first done. *)
          (*            by iExists _. *)
          (*         **  iNext. *)
          (*             iExists _, _. *)
          (*             erewrite kmap_insert; last (intros ???; by simplify_eq). *)
          (*             replace (_-_)%Z with (Z.of_nat (tries' - 1)); last first.  *)
          (*             { rewrite Nat2Z.inj_sub; first lia. *)
          (*               destruct tries'; last lia. *)
          (*               done. } *)
          (*             iFrame "Hf Hl". *)
          (*             iSplit; last iRight. *)
          (*             --- iPureIntro. lia. *)
          (*             --- iFrame. *)
          (*                 iPureIntro. *)
          (*                 rewrite elem_of_map. *)
          (*                 intros ?. destruct!/=. *)
          (*                 set_solver.        *)     
    }
    (** * Final bit *)
    iIntros (f') "#Hinterp'".
    wp_bind (f' _)%E.
    rewrite refines_eq /refines_def.
    iApply (pgl_wp_wand); first iApply "Hinterp'".
    { iExists (nat_to_fin (fin_to_nat_lt _)). by rewrite fin_to_nat_to_fin. }
    iIntros (?) "[%guess ->]".
    wp_pures. 
    iInv "Hinv" as ">(%tries'&%m&Hf&Hl&%& (%s'&%Hdisjoint&%Hnonempty&Hurn &Hor))" "Hclose".
    iDestruct ("Hor") as "[Hor|Htoken']"; last first.
    { iCombine "Htoken" "Htoken'" gives "[]". }
    iDestruct "Hor" as "(%Hnotin&Herr&Herr'&%H1)".
    assert (is_valid_urn (urn_unif s')).
    { simpl.
      intros ->.
      rewrite size_empty in H1. lia.
    }

    
    destruct (decide (guess ∈ dom m)) as [Hlookup|].
      -- (** Return something hashed before *)
        rewrite elem_of_dom in Hlookup.
        destruct Hlookup.
        
        wp_apply (wp_hashfun_prev _ _ _ _ _ _ guess (l↪ _) with "[$Hurn $Hf]").
        ++ done.
        ++ simplify_map_eq.
           erewrite lookup_kmap_Some; first naive_solver.
           intros ???. by simplify_eq.
        ++ iSplit.
           ** iModIntro.
              iIntros.
              rewrite rupd_unseal/rupd_def.
              iIntros  (?) "[? Hu]". iSplit; last iFrame.
              iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup".
              iPureIntro.
              intros. simpl. case_bool_decide; naive_solver.
           ** iModIntro.
              iApply big_sepS_intro.
              iModIntro.
              setoid_rewrite elem_of_difference.
              iIntros (?) "[%Hlookup' %]".
              iIntros "?".
              rewrite rupd_unseal/rupd_def.
              iIntros  (?) "[? Hu]". iSplit; last iFrame.
              iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup".
              iPureIntro.
              intros.
              eapply urns_f_distr_lookup in Hlookup; last done; last done.
              destruct Hlookup as (?&Hsome&Hin).
              eexists _; split; last done.
              simpl.
              rewrite elem_of_dom in Hlookup'.
              destruct Hlookup' as [? Hlookup'].
              rewrite lookup_insert_Some in Hlookup'.
              destruct!/=.
              --- rewrite Hsome/=. rewrite bool_decide_eq_false_2; first done.
                  intros ?. simplify_eq.
                  apply Hdisjoint in Hin.
                  apply Hin.
                  rewrite elem_of_map.
                  eexists _; split; first done.
                  rewrite elem_of_dom. naive_solver.
              --- rename select (kmap _ _ !! _ = _) into K1.
                  apply lookup_kmap_Some in K1; last (intros ???; by simplify_eq).
                  destruct!/=. rewrite bool_decide_eq_false_2; first done.
                  intros ?. simplify_eq.
                  set_unfold. simplify_eq.
        ++ iIntros "[Hf Hu]".
           wp_pures.
           rewrite bool_decide_eq_false_2; last first.
           { intros ?. simplify_eq.
             naive_solver.
           }
           iMod ("Hclose" with "[Htoken Hl Hf Hu]").
           { iNext.
             iFrame "Hl Hf Hu".
             repeat iSplit; try done.
             by iRight. 
           }
           by iApply "HΦ".
      -- iAssert (pupd ∅ ∅ (∃s'', ⌜ s'' ⊆ s' ⌝ ∗ ⌜ s''≠∅⌝ ∗
                                  l ↪ urn_unif s'' ∗ ⌜Z.of_nat guess∉ s''⌝
                 ))%I with "[Herr' Hurn]" as ">H'".
         { destruct (decide (Z.of_nat guess ∈ s')); last first.
           - iModIntro.
             iFrame.
             iPureIntro. simpl in *. naive_solver.
           - iMod (pupd_resolve_urn _ _ (λ x, if bool_decide (x=Z.of_nat guess) then nnreal_one else nnreal_zero) with "[$][$]") as "(%&?&?&%)".
             + done.
             + erewrite (SeriesC_ext _ (λ x, if bool_decide (x=Z.of_nat guess) then nnreal_one else nnreal_zero)); last first.
               -- intros.
                  case_bool_decide as H3; first by case_bool_decide.
                  rewrite bool_decide_eq_false_2; first done.
                  intros ->. apply H3. set_solver.
               -- rewrite SeriesC_singleton.
                  simpl.
                  rewrite !Rdiv_def.
                  apply Rmult_le_compat_r.
                  ++ rewrite -Rdiv_1_l.
                     apply Rdiv_INR_ge_0.
                  ++ replace 1%R with (INR 1) by done.
                     apply le_INR.
                     lia.
             + exists 1.
               intros.
               case_bool_decide; simpl; lra.
             + case_bool_decide.
               * by iDestruct (ec_contradict with "[$]") as "[]".
               * iFrame.
                 iModIntro.
                 iPureIntro.
                 set_solver.       
         }
         iDestruct "H'" as "(%s''&%&%&Hurn &%)".
         wp_apply (wp_insert_new _ _ _ _ _ _ (λ x, if bool_decide (x= secret) then nnreal_one else nnreal_zero)%R (l↪ _) with "[$Hf $Herr $Hurn]").
         ++ done.
         ++ intros. case_bool_decide; simpl; lra.
         ++ rewrite SeriesC_scal_l. rewrite SeriesC_singleton.
            rewrite Rmult_1_r.
            rewrite S_INR.
            replace 1%R with (INR 1) by done.
            rewrite -!plus_INR.
            simpl.
            rewrite !Rdiv_def.
            apply Rmult_le_compat_r.
            ** rewrite -Rdiv_1_l.
               apply Rdiv_INR_ge_0.
            ** replace 1%R with (INR 1) by done.
               apply le_INR.
               lia.
         ++ iModIntro.
            iApply big_sepS_intro.
            iModIntro.
            iIntros (?) "%Hlookup'".
            iIntros "?".
            rewrite rupd_unseal/rupd_def.
            iIntros  (?) "[? Hu]". iSplit; last iFrame.
            iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup".
            iPureIntro.
            intros.
            eapply urns_f_distr_lookup in Hlookup; last done; last done.
            destruct Hlookup as (?&Hsome&Hin).
            eexists _; split; last done.
            simpl.
            rewrite elem_of_dom in Hlookup'.
            destruct Hlookup' as [? Hlookup'].
            rewrite lookup_insert_Some in Hlookup'.
            destruct!/=.
            ** rewrite Hsome/=.
               rewrite bool_decide_eq_false_2; first done.
               intros ?. simplify_eq.
            ** rename select (kmap _ _ !!_=_) into Hlookup'.
               apply lookup_kmap_Some in Hlookup'; last (intros ???; by simplify_eq).
               destruct!/=.
               rewrite bool_decide_eq_false_2; first done.
               intros ?. simplify_eq.
               rename select (m!!_=Some _) into Hcontra.
               apply elem_of_dom_2 in Hcontra.
               set_solver.
         ++ iIntros (?) "(Hf&Hurn &Herr)".
            case_bool_decide.
            { by iDestruct (ec_contradict with "[$]") as "[]". }
            wp_pures.
            iMod ("Hclose" with "[-HΦ]").
            { iNext.
              iFrame "Hl".
              rewrite insert_commute; last done.
              iExists _.
              erewrite kmap_insert; first iFrame "Hf"; last (intros ???; by simplify_eq).
              iSplit; first done.
              iFrame "Hurn".
              repeat iSplit; last by iRight.
              - iPureIntro.
                set_solver.
              - done.
            }
            iApply "HΦ".
            iModIntro.
            iPureIntro.
            split; first done.
            rewrite bool_decide_eq_false_2; first done.
            intros ?. simplify_eq.
  Admitted.
        
End prog.


(* iModIntro. *)
(* iApply big_sepS_intro. *)
(* iModIntro. *)
(* iIntros (?) "%Hlookup'". *)
(* iIntros "?". *)
(* rewrite rupd_unseal/rupd_def. *)
(* iIntros  (?) "[? Hu]". iSplit; last iFrame. *)
(* iDestruct (ghost_map_lookup with "Hu [$]") as "%Hlookup". *)
(* iPureIntro. *)
(* intros. *)
(* eapply urns_f_distr_lookup in Hlookup; last done; last done. *)
(* destruct Hlookup as (?&Hsome&Hin). *)
(* eexists _; split; last done. *)
