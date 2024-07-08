(** The PRP/PRF switching Lemma.

References:
- Lemma 1, Bellare and Rogaway, 2006, Code-Based Game-Playing Proofs and the Security of Triple Encryption.
- Lemma 6.7, Mike Rosulek, 2020, The Joy of Cryptography.
- Theorem 4.4, Boneh and Shoup, 2023, A Graduate Course in Applied Cryptography (Version 0.6).

Our definition deviates from Rosulek's and Boneh/Shoup in that we wrap the encryption oracle with [q_calls] to enforce the bound [Q] on the number of oracle calls, while loc. cit. rely on the assumption that the adversary runs in polynomial time in the security parameter.

     *)

From clutch Require Import lib.flip.
From clutch.approxis Require Import approxis map list prf prp.
Set Default Proof Using "Type*".

Section prp_prf.

  Variable Key : nat.
  Variable val_size : nat.
  Let Input := val_size.
  Let Output := val_size.

  (** RandML types of the scheme. *)
  Definition TKey := TInt.
  Definition TInput := TInt.
  Definition TOutput := TInt.

  (** We will prove the PRF/PRP switching lemma.
      We assume that the adversaries are well-typed. *)
  Variable adv : val.
  Definition TAdv := ((TInput → (TUnit+ TOutput)) → TBool)%ty.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).
  Definition q_calls := q_calls Input.
  Definition PRF := PRF val_size val_size.
  Definition PRP := PRP val_size.
  (* Definition PRP_PRF : val := λ:"b" "adv",
         if: "b" then PRP #false "adv" #() else PRF #false "adv" #(). *)

  Local Opaque INR.
  Local Opaque is_list.
  Local Ltac smash := 
    repeat (apply Rcomplements.Rdiv_le_0_compat||apply pos_INR_S||apply pos_INR). 

  Section proofs.
    Context `{!approxisRGS Σ}.

    Lemma refines_list_seq_l E K e A (n m : nat) :
      (∀ v : val, ⌜is_list (seq n m) v⌝ -∗ REL (fill K (of_val v)) << e @ E : A)
      -∗ REL (fill K (list_seq #n #m)) << e @ E : A.
    Proof.
      iIntros "Hlog".
      iApply refines_wp_l.
      by iApply wp_list_seq.
    Qed.

    Lemma refines_list_seq_r E K e A (n m :nat):
      (∀ v : val, ⌜is_list (seq n m) v⌝ -∗ REL e << (fill K (of_val v)) @ E : A)
      -∗ REL e << (fill K (list_seq #n #m)) @ E : A.
    Proof.
      iIntros "Hlog".
      iApply refines_step_r.
      iIntros.
      iMod (spec_list_seq with "[$]") as "(%&?&?)".
      iModIntro.
      iFrame.
      iApply ("Hlog" with "[$]").
    Qed.

    (* Can we give a nice *amortized* spec for relating
       [q_calls random_function] and [q_calls random_permutation] ? *)

    Theorem PRP_PRF (Q : nat) ε :
      (INR (fold_left (Nat.add) (seq 0 Q) 0%nat) / INR (S val_size))%R = ε
      →
      ↯ ε ⊢ (REL (PRP #false adv ((λ: "_", #()),#()) #Q) << (PRF #false adv ((λ: "_", #()),#()) #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
      iIntros (<-) "Hε".
      rewrite /PRP/PRF/prp.PRP/prf.PRF...
      rewrite /random_permutation/random_function...
      rewrite /random_permutation_state...
      rel_apply_l refines_init_map_l.
      iIntros (mapref) "mapref"...
      rel_apply_r refines_init_map_r.
      iIntros (mapref') "mapref'"...
      replace 0%Z with (Z.of_nat 0%nat) by lia.
      rel_apply_l (refines_list_seq_l _ _ _ _ 0%nat).
      iIntros (?) "%"...
      rel_alloc_l unused as "unused"...
      rewrite /query_prp... 
      rel_bind_l (q_calls _ _).
      rel_bind_r (q_calls _ _).
      unshelve iApply (refines_bind with "[-][]").
      { exact (interp (TInput → (TUnit + TOutput)) []). }
      2: {
        iIntros (f f') "Hff'".
        simpl.
        unshelve iApply (refines_app with "[] [Hff']").
        3: rel_values.
        rel_arrow_val.
        iIntros (o o') "Hoo'". rel_pures_l ; rel_pures_r.
        repeat rel_apply refines_app. 3: rel_values.
        Unshelve.
        3: exact (interp TBool []).
        1: { rel_arrow_val. iIntros (??) "#(%_&->&->)". rel_pures_l ; rel_pures_r. rel_values. }
        replace (lrel_arr
                   (lrel_arr 
                      lrel_int (lrel_sum lrel_unit lrel_int))
                   (interp TBool nil)) with
          (interp TAdv []) by easy.
        iApply refines_typed.
        assumption.
      }

      rewrite /q_calls /bounded_oracle.q_calls.
      rel_alloc_l counter as "counter".
      rel_alloc_r counter' as "counter'"...
      replace 0%Z with (Z.of_nat 0%nat) by lia.
      erewrite <-fmap_empty.
      iApply (refines_na_alloc
                (∃ (q : nat) (M:gmap nat Z) (l:list nat) v',
                    ↯ (fold_left Nat.add (seq q (Q-q)) 0%nat / S val_size)
                    ∗ counter ↦ #q
                    ∗ counter' ↦ₛ #q
                    ∗ map_list mapref ((λ b, LitV (LitInt b)) <$> M)
                    ∗ map_slist mapref' ((λ b, LitV (LitInt b)) <$> M)
                    ∗ ⌜ (size (M) <= q)%nat ⌝
                    ∗ ⌜ ∀ x, x ∈ (dom M) -> (x < S val_size)%nat ⌝
                    ∗ ⌜NoDup l⌝
                    ∗ ⌜is_list l v'⌝
                    ∗ ⌜(S val_size - (size (M)) <=length l<=S val_size)%nat⌝  
                    ∗ unused ↦ v'
                    ∗ ⌜(forall x:nat, Z.of_nat x∈ ((map_img M):gset _) -> x ∈ l -> False)⌝
                    ∗ ⌜∀ x, x ∈ l -> (x<S val_size)%nat ⌝
                )%I
                (nroot.@"cpa")); iFrame.
      replace (Q-0) with Q by lia; iFrame.
      iSplitL. 
      { (* solve obligations to establish invariant *)
        iPureIntro. simpl.
        eexists _.
        repeat split; try done.
        - rewrite cons_seq. apply NoDup_seq. 
        - rewrite cons_seq. by rewrite seq_length.
        - rewrite cons_seq. by rewrite seq_length.
        - intros ?. rewrite cons_seq. rewrite elem_of_seq. lia.         
      }
      iIntros "#Hinv".
      rel_arrow_val.
      iIntros (??) "(%n&->&->)"...
      rewrite -bool_decide_and.
      iApply (refines_na_inv with "[$Hinv]"); first done.
      iIntros "[>(%q&%M&%l&%v'&Hε&Hcounter&Hcounter'&Hml&Hml'&%&%&%HNoDup&%&%Hlen&unused&%Hdisjoint&%) Hclose]".
      rel_load_l; rel_load_r...
      rewrite -bool_decide_and.
      case_bool_decide; last first.
      { (* input is not valid or we exceed query num*)
        idtac...
        iApply refines_na_close; iFrame.
        iSplit; first (iPureIntro; by exists l)...
        rel_values. repeat iExists _. by iLeft.
      }
      idtac...
      rel_load_l; rel_load_r...
      rel_store_l; rel_store_r...
      replace n with (Z.of_nat (Z.to_nat n)) by lia.
      rel_apply_l (refines_get_l with "[-Hml][$Hml]").
      iIntros (?) "Hml ->".
      rel_apply_r (refines_get_r with "[-Hml'][$]").
      iIntros (?) "Hml' ->".
      replace (Z.of_nat q+1)%Z with (Z.of_nat (S q)) by lia.
      replace (Q-q) with (S (Q-S q)) by lia.
      rewrite -cons_seq.
      rewrite fold_symmetric; try lia.
      simpl. rewrite -fold_symmetric; try lia.
      rewrite plus_INR Rdiv_plus_distr.
      destruct (((λ b : Z, #b) <$> M)!!Z.to_nat n) eqn:Hres...
      { (* we query something from before*)
        iApply refines_na_close; iFrame.
        iSplitL.
        - iModIntro. iExists M, l. iFrame.
          iSplitL.
          + iApply (ec_weaken with "[$]").
            split.
            * rewrite fold_symmetric; try lia.
              smash.
            * rewrite Rplus_comm. apply Rplus_le_0_compat.
              smash.
          + iPureIntro; repeat split; (done||lia).
        - rewrite lookup_fmap_Some in Hres.
          destruct Hres as (?&<-&?).
          rel_values. repeat iExists _. iRight. iPureIntro.
          simpl.
          repeat split; by eexists _.
      }
      rel_load_l.
      rel_apply_l refines_list_length_l; first done.
      iIntros (?) "->"...
      (* make sure list has at least one element*)
      assert (size(M)<S val_size)%nat.
      { apply Nat.nle_gt.
        intros ?.
        unshelve epose proof set_subseteq_size_eq (dom M) (set_seq 0 (S val_size)) _ _ as K.
        - intros ??. rewrite elem_of_set_seq.
          split; first lia.
          set_unfold. naive_solver.
        - rewrite size_dom. rewrite size_set_seq. lia.
        - eapply is_Some_None. rewrite <-Hres.
          rewrite -elem_of_dom.
          rewrite dom_fmap.
          rewrite K.
          rewrite elem_of_set_seq. lia.
      }
      (* here need to lift coupling rule to logical relations... *)
      set f := (λ n : nat, if (n <=? val_size) then (nth n l 0) else n + val_size).
      rel_apply (refines_couple_UU_err _ _ (mknonnegreal _ _) f); try lia.
      { intros. rewrite /f.
        rewrite leb_correct; try lia.
        apply Forall_nth; last lia.
        rewrite Forall_forall.
        done. 
      }
      { rewrite /f.
        intros ????.
        rewrite !leb_correct; try lia.
        apply NoDup_nth; try lia.
        by apply NoDup_ListNoDup.
      }
      { done. }
      iDestruct (ec_split with "[$]") as "[Hε Hε']"; try smash.
      iSplitL "Hε".
      { iApply ec_weaken; last done.
        split.
        - rewrite -Rdiv_def.
          smash. rewrite -minus_INR; last lia.
          smash.
        - rewrite Rdiv_def.
          apply Rmult_le_compat_r.
          + apply Rlt_le.
            apply RinvN_pos'.
          + rewrite -minus_INR; last lia.
            apply le_INR. lia.
      } 
      iIntros (x). iModIntro. rewrite /f...
      pose proof fin_to_nat_lt x.
      rewrite leb_correct; last lia.
      rel_load_l.
      rel_apply_l refines_list_remove_nth_l.
      { iPureIntro. split; first done. lia. }
      simpl.
      iIntros (?) "(%&%&%&%&->&<-&->&%)"...
      rewrite nth_middle.
      rel_apply_l (refines_set_l with "[-Hml][$]").
      iIntros "Hml".
      rel_apply_r (refines_set_r with "[-Hml'][$]").
      iIntros "Hml'"...
      rel_store_l...
      iApply (refines_na_close).
      iSplitR "Hclose"; last first.
      { iFrame.
        rel_values.
        repeat iExists _. iRight.
        iPureIntro; repeat split; try done.
        by eexists (Z.of_nat _). 
      }
      iModIntro.
      iExists _, (<[Z.to_nat n:=_]> M), (_++_).
      rewrite fmap_insert. iFrame.
      iPureIntro; repeat split.
      - rewrite map_size_insert.
        case_match; simpl; lia.
      - intros ?. rewrite dom_insert.
        set_unfold. intros [|]; try lia.
        naive_solver.
      - rewrite NoDup_ListNoDup.
        eapply NoDup_remove_1.
        rewrite -NoDup_ListNoDup.
        done.
      - done.
      - rewrite map_size_insert_None.
        + rewrite app_length.
          rewrite app_length cons_length in Hlen. lia.
        + rewrite lookup_fmap in Hres.
          rewrite fmap_None in Hres. done.
      - rewrite app_length.
        rewrite app_length cons_length in Hlen. lia.
      - intros ?. rewrite elem_of_map_img.
        intros [? K].
        rewrite lookup_insert_Some in K.
        destruct K as [[<- K']|[K1 K2]].
        + apply Nat2Z.inj' in K'. subst.
          rewrite NoDup_ListNoDup in HNoDup.
          apply NoDup_remove_2 in HNoDup.
          rewrite elem_of_list_In. done.
        + intros ?. set_unfold.
          eapply Hdisjoint.
          * rewrite elem_of_map_img. naive_solver.
          * naive_solver.
      - set_unfold. naive_solver.
        Unshelve.
        rewrite -Rdiv_def.
        smash.
        rewrite -minus_INR; last lia.
        smash.
    Qed.
    
    Theorem PRF_PRP (Q : nat) ε :
      (INR (fold_left (Nat.add) (seq 0 Q) 0%nat) / INR (S val_size))%R = ε
      →
      ↯ ε ⊢ (REL (PRF #false adv ((λ: "_", #()),#()) #Q) << (PRP #false adv ((λ: "_", #()),#()) #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
    iIntros (<-) "Hε".
      rewrite /PRP/PRF/prp.PRP/prf.PRF...
      rewrite /random_permutation/random_function...
      rewrite /random_permutation_state...
      rel_apply_l refines_init_map_l.
      iIntros (mapref) "mapref"...
      rel_apply_r refines_init_map_r.
      iIntros (mapref') "mapref'"...
      replace 0%Z with (Z.of_nat 0%nat) by lia.
      rel_apply_r (refines_list_seq_r _ _ _ _ 0%nat).
      iIntros (?) "%"...
      rel_alloc_r unused as "unused"...
      rewrite /query_prp... 
      rel_bind_l (q_calls _ _).
      rel_bind_r (q_calls _ _).
      unshelve iApply (refines_bind with "[-][]").
      { exact (interp (TInput → (TUnit + TOutput)) []). }
      2: {
        iIntros (f f') "Hff'".
        simpl.
        unshelve iApply (refines_app with "[] [Hff']").
        3: rel_values.
        rel_arrow_val.
        iIntros (o o') "Hoo'". rel_pures_l ; rel_pures_r.
        repeat rel_apply refines_app. 3: rel_values.
        Unshelve.
        3: exact (interp TBool []).
        1: { rel_arrow_val. iIntros (??) "#(%_&->&->)". rel_pures_l ; rel_pures_r. rel_values. }
        replace (lrel_arr
                   (lrel_arr 
                      lrel_int (lrel_sum lrel_unit lrel_int))
                   (interp TBool nil)) with
          (interp TAdv []) by easy.
        iApply refines_typed.
        assumption.
      }

      rewrite /q_calls /bounded_oracle.q_calls.
      rel_alloc_l counter as "counter".
      rel_alloc_r counter' as "counter'"...
      replace 0%Z with (Z.of_nat 0%nat) by lia.
      erewrite <-fmap_empty.
      iApply (refines_na_alloc
                (∃ (q : nat) (M:gmap nat Z) (l:list nat) v',
                    ↯ (fold_left Nat.add (seq q (Q-q)) 0%nat / S val_size)
                    ∗ counter ↦ #q
                    ∗ counter' ↦ₛ #q
                    ∗ map_list mapref ((λ b, LitV (LitInt b)) <$> M)
                    ∗ map_slist mapref' ((λ b, LitV (LitInt b)) <$> M)
                    ∗ ⌜ (size (M) <= q)%nat ⌝
                    ∗ ⌜ ∀ x, x ∈ (dom M) -> (x < S val_size)%nat ⌝
                    ∗ ⌜NoDup l⌝
                    ∗ ⌜is_list l v'⌝
                    ∗ ⌜(S val_size - (size (M)) <=length l<=S val_size)%nat⌝  
                    ∗ unused ↦ₛ v'
                    ∗ ⌜(forall x:nat, Z.of_nat x∈ ((map_img M):gset _) -> x ∈ l -> False)⌝
                    ∗ ⌜∀ x, x ∈ l -> (x<S val_size)%nat ⌝
                )%I
                (nroot.@"cpa")); iFrame.
      replace (Q-0) with Q by lia; iFrame.
      iSplitL. 
      { (* solve obligations to establish invariant *)
        iPureIntro. simpl.
        eexists _.
        repeat split; try done.
        - rewrite cons_seq. apply NoDup_seq. 
        - rewrite cons_seq. by rewrite seq_length.
        - rewrite cons_seq. by rewrite seq_length.
        - intros ?. rewrite cons_seq. rewrite elem_of_seq. lia.         
      }
      iIntros "#Hinv".
      rel_arrow_val.
      iIntros (??) "(%n&->&->)"...
      rewrite -bool_decide_and.
      iApply (refines_na_inv with "[$Hinv]"); first done.
      iIntros "[>(%q&%M&%l&%v'&Hε&Hcounter&Hcounter'&Hml&Hml'&%&%&%HNoDup&%&%Hlen&unused&%Hdisjoint&%) Hclose]".
      rel_load_l; rel_load_r...
      rewrite -bool_decide_and.
      case_bool_decide; last first.
      { (* input is not valid or we exceed query num*)
        idtac...
        iApply refines_na_close; iFrame.
        iSplit; first (iPureIntro; by exists l)...
        rel_values. repeat iExists _. by iLeft.
      }
      idtac...
      rel_load_l; rel_load_r...
      rel_store_l; rel_store_r...
      replace n with (Z.of_nat (Z.to_nat n)) by lia.
      rel_apply_l (refines_get_l with "[-Hml][$Hml]").
      iIntros (?) "Hml ->".
      rel_apply_r (refines_get_r with "[-Hml'][$]").
      iIntros (?) "Hml' ->".
      replace (Z.of_nat q+1)%Z with (Z.of_nat (S q)) by lia.
      replace (Q-q) with (S (Q-S q)) by lia.
      rewrite -cons_seq.
      rewrite fold_symmetric; try lia.
      simpl. rewrite -fold_symmetric; try lia.
      rewrite plus_INR Rdiv_plus_distr.
      destruct (((λ b : Z, #b) <$> M)!!Z.to_nat n) eqn:Hres...
      { (* we query something from before*)
        iApply refines_na_close; iFrame.
        iSplitL.
        - iModIntro. iExists M, l. iFrame.
          iSplitL.
          + iApply (ec_weaken with "[$]").
            split.
            * rewrite fold_symmetric; try lia.
              smash.
            * rewrite Rplus_comm. apply Rplus_le_0_compat.
              smash.
          + iPureIntro; repeat split; (done||lia).
        - rewrite lookup_fmap_Some in Hres.
          destruct Hres as (?&<-&?).
          rel_values. repeat iExists _. iRight. iPureIntro.
          simpl.
          repeat split; by eexists _.
      }
      rel_load_r.
      rel_apply_r refines_list_length_r; first done.
      iIntros (?) "->"...
      (* make sure list has at least one element*)
      assert (size(M)<S val_size)%nat.
      { apply Nat.nle_gt.
        intros ?.
        unshelve epose proof set_subseteq_size_eq (dom M) (set_seq 0 (S val_size)) _ _ as K.
        - intros ??. rewrite elem_of_set_seq.
          split; first lia.
          set_unfold. naive_solver.
        - rewrite size_dom. rewrite size_set_seq. lia.
        - eapply is_Some_None. rewrite <-Hres.
          rewrite -elem_of_dom.
          rewrite dom_fmap.
          rewrite K.
          rewrite elem_of_set_seq. lia.
      }
      (* here need to lift coupling rule to logical relations... *)
      set f := (λ n : nat, if (n <=? val_size) then (nth n l 0) else n + val_size).
      rel_apply (refines_couple_UU_err_rev _ _ (mknonnegreal _ _) f); try lia.
      { intros. rewrite /f.
        rewrite leb_correct; try lia.
        apply Forall_nth; last lia.
        rewrite Forall_forall.
        done. 
      }
      { rewrite /f.
        intros ????.
        rewrite !leb_correct; try lia.
        apply NoDup_nth; try lia.
        by apply NoDup_ListNoDup.
      }
      { done. }
      iDestruct (ec_split with "[$]") as "[Hε Hε']"; try smash.
      iSplitL "Hε".
      { iApply ec_weaken; last done.
        split.
        - rewrite -Rdiv_def.
          smash. rewrite -minus_INR; last lia.
          smash.
        - rewrite Rdiv_def.
          apply Rmult_le_compat_r.
          + apply Rlt_le.
            apply RinvN_pos'.
          + rewrite -minus_INR; last lia.
            apply le_INR. lia.
      } 
      iIntros (x). iModIntro. rewrite /f...
      pose proof fin_to_nat_lt x.
      rewrite leb_correct; last lia.
      rel_load_r.
      rel_apply_r refines_list_remove_nth_r.
      { iPureIntro. split; first done. lia. }
      simpl.
      iIntros (?) "(%&%&%&%&->&<-&->&%)"...
      rewrite nth_middle.
      rel_apply_l (refines_set_l with "[-Hml][$]").
      iIntros "Hml".
      rel_apply_r (refines_set_r with "[-Hml'][$]").
      iIntros "Hml'"...
      rel_store_r...
      iApply (refines_na_close).
      iSplitR "Hclose"; last first.
      { iFrame.
        rel_values.
        repeat iExists _. iRight.
        iPureIntro; repeat split; try done.
        by eexists (Z.of_nat _). 
      }
      iModIntro.
      iExists _, (<[Z.to_nat n:=_]> M), (_++_).
      rewrite fmap_insert. iFrame.
      iPureIntro; repeat split.
      - rewrite map_size_insert.
        case_match; simpl; lia.
      - intros ?. rewrite dom_insert.
        set_unfold. intros [|]; try lia.
        naive_solver.
      - rewrite NoDup_ListNoDup.
        eapply NoDup_remove_1.
        rewrite -NoDup_ListNoDup.
        done.
      - done.
      - rewrite map_size_insert_None.
        + rewrite app_length.
          rewrite app_length cons_length in Hlen. lia.
        + rewrite lookup_fmap in Hres.
          rewrite fmap_None in Hres. done.
      - rewrite app_length.
        rewrite app_length cons_length in Hlen. lia.
      - intros ?. rewrite elem_of_map_img.
        intros [? K].
        rewrite lookup_insert_Some in K.
        destruct K as [[<- K']|[K1 K2]].
        + apply Nat2Z.inj' in K'. subst.
          rewrite NoDup_ListNoDup in HNoDup.
          apply NoDup_remove_2 in HNoDup.
          rewrite elem_of_list_In. done.
        + intros ?. set_unfold.
          eapply Hdisjoint.
          * rewrite elem_of_map_img. naive_solver.
          * naive_solver.
      - set_unfold. naive_solver.
        Unshelve.
        rewrite -Rdiv_def.
        smash.
        rewrite -minus_INR; last lia.
        smash.
    Qed.

  End proofs.

End prp_prf.
