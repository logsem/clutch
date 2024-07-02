(** The PRP/PRF switching Lemma.

References:
- Lemma 1, Bellare and Rogaway, 2006, Code-Based Game-Playing Proofs and the Security of Triple Encryption.
- Lemma 6.7, Mike Rosulek, 2020, The Joy of Cryptography.
- Theorem 4.4, Boneh and Shoup, 2023, A Graduate Course in Applied Cryptography (Version 0.6).

Our definition deviates from Rosulek's and Boneh/Shoup in that we wrap the encryption oracle with [q_calls] to enforce the bound [Q] on the number of oracle calls, while loc. cit. rely on the assumption that the adversary runs in polynomial time in the security parameter.

     *)

From clutch Require Import lib.flip.
From clutch.paris Require Import paris map list prf prp examples.prf_cpa.
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
  Local Opaque seq.

  Section proofs.
    Context `{!parisRGS Σ}.

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

      rewrite /q_calls /prf_cpa.q_calls /bounded_oracle.q_calls...
      rel_alloc_l counter as "counter".
      rel_alloc_r counter' as "counter'"...
      replace 0%Z with (Z.of_nat 0%nat) by lia.
      erewrite <-fmap_empty.
      iApply (refines_na_alloc
                (∃ (q : nat) (M:gmap nat Z) (l:list nat),
                    ↯ (fold_left Nat.add (seq q Q) 0%nat / S val_size)
                    ∗ counter ↦ #q
                    ∗ counter' ↦ₛ #q
                    ∗ map_list mapref ((λ b, LitV (LitInt b)) <$> M)
                    ∗ map_slist mapref' ((λ b, LitV (LitInt b)) <$> M)
                    ∗ ⌜ (size (dom M) <= q)%nat ⌝
                    ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S val_size)%nat ⌝
                    ∗ ⌜NoDup l⌝
                    ∗ ⌜is_list l v⌝
                    ∗ ⌜(S val_size - q <=length l)%nat⌝  
                    ∗ unused ↦ v
                    ∗ ⌜(forall x:nat, x∈ ((map_img M):gset _) -> x ∈ l -> False)⌝
                    ∗ ⌜∀ x, x ∈ l -> (x<S val_size)%nat ⌝
                )%I
                (nroot.@"cpa")); iFrame.
      iSplit. 
      { (* solve obligations to establish invariant *)
        iPureIntro. simpl.
        eexists _.
        repeat split; try done.
        - by set_unfold.
        - apply NoDup_seq. 
        - by rewrite seq_length.
        - intros ?. rewrite elem_of_seq. lia.         
      }
      iIntros "#Hinv".
      rel_arrow_val.
      iIntros (??) "(%n&->&->)"...
      rewrite -bool_decide_and.
      iApply (refines_na_inv with "[$Hinv]"); first done.
      iIntros "[>(%q&%M&%l&Hε&Hcounter&Hcounter'&Hml&Hml'&%&%&%&%&%&unused&%&%) Hclose]".
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
      destruct (((λ b : Z, #b) <$> M)!!Z.to_nat n) eqn:Hres...
      { (* we query something from before*)
        replace (Z.of_nat q+1)%Z with (Z.of_nat (S q)) by lia.
        iApply refines_na_close; iFrame.
        iSplitL.
        - iModIntro. iExists M, l. iFrame.
          iSplitL.
          + admit.
          + iPureIntro; repeat split; (done||lia).
        - rewrite lookup_fmap_Some in Hres.
          destruct Hres as (?&<-&?).
          rel_values. repeat iExists _. iRight. iPureIntro.
          simpl.
          repeat split; by eexists _.
      }
      
    Admitted.

    Theorem PRF_PRP (Q : nat) ε :
      (INR (fold_left (Nat.add) (seq 0 Q) 0%nat) / INR (S val_size))%R = ε
      →
      ↯ ε ⊢ (REL (PRF #false adv ((λ: "_", #()),#()) #Q) << (PRP #false adv ((λ: "_", #()),#()) #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
    Admitted.

  End proofs.

End prp_prf.
