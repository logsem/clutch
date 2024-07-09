(* CPA security of a PRF based symmetric encryption scheme. *)
From clutch.approxis Require Import approxis map list.
From clutch.approxis.examples Require Import prf symmetric.
Set Default Proof Using "Type*".

Section defs.

  (** We will prove CPA security of a symmetric encryption scheme based on an
  (idealised) PRF.

References for the encryption scheme:
- Definition 7.4, Mike Rosulek, 2020, The Joy of Cryptography.
- Construction 3.28, Jonathan Katz and Yehuda Lindell, 2021, Introduction to Modern Cryptography (3rd edition).

References for the CPA security proof:
- Claim 7.5, Mike Rosulek, 2020, The Joy of Cryptography.
- Theorem 3.29, Jonathan Katz and Yehuda Lindell, 2021, Introduction to Modern Cryptography (3rd edition).

We prove the portions of the above theorems that are concerned with the reduction after the PRF is replaced with the idealised PRF.
*)

  (** Parameters of the PRF. *)
  Variable Key : nat.
  Variable Input : nat.
  Variable Output : nat.

  Let Message := Output.
  Let Cipher := Input * Output.

  Local Opaque INR.

  (** Parameters of the generic PRF-based encryption scheme. *)
  Variable xor : val.
  Variable (xor_sem : fin (S Message) -> fin (S Output) -> fin (S Output)).
  Variable H_xor : forall x, Bij (xor_sem x).
  Variable (xor_correct_l: forall `{!approxisRGS Σ} E K (x : Z) (y : fin (S Message))
                             (_: (0<=x)%Z)
                             (Hx : ((Z.to_nat x) < S Message)) e A,
    (REL (fill K (of_val #(xor_sem (nat_to_fin Hx) (y)))) << e @ E : A)
    -∗ REL (fill K (xor #x #y)) << e @ E : A).
  
  Variable (xor_correct_r: ∀ `{!approxisRGS Σ} E K (x : Z) (y : fin (S Message))
                             (_: (0<=x)%Z)
                             (Hx : ((Z.to_nat x) < S Message)) e A,
    (REL e << (fill K (of_val #(xor_sem (nat_to_fin Hx) (y)))) @ E : A)
    -∗ REL e << (fill K (xor #x #y)) @ E : A).

  (** Generic PRF-based symmetric encryption. *)
  Definition prf_enc : val :=
    λ:"prf" "key",
      let: "prf_key" := "prf" "key" in
      λ: "msg",
        let: "r" := rand #Input in
        let: "z" := "prf_key" "r" in
        ("r", xor "msg" "z").

  (** We specialize the construction to an idealized random function family. *)
  Definition rf_keygen : val := λ:<>, rand #Key.
  Definition rf_enc : expr := prf_enc (random_function Output).
  Definition rf_rand_cipher : val := λ:<>, let:"i" := rand #Input in let:"o" := rand #Output in ("i", "o").
  Definition rf_scheme : expr := (rf_keygen, (rf_enc, rf_rand_cipher)).

  (** RandML types of the scheme. *)
  Definition TMessage := TInt.
  Definition TKey := TInt.
  Definition TInput := TInt.
  Definition TOutput := TInt.
  Definition TCipher := (TInput * TMessage)%ty.

  (** We will prove CPA security of the scheme using the idealised random
      function. We assume that the adversaries are well-typed. *)
  Variable adv : val.
  Definition TAdv := ((TMessage → (TUnit + TCipher)) → TBool)%ty.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).
  Definition q_calls := q_calls Message.
  Definition CPA := CPA Message.
  Definition CPA_rf : val := λ:"b" "adv", CPA "b" "adv" rf_scheme.


  Section proofs.
    Context `{!approxisRGS Σ}.

    Lemma nat_to_fin_list (l:list nat):
      (∀ x, x ∈ l -> (x < S Input)%nat) ->
      ∃ l': (list (fin (S Input))), fin_to_nat <$> l' = l.
    Proof.
      clear.
      induction l as [|a l'].
      - intros. exists []. naive_solver.
      - intros. set_unfold.
        assert (a<S Input) as H' by naive_solver.
        unshelve epose proof IHl' _ as [l ?]; first naive_solver.
        exists (nat_to_fin H'::l).
        simpl.
        repeat f_equal; last done.
        by rewrite fin_to_nat_to_fin.
    Qed.

    Theorem rf_is_CPA (Q : nat) :
      ↯ (Q * Q / (2 * S Input)) ⊢ (REL (CPA #true adv rf_scheme #Q) << (CPA #false adv rf_scheme #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
      iIntros "ε".
      rel_pures_l.
      rewrite /CPA/symmetric.CPA.
      rewrite /rf_scheme/rf_enc/prf_enc.
      idtac...
      rewrite /rf_keygen...
      rel_apply (refines_couple_UU Key).
      iIntros (key) "!>"...
      rewrite /random_function...
      rel_apply_l refines_init_map_l.
      iIntros (mapref) "mapref"...
      rel_bind_l (q_calls _ _)%E.
      rel_bind_r (q_calls _ _)%E.
      unshelve iApply (refines_bind with "[-] []").
      1:{ exact (interp (TMessage → (TUnit + TCipher)) []). }
      2:{
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
                   (lrel_arr lrel_int
                      (lrel_sum lrel_unit (lrel_prod lrel_int lrel_int)))
                   (interp TBool nil)) with
          (interp TAdv []) by easy.
        iApply refines_typed.
        assumption.
      }

      rewrite /q_calls/bounded_oracle.q_calls...
      rel_alloc_l counter as "counter"... rel_alloc_r counter' as "counter'"...

      iApply (refines_na_alloc
                (∃ (q : nat) M,
                    ↯ ((Q*Q-q*q) / (2 * S Input))
                    ∗ counter ↦ #q
                    ∗ counter' ↦ₛ #q
                    ∗ map_list mapref M
                    ∗ ⌜ size (dom M) = q ⌝
                    ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S Input)%nat ⌝
                )%I
                (nroot.@"cpa")); iFrame.
      iSplitL.
      1: { iExists 0.
           rewrite INR_0.
           replace (Q*Q-0*0)%R with (Q*Q)%R by lra.
           iFrame. iPureIntro; set_solver.
      }
      iIntros "#Hinv".
      rel_arrow_val.
      iIntros (??) "#(%msg&->&->)" ; rel_pures_l ; rel_pures_r.
      iApply (refines_na_inv with "[$Hinv]"); [done|].
      iIntros "(> (%q & %M & ε & counter & counter' & mapref & %dom_q & %dom_range) & Hclose)".
      case_bool_decide as Hm.
      - rel_load_l ; rel_load_r...
        rewrite /rf_rand_cipher.
        rewrite -bool_decide_and.
        case_bool_decide as Hq.
        + rel_load_l ; rel_load_r... rel_store_l ; rel_store_r...
          assert (Z.to_nat msg < S Message) as Hmsg by lia.
          pose proof nat_to_fin_list (elements(dom M)) dom_range as [l' Hl'].
          rel_apply (refines_couple_couple_avoid _ l').
          { apply NoDup_fmap with fin_to_nat; first apply fin_to_nat_inj.
            rewrite Hl'. apply NoDup_elements. }
          replace (length l') with q; last first.
          { erewrite <-fmap_length, Hl'.
            by replace (length (elements (dom M))) with (size (dom M)).
          }
          pose proof pos_INR_S (Input).
          assert (0<=q/S Input)%R.
          { apply Rcomplements.Rdiv_le_0_compat; last done.
            apply pos_INR. }
          assert (0<=(Q * Q - (q+1)%nat * (q+1)%nat)/(2*S Input))%R.
          { apply Rcomplements.Rdiv_le_0_compat; last lra.
            rewrite -!mult_INR. apply Rle_0_le_minus.
            apply le_INR. rewrite -Nat.square_le_mono. lia. }
          iDestruct (ec_weaken _ (q/S Input+((Q * Q - (q + 1)%nat * (q + 1)%nat))/ (2 * S Input)) with "[$]") as "ε".
          { split; first lra.
            apply Rcomplements.Rle_minus_r.
            rewrite Rminus_def -Rdiv_opp_l -Rdiv_plus_distr.
            rewrite Rdiv_mult_distr.
            rewrite !Rdiv_def.
            apply Rmult_le_compat_r.
            { apply Rlt_le. by apply Rinv_0_lt_compat. }
            rewrite -Rcomplements.Rle_div_r; last lra.
            trans ((q + 1)%nat * (q + 1)%nat-q*q)%R; last lra.
            rewrite plus_INR. 
            replace (INR 1) with 1%R by done. lra.
          }
          iDestruct (ec_split with "[$]") as "[ε ε']"; [done|done|].
          iFrame.
          iIntros (r_in) "!> %r_fresh"...
          rel_apply_l (refines_get_l with "[-mapref] [$mapref]").
          iIntros (?) "mapref #->"...
          assert ((M !! fin_to_nat r_in) = None) as ->.
          { apply not_elem_of_dom_1.
            rewrite -elem_of_elements.
            rewrite -Hl'.
            intros K. apply elem_of_list_fmap_2_inj in K; last apply fin_to_nat_inj.
            done.
          }
          simpl...
          unshelve rel_apply (refines_couple_UU _ (xor_sem (Fin.of_nat_lt Hmsg))).
          iIntros (y) "!>"...
          rel_apply_l (refines_set_l with "[-mapref] [$mapref]").
          iIntros "mapref"...
          rel_bind_l (xor _ _).
          rel_apply_l xor_correct_l; first done.
          iApply (refines_na_close with "[-]").
          iFrame.
          iSplitL.
          { replace (Z.of_nat q + 1)%Z with (Z.of_nat (q+1)) by lia.
            iFrame.
            iModIntro.
            iPureIntro; split.
            - rewrite size_dom. rewrite size_dom in dom_q.
              rewrite map_size_insert_None; first lia.
              apply not_elem_of_dom_1.
              rewrite -elem_of_elements.
              rewrite -Hl'.
              intros K.
              apply elem_of_list_fmap_2_inj in K; last apply fin_to_nat_inj.
              done.
            - intros x.
              rewrite elem_of_elements.
              set_unfold.
              intros [|]; last naive_solver.
              subst. apply fin_to_nat_lt.
          } 
          idtac...
          rel_values.
          repeat iExists _.
          iModIntro. iRight. repeat iSplit ; iPureIntro ; eauto.
          simpl. by repeat unshelve eexists.
        + iApply (refines_na_close with "[-]").
          iFrame.
          iSplit...
          { done. }
          rel_values. repeat iExists _. iLeft. done.
      - rel_load_l ; rel_load_r...
        rewrite /rf_rand_cipher.
        rewrite andb_false_r...
        iApply (refines_na_close with "[-]").
        iFrame.
        iSplit.
        { done. }
        rel_values. repeat iExists _. iLeft. done.
    Qed.

    Theorem rf_is_CPA' (Q : nat) :
      ↯ (Q * Q / (2 * S Input)) ⊢ (REL (CPA #false adv rf_scheme #Q) << (CPA #true adv rf_scheme #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
      iIntros "ε".
      rel_pures_l.
      rewrite /CPA/symmetric.CPA.
      rewrite /rf_scheme/rf_enc/prf_enc...
      rewrite /rf_keygen...
      rel_apply (refines_couple_UU Key).
      iIntros (key) "!>"...
      rewrite /random_function...
      rel_apply_r refines_init_map_r.
      iIntros (mapref) "mapref"...
      rel_bind_l (q_calls _ _)%E.
      rel_bind_r (q_calls _ _)%E.
      unshelve iApply (refines_bind with "[-] []").
      1:{ exact ((interp (TMessage → (TUnit + TCipher))) []). }
      2:{
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
                   (lrel_arr lrel_int
                      (lrel_sum lrel_unit (lrel_prod lrel_int lrel_int)))
                   (interp TBool nil)) with
          (interp TAdv []) by easy.
        iApply refines_typed.
        assumption.
      }

      rewrite /q_calls/bounded_oracle.q_calls...
      rel_alloc_l counter as "counter"... rel_alloc_r counter' as "counter'"...

      iApply (refines_na_alloc
                (∃ (q : nat) M,
                    ↯ ((Q*Q-q*q) / (2 * S Input))
                    ∗ counter ↦ #q
                    ∗ counter' ↦ₛ #q
                    ∗ map_slist mapref M
                    ∗ ⌜ size (dom M) = q ⌝
                    ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S Input)%nat ⌝
                )%I
                (nroot.@"cpa")); iFrame.
      iSplitL.
      1: { iExists 0.
           rewrite INR_0.
           replace (Q*Q-0*0)%R with (Q*Q)%R by lra.
           iFrame. iPureIntro; set_solver.
      }
      iIntros "#Hinv".
      rel_arrow_val.
      iIntros (??) "#(%msg&->&->)" ; rel_pures_l ; rel_pures_r.
      iApply (refines_na_inv with "[$Hinv]"); [done|].
      iIntros "(> (%q & %M & ε & counter & counter' & mapref & %dom_q & %dom_range) & Hclose)".
      rewrite -bool_decide_and.
      case_bool_decide as Hm.
      - rel_load_l ; rel_load_r...
        rewrite /rf_rand_cipher.
        case_bool_decide as Hq...
        + rel_load_l ; rel_load_r... rel_store_l ; rel_store_r...
          assert (Z.to_nat msg < S Message) as Hmsg by lia.
          pose proof nat_to_fin_list (elements(dom M)) dom_range as [l' Hl'].
          rel_apply (refines_couple_couple_avoid _ l').
          { apply NoDup_fmap with fin_to_nat; first apply fin_to_nat_inj.
            rewrite Hl'. apply NoDup_elements. }
          replace (length l') with q; last first.
          { erewrite <-fmap_length, Hl'.
            by replace (length (elements (dom M))) with (size (dom M)).
          }
          pose proof pos_INR_S (Input).
          assert (0<=q/S Input)%R.
          { apply Rcomplements.Rdiv_le_0_compat; last done.
            apply pos_INR. }
          assert (0<=(Q * Q - (q+1)%nat * (q+1)%nat)/(2*S Input))%R.
          { apply Rcomplements.Rdiv_le_0_compat; last lra.
            rewrite -!mult_INR. apply Rle_0_le_minus.
            apply le_INR. rewrite -Nat.square_le_mono. lia. }
          iDestruct (ec_weaken _ (q/S Input+((Q * Q - (q + 1)%nat * (q + 1)%nat))/ (2 * S Input)) with "[$]") as "ε".
          { split; first lra.
            apply Rcomplements.Rle_minus_r.
            rewrite Rminus_def -Rdiv_opp_l -Rdiv_plus_distr.
            rewrite Rdiv_mult_distr.
            rewrite !Rdiv_def.
            apply Rmult_le_compat_r.
            { apply Rlt_le. by apply Rinv_0_lt_compat. }
            rewrite -Rcomplements.Rle_div_r; last lra.
            trans ((q + 1)%nat * (q + 1)%nat-q*q)%R; last lra.
            rewrite plus_INR. 
            replace (INR 1) with 1%R by done. lra.
          }
          iDestruct (ec_split with "[$]") as "[ε ε']"; [done|done|].
          iFrame.
          iIntros (r_in) "!> %r_fresh"...
          rel_apply_r (refines_get_r with "[-mapref] [$mapref]").
          iIntros (?) "mapref #->"...
          assert ((M !! fin_to_nat r_in) = None) as ->.
          { apply not_elem_of_dom_1.
            rewrite -elem_of_elements.
            rewrite -Hl'.
            intros K. apply elem_of_list_fmap_2_inj in K; last apply fin_to_nat_inj.
            done.
          }
          simpl...
          unshelve rel_apply (refines_couple_UU _ (f_inv (xor_sem (Fin.of_nat_lt Hmsg)))).
          { apply H_xor. }
          { split.
            - intros ?? H'.
              apply (f_equal (xor_sem (nat_to_fin Hmsg))) in H'.
              by rewrite !f_inv_cancel_r in H'.
            - intros y. exists (xor_sem (nat_to_fin Hmsg) y).
              apply f_inv_cancel_l. apply H_xor. 
          }
          iIntros (y) "!>"...
          rel_apply_r (refines_set_r with "[-mapref] [$mapref]").
          iIntros "mapref"...
          rel_bind_r (xor _ _).
          rel_apply_r xor_correct_r; first lia.
          iApply (refines_na_close with "[-]").
          iFrame.
          iSplitL.
          { replace (Z.of_nat q + 1)%Z with (Z.of_nat (q+1)) by lia.
            iFrame.
            iModIntro.
            iPureIntro; split.
            - rewrite size_dom. rewrite size_dom in dom_q.
              rewrite map_size_insert_None; first lia.
              apply not_elem_of_dom_1.
              rewrite -elem_of_elements.
              rewrite -Hl'.
              intros K.
              apply elem_of_list_fmap_2_inj in K; last apply fin_to_nat_inj.
              done.
            - intros x.
              rewrite elem_of_elements.
              set_unfold.
              intros [|]; last naive_solver.
              subst. apply fin_to_nat_lt.
          } 
          idtac...
          rel_values.
          repeat iExists _.
          iModIntro. iRight. repeat iSplit ; iPureIntro ; eauto.
          simpl.
          exists #r_in. eexists #r_in.
          exists #y.
          eexists. repeat split ; try eauto with done.
          1: by eexists. exists y. split ; first done.
          by erewrite f_inv_cancel_r.
        + iApply (refines_na_close with "[-]").
          iFrame.
          iSplit.
          { done. }
          rel_values. repeat iExists _. iLeft. done.
      - rel_load_l ; rel_load_r...
        rewrite /rf_rand_cipher.
        rewrite andb_false_r...
        iApply (refines_na_close with "[-]").
        iFrame.
        iSplit.
        { done. }
        rel_values. repeat iExists _. iLeft. done.
    Qed.
    

  End proofs.

  Lemma rf_CPA_ARC Σ `{approxisRGpreS Σ} σ σ' (Q : nat) :
    ARcoupl
      (lim_exec ((CPA #true adv rf_scheme #Q), σ))
      (lim_exec ((CPA #false adv rf_scheme #Q), σ'))
      (=)
      (Q * Q / (2 * S Input)).
  Proof.
    unshelve eapply approximates_coupling ; eauto.
    1: exact (fun _ => lrel_bool).
    { repeat apply Rmult_le_pos; try apply pos_INR.
      rewrite -Rdiv_1_l.
      pose proof Rdiv_INR_ge_0 (S Input).
      cut ((0 <= (2*1) / (2 * INR (S Input))))%R; first lra.
      rewrite Rmult_comm.
      rewrite Rmult_div_swap.
      rewrite (Rmult_comm 2%R).
      rewrite Rdiv_mult_distr.
      lra.
    }
    1: by iIntros (???) "#(%b&->&->)".
    iIntros. by iApply rf_is_CPA.
  Qed.

  Lemma rf_CPA_ARC' Σ `{approxisRGpreS Σ} σ σ' (Q : nat) :
    ARcoupl
      (lim_exec ((CPA #false adv rf_scheme #Q), σ))
      (lim_exec ((CPA #true adv rf_scheme #Q), σ'))
      (=)
      (Q * Q / (2 * S Input)).
  Proof.
    unshelve eapply approximates_coupling ; eauto.
    1: exact (fun _ => lrel_bool).
    { repeat apply Rmult_le_pos; try apply pos_INR.
      rewrite -Rdiv_1_l.
      pose proof Rdiv_INR_ge_0 (S Input).
      cut ((0 <= (2*1) / (2 * INR (S Input))))%R; first lra.
      rewrite Rmult_comm.
      rewrite Rmult_div_swap.
      rewrite (Rmult_comm 2%R).
      rewrite Rdiv_mult_distr.
      lra.
    }
    1: by iIntros (???) "#(%b&->&->)".
    iIntros. by iApply rf_is_CPA'.
  Qed.

  Corollary CPA_bound_1 Σ `{approxisRGpreS Σ} σ σ' (Q : nat) :
    (((lim_exec ((CPA #true adv rf_scheme #Q), σ)) #true)
     <=
       ((lim_exec ((CPA #false adv rf_scheme #Q), σ')) #true) + (Q * Q / (2 * S Input)))%R.
  Proof.
    apply ARcoupl_eq_elim.
    by eapply rf_CPA_ARC.
  Qed.

  Corollary CPA_bound_2 Σ `{approxisRGpreS Σ} σ σ' (Q : nat) :
    (((lim_exec ((CPA #false adv rf_scheme #Q), σ)) #true)
     <=
       ((lim_exec ((CPA #true adv rf_scheme #Q), σ')) #true) + (Q * Q / (2 * S Input)))%R.
  Proof.
    apply ARcoupl_eq_elim.
    by eapply rf_CPA_ARC'.
  Qed.

  Lemma CPA_bound Σ `{approxisRGpreS Σ} σ σ' (Q : nat) :
    (Rabs (((lim_exec ((CPA #true adv rf_scheme #Q), σ)) #true) -
           ((lim_exec ((CPA #false adv rf_scheme #Q), σ')) #true)) <= (Q * Q / (2 * S Input)))%R.
  Proof.
    apply Rabs_le.
    pose proof CPA_bound_1 Σ σ σ' Q.
    pose proof CPA_bound_2 Σ σ' σ Q.
    split; lra.
  Qed.
  
End defs.

Section implementation.
  Variable adv : val.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).
  Definition bit:=64.
  Definition Output' := 2^bit - 1.
  Definition Input' := 2^8-1.
  Definition Key' := 2^8-1.
  Notation Message' := Output'.
  Notation Output := (S Output').
  Lemma Output_pos: 0<Output.
  Proof. lia. Qed.
  
  Definition xor:val :=
    (λ: "x" "y", let: "sum" := "x" + "y" in
                 if: "sum" < #Output then "sum" else "sum" - #Output)%V.

  Lemma xor_sem_aux (x y:fin (Output)):
    (if bool_decide (fin_to_nat x + fin_to_nat y<Output)
    then fin_to_nat x + fin_to_nat y
    else fin_to_nat x + fin_to_nat y - Output) < Output.     
  Proof.
    case_bool_decide; first done.
    pose proof fin_to_nat_lt x.
    pose proof fin_to_nat_lt y.
    lia.
  Qed.

  Definition xor_sem x y := nat_to_fin (xor_sem_aux x y).
  
  Lemma xor_sem_bij x: Bij (xor_sem x).
  Proof.
    split.
    - intros y y'. rewrite /xor_sem.
      intros H.
      apply (f_equal fin_to_nat) in H.
      rewrite !fin_to_nat_to_fin in H.
      apply fin_to_nat_inj.
      pose proof fin_to_nat_lt x.
      pose proof fin_to_nat_lt y.
      pose proof fin_to_nat_lt y'.
      case_bool_decide; case_bool_decide; lia.
    - rewrite /xor_sem. intros y.
      pose proof fin_to_nat_lt x.
      pose proof fin_to_nat_lt y.
      destruct (decide (x<=y)) eqn:Heqn.
      + assert (y-x<Output) as K by lia.
        exists (nat_to_fin K).
        apply fin_to_nat_inj.
        rewrite !fin_to_nat_to_fin.
        case_bool_decide; lia.
      + assert (Output+y-x<Output) as K by lia.
        exists (nat_to_fin K).
        apply fin_to_nat_inj.
        rewrite !fin_to_nat_to_fin.
        case_bool_decide; lia.
  Qed.
  
  Lemma xor_correct_l `{!approxisRGS Σ} E K (x : Z) (y : fin (S Message'))
    (_: (0<=x)%Z)
    (Hx : ((Z.to_nat x) < S Message')) e A:
    (REL (fill K (of_val #(xor_sem (nat_to_fin Hx) (y)))) << e @ E : A)
    -∗ REL (fill K (xor #x #y)) << e @ E : A.
  Proof with rel_pures_l.
    iIntros "H".
    rewrite /xor...
    rewrite /xor_sem. rewrite !fin_to_nat_to_fin.
    case_bool_decide.
    - rewrite bool_decide_eq_true_2; last lia...
      replace (Z.of_nat (Z.to_nat x + fin_to_nat y))%Z with (x + Z.of_nat (fin_to_nat y))%Z; first done.
      rewrite Nat2Z.inj_add. rewrite Z2Nat.id; lia.
    - rewrite bool_decide_eq_false_2; last lia...
      replace (Z.of_nat (Z.to_nat x + fin_to_nat y - S Message'))%Z with (x + Z.of_nat (fin_to_nat y) - Z.of_nat (S Message'))%Z by lia.
      done.
  Qed.
  
  Lemma xor_correct_r  `{!approxisRGS Σ} E K (x : Z) (y : fin (S Message')) 
    (_: (0<=x)%Z) (Hx : ((Z.to_nat x) < S Message')) e A:
    (REL e << (fill K (of_val #(xor_sem (nat_to_fin Hx) (y)))) @ E : A)
    -∗ REL e << (fill K (xor #x #y)) @ E : A.
  Proof with rel_pures_r.
    iIntros "H".
    rewrite /xor...
    rewrite /xor_sem. rewrite !fin_to_nat_to_fin.
    case_bool_decide.
    - rewrite bool_decide_eq_true_2; last lia...
      replace (Z.of_nat (Z.to_nat x + fin_to_nat y))%Z with (x + Z.of_nat (fin_to_nat y))%Z; first done.
      rewrite Nat2Z.inj_add. rewrite Z2Nat.id; lia.
    - rewrite bool_decide_eq_false_2; last lia...
      replace (Z.of_nat (Z.to_nat x + fin_to_nat y - S Message'))%Z with (x + Z.of_nat (fin_to_nat y) - Z.of_nat (S Message'))%Z by lia.
      done.
  Qed.

  Lemma CPA_bound_realistic σ σ' (Q : nat) :
    (Rabs (((lim_exec (((CPA Output') #true adv (rf_scheme Key' Input' Output' xor) #Q), σ)) #true) -
             ((lim_exec (((CPA Output') #false adv (rf_scheme Key' Input' Output' xor) #Q), σ')) #true)) <= (Q * Q / (2 * S Input')))%R.
  Proof.
    unshelve epose proof CPA_bound Key' Input' Output' xor xor_sem _ _ _ adv _ _ σ σ' Q as H.
    - apply xor_sem_bij.
    - intros. by apply xor_correct_l.
    - intros. by apply xor_correct_r.
    - done.
    - apply approxisRΣ.
    - apply subG_approxisRGPreS. apply subG_refl.
    - apply H. 
  Qed.
      
End implementation.
