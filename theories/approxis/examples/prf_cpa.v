(* CPA security of a PRF based symmetric encryption scheme. *)
From clutch.approxis Require Import approxis map list.
From clutch.approxis.examples Require Import prf symmetric security_aux option xor.
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
  Variable xor_struct : XOR (Key := Message) (Support := Output).

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
  Definition rf_enc : val :=
    λ:"key", prf_enc (λ:<>, random_function #Output) "key".
  Definition rf_rand_cipher : val :=
    λ:<>, let:"i" := rand #Input in let:"o" := rand #Output in ("i", "o").
  Definition rf_dec : val := #().
  Local Instance SYM_param : SYM_params :=
    {| card_key := Key ; card_message := Message ; card_cipher := Cipher |}.
  Local Instance sym_rf_scheme : SYM :=
    {| keygen := rf_keygen ;
      enc := rf_enc ; rand_cipher := rf_rand_cipher ; dec := rf_dec |}.
  Definition rf_scheme : val := sym_scheme.

  (** RandML types of the scheme. *)
  Definition TMessage := TInt.
  Definition TKey := TInt.
  Definition TInput := TInt.
  Definition TOutput := TInt.
  Definition TCipher := (TInput * TMessage)%ty.

  (** We will prove CPA security of the scheme using the idealised random
      function. We assume that the adversaries are well-typed. *)
  Variable adv : val.
  Definition TAdv := ((TMessage → (TOption TCipher)) → TBool)%ty.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).


  Section proofs.
    Context `{!approxisRGS Σ}.
    Variable xor_spec : XOR_spec.


(* Proof Sketch

We track the previously sampled PRF elements in the map M. To ensure that we
query a fresh element and PRF behaves randomly, we pay |dom(M)| error credits.
The counter q tracks this size, i.e., q = |dom(M)|.

In total, we have an error budget of ε₀ = (Q-1)Q/2N. This is enough to sum over
Q calls, each of which consumes error q/N, where q is the number of previously
executed calls. For example, on the first call, q=0 and we need 0 error credits.
On the second call, we start with q=1, and we need 1/N error credits for the
current round, and end up with q=2 and ε₀ - 1/N credits. On the third call, q=2,
we need ↯ 2/N, and end up with q=3 and ↯ (ε₀ - 1/N - 2/N). In the last round, we
start with q=Q-1, spend q/N, and have end up having consumed all ε₀ credits.

| call q | initial budget       | cost    | q end | budget end           |
|--------|----------------------|---------|-------|----------------------|
|      0 | ε₀                   | 0/N     |     1 | ε₀                   |
|      1 | ε₀                   | 1/N     |     2 | ε₀ - 1/N             |
|      2 | ε₀ - 1/N             | 2/N     |     3 | ε₀ - 1/N - 2/N       |
|      3 | ε₀ - 1/N - 2/N       | 3/N     |     4 | ε₀ - 1/N - 2/N - 3/N |
|      q | ε₀ - (0+1+2+…+q-1)/N | q/N     |   q+1 | ε₀ - (0+1+…+q-1+q)/N |
|    Q-1 | ε₀ - (0+1+2+…+Q-2)/N | (Q-1)/N |     Q | 0                    |


Since sum_{i=0}^{q-1} i/N = (q-1)q/2N, each round starts with
ε_q = ε₀ - (q-1)q/2N and ends with ε_(q+1) = ε₀ - q(q+1)/2N.

Let ε_q = 0/N+1/N+...+(q-1)/N = sum_{i=0}^{q-1}{i/N} = (q-1)q/2N
be the amount of credits spent so far.

The credits stored in the invariant step from ε_Q-ε_q to ε_Q-ε_q+1.

Since ε_{q+1} = q(q+1)/2N = (q*q + q)/2N = (q*q - q + 2q)/2N = ((q-1)q + 2q)/2N
 = ε_q + q/N

we can split off q/N credits to spend on sampling a fresh element, as required.
*)



    (* Auxiliary lemmas *)
    Lemma split_credit_step (Q N' q : nat) :
      ((Q - 1) * Q / (2 * (S N')) - (q-1) * q / (2*(S N')) )%R
      =
        ((Q - 1) * Q / (2 * (S N')) - (((q+1)-1) * (q+1) / (2* (S N'))) + q/(S N') )%R.
    Proof. field. real_solver. Qed.

    Lemma map_insert_fresh_size (N' : nat) (q : nat) (M : gmap nat val)
      (l' : list (fin (S N')))
      (dom_q : size (dom M) = q)
      (Hl' : fin_to_nat <$> l' = elements (dom M))
      (r_in : fin (S N'))
      (r_fresh : r_in ∉ l') (y : nat) :
      size (dom (<[(fin_to_nat r_in):=#y]> M)) = q + 1.
    Proof.
      rewrite size_dom. rewrite size_dom in dom_q.
      rewrite map_size_insert_None ; [clear -dom_q ; lia|].
      apply not_elem_of_dom_1.
      rewrite -elem_of_elements.
      rewrite -Hl'.
      intros K.
      apply elem_of_list_fmap_2_inj in K ; last apply fin_to_nat_inj.
      done.
    Qed.

    (* TODO Make it so that `iFrame "ε"` generates the obligation `ε = ε'`.
       Currently, one has to write the equation or apply ec_eq manually. *)
    Local Instance ec_frame_eq ε ε' :
      ε = ε' ->
      Frame false (↯ ε) (↯ ε') emp | 0.
    Proof.
      intros ->. simpl. iIntros "[??]". iFrame.
    Defined.


    Theorem rf_is_CPA (Q : nat) :
      ↯ ((Q-1) * Q / (2 * S Input))
      ⊢
      (REL (CPA #true adv rf_scheme #Q)
           <<
           (CPA #false adv rf_scheme #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
      iIntros "ε".
      rewrite /CPA/symmetric.CPA...
      rewrite /rf_scheme/rf_enc/prf_enc.
      rewrite /get_keygen... rewrite /rf_keygen...
      rel_apply (refines_couple_UU Key id) => //.
      iIntros (key) "!> %"...
      rewrite /get_enc/get_rand_cipher...
      rewrite /rf_enc /prf_enc /random_function...
      rel_apply_l refines_init_map_l.
      iIntros (mapref) "mapref". idtac...
      rewrite /prf_enc/get_card_message...
      rel_bind_l (q_calls _ _ _)%E ; rel_bind_r (q_calls _ _ _)%E.
      unshelve iApply (refines_bind with "[-] []").
      1: exact (interp (TMessage → (TOption TCipher)) []).
      2:{
        iIntros (f f') "Hff'" => /=.
        unshelve iApply (refines_app with "[] [Hff']").
        3: rel_values.
        rel_arrow_val.
        iIntros (o o') "Hoo'"...
        repeat rel_apply refines_app. 3: rel_values.
        Unshelve. 3: exact (interp TBool []).
        1: { rel_arrow_val. lrintro... rel_values. }
        replace (_ → _)%lrel with (interp TAdv []) by easy.
        iApply refines_typed. assumption.
      }
      rewrite /q_calls...
      rel_alloc_l counter as "counter" ; rel_alloc_r counter' as "counter'"...

      iApply (refines_na_alloc
                (∃ (q : nat) M,
                    ↯ (((Q-1)*Q) / (2 * S Input) -
                              ((q-1)*q) / (2 * S Input))
                    ∗ counter ↦ #q
                    ∗ counter' ↦ₛ #q
                    ∗ map_list mapref M
                    ∗ ⌜ size (dom M) = q ⌝
                    ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S Input)%nat ⌝
                )%I
                (nroot.@"cpa")); iFrame.
      iSplitL.
      1: { iExists 0. iFrame. iSplitL ; [|iPureIntro ; set_solver].
           (* See TODO ec_frame_eq. *)
           (* try iFrame "ε".
              iNext.
              eapply (coq_tactics.tac_frame _ "ε" false _ _ True).
                1: simpl. 1: reflexivity.
                2: simpl ; done.
                apply ec_frame_eq. *)
           iApply (ec_eq with "[$]").
           (* setoid_rewrite Qdiv_0_l. setoid_rewrite Qminus_0_r.
                done. *)
           (* apply Qreals.Qeq_eqR. *)
           qify_r ; zify_q ; nia.
      }
      iIntros "#Hinv".
      rel_arrow_val ; lrintro "msg"...
      iApply (refines_na_inv with "[$Hinv]"); [done|].
      iIntros "(> (%q & %M & ε & counter & counter' & mapref & %dom_q & %dom_range) & Hclose)".
      case_bool_decide as Hm.
      - rel_load_l ; rel_load_r...
        rewrite /rf_rand_cipher.
        rewrite -bool_decide_and.
        case_bool_decide as Hq.
        + rel_load_l ; rel_load_r... rel_store_l ; rel_store_r...
          assert (Z.to_nat msg < S Message) as Hmsg by lia.
          pose proof nat_to_fin_list _ (elements(dom M)) dom_range as [l' Hl'].
          rel_apply (refines_couple_couple_avoid _ l').
          { apply (NoDup_fmap fin_to_nat). rewrite Hl'. apply NoDup_elements. }
          replace (length l') with q. 2: by erewrite <-fmap_length, Hl'.
          pose proof pos_INR_S (Input).
          rewrite split_credit_step.
          iDestruct (ec_split with "[$]") as "[ε ε']".
          1,2: qify_r ; zify_q ; nia.
          iFrame.
          iIntros (r_in) "!> %r_fresh"...
          rel_apply_l (refines_get_l with "[-mapref] [$mapref]").
          iIntros (?) "mapref #->"...
          assert ((M !! fin_to_nat r_in) = None) as ->.
          { apply not_elem_of_dom_1. rewrite -elem_of_elements -Hl'. intros K.
            by apply elem_of_list_fmap_2_inj in K ; [|apply fin_to_nat_inj]. }
          simpl...
          rel_apply (refines_couple_UU _ (xor_sem (Z.to_nat msg))).
          1: by apply xor_dom. 
          iIntros (y) "!> %"...
          rel_apply_l (refines_set_l with "[-mapref] [$mapref]").
          iIntros "mapref"...
          rel_bind_l (xor _ _).
          rel_apply_l xor_correct_l; [done | done | lia |].
          iApply (refines_na_close with "[-]").
          iFrame. iSplitL... 2: rel_vals.
          iExists (q+1).
          nify_r.
          replace (Z.of_nat q + 1)%Z with (Z.of_nat (q+1)) by lia.
          iFrame.
          iPureIntro; split.
          * eapply map_insert_fresh_size ; eauto.
          * intros x. rewrite elem_of_elements. set_unfold.
            intros [|]; last naive_solver. subst. apply fin_to_nat_lt.
        + iApply (refines_na_close with "[-]").
          iFrame ; iSplit... 1: done. rel_vals.
      - rel_load_l ; rel_load_r... rewrite andb_false_r...
        iApply (refines_na_close with "[-]").
        iFrame ; iSplit... 1: done. rel_vals.
        Unshelve. apply xor_bij.
    Qed.


    Theorem rf_is_CPA' (Q : nat) :
      ↯ ((Q-1) * Q / (2 * S Input)) ⊢ (REL (CPA #false adv rf_scheme #Q) << (CPA #true adv rf_scheme #Q) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
      iIntros "ε".
      rewrite /CPA/symmetric.CPA...
      rewrite /rf_scheme/rf_enc/prf_enc.
      rewrite /get_keygen... rewrite /rf_keygen...
      rel_apply (refines_couple_UU Key id) => //.
      iIntros (key) "!> %"...
      rewrite /get_enc/get_rand_cipher...
      rewrite /rf_enc /prf_enc /random_function...
      rel_apply_r refines_init_map_r.
      iIntros (mapref) "mapref". idtac...
      rewrite /prf_enc/get_card_message...
      rel_bind_l (q_calls _ _ _)%E ; rel_bind_r (q_calls _ _ _)%E.
      unshelve iApply (refines_bind with "[-] []").
      1: exact (interp (TMessage → (TOption TCipher)) []).
      2:{
        iIntros (f f') "Hff'" => /=.
        unshelve iApply (refines_app with "[] [Hff']").
        3: rel_values.
        rel_arrow_val.
        iIntros (o o') "Hoo'"...
        repeat rel_apply refines_app. 3: rel_values.
        Unshelve. 3: exact (interp TBool []).
        1: { rel_arrow_val. lrintro... rel_values. }
        replace (_ → _)%lrel with (interp TAdv []) by easy.
        iApply refines_typed. assumption.
      }
      rewrite /q_calls...
      rel_alloc_l counter as "counter" ; rel_alloc_r counter' as "counter'"...

      iApply (refines_na_alloc
                (∃ (q : nat) M,
                    ↯ (((Q-1)*Q) / (2 * S Input) -
                         ((q-1)*q) / (2 * S Input))
                    ∗ counter ↦ #q
                    ∗ counter' ↦ₛ #q
                    ∗ map_slist mapref M
                    ∗ ⌜ size (dom M) = q ⌝
                    ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S Input)%nat ⌝
                )%I
                (nroot.@"cpa")); iFrame.
      iSplitL.
      1: { iExists 0.
           iFrame. iSplitL. 2: iPureIntro ; set_solver.
           iApply (ec_eq with "[$]").
           field_simplify_eq ; try real_solver. nify_r. nat_solver. }
      iIntros "#Hinv".
      rel_arrow_val ; lrintro "msg"...
      iApply (refines_na_inv with "[$Hinv]"); [done|].
      iIntros "(> (%q & %M & ε & counter & counter' & mapref & %dom_q & %dom_range) & Hclose)".
      case_bool_decide as Hm.
      - rel_load_l ; rel_load_r...
        rewrite /rf_rand_cipher.
        rewrite -bool_decide_and.
        case_bool_decide as Hq.
        + rel_load_l ; rel_load_r... rel_store_l ; rel_store_r...
          assert (Z.to_nat msg < S Message) as Hmsg by lia.
          pose proof nat_to_fin_list _ (elements(dom M)) dom_range as [l' Hl'].
          rel_apply (refines_couple_couple_avoid _ l').
          { apply NoDup_fmap with fin_to_nat; [apply fin_to_nat_inj|].
            rewrite Hl'. apply NoDup_elements. }
          replace (length l') with q. 2: by erewrite <-fmap_length, Hl'.
          pose proof pos_INR_S (Input).
          rewrite split_credit_step.
          iDestruct (ec_split with "[$]") as "[ε ε']".
          1,2: qify_r ; zify_q ; nia.
          iFrame.
          iIntros (r_in) "!> %r_fresh"...
          rel_apply_r (refines_get_r with "[-mapref] [$mapref]").
          iIntros (?) "mapref #->"...
          assert ((M !! fin_to_nat r_in) = None) as ->.
          { apply not_elem_of_dom_1. rewrite -elem_of_elements -Hl'. intros K.
            by apply elem_of_list_fmap_2_inj in K ; [|apply fin_to_nat_inj]. }
          simpl...
          unshelve rel_apply (refines_couple_UU _ (f_inv (xor_sem (Z.to_nat msg)))).
          3: apply _.
          { apply xor_bij. }
          { split.
            - intros ?? H'.
              apply (f_equal (xor_sem (Z.to_nat msg))) in H'.
              by rewrite !f_inv_cancel_r in H'.
            - intros y. exists (xor_sem (Z.to_nat msg) y).
              apply f_inv_cancel_l. apply xor_bij.
          }
          {
            apply fin.f_inv_restr; auto. by apply xor_dom.
          }
          iIntros (y) "!> %"...
          rel_apply_r (refines_set_r with "[-mapref] [$mapref]").
          iIntros "mapref"...
          rel_bind_r (xor _ _).
          rel_apply_r xor_correct_r; [lia | lia | |].
          { apply fin.f_inv_restr; auto. 2: lia. by apply xor_dom. }
          iApply (refines_na_close with "[-]").
          iFrame. iSplitL...
          2: { rel_vals. by erewrite f_inv_cancel_r. }
          iExists (q+1).
          nify_r.
          replace (Z.of_nat q + 1)%Z with (Z.of_nat (q+1)) by lia.
          iFrame.
          iPureIntro; split.
          * eapply map_insert_fresh_size ; eauto.
          * intros x. rewrite elem_of_elements. set_unfold.
            intros [|]; last naive_solver. subst. apply fin_to_nat_lt.
        + iApply (refines_na_close with "[-]").
          iFrame ; iSplit... 1: done. rel_vals.
      - rel_load_l ; rel_load_r... rewrite andb_false_r...
        iApply (refines_na_close with "[-]").
        iFrame ; iSplit... 1: done. rel_vals.
    Qed.


  End proofs.


  Lemma rf_CPA_ARC `{approxisRGpreS Σ} `{forall foo, @XOR_spec Σ foo _ _ xor_struct} σ σ' (Q : nat) :
    ARcoupl
      (lim_exec ((CPA #true adv rf_scheme #Q), σ))
      (lim_exec ((CPA #false adv rf_scheme #Q), σ'))
      (=)
      ((Q-1) * Q / (2 * S Input)).
  Proof.
    unshelve eapply approximates_coupling ; eauto.
    - exact (fun _ => lrel_bool).
    - qify_r ; zify_q ; nia.
    - by iIntros (???) "#(%b&->&->)".
    - iIntros ; iApply rf_is_CPA ; auto.
  Qed.

  Lemma rf_CPA_ARC' Σ `{approxisRGpreS Σ} `{forall foo, @XOR_spec Σ foo _ _ xor_struct} σ σ' (Q : nat) :
    ARcoupl
      (lim_exec ((CPA #false adv rf_scheme #Q), σ))
      (lim_exec ((CPA #true adv rf_scheme #Q), σ'))
      (=)
      ((Q-1) * Q / (2 * S Input)).
  Proof.
    unshelve eapply approximates_coupling ; eauto.
    - exact (fun _ => lrel_bool).
    - qify_r ; zify_q ; nia.
    - by iIntros (???) "#(%b&->&->)".
    - by iIntros ; iApply rf_is_CPA'.
  Qed.

  Corollary CPA_bound_1 Σ `{approxisRGpreS Σ} `{forall foo, @XOR_spec Σ foo _ _ xor_struct} σ σ' (Q : nat) :
    (((lim_exec ((CPA #true adv rf_scheme #Q), σ)) #true)
     <=
       ((lim_exec ((CPA #false adv rf_scheme #Q), σ')) #true) + ((Q-1) * Q / (2 * S Input)))%R.
  Proof.
    apply ARcoupl_eq_elim.
    by eapply rf_CPA_ARC.
  Qed.

  Corollary CPA_bound_2 Σ `{approxisRGpreS Σ} `{forall foo, @XOR_spec Σ foo _ _ xor_struct} σ σ' (Q : nat) :
    (((lim_exec ((CPA #false adv rf_scheme #Q), σ)) #true)
     <=
       ((lim_exec ((CPA #true adv rf_scheme #Q), σ')) #true) + ((Q-1) * Q / (2 * S Input)))%R.
  Proof.
    apply ARcoupl_eq_elim.
    by eapply rf_CPA_ARC'.
  Qed.

  Lemma CPA_bound Σ `{approxisRGpreS Σ} `{forall foo, @XOR_spec Σ foo _ _ xor_struct} σ σ' (Q : nat) :
    (Rabs (((lim_exec ((CPA #true adv rf_scheme #Q), σ)) #true) -
           ((lim_exec ((CPA #false adv rf_scheme #Q), σ')) #true)) <= ((Q-1) * Q / (2 * S Input)))%R.
  Proof.
    apply Rabs_le.
    pose proof CPA_bound_1 Σ σ σ' Q.
    pose proof CPA_bound_2 Σ σ' σ Q.
    split; lra.
  Qed.

End defs.

Section implementation.
  (* Definition bit:=64. *)
  Variable bit : nat.
  Variable Q : nat.
  Variable adv : val.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).

  Definition Output' := xor.Output' bit.
  Definition Input' := xor.Output' bit.
  Definition Key' := xor.Output' bit.

  #[local] Instance XOR_mod : @xor.XOR Output' Output' := xor.XOR_mod bit.
  #[local] Instance XOR_spec_mod `{!approxisRGS Σ} : @xor.XOR_spec _ _ _ _ XOR_mod := xor.XOR_spec_mod bit.


  Lemma CPA_bound_realistic σ σ' :
    (Rabs (((lim_exec ((CPA #true adv (rf_scheme Key' Input' Output' _) #Q), σ)) #true) -
             ((lim_exec ((CPA #false adv (rf_scheme Key' Input' Output' _) #Q), σ')) #true)) <= ((Q-1) * Q / (2 * S Input')))%R.
  Proof.
    unshelve epose proof CPA_bound Key' Input' Output' _ adv _ _ σ σ' Q as H.
    - apply _.
    - assumption.
    - apply approxisRΣ.
    - apply subG_approxisRGPreS. apply subG_refl.
    - intros. apply _.
    - done.
  Qed.

End implementation.
