(* CPA security of a PRF based symmetric encryption scheme. *)
From clutch Require Import lib.flip.
From clutch.paris Require Import paris map list.
Set Default Proof Using "Type*".

Section defs.

  (* symmetric encryption scheme = { keygen : unit -> key ; enc : key -> message -> cipher } *)

  (* prf : Key -> Input -> Output *)
  (* xor : 2^n -> 2^n -> 2^n *)
  (* The scheme computes the ciphertext as *)
  (* let r = rand_input () in (r, (xor (prf key r) msg)) *)
  (* hence for the sake of the scheme, Output = Message and Cipher = Input * Output. *)

  Variable Key : nat.
  Variable Input : nat.
  Variable Output : nat.
  Let Message := Output.
  Let Cipher := Input * Output.

  (* Let rand_cipher := (λ:<>, rand #Cipher)%E. *)
  Let keygen scheme : expr := Fst scheme.
  Let enc scheme : expr := Fst (Snd scheme).
  Let rand_cipher scheme : expr := Snd (Snd scheme).

  Local Opaque INR.

  Definition q_calls : val :=
    λ:"Q" "f" "g",
      let: "counter" := ref #0 in
      λ:"x", if: (BinOp AndOp (! "counter" < "Q") ("x" < #Message))
             then ("counter" <- !"counter" + #1 ;; "f" "x")
             else "g" "x".

  Definition CPA : val :=
    λ:"b" "adv" "scheme" "Q",
      let: "rr_key_b" :=
        let: "key" := keygen "scheme" #() in
        (* let: "enc_key" := enc "scheme" "key" in *)
        if: "b" then
          (* "enc_key" *)
          enc "scheme" "key"
        else
          rand_cipher "scheme" in
      let: "oracle" := q_calls "Q" "rr_key_b" (rand_cipher "scheme") in
      let: "b'" := "adv" "oracle" in
      "b'".

  Variable xor : val.
  (* We probably need to assume that forall x, Bij (xor x). *)
  Variable (xor_sem : fin (S Message) -> fin (S Output) -> fin (S Output)).
  Variable H_xor : forall x, Bij (xor_sem x).

  Definition prf_enc : val :=
    λ:"prf" "key",
      let: "prf_key" := "prf" "key" in
      λ: "msg",
        let: "r" := rand #Input in
        let: "z" := "prf_key" "r" in
        ("r", xor "msg" "z").

  Section security_defs.
    (* Tentative sketch of security definitions as we'd write them at the toplevel. *)
    (* Arguments to the game (adversary, scheme, ...) are omitted. *)

    Variable ε : R.

    (* book statement *)
    Check
      (let φ := (λ v, bool_decide (v = #true)) in
       forall σ, prob (lim_exec ((CPA #true)%E, σ)) φ = prob (lim_exec ((CPA #false)%E, σ)) φ + ε)%R.

    (* what we get from ARcoupl_eq_elim *)
    Check
      (forall σ, (lim_exec ((CPA #true)%E, σ)) #true = (lim_exec ((CPA #false)%E, σ)) #true + ε)%R.

    (* what we get from adequacy *)
    Check
      (forall σ,
          ARcoupl (lim_exec ((CPA #true)%E, σ)) (lim_exec ((CPA #false)%E, σ)) (=) ε).

    (* the refinement we might prove for some ε *)
    Check
      (⊢  ⤇ (CPA #true) -∗ ↯ ε -∗ WP (CPA #false) {{ v, ∃ v', ⤇ Val v' ∗ ⌜v = v'⌝ }} ).
  End security_defs.

  (* An idealised random function family. *)
  Definition random_function : val :=
    λ: "_key",
      (* Create a reference to a functional map *)
      let: "mapref" := init_map #() in
      λ: "x",
        match: get "mapref" "x" with
        | SOME "y" => "y"
        | NONE =>
            let: "y" := (rand #Output) in
            set "mapref" "x" "y";;
            "y"
        end.

  Definition rf_keygen : val := λ:<>, rand #Key.
  Definition rf_enc : expr := prf_enc random_function.
  Definition rf_rand_cipher : val := λ:<>, let:"i" := rand #Input in let:"o" := rand #Output in ("i", "o").
  Definition rf_scheme : expr := (rf_keygen, (rf_enc, rf_rand_cipher)).

  Definition CPA_rf : val := λ:"b" "adv", CPA "b" "adv" rf_scheme.

  Definition TMessage := TInt.
  Definition TKey := TInt.
  Definition TInput := TInt.
  Definition TOutput := TInt.
  Definition TCipher := (TInput * TMessage)%ty.
  Definition TAdv := ((TMessage → TCipher) → TBool)%ty.
  Variable adv : val.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).


  Section proofs.
    Context `{!parisRGS Σ}.

    Lemma refines_init_map_l E K e A :
      (∀ l : loc, map_list l ∅ -∗ REL (fill K (of_val #l)) << e @ E : A)
      -∗ REL (fill K (init_map #())) << e @ E : A.
    Admitted.

    Lemma refines_init_map_r E K e A :
      (∀ l : loc, map_list l ∅ -∗ REL e << (fill K (of_val #l)) @ E : A)
      -∗ REL e << (fill K (init_map #())) @ E : A.
    Admitted.

    Lemma refines_get_l E K lm m (n: nat) e A :
      (∀ res, map_list lm m -∗
              ⌜ res = opt_to_val (m !! n) ⌝
              -∗ REL (fill K (of_val res)) << e @ E : A)
      -∗ map_list lm m -∗ REL (fill K (get #lm #n)) << e @ E : A.
    Admitted.

    Lemma refines_set_l E K lm m (v : val) (n: nat) e A :
      (map_list lm (<[n := v]>m)
       -∗ REL (fill K (of_val #())) << e @ E : A)
      -∗ map_list lm m -∗ REL (fill K (set #lm #n v)) << e @ E : A.
    Admitted.

    Lemma foobar E K (x : Z) (y : fin (S Message)) (Hx : ((Z.to_nat x) < S Message)) e A :
      (REL (fill K (of_val #(xor_sem (nat_to_fin Hx) (y)))) << e @ E : A)
      -∗ REL (fill K (xor #x #y)) << e @ E : A.
    Admitted.

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
    ↯ (Q * Q / (2 * Input)) ⊢ (REL (CPA #true adv rf_scheme #Q) << (CPA #false adv rf_scheme #Q) : lrel_bool).
  Proof with (rel_pures_l ; rel_pures_r).
    iIntros "ε".
    rel_pures_l.
    rewrite /CPA.
    rewrite /rf_scheme/rf_enc/prf_enc.
    idtac...
    rewrite /rf_keygen...
    rel_apply (refines_couple_UU Key).
    iIntros (key) "!>"...
    rewrite /random_function...
    rel_apply_l refines_init_map_l.
    iIntros (mapref) "mapref"...
    rel_bind_l (q_calls _ _ _)%E.
    rel_bind_r (q_calls _ _ _)%E.
    unshelve iApply (refines_bind with "[-] []").
    1:{ exact (interp (TMessage → TCipher) []). }
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
      replace (lrel_arr (lrel_arr lrel_int (lrel_prod lrel_int lrel_int))
                 (interp TBool nil)) with
        (interp TAdv []) by easy.
      iApply refines_typed.
      assumption.
    }

    rewrite /q_calls...
    rel_alloc_l counter as "counter"... rel_alloc_r counter' as "counter'"...

    iApply (refines_na_alloc
              (∃ (q : nat) M,
                  ↯ ((Q-q) * (Q-q) / (2 * Input))
                  ∗ counter ↦ #q
                  ∗ counter' ↦ₛ #q
                  ∗ map_list mapref M
                  ∗ ⌜ size (dom M) = q ⌝
                  ∗ ⌜ ∀ x, x ∈ elements (dom M) -> (x < S Input)%nat ⌝
              )%I
              (nroot.@"cpa")); iFrame.
    iSplitL.
    1: { iExists 0. rewrite Rminus_0_r. iFrame. iPureIntro; set_solver.
    }
    iIntros "#Hinv".
    rel_arrow_val.
    iIntros (??) "#(%msg&->&->)" ; rel_pures_l ; rel_pures_r.
    iApply (refines_na_inv with "[$Hinv]"); [done|].
    iIntros "(> (%q & %M & ε & counter & counter' & mapref & %dom_q & %dom_range) & Hclose)".
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
      iDestruct (ec_weaken _ (q/S Input+((Q - (q+1)%nat) * (Q - (q+1)%nat)/ (2 * Input))) with "[$]") as "ε".
      { admit. }
      iDestruct (ec_split with "[$]") as "[ε ε']".
      { admit. }
      { admit. }
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
      rel_apply_l foobar.
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
      iModIntro. repeat iSplit ; iPureIntro ; eauto. 
    + iApply (refines_na_close with "[-]").
      iFrame.
      iSplit.
      { done. }
      rel_apply (refines_couple_UU Input).
      iIntros (?) "!>"...
      rel_apply (refines_couple_UU Output id).
      iIntros (?) "!>"...
      rel_values => //.
      iModIntro.
      iExists _,_,_,_.
      repeat iSplit ; try done.
      all: iExists _ ; done.
    - rel_load_l ; rel_load_r...
      rewrite /rf_rand_cipher.
      rewrite andb_false_r...
      iApply (refines_na_close with "[-]").
      iFrame.
      iSplit.
      { done. }
      rel_apply (refines_couple_UU Input).
      iIntros (?) "!>"...
      rel_apply (refines_couple_UU Output id).
      iIntros (?) "!>"...
      rel_values => //.
      iModIntro.
      iExists _,_,_,_.
      repeat iSplit ; try done.
      all: iExists _ ; done.
  Admitted.

End proofs.

Lemma rf_CPA_ARC Σ `{parisRGpreS Σ} σ σ' (Q : nat) :
  ARcoupl
    (lim_exec ((CPA #true adv rf_scheme #Q), σ))
    (lim_exec ((CPA #false adv rf_scheme #Q), σ'))
    (=)
    (Q * Q / (2 * Input)).
Proof.
  unshelve eapply approximates_coupling ; eauto.
  1: exact (fun _ => lrel_bool).
  { repeat apply Rmult_le_pos; try apply pos_INR.
    rewrite -Rdiv_1_l.
    pose proof Rdiv_INR_ge_0 Input.
    cut ((0 <= (2*1) / (2 * INR Input)))%R; first lra.
    rewrite Rmult_comm.
    rewrite Rmult_div_swap.
    rewrite (Rmult_comm 2%R).
    rewrite Rdiv_mult_distr.
    lra.
  }
  1: by iIntros (???) "#(%b&->&->)".
  iIntros. by iApply rf_is_CPA.
Qed.

Corollary foo Σ `{parisRGpreS Σ} σ σ' (Q : nat) :
  (((lim_exec ((CPA #true adv rf_scheme #Q), σ)) #true)
    <=
      ((lim_exec ((CPA #false adv rf_scheme #Q), σ')) #true) + (Q * Q / (2 * Input)))%R.
Proof.
  apply ARcoupl_eq_elim.
  by eapply rf_CPA_ARC.
Qed.

End defs. 
