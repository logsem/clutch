From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.approxis Require Import map reltac2 approxis option.
From clutch.approxis.examples Require Import
  security_aux option symmetric_init wmf_protocol linked_list
  pubkey advantage_laws iterable_expression intptxt_ideal_dec.
From mathcomp Require Import ssrbool.
Set Default Proof Using "All".
Import map.

Section defs.
     
  Context `{!approxisRGS Σ}.

  (* security parameter *)
  Variable η : nat.

  Let N := 2^η - 1.

  Variable Key Output : nat.

  (* ASSUMPTION ON THE ENCRYPTION SCHEME *)
  Definition lrel_id : lrel Σ := lrel_nat.

  Definition lrel_rand : lrel Σ := lrel_int_bounded 0 N.
  Definition lrel_msg : lrel Σ := (lrel_id * lrel_rand)%lrel.
  Variable lrel_cipher : lrel Σ.
  Variable lrel_key : lrel Σ.

  Definition lrel_protocol : lrel Σ :=
    lrel_rand →
      (() + (lrel_id * lrel_cipher)) *
      ((lrel_id * lrel_cipher) → () + lrel_cipher) *
      (lrel_cipher → () + ()).

  Variable senc : list loc → val.
  Variable sdec : list loc → val.

  Variable P0l : list loc → iProp Σ.
  Variable P0r : list loc → iProp Σ.

  Variable Pl : list loc → iProp Σ.
  Variable Pr : list loc → iProp Σ.
  Variable Plr : list loc → list loc → iProp Σ.

  Definition P0_P_l_prop := ∀ lls, P0l lls -∗ Pl lls.
  Definition P0_P_r_prop := ∀ rls, P0r rls -∗ Pr rls.
  Definition P0lr_Plr_prop := ∀ lls rls, P0l lls -∗ P0r rls -∗ Plr lls rls.
  Hypothesis P0_P_l : P0_P_l_prop.
  Hypothesis P0_P_r : P0_P_r_prop.
  Hypothesis P0lr_Plr : P0lr_Plr_prop.
  
  #[local] Instance sym_params : SYM_init_params := @sym_params_wmf η Key Output.

  Context `{sym : !SYM_init}.

  Let init_scheme : expr → expr := init_scheme η Key Output.

  Definition refines_init_scheme_l_prop := forall K e E A,
    (∀ lls,
      P0l lls -∗
      refines E
        (fill K (senc lls, sdec lls))
        e A)
    ⊢ refines E
        (fill K (get_enc_scheme sym_scheme #()))
        e A.

  Definition refines_init_scheme_r_prop := forall K e E A,
    (∀ rls,
      P0r rls -∗
      refines E
        e
        (fill K (senc rls, sdec rls))
        A)
    ⊢ refines E
        e
        (fill K (get_enc_scheme sym_scheme #()))
        A.

  Hypothesis refines_init_scheme_l : refines_init_scheme_l_prop.

  Hypothesis refines_init_scheme_r : refines_init_scheme_r_prop.

  Definition refines_sym_keygen_couple_prop := forall K K' E A,
    (∀ key key',
      (lrel_car lrel_key) key key' -∗
        refines E
          (fill K  (Val key))
          (fill K' (Val key'))
          A)
    ⊢ refines E
        (fill K  (keygen #()))
        (fill K' (keygen #()))
        A.
  Hypothesis refines_sym_keygen_couple : refines_sym_keygen_couple_prop.

  Definition refines_keygen_l_prop := forall K e E A,
    (∀ key,
      left_lrel lrel_key key -∗
      refines E
        (fill K (Val key))
        e A)
    ⊢ refines E
        (fill K (symmetric_init.keygen #()))
        e A.
  Definition refines_keygen_r_prop := forall K e E A,
    (∀ key,
      right_lrel lrel_key key -∗
      refines E
        e
        (fill K (Val key))
        A)
    ⊢ refines E
        e
        (fill K (symmetric_init.keygen #()))
        A.
  Hypothesis refines_keygen_l : refines_keygen_l_prop.
  Hypothesis refines_keygen_r : refines_keygen_r_prop.

  Definition sym_is_cipher_l {lls : list loc} (msg : val) (c k : val) : iProp Σ :=
    ∀ K e E A,
      (Pl lls -∗
        refines E
        (fill K (Val msg))
        e A)
    -∗ refines E
        (fill K (sdec lls k c))
        e A.
  
  Definition sym_is_cipher_r {rls : list loc} (msg : val) (c k : val) : iProp Σ :=
    ∀ K e E A,
      (Pr rls -∗
        refines E
        e (fill K (Val msg)) A)
    -∗ refines E
        e (fill K (sdec rls k c)) A.

  Definition refines_senc_l_prop :=
    ∀ (lls : list loc) (msg : val) (k : val) K e' E A,
    left_lrel lrel_key k ∗ left_lrel lrel_msg msg ∗ Pl lls ⊢
      ((∀ (c : val),
        left_lrel lrel_cipher c
      -∗ @sym_is_cipher_l lls msg c k
      -∗ refines E
          (fill K (Val c))
          e'
          A)
    -∗ refines E
        (fill K (senc lls k msg))
        e'
        A).
  
  Definition refines_senc_r_prop :=
    ∀ (rls : list loc) (msg : val) (k : val) K e E A,
    right_lrel lrel_key k ∗ right_lrel lrel_msg msg ∗ Pr rls ⊢
      ((∀ (c' : val),
        right_lrel lrel_cipher c'
      -∗ @sym_is_cipher_r rls msg c' k
      -∗ refines E
          e
          (fill K (Val c'))
          A)
    -∗ refines E
        e
        (fill K (senc rls k msg))
        A).

  Hypothesis refines_senc_l : refines_senc_l_prop.

  Hypothesis refines_senc_r : refines_senc_r_prop.

  Section linked_list_instance.
    (* all messages encrypted in this protocol are of the form
      (an identifier, an integer ≤ N) *)

    Definition elem_eq : val :=
      λ: "x" "y", Fst "x" = Fst "y" `and` Snd "x" = Snd "y".
      
    Lemma refines_elem_eq_l : (refines_elem_eq_l_prop elem_eq
      (λ x, half_lrel lrel_msg x)).
    Proof with rel_pures_l.
      rewrite /refines_elem_eq_l_prop.
      iIntros (x y).
      iIntros (K e E A).
      rewrite /elem_eq...
      iIntros "[[Hcarx | Hcarx] [[Hcary | Hcary] Hrel]]";
      rewrite /left_lrel/right_lrel/lrel_msg;
      iDestruct "Hcarx" as (v_tmp x1 x1' x2 x2')
      "[%eqx [%eqx' [[%lx [%eqx1 %eqx1']] [%lx' [%eqx2 [%eqx2' _]]]]]]";
      iDestruct "Hcary" as (v_tmp' y1 y1' y2 y2')
      "[%eqy [%eqy' [[%ly [%eqy1 %eqy1']] [%ly' [%eqy2 [%eqy2' _]]]]]]"; subst;
      simpl; rel_pures_l;
      destruct (bool_decide (#lx = #ly));
      destruct (bool_decide (#lx' = #ly')); rel_apply "Hrel".
    Qed.

    Lemma refines_elem_eq_r : (refines_elem_eq_r_prop elem_eq
      (λ x, half_lrel lrel_msg x)).
    Proof with rel_pures_r.
      rewrite /refines_elem_eq_l_prop.
      iIntros (x y).
      iIntros (K e E A).
      rewrite /elem_eq...
      iIntros "[[Hcarx | Hcarx] [[Hcary | Hcary] Hrel]]";
      rewrite /left_lrel/right_lrel/lrel_msg;
      iDestruct "Hcarx" as (v_tmp x1 x1' x2 x2')
      "[%eqx [%eqx' [[%lx [%eqx1 %eqx1']] [%lx' [%eqx2 [%eqx2' _]]]]]]";
      iDestruct "Hcary" as (v_tmp' y1 y1' y2 y2')
      "[%eqy [%eqy' [[%ly [%eqy1 %eqy1']] [%ly' [%eqy2 [%eqy2' _]]]]]]"; subst;
      simpl; rel_pures_r;
      destruct (bool_decide (#lx = #ly));
      destruct (bool_decide (#lx' = #ly')); rel_apply "Hrel".
    Qed.

  End linked_list_instance.

  Variable is_ciphertext : val.
  (* all messages encrypted in this protocol are of the form
    (an identifier, an integer ≤ N) *)
  Definition is_plaintext : val :=
    λ: "x", #0 ≤ (Fst "x") `and` #0 ≤ (Snd "x") `and` (Snd "x") ≤ #N.
  Variable is_key : val.

  Lemma refines_is_plaintext_l : refines_is_plaintext_l_prop lrel_msg is_plaintext.
  Proof with rel_pures_l.
    rewrite /refines_is_plaintext_l_prop.
    iIntros (c K e E A)
      "[%c' [%x1 [%x2 [%x1' [%x2' [%Heqc [%Heqc' Hcompx]]]]]]] Hrel".
    iDestruct "Hcompx" as
      "[[%id [%eqx1 %eqx1']] [%msg [%eqx2 [%eqx2' [%Hbound1 %Hbound2]]]]]"; subst.
    eapply bool_decide_eq_true in Hbound1;
    eapply bool_decide_eq_true in Hbound2.
    assert (Hboundid : bool_decide (0 ≤ id)%Z = true).
    { apply bool_decide_eq_true. lia. }
    rewrite /is_plaintext...
    rewrite Hbound1 Hbound2 Hboundid...
    rel_apply "Hrel".
    Unshelve.
    all: apply Z_le_dec.
  Qed.

  Hypothesis refines_is_ciphertext_l :
    @refines_is_ciphertext_l_prop _ _ lrel_cipher is_ciphertext.
  Hypothesis refines_is_ciphertext_r :
    @refines_is_ciphertext_r_prop _ _ lrel_cipher is_ciphertext.
  Hypothesis refines_is_plaintext_r :
    @refines_is_plaintext_r_prop _ _ lrel_msg is_plaintext.
  Hypothesis refines_is_plaintext_l :
    @refines_is_plaintext_l_prop _ _ lrel_msg is_plaintext.
  Hypothesis refines_is_key_l :
    @refines_is_key_l_prop _ _ lrel_key is_key.
  Hypothesis refines_is_key_r :
    @refines_is_key_r_prop _ _ lrel_key is_key.

  Section logrel.

    (*
      A → S : (A, B, {n}_ka)
      S → B : {A, n}_kb
    *)
    Definition init_id_dis : val :=
      λ: <>,
        let: "A" := #0 in
        let: "B" := #1 in
        let: "Bd" := #2 in
        ("A", "B", "Bd").

    Definition a_to_s_once : val :=
      λ: "A" "B" "b" "senc" "ka", (* parameters of the protocol *)
        let: "run" := ref #true in
        λ: "r_adv", (* attacker provided random *)
          if: ! "run" then
          "run" <- #false;;
            SOME
              (if: "b" then
                (* #0 is dummy so senc always encrypt pairs
                  and thus stay semantically typed *)
                ("A", ("B", "senc" "ka" (#0, rand #N)))
              else
                ("A", ("B", "senc" "ka" (#0, "r_adv"))))
          else
            NONE.

    (* TODO when this definition is stable, copy paste in symmetric_init
      and recompile *)
    Definition s_to_b_maybe_d_once : val :=
      λ: "A" "B" "Bd" "b" "senc" "sdec" "ka" "kb" "kbd", (* parameters of the protocol *)
        let: "run" := ref #true in
        λ: "input",
          if: ! "run" then
            "run" <- #false;;
            let: "nonce" := "sdec" "ka" (Snd "input") in
            let: "nonce" := Snd "nonce" in
            let: "sender" := Fst "input" in
            let: "dest" := Snd "sender" in
            let: "sender" := Fst "sender" in
            if: "sender" = "A" `and` "dest" = "B" then
              SOME ("senc" "kb" ("sender", "nonce"))
            else if: "sender" = "A" `and` "dest" = "Bd" then
              SOME ("senc" "kbd" ("sender", "nonce"))
            else NONE
          else
            NONE.

    Definition bd_recv : val :=
      λ: "A" "sdec" "kbd",
        let: "run" := ref #true in
        λ: "input",
          if: ! "run" then
            "run" <- #false;;
            let: "decr" := "sdec" "kbd" "input" in
            let: "sender" := Fst "decr" in
            let: "nonce" := Snd "decr" in
            if: "sender" = "A" then SOME "nonce" else NONE
          else NONE.

    Definition wmf_once_unsafe : expr :=
          let: "A" := init_id_dis #() in
          let: "Bd" := Snd "A" in
          let: "A" := Fst "A" in
          let: "B" := Snd "A" in
          let: "A" := Fst "A" in
          λ: "b" "enc_scheme",
            let: "ka" := keygen #() in
            let: "kb" := keygen #() in
            (* a key for dishonest agent Bd, available to the attacker: *)
            let: "kbd" := keygen #() in
            let: "a_to_s" := a_to_s_once "A" "B" "b"
                (symmetric_init.get_enc "enc_scheme") "ka" in
            let: "s_to_b" := s_to_b_maybe_d_once "A" "B" "Bd" "b"
                (symmetric_init.get_enc "enc_scheme")
                (symmetric_init.get_dec "enc_scheme")
                "ka" "kb" "kbd" in
            let: "b_recv" := b_recv_once "A" "B" "b" "kb" in
            let: "bd_recv" := bd_recv "A"
              (symmetric_init.get_dec "enc_scheme") "kbd" in
            (("kbd", "Bd"),
              ("a_to_s",
              "s_to_b",
              "b_recv",
              "bd_recv")).

    Definition attack : expr :=
      let: "run" := ref #true in
      λ: "b",
        if: ! "run" then
          "run" <- #false;;
          let: "radv" := rand #N in
          let: "protocol" := wmf_once_unsafe "b"
            (symmetric_init.get_enc_scheme sym_scheme #()) in
          let: "kbd" := Fst "protocol" in
          let: "Bd" := Snd "kbd" in

          let: "kbd" := Fst "kbd" in
          let: "protocol" := Snd "protocol" in
          let: "bd_recv" := Snd "protocol" in
          let: "protocol" := Fst "protocol" in
          let: "b_recv" := Snd "protocol" in
          let: "protocol" := Fst "protocol" in
          let: "s_to_b" := Snd "protocol" in
          let: "a_to_s" := Fst "protocol" in

          let:m "msg1" := "a_to_s" "radv" in
          let: "Atag" := Fst "msg1" in
          let: "msg1" := Snd "msg1" in
          (* we throw away the tag `B` *)
          let: "nonce_encrypted" := Snd "msg1" in
          let:m "msg2" := "s_to_b" ("Atag", "Bd", "nonce_encrypted") in
          let:m "nonce" := "bd_recv" "msg2" in
          "nonce" ≠ "radv"
        else "b".
    
    (* Maybe proving the attack is more of a unary property *)

    Lemma attack__rand_id :
      ↯ (1/(S N)) ⊢ refines top attack (λ: "b", rand #N;; "b") (lrel_bool → lrel_bool).
    Proof with rel_pures_l; rel_pures_r. iIntros "Herr".
      rewrite /attack. rel_alloc_l run as "Hrun"...
      rel_apply (refines_na_alloc (run ↦ #true ∗ ↯ (1 / (S N)) ∨ run ↦ #false)
        (nroot.@"attack_true")).
      iSplitL.
      { iLeft; iFrame. }
      iIntros "#Inv".
      rel_arrow_val. iIntros (b1 b2) "[%b [%eq1 %eq2]]"; subst...
      rel_apply refines_na_inv. iSplit; first iAssumption.
      iIntros "[[[Hrun Herr] | Hrun] Hclose]"; rel_load_l...
      2: {
        rel_apply refines_randU_r.
        iIntros (n_dummy _)... rel_apply refines_na_close; iFrame.
        rel_vals.
      }
      rel_store_l...
      rel_apply refines_randU_l. iIntros (radv Hradvbound)...
      rewrite /init_id_dis...
      rel_apply refines_init_scheme_l.
      iIntros (lls) "HP"...
      rel_apply refines_keygen_l.
      iIntros (ka) "#Hrelka"...
      rel_apply refines_keygen_l.
      iIntros (kb) "#Hrelkb"...
      rel_apply refines_keygen_l.
      iIntros (kbd) "#Hrelkbd"...
      rewrite /a_to_s_once/wmf_protocol.a_to_s_once/get_enc...
      rel_alloc_l run1 as "Hrun1"...
      rewrite /s_to_b_maybe_d_once/get_dec...
      rel_alloc_l run2 as "Hrun2"...
      rewrite /b_recv_once...
      rel_alloc_l run3 as "Hrun3"...
      rewrite /bd_recv...
      rel_alloc_l run4 as "Hrun4"...
      rel_load_l...
      rel_store_l...
      destruct b...
      - rewrite /N.
        epose proof (nat_to_fin_list N [radv] _) as [l_fin Hlst].
        Unshelve. 2: {
          intros x H; rewrite elem_of_list_singleton in H; subst. lia.
        }
        rel_apply (refines_couple_couple_avoid N l_fin N).
        { apply (NoDup_fmap fin_to_nat). rewrite Hlst.
          constructor; last constructor. apply not_elem_of_nil. }
        erewrite <-fmap_length, Hlst. simpl.
        iSplitL "Herr".
        { rewrite /N. iAssumption. }
        iModIntro.
        iIntros (nonce Hnotin)...
        assert (Hnonceradv : fin_to_nat nonce ≠ radv).
        {
          intro eq.
          apply Hnotin.
          eapply elem_of_list_fmap_2_inj; first apply fin_to_nat_inj.
          rewrite Hlst. rewrite eq. apply elem_of_list_singleton. done.
        }
        rel_apply refines_na_close. iFrame.
        iClear "Inv".
        rel_apply (refines_senc_l with "[HP]").
        {
          iSplitR; first iAssumption.
          iSplitR.
          {
            iExists (#0, #nonce)%V, _, _, _, _.
            repeat iSplit.
            1, 2: done.
            { iExists 0; done. }
            iExists nonce; iPureIntro; repeat split; try lia.
            apply inj_le.
            apply fin.fin_to_nat_le.
          }
          iApply P0_P_l. iAssumption.
        }
        iIntros (c) "#Hrelcipher Hcipher"...
        rel_load_l; rel_store_l...
        rel_apply "Hcipher".
        iIntros "HP"...
        rel_apply (refines_senc_l with "[HP]").
        {
          iSplitR; first iAssumption.
          iSplitR.
          {
            iExists (#0, #nonce)%V, _, _, _, _.
            repeat iSplit.
            1, 2: done.
            { iExists 0; done. }
            iExists nonce; iPureIntro; repeat split; try lia.
            apply inj_le.
            apply fin.fin_to_nat_le.
          }
          iAssumption.
        }
        iClear "Hrelcipher". clear c.
        iIntros (c) "#Hrelcipher Hcipher"...
        rel_load_l.
        rel_store_l...
        rel_apply "Hcipher".
        iIntros "HP"...
        destruct (bool_decide (#nonce = #radv)) eqn:eqnonceradv_check.
        { exfalso. apply bool_decide_eq_true in eqnonceradv_check.
          apply Hnonceradv. injection eqnonceradv_check. intro H.
          apply Nat2Z.inj. assumption. }
        rel_vals.
      - iClear "Herr".
        rel_apply refines_na_close; iFrame. iClear "Inv".
        rel_apply (refines_senc_l with "[HP]").
        {
          iSplitR; first iAssumption.
          iSplitR.
          {
            iExists (#0, #radv)%V, _, _, _, _.
            repeat iSplit.
            1, 2: done.
            { iExists 0; done. }
            iExists radv; iPureIntro; repeat split; try lia.
          }
          iApply P0_P_l. iAssumption.
        }
        iIntros (c) "#Hrelcipher Hcipher"...
        rel_load_l; rel_store_l...
        rel_apply "Hcipher".
        iIntros "HP"...
        rel_apply (refines_senc_l with "[HP]").
        {
          iSplitR; first iAssumption.
          iSplitR.
          {
            iExists (#0, #radv)%V, _, _, _, _.
            repeat iSplit.
            1, 2: done.
            { iExists 0; done. }
            iExists radv; iPureIntro; repeat split; try lia.
          }
          iAssumption.
        }
        iClear "Hrelcipher". clear c.
        iIntros (c) "#Hrelcipher Hcipher"...
        rel_load_l.
        rel_store_l...
        rel_apply "Hcipher".
        iIntros "HP"...
        rel_apply refines_randU_r.
        iIntros (n _)...
        rel_vals.
        destruct (bool_decide (#radv = #radv)) eqn:eqradv_check.
        2: { exfalso. apply bool_decide_eq_false in eqradv_check.
          apply eqradv_check. reflexivity. }
        simpl. iExists false. done.
  Qed.

    Lemma rand_id__attack :
      ↯ (1/(S N)) ⊢ refines top (λ: "b", rand #N;; "b") attack (lrel_bool → lrel_bool).
    Proof with rel_pures_l; rel_pures_r. iIntros "Herr".
      rewrite /attack. rel_alloc_r run as "Hrun"...
      rel_apply (refines_na_alloc (run ↦ₛ #true ∗ ↯ (1 / (S N)) ∨ run ↦ₛ #false)
        (nroot.@"attack_true")).
      iSplitL.
      { iLeft; iFrame. }
      iIntros "#Inv".
      rel_arrow_val. iIntros (b1 b2) "[%b [%eq1 %eq2]]"; subst.
      rel_apply refines_na_inv. iSplit; first iAssumption.
      iIntros "[[[Hrun Herr] | Hrun] Hclose]"; rel_pure_l; rel_load_r...
      2: {
        rel_apply refines_randU_l.
        iIntros (n_dummy _)... rel_apply refines_na_close; iFrame.
        rel_vals.
      }
      rel_store_r...
      rel_apply refines_randU_r. iIntros (radv Hradvbound)...
      rewrite /init_id_dis...
      rel_apply refines_init_scheme_r.
      iIntros (rls) "HP"...
      rel_apply refines_keygen_r.
      iIntros (ka) "#Hrelka"...
      rel_apply refines_keygen_r.
      iIntros (kb) "#Hrelkb"...
      rel_apply refines_keygen_r.
      iIntros (kbd) "#Hrelkbd"...
      rewrite /a_to_s_once/wmf_protocol.a_to_s_once/get_enc...
      rel_alloc_r run1 as "Hrun1"...
      rewrite /s_to_b_maybe_d_once/get_dec...
      rel_alloc_r run2 as "Hrun2"...
      rewrite /b_recv_once...
      rel_alloc_r run3 as "Hrun3"...
      rewrite /bd_recv...
      rel_alloc_r run4 as "Hrun4"...
      rel_load_r...
      rel_store_r...
      destruct b...
      - rewrite /N.
        epose proof (nat_to_fin_list N [radv] _) as [l_fin Hlst].
        Unshelve. 2: {
          intros x H; rewrite elem_of_list_singleton in H; subst. lia.
        }
        rel_apply (refines_couple_couple_avoid N l_fin N).
        { apply (NoDup_fmap fin_to_nat). rewrite Hlst.
          constructor; last constructor. apply not_elem_of_nil. }
        erewrite <-fmap_length, Hlst. simpl.
        iSplitL "Herr".
        { rewrite /N. iAssumption. }
        iModIntro.
        iIntros (nonce Hnotin)...
        assert (Hnonceradv : fin_to_nat nonce ≠ radv).
        {
          intro eq.
          apply Hnotin.
          eapply elem_of_list_fmap_2_inj; first apply fin_to_nat_inj.
          rewrite Hlst. rewrite eq. apply elem_of_list_singleton. done.
        }
        rel_apply refines_na_close. iFrame.
        iClear "Inv".
        rel_apply (refines_senc_r with "[HP]").
        {
          iSplitR; first iAssumption.
          iSplitR.
          {
            iExists (#0, #nonce)%V, _, _, _, _.
            repeat iSplit.
            1, 2: done.
            { iExists 0; done. }
            iExists nonce; iPureIntro; repeat split; try lia.
            apply inj_le.
            apply fin.fin_to_nat_le.
          }
          iApply P0_P_r. iAssumption.
        }
        iIntros (c) "#Hrelcipher Hcipher"...
        rel_load_r; rel_store_r...
        rel_apply "Hcipher".
        iIntros "HP"...
        rel_apply (refines_senc_r with "[HP]").
        {
          iSplitR; first iAssumption.
          iSplitR.
          {
            iExists (#0, #nonce)%V, _, _, _, _.
            repeat iSplit.
            1, 2: done.
            { iExists 0; done. }
            iExists nonce; iPureIntro; repeat split; try lia.
            apply inj_le.
            apply fin.fin_to_nat_le.
          }
          iAssumption.
        }
        iClear "Hrelcipher". clear c.
        iIntros (c) "#Hrelcipher Hcipher"...
        rel_load_r.
        rel_store_r...
        rel_apply "Hcipher".
        iIntros "HP"...
        destruct (bool_decide (#nonce = #radv)) eqn:eqnonceradv_check.
        { exfalso. apply bool_decide_eq_true in eqnonceradv_check.
          apply Hnonceradv. injection eqnonceradv_check. intro H.
          apply Nat2Z.inj. assumption. }
        rel_vals.
      - iClear "Herr".
        rel_apply refines_na_close; iFrame. iClear "Inv".
        rel_apply (refines_senc_r with "[HP]").
        {
          iSplitR; first iAssumption.
          iSplitR.
          {
            iExists (#0, #radv)%V, _, _, _, _.
            repeat iSplit.
            1, 2: done.
            { iExists 0; done. }
            iExists radv; iPureIntro; repeat split; try lia.
          }
          iApply P0_P_r. iAssumption.
        }
        iIntros (c) "#Hrelcipher Hcipher"...
        rel_load_r; rel_store_r...
        rel_apply "Hcipher".
        iIntros "HP"...
        rel_apply (refines_senc_r with "[HP]").
        {
          iSplitR; first iAssumption.
          iSplitR.
          {
            iExists (#0, #radv)%V, _, _, _, _.
            repeat iSplit.
            1, 2: done.
            { iExists 0; done. }
            iExists radv; iPureIntro; repeat split; try lia.
          }
          iAssumption.
        }
        iClear "Hrelcipher". clear c.
        iIntros (c) "#Hrelcipher Hcipher"...
        rel_load_r.
        rel_store_r...
        rel_apply "Hcipher".
        iIntros "HP"...
        rel_apply refines_randU_l.
        iIntros (n _)...
        rel_vals.
        destruct (bool_decide (#radv = #radv)) eqn:eqradv_check.
        2: { exfalso. apply bool_decide_eq_false in eqradv_check.
          apply eqradv_check. reflexivity. }
        simpl. iExists false. done.
  Qed.

  Lemma rand_id__id :
    ⊢ refines top (λ: "b", rand #N;; "b")  (λ: "b", "b") (lrel_bool → lrel_bool).
  Proof with rel_pures_l; rel_pures_r.
    rel_arrow_val.
    iIntros (b1 b2) "[%b [%eq1 %eq2]]"; subst...
    rel_apply refines_randU_l.
    iIntros (n _)... rel_vals.
  Qed.

  Lemma id__rand_d :
    ⊢ refines top (λ: "b", "b") (λ: "b", rand #N;; "b") (lrel_bool → lrel_bool).
  Proof with rel_pures_l; rel_pures_r.
    rel_arrow_val.
    iIntros (b1 b2) "[%b [%eq1 %eq2]]"; subst...
    rel_apply refines_randU_r.
    iIntros (n _)... rel_vals.
  Qed.

  End logrel.

End defs.