From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.approxis Require Import map reltac2 approxis option.
From clutch.approxis.examples Require Import
  security_aux option symmetric_init wmf_protocol linked_list
  pubkey advantage_laws iterable_expression intptxt_ideal_dec.
From mathcomp Require Import ssrbool.
Set Default Proof Using "All".
Import map.

Ltac try_close_inv :=
  try (by (iLeft; iFrame; try_close_inv)); try (by (iRight; iFrame; try_close_inv)).

Section logrel.

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

  Let CPA' : val := CPA' η Key Output.

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

  Definition sym_is_cipher_lr_l {lls rls : list loc} (msg : val) (c k : val) : iProp Σ :=
    ∀ K e E A,
      (Plr lls rls -∗
        refines E
        (fill K (Val msg))
        e A)
    -∗ refines E
        (fill K (sdec lls k c))
        e A.
  
  Definition sym_is_cipher_lr_r {lls rls : list loc} (msg : val) (c k : val) : iProp Σ :=
    ∀ K e E A,
      (Plr lls rls -∗
        refines E
        e (fill K (Val msg)) A)
    -∗ refines E
        e (fill K (sdec rls k c)) A.

  Definition refines_senc_lr_l_prop :=
    ∀ (lls rls : list loc) (msg msg' : val) (k k' : val) K K' E A,
    lrel_key k k' ∗ lrel_msg msg msg' ∗ Plr lls rls ⊢
      ((∀ (c c' : val),
        lrel_cipher c c'
      -∗ @sym_is_cipher_lr_l lls rls msg c k
      -∗ refines E
          (fill K (Val c))
          (fill K' (Val c'))
          A)
    -∗ refines E
        (fill K  (senc lls k  msg ))
        (fill K' (senc rls k' msg'))
        A).
      
  Definition refines_senc_lr_r_prop :=
    ∀ (lls rls : list loc) (msg msg' : val) (k k' : val) K K' E A,
    lrel_key k k' ∗ lrel_msg msg msg' ∗ Plr lls rls ⊢
      ((∀ (c c' : val),
        lrel_cipher c c'
      -∗ @sym_is_cipher_lr_r lls rls msg c' k
      -∗ refines E
          (fill K (Val c))
          (fill K' (Val c'))
          A)
    -∗ refines E
        (fill K  (senc lls k  msg ))
        (fill K' (senc rls k' msg'))
        A).

  Hypothesis refines_couple_senc_lr_l : refines_senc_lr_l_prop.

  Hypothesis refines_couple_senc_lr_r : refines_senc_lr_r_prop.

  Definition senc_sem_typed_prop :=
    ∀ lls rls (𝒩 : namespace) (P : iProp Σ),
    (∃ (Q : iProp Σ),
      P ⊣⊢
        (Q
      ∗ Plr lls rls)
    ) →
    na_invP 𝒩 P
      ⊢ refines top (senc lls)
      (senc rls) (lrel_key → lrel_msg → lrel_cipher).

  Hypothesis senc_sem_typed : senc_sem_typed_prop.

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

  Hypothesis sdec_sem_typed : @sdec_sem_typed_prop _ _
    lrel_msg lrel_cipher lrel_key sdec Plr.

  Definition refines_couple_sdec_prop := ∀ K K' E (A : lrel Σ) k k' c c' lls rls,
       Plr lls rls
    -∗ lrel_key k k'
    -∗ lrel_cipher c c'
    -∗
    ((∀ decr decr', lrel_msg decr decr' -∗ Plr lls rls -∗
      (REL fill K (Val decr) << fill K' (Val decr') @ E : A))
    -∗ REL fill K (sdec lls k c) << fill K' (sdec rls k' c') @ E : A).
  
  Hypothesis refines_couple_sdec : refines_couple_sdec_prop.

  Definition PTXT' : val := PTXT' is_ciphertext is_plaintext elem_eq.

  Definition PTXT'' : val :=
    λ: "b" "adv" "scheme" "Q_enc_key" "Q_enc" "Q_dec",
      let: "record_plaintext" := init_linked_list #() in
      let: "enc_scheme" := get_enc_scheme "scheme" #() in
      let: "enc" := get_enc "enc_scheme" in
      let: "dec" := get_dec "enc_scheme" in
      let: "key" := get_keygen "scheme" #() in
      let: "enc_key" := λ: "msg", add_list "record_plaintext" "msg";;
        "enc" "key" "msg" in
      let: "oracle_enc_key" := q_calls_general_test is_plaintext "Q_enc" "enc_key" in
      let: "oracle_enc" :=
        q_calls_general_test
          (λ: "p", is_key (Fst "p") `and` is_plaintext (Snd "p"))
          "Q_enc"
          (λ: "p", "enc" (Fst "p") (Snd "p")) in
      let: "oracle_enc" := λ: "k" "msg", "oracle_enc" ("k", "msg") in
      let: "oracle_lr" :=
        let: "counter" := ref #0 in
        λ: "c",
          if: "b" then
            if: is_ciphertext "c" then
              let: "decrypted" := "dec" "key" "c" in
              if: ! "counter" < "Q_dec" then
                "counter" <- ! "counter" + #1;;
                let: "decrypted'" := "dec" "key" "c" in
                if: elem_of_linked_list elem_eq
                  "record_plaintext" "decrypted'" then
                  SOME "decrypted"
                else
                  NONEV
              else NONEV
            else NONEV
          else
            if: is_ciphertext "c" then
              if: ! "counter" < "Q_dec" then
                "counter" <- ! "counter" + #1;;
                SOME ("dec" "key" "c")
              else NONEV
            else NONEV
      in
      let: "b'" := "adv" "oracle_enc_key" "oracle_enc" "oracle_lr" in
      "b'".
  
  Let wmf_once := wmf_once η Key Output.

  Definition a_to_s_adv : val :=
    λ:  "A" "B" "b" "senc_oracle",
      let: "run" := ref #true in
      λ: "r_adv",
        if: ! "run" then
          "run" <- #false;;
          SOME
            (if: "b" then
              let: "nonce" := rand #N in
              let:m "c" := "senc_oracle" ("B", "nonce") in
              ("A", "c")
            else
              let:m "c" := "senc_oracle" ("B", "r_adv") in
              ("A", "c"))
        else NONE.

  Definition s_to_b_adv : val :=
    λ: "A" "B" "b" "senc_oracle" "sdec_oracle_a" "kb",
      let: "run" := ref #true in
      λ: "input",
        if: ! "run" then
          "run" <- #false;;
          let:m "nonce" := "sdec_oracle_a" (Snd "input") in
          let: "sender" := Fst "input" in
          let: "dest" := Fst "nonce" in
          let: "nonce" := Snd "nonce" in
          if: "sender" = "A" `and` "dest" = "B" then
            "senc_oracle" "kb" ("sender", "nonce")
          else (**"senc_oracle" "kb" ("sender", "nonce");;*) NONE
        else NONE.

  Definition wmf_once_adv_ptxt : expr :=
    let: "B" := init_id #() in  
    let: "A" := Fst "B" in
    let: "B" := Snd "B" in
    λ: "b" "enc_oracle_a" "enc_oracle" "dec_oracle_a",
      let: "kb" := keygen #() in
        let: "a_to_s" := a_to_s_adv "A" "B" "b"
          "enc_oracle_a" in
        let: "s_to_b" := s_to_b_adv "A" "B" "b"
          "enc_oracle" "dec_oracle_a" "kb" in
        let: "b_recv" := b_recv_once "A" "B" "b" "kb" in
      λ: "r_adv",
        ("a_to_s" "r_adv",
         "s_to_b",
         "b_recv").

  #[local] Instance wmf_msg_inj : Inject val val.
  Proof. unshelve econstructor.
    - exact (λ x, x).
    - intros x y H; done.
  Defined.

  Lemma wmf_once_true__wmf_adv_ptxt_false (adv : val) :
      (lrel_protocol → lrel_bool)%lrel adv adv
    ⊢ REL (adv (init_scheme (wmf_once #true))) <<
        (PTXT'' #false
          (λ: "senc_oracle" "senc_oracle_gen" "sdec_oracle",
            adv (wmf_once_adv_ptxt #true
              "senc_oracle" "senc_oracle_gen" "sdec_oracle"))
          sym_scheme
          #1 #1 #1)
      : lrel_bool.
  Proof with rel_pures_l; rel_pures_r.
    iIntros "#Hreladv".
    rewrite /init_scheme/wmf_protocol.init_scheme/PTXT''.
      (* /PTXT'/intptxt_ideal_dec.PTXT''. *)
    rel_apply refines_init_scheme_l.
    iIntros (lls) "HP"...
    rel_apply refines_init_list_r.
    iIntros (record) "Hrecord"...
    rel_apply refines_init_scheme_r.
    iIntros (rls) "HP'"...
    rewrite /get_enc/get_dec/get_keygen...
    rewrite /init_id...
    rel_apply refines_sym_keygen_couple.
    iIntros (ka ka') "#Hrelka"...
    rewrite /q_calls_general_test...
    rel_alloc_r cnt_enc as "Hcntenc".
    rel_alloc_r cnt_encgen as "Hcntencgen".
    rel_alloc_r cnt_dec as "Hcntdec"...
    rewrite /init_id...
    rel_bind_l _.
    rel_bind_r (adv _).
    rel_apply (refines_bind with "[-]").
    2: {
      iIntros (v v') "Hrelv"...
      rel_vals.
    }
    rel_apply refines_app; first rel_vals.
    iClear "Hreladv".
    rel_apply refines_sym_keygen_couple.
    iIntros (kb kb') "#Hrelkb"...
    rewrite /a_to_s_once/a_to_s_adv...
    rel_alloc_l run1 as "Hrun1";
    rel_alloc_r run1' as "Hrun1'"...
    rewrite /s_to_b_once/s_to_b_adv/get_enc...
    rel_alloc_l run2 as "Hrun2";
    rel_alloc_r run2' as "Hrun2'"...
    rewrite /b_recv_once...
    rel_alloc_l run3 as "Hrun3";
    rel_alloc_r run3' as "Hrun3'"...
    set (P := (
          Plr lls rls ∗ (
            run1  ↦  #false
          ∗ run1' ↦ₛ #false
          ∗ (∃ (nonce : nat),
                linked_slist wmf_msg_inj record [(#1, #nonce)%V]
              ∗ True)
          ∗ cnt_enc ↦ₛ #1
          ∗ ( run2  ↦  #false
            ∗ run2' ↦ₛ #false
            ∗ cnt_dec ↦ₛ #1
            ∗ (cnt_encgen ↦ₛ #1 ∨ cnt_encgen ↦ₛ #0)
            ∗ ( run3  ↦  #false
              ∗ run3' ↦ₛ #false ∨
                run3  ↦  #true
              ∗ run3' ↦ₛ #true)
            ∨ run2  ↦  #true
            ∗ run2' ↦ₛ #true
            ∗ cnt_dec ↦ₛ #0
            ∗ cnt_encgen ↦ₛ #0
            ∗ ( run3  ↦  #false
              ∗ run3' ↦ₛ #false ∨
                run3  ↦  #true
              ∗ run3' ↦ₛ #true))
          ∨ run1  ↦  #true
          ∗ run1' ↦ₛ #true
          ∗ linked_slist wmf_msg_inj record []
          ∗ cnt_enc ↦ₛ #0
          ∗ ( run2  ↦  #false
            ∗ run2' ↦ₛ #false
            ∗ cnt_dec ↦ₛ #1
            ∗ (cnt_encgen ↦ₛ #1 ∨ cnt_encgen ↦ₛ #0)
            ∗ ( run3  ↦  #false
              ∗ run3' ↦ₛ #false ∨
                run3  ↦  #true
              ∗ run3' ↦ₛ #true)
            ∨ run2  ↦  #true
            ∗ run2' ↦ₛ #true
            ∗ cnt_dec ↦ₛ #0
            ∗ cnt_encgen ↦ₛ #0
            ∗ ( run3  ↦  #false
              ∗ run3' ↦ₛ #false ∨
                run3  ↦  #true
              ∗ run3' ↦ₛ #true))
        ))%I).
    rel_apply (refines_na_alloc P (nroot.@"wmf_once__wmf_adv_ptxt_true".@"global")).
    iSplitL.
    { iSplitL "HP HP'";
      first iApply (P0lr_Plr with "HP HP'").
      repeat (iRight; iFrame). }
    iIntros "#Inv". rewrite /lrel_protocol.
    rel_arrow_val.
    iIntros (v1 v2) "[%r_adv [%eq1 [%eq2 %Hradvbound]]]"; subst...
    repeat rel_apply refines_pair.
    - rel_apply refines_na_inv; iSplit; first iAssumption.
      iIntros "[
        [HP
          [[Hrun1 [Hrun1' [Hlst [Hcnt H]]]]|[Hrun1 [Hrun1' [Hlst [Hcnt H]]]]]]
        Hclose]"; rel_load_l; rel_load_r...
      + rel_apply refines_na_close. iFrame. iSplitL; first (iLeft; iFrame).
        rel_vals.
      + rel_store_l; rel_store_r...
        rel_apply refines_couple_UU; first done.
        iModIntro; iIntros (nonce Hnoncebound)...
        rel_apply refines_is_plaintext_r.
        {
          iExists _.
          iExists _, _, _, _.
          repeat iSplit.
          * iPureIntro; done.
          * iPureIntro; done.
          * iExists 1. iPureIntro; split; done.
          * iExists nonce. iPureIntro; repeat split; lia.
        }
        rel_load_r... rel_load_r; rel_store_r...
        replace ((#1, #nonce)%V) with (inject (#1, #nonce)%V) by done.
        rel_apply (refines_add_list_r with "[-Hlst]").
        2: { iAssumption. }
        iIntros "Hlst"...
        rel_apply refines_na_close. iFrame.
        iSplitL.
        {
          iLeft. iFrame.
        }
        rel_bind_l (senc _ _ _);
        rel_bind_r (senc _ _ _).
        rel_apply refines_bind.
        { repeat rel_apply refines_app; first (iApply senc_sem_typed; last iAssumption).
          - eexists. apply bi.equiv_entails. split; iIntros "H"; first last.
            + iDestruct "H" as "[HP H]"; iFrame. iAssumption.
            + iDestruct "H" as "[HP H]"; iFrame.
          - rel_vals.
          - rel_vals; first iExists 1; last iExists _; iPureIntro; repeat split; lia.
        }
        iIntros (v v') "#Hrel"...
        rel_vals; first iExists 0; done.
    - rel_arrow_val.
      iIntros (input1 input2) "[%id_ [%id_' [%c [%c'
        [%Hinputeq1 [%Hinputeq2 [[%id [%eqid1 %eqid2]] #Hrelcipher]]]]]]]"; subst...
      rel_apply refines_na_inv; iSplit; first iAssumption.
      iIntros "[
        [HP
          [[Hrun1 [Hrun1' [Hlst [Hcnt_enc [
            [Hrun2 [Hrun2' [Hcnt_dec H]]]|
            [Hrun2 [Hrun2' [Hcnt_dec H]]]
            ]]]]] |
           [Hrun1 [Hrun1' [Hlst [Hcnt_enc [
            [Hrun2 [Hrun2' [Hcnt_dec H]]]|
            [Hrun2 [Hrun2' [Hcnt_dec H]]]
            ]]]]]]]
        Hclose]"; rel_load_l; rel_load_r; rel_pures_l; rel_pures_r;
      try by (
        rel_apply refines_na_close; iFrame; iSplitL;
          try (by try (iLeft; iFrame; iLeft; iFrame); rel_vals);
          try (by try (iLeft; iFrame; iRight; iFrame); rel_vals);
          try (by try (iRight; iFrame; iLeft; iFrame); rel_vals "ka");
          try (by try (iRight; iFrame; iRight; iFrame); rel_vals))...
      + rel_store_l; rel_store_r...
        rel_apply (refines_is_ciphertext_r with "[Hrelcipher]")...
        { iExists c. iAssumption. }
        rel_load_r; rel_load_r; rel_store_r...
        rel_apply (refines_couple_sdec with "HP").
        1, 2: iAssumption.
        iIntros (decrypted1 decrypted2) "[%iddest [%iddest' [%crecv [%crecv'
        [%Hinputeq1 [%Hinputeq2 [[%id_dest
          [%eqiddest1 %eqiddest2]] [%r [%eqr1 [%eqr2 %Hrbound]]]]]]]]]] HP"; subst...
        destruct (bool_decide (#id = #0)) eqn:eqid;
        destruct (bool_decide (#id_dest = #1)) eqn:eqiddest...
        2, 3, 4:
          rel_apply refines_na_close;
          iFrame; iSplitL; first
          (
            iFrame; iLeft; iFrame; iLeft; iFrame;
            iDestruct "H" as "[Hcnt H]"; iSplitR "H";
            last iAssumption;
            iRight; done
          );
          rel_vals.
        rel_apply refines_is_plaintext_r...
        { iExists (#id, #r)%V. iExists _, _, _, _.
          repeat iSplit. 1, 2: iPureIntro; done.
          - iExists id. done.
          - iExists r. iPureIntro; repeat split; lia. }
        rel_apply refines_is_key_r...
        {
          iExists kb. iAssumption.
        }
        iDestruct "H" as "[Hcntencgen H]".
        rel_load_r... rel_load_r; rel_store_r...
        rel_apply refines_na_close.
        iFrame; iSplitL.
        { iFrame. iLeft. iFrame. iLeft; iFrame. }
        rel_apply refines_injr.
        repeat rel_apply refines_app.
        * rel_apply senc_sem_typed; last iAssumption.
            eexists. apply bi.equiv_entails.
            split; iIntros "H".
            -- iDestruct "H" as "[HP H]"; iFrame. iAssumption.
            -- iDestruct "H" as "[H HP]"; iFrame.
        * rel_vals.
        * rel_vals.
          -- iExists id. done.
          -- iExists r. done.
      + rel_store_l; rel_store_r...
        rel_apply (refines_is_ciphertext_r with "[Hrelcipher]")...
        { iExists c. iAssumption. }
        rel_load_r; rel_load_r; rel_store_r...
        rel_apply (refines_couple_sdec with "HP").
        1, 2: iAssumption.
        iIntros (decrypted1 decrypted2) "[%iddest [%iddest' [%crecv [%crecv'
        [%Hinputeq1 [%Hinputeq2 [[%id_dest
          [%eqiddest1 %eqiddest2]] [%r [%eqr1 [%eqr2 %Hrbound]]]]]]]]]] HP"; subst...
        destruct (bool_decide (#id = #0)) eqn:eqid;
        destruct (bool_decide (#id_dest = #1)) eqn:eqiddest...
        2, 3, 4:
          rel_apply refines_na_close;
          iFrame; iSplitL; first
          (
            iFrame; iRight; iFrame; iLeft; iFrame;
            iDestruct "H" as "[Hcnt H]"; iSplitR "H";
            last iAssumption;
            iRight; done
          );
          rel_vals.
        rel_apply refines_is_plaintext_r...
        { iExists (#id, #r)%V. iExists _, _, _, _.
          repeat iSplit. 1, 2: iPureIntro; done.
          - iExists id. done.
          - iExists r. iPureIntro; repeat split; lia. }
        rel_apply refines_is_key_r...
        {
          iExists kb. iAssumption.
        }
        iDestruct "H" as "[Hcntencgen H]".
        rel_load_r... rel_load_r; rel_store_r...
        rel_apply refines_na_close.
        iFrame; iSplitL.
        { iFrame. iRight. iFrame. iLeft; iFrame. }
        rel_apply refines_injr.
        repeat rel_apply refines_app.
        * rel_apply senc_sem_typed; last iAssumption.
            eexists. apply bi.equiv_entails.
            split; iIntros "H".
            -- iDestruct "H" as "[HP H]"; iFrame. iAssumption.
            -- iDestruct "H" as "[H HP]"; iFrame.
        * rel_vals.
        * rel_vals.
          -- iExists id. done.
          -- iExists r. done.
    - rel_arrow_val.
      iIntros (input1 input2) "#Hrelcipher"; subst...
      rel_apply refines_na_inv; iSplit; first iAssumption.
      iIntros "[
        [HP
          [[Hrun1 [Hrun1' [Hlst [Hcnt_enc [
            [Hrun2 [Hrun2' [Hcnt_dec [Hcntgen [[Hcnt3 Hcnt3'] | [Hcnt3 Hcnt3']] ]]]]|
            [Hrun2 [Hrun2' [Hcnt_dec [Hcntgen [[Hcnt3 Hcnt3'] | [Hcnt3 Hcnt3']] ]]]]
            ]]]]] |
           [Hrun1 [Hrun1' [Hlst [Hcnt_enc [
            [Hrun2 [Hrun2' [Hcnt_dec [Hcntgen [[Hcnt3 Hcnt3'] | [Hcnt3 Hcnt3']] ]]]]|
            [Hrun2 [Hrun2' [Hcnt_dec [Hcntgen [[Hcnt3 Hcnt3'] | [Hcnt3 Hcnt3']] ]]]]
            ]]]]]]]
        Hclose]";
      rel_load_l; rel_load_r;
      try (rel_store_l; rel_store_r); rel_pures_l; rel_pures_r.
      all: rel_apply refines_na_close; iFrame; iSplitL; first (
        try (by try (iLeft; iFrame; iLeft; iFrame; iLeft; iFrame));
        try (by try (iLeft; iFrame; iLeft; iFrame; iRight; iFrame));
        try (by try (iLeft; iFrame; iRight; iFrame; iLeft; iFrame));
        try (by try (iLeft; iFrame; iRight; iFrame; iRight; iFrame));
        try (by try (iRight; iFrame; iLeft; iFrame; iLeft; iFrame));
        try (by try (iRight; iFrame; iLeft; iFrame; iRight; iFrame));
        try (by try (iRight; iFrame; iRight; iFrame; iLeft; iFrame));
        try (by try (iRight; iFrame; iRight; iFrame; iRight; iFrame))
      ).
      all: rel_vals.
  Qed.

  (* We use the PTXT assumption to establish some kind
    of private channel between a and s *)
  Definition a_to_s_private_channel : val :=
    λ:  "A" "B" "b" "channel" "senc" "ka",
      let: "run" := ref #true in
      λ: "r_adv",
        if: ! "run" then
          "run" <- #false;;
          SOME
            (if: "b" then
              let: "nonce" := rand #N in
              "channel" <- SOME ("B", "nonce");;
              let: "c" := "senc" "ka" ("B", "nonce") in
              ("A", "c")
            else
              "channel" <- SOME ("B", "r_adv");;
              let:m "c" := "senc" "ka" ("B", "r_adv") in
              ("A", "c"))
        else NONE.

  Definition s_to_b_private_channel : val :=
    λ: "A" "B" "b" "channel" "senc" "sdec" "ka" "kb",
      let: "run" := ref #true in
      λ: "input",
        if: ! "run" then
          "run" <- #false;;
          let: "decr" := "sdec" "ka" (Snd "input") in
          let:m "ptxt" := ! "channel" in
          if: elem_eq "decr" "ptxt" then
            let: "sender" := Fst "input" in
            let: "dest" := Fst "ptxt" in
            let: "nonce" := Snd "ptxt" in
            if: "sender" = "A" `and` "dest" = "B" then
              SOME ("senc" "kb" ("sender", "nonce"))
            else NONE
          else NONE
        else NONE.

  Definition wmf_once_private_channel : expr :=
    let: "B" := init_id #() in  
    let: "A" := Fst "B" in
    let: "B" := Snd "B" in
    let: "a_s__channel" := ref NONE in 
    λ: "b" "enc_scheme",
      let: "ka" := keygen #() in
      let: "kb" := keygen #() in
        let: "a_to_s" := a_to_s_private_channel "A" "B" "b" "a_s__channel"
          (get_enc "enc_scheme") "ka" in
        let: "s_to_b" := s_to_b_private_channel "A" "B" "b" "a_s__channel"
          (get_enc "enc_scheme") (get_dec "enc_scheme") "ka" "kb" in
        let: "b_recv" := b_recv_once "A" "B" "b" "kb" in
      λ: "r_adv",
        ("a_to_s" "r_adv",
         "s_to_b",
         "b_recv").

  Definition refines_sdec_lr_l_prop :=
    ∀ (lls rls : list loc) (c c' : val) (k k' : val) K K' E A,
    lrel_key k k' ∗ lrel_cipher c c' ∗ Plr lls rls ⊢
      ((∀ (m m' : val),
        lrel_msg m m'
      -∗ @sym_is_cipher_lr_l lls rls m c k
      -∗ refines E
          (fill K (Val m))
          (fill K' (Val m'))
          A)
    -∗ refines E
        (fill K  (sdec lls k  c ))
        (fill K' (sdec rls k' c'))
        A).

  Definition refines_sdec_lr_r_prop :=
    ∀ (lls rls : list loc) (c c' : val) (k k' : val) K K' E A,
    lrel_key k k' ∗ lrel_cipher c c' ∗ Plr lls rls ⊢
      ((∀ (m m' : val),
        lrel_msg m m'
      -∗ @sym_is_cipher_lr_r lls rls m c k
      -∗ refines E
          (fill K (Val m))
          (fill K' (Val m'))
          A)
    -∗ refines E
        (fill K  (sdec lls k  c ))
        (fill K' (sdec rls k' c'))
        A).

  Hypothesis refines_sdec_lr_l : refines_sdec_lr_l_prop.
  Hypothesis refines_sdec_lr_r : refines_sdec_lr_r_prop.

  Lemma wmf_adv_ptxt_false__wmf_private_channel_true (adv : val) :
      (lrel_protocol → lrel_bool)%lrel adv adv
    ⊢ REL
        (PTXT'' #true
          (λ: "senc_oracle" "senc_oracle_gen" "sdec_oracle",
            adv (wmf_once_adv_ptxt #true
              "senc_oracle" "senc_oracle_gen" "sdec_oracle"))
          sym_scheme
          #1 #1 #1) <<
        (adv (init_scheme (wmf_once_private_channel #true)))
      : lrel_bool.
  Proof with rel_pures_l; rel_pures_r.
    iIntros "#Hadv".
    rewrite /PTXT''/init_scheme/wmf_protocol.init_scheme...
    rel_apply refines_init_list_l.
    Unshelve.
    2: exact val.
    2: apply _.
    iIntros (l_record) "Hrecordlst"...
    rel_apply refines_init_scheme_l;
    iIntros (lls) "HP";
    rel_apply refines_init_scheme_r;
    iIntros (rls) "HP'"...
    rewrite /get_enc/get_dec/get_keygen...
    rewrite /init_id...
    rel_alloc_r channel as "Hchannel"...
    rel_apply refines_sym_keygen_couple.
    iIntros (ka ka') "#Hrelka"...
    rewrite /q_calls_general_test...
    rel_alloc_l cnt_enc as "Hcntenc".
    rel_alloc_l cnt_encgen as "Hcntencgen".
    rel_alloc_l cnt_dec as "Hcntdec"...
    rewrite /init_id...
    rel_bind_l (adv _).
    rel_bind_r (adv _).
    rel_apply (refines_bind with "[-]").
    2: {
      iIntros (v v') "Hrelv"...
      rel_vals.
    }
    rel_apply (refines_app with "[]"); first (rel_vals; iAssumption).
    rel_apply refines_sym_keygen_couple.
    iIntros (kb kb') "#Hrelkb"...
    rewrite /a_to_s_adv/a_to_s_private_channel...
    rel_alloc_l run1 as "Hrun1";
    rel_alloc_r run1' as "Hrun1'"...
    rewrite /s_to_b_adv/s_to_b_private_channel.
    rel_alloc_l run2 as "Hrun2";
    rel_alloc_r run2' as "Hrun2'"...
    rewrite /b_recv_once...
    rel_alloc_l run3 as "Hrun3";
    rel_alloc_r run3' as "Hrun3'"...
    set (P := (
          Plr lls rls ∗ (
            run1  ↦  #false
          ∗ run1' ↦ₛ #false
          ∗ (∃ (nonce : nat),
                linked_list wmf_msg_inj l_record [(#1, #nonce)%V]
              ∗ channel ↦ₛ SOMEV (#1, #nonce)%V
              ∗ ⌜nonce ≤ N⌝)
          ∗ cnt_enc ↦ #1
          ∗ ( run2  ↦  #false
            ∗ run2' ↦ₛ #false
            ∗ cnt_dec ↦ #1
            ∗ (cnt_encgen ↦ #1 ∨ cnt_encgen ↦ #0)
            ∗ ( run3  ↦  #false
              ∗ run3' ↦ₛ #false ∨
                run3  ↦  #true
              ∗ run3' ↦ₛ #true)
            ∨ run2  ↦  #true
            ∗ run2' ↦ₛ #true
            ∗ cnt_dec ↦ #0
            ∗ cnt_encgen ↦ #0
            ∗ ( run3  ↦  #false
              ∗ run3' ↦ₛ #false ∨
                run3  ↦  #true
              ∗ run3' ↦ₛ #true))
          ∨ run1  ↦  #true
          ∗ run1' ↦ₛ #true
          ∗ (linked_list wmf_msg_inj l_record []
          ∗ channel ↦ₛ NONEV)
          ∗ cnt_enc ↦ #0
          ∗ ( run2  ↦  #false
            ∗ run2' ↦ₛ #false
            ∗ cnt_dec ↦ #1
            ∗ (cnt_encgen ↦ #1 ∨ cnt_encgen ↦ #0)
            ∗ ( run3  ↦  #false
              ∗ run3' ↦ₛ #false ∨
                run3  ↦  #true
              ∗ run3' ↦ₛ #true)
            ∨ run2  ↦  #true
            ∗ run2' ↦ₛ #true
            ∗ cnt_dec ↦ #0
            ∗ cnt_encgen ↦ #0
            ∗ ( run3  ↦  #false
              ∗ run3' ↦ₛ #false ∨
                run3  ↦  #true
              ∗ run3' ↦ₛ #true))
        ))%I).
    rel_apply (refines_na_alloc P (nroot.@"wmf_once__wmf_adv_ptxt_true".@"global")).
    iSplitL.
    { iSplitL "HP HP'";
      first iApply (P0lr_Plr with "HP HP'").
      repeat (iRight; iFrame). }
    iIntros "#Inv".
    rel_arrow_val.
    iIntros (radv1 radv2) "[%r_adv [%eq1 [%eq2 %Hradvbound]]]"; subst...
    repeat rel_apply refines_pair.
    - rel_apply refines_na_inv. iSplit; first iAssumption.
      iIntros "[
        [HP
          [[Hrun1 [Hrun1' [Hlst [Hcnt H]]]]|[Hrun1 [Hrun1' [[Hlst Hchannel] [Hcnt H]]]]]]
        Hclose]"; rel_load_l; rel_load_r...
      + rel_apply refines_na_close. iFrame. iSplitL.
        { iLeft. iFrame. }
        rel_vals.
      + rel_store_l; rel_store_r...
        rel_apply refines_couple_UU; first done.
        iModIntro; iIntros (nonce Hnoncebound)...
        rel_apply refines_is_plaintext_l.
        { iExists (#1, #nonce)%V. iExists _, _, _, _.
          repeat iSplit. 1, 2: iPureIntro; done.
          all: iExists _; iPureIntro; repeat split; try lia.
          all: rewrite -(Z2Nat.id 1); done. }
        rel_load_l...
        rel_load_l; rel_store_l...
        replace (#1, #nonce)%V with (inject (#1, #nonce)%V) by done.
        rel_apply (refines_add_list_l with "[-Hlst]"); last iAssumption.
        iIntros "Hlst"...
        rel_store_r...
        rel_apply refines_na_close.
        iFrame. iSplitL.
        { iLeft. iFrame. done. }
        rel_bind_l (senc _ _ _).
        rel_bind_r (senc _ _ _).
        rel_apply refines_bind.
        2: {
          iIntros (c1 c2) "#Hrelc"...
          rel_vals; last iAssumption.
          iExists 0; done.
        }
        repeat rel_apply refines_app.
        * rel_apply senc_sem_typed; last iAssumption.
          eexists. apply bi.equiv_entails; split; iIntros "H".
          -- iDestruct "H" as "[H HP]". iFrame. iAssumption.
          -- iDestruct "H" as "[H HP]". iFrame.
        * rel_vals.
        * rel_vals; iExists _; iPureIntro; repeat split;
          try rewrite -(Z2Nat.id 1); try lia; done.
    - rel_arrow_val.
      iIntros (input1 input2) "[%id_ [%id_' [%c [%c'
        [%Hinputeq1 [%Hinputeq2 [[%id [%eqid1 %eqid2]] #Hrelcipher]]]]]]]"; subst...
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[
        [HP
          [[Hrun1 [Hrun1' [Hlst [Hcnt H]]]]|[Hrun1 [Hrun1' [[Hlst Hchannel] [Hcnt H]]]]]]
        Hclose]";
      iDestruct "H" as "[[Hrun2 [Hrun2' [Hcntdec [Hcntencgen H]]]] |
        [Hrun2 [Hrun2' [Hcntdec [Hcntencgen H]]]] ]"; rel_load_l; rel_load_r...
      1, 3: (rel_apply refines_na_close; iFrame;
        iSplitL;
        first try  (iFrame; iLeft; iFrame; iLeft; iFrame);
        first try  (iFrame; iRight; iFrame; iLeft; iFrame);
        rel_vals).
      + rel_store_l; rel_store_r...
        rel_apply refines_is_ciphertext_l...
        { iExists c'; done. }
        rel_apply (refines_sdec_lr_l with "[HP]").
        {
          iSplit; first iAssumption.
          iSplit; first iAssumption.
          iAssumption.
        }
        iIntros (decrypted1 decrypted2) "[%iddest [%iddest' [%crecv [%crecv'
        [%Hinputeq1 [%Hinputeq2 [[%id_dest
          [%eqiddest1 %eqiddest2]] [%r [%eqr1 [%eqr2 %Hrbound]]]]]]]]]]
          Hiscipher"; subst...
        rel_load_l...
        rel_load_l... rel_store_l...
        iDestruct "Hlst" as (nonce) "[Hl_list [Hchannel %Hnoncebound]]".
        rel_load_r...
        rel_apply refines_elem_eq_r.
        iSplitR; last iSplitR.
        { iLeft. iExists (#id_dest, #r)%V. iExists _, _, _, _.
          repeat iSplit.
          1, 2: iPureIntro; done.
          - iExists id_dest. done.
          - iExists r. done. }
        { iLeft. iExists (#1, #nonce)%V. iExists _, _, _, _.
          repeat iSplit.
          1, 2: iPureIntro; done.
          - iExists 1. done.
          - iExists nonce. iPureIntro; repeat split; lia. }
        rel_apply "Hiscipher".
        iIntros "HP"...
        unshelve rel_apply (refines_elem_of_l lrel_msg with "
          [Hrun1 Hrun1' Hrun2 Hrun2' Hchannel
           Hcnt Hcntdec Hcntencgen H Hclose HP]
          [Hl_list]
          []"); try iAssumption.
        1: exact lrel_cipher.
        1: exact lrel_key.
        1: exact is_ciphertext.
        1: exact is_plaintext.
        1: apply refines_is_ciphertext_r.
        1: apply refines_is_ciphertext_l.
        1: apply refines_is_plaintext_r.
        1: apply refines_is_plaintext_l.
        3: apply refines_elem_eq_l.
        3: apply refines_elem_eq_r.
        1, 2: shelve.
        2: {
          iSplit.
          - simpl. iSplit; last done.
            iLeft. iExists (#1, #nonce)%V.
            iExists _, _, _, _. repeat iSplit.
            1, 2: iPureIntro; done.
            + iExists 1. iPureIntro. split;
              f_equal.
            + iExists nonce. iPureIntro; repeat split; lia. 
          - simpl.
            iLeft. iExists (#id_dest, #r)%V.
            iExists _, _, _, _. repeat iSplit.
            1, 2: iPureIntro; done.
            + iExists id_dest. iPureIntro. split;
              f_equal.
            + iExists r. iPureIntro; repeat split; lia. 
        }
        iIntros (b) "Hlst %eq".
        rewrite elem_of_list_singleton in eq.
        destruct (bool_decide (#id_dest = #1)) eqn:Hdecid;
        destruct (bool_decide (#r = #nonce)) eqn:Hdecr;
        try apply bool_decide_eq_true in Hdecid as eqid;
        try apply bool_decide_eq_true in Hdecr as eqr;
        try apply bool_decide_eq_false in Hdecid as eqid;
        try apply bool_decide_eq_false in Hdecr as eqr;
        rel_pures_l; rel_pures_r;
        try ( destruct b; first
          ( destruct eq as [eq' _];
            unshelve epose proof (eq' _) as eq;
            try done;
            injection eq;
            intros eqr' eqid';
            exfalso; apply eqr; f_equal;
            rewrite eqr'; done );
          rel_pures_l; rel_pures_r;
          rel_apply refines_na_close; iFrame;
          iSplitL; last rel_vals;
          iFrame; iLeft; iFrame;
          iSplitR; first (iPureIntro; lia);
          iLeft; iFrame ).
        2: {
          destruct b...
          { destruct eq as [eq' _];
            unshelve epose proof (eq' _) as eq; first done.
            injection eq;
            intros eqr' eqid';
            exfalso; apply eqid; f_equal;
            rewrite eqid'; done. }
          rel_apply refines_na_close; iFrame;
          iSplitL; last rel_vals;
          iFrame; iLeft; iFrame;
          iSplitR; first (iPureIntro; lia).
          iLeft. iFrame. }
        destruct eq as [_ eqb'].
        unshelve epose proof (eqb' _) as eqb.
        { rewrite eqid. rewrite eqr. done. }
        subst...
        rewrite eqid...
        destruct (bool_decide (#id = #0)) eqn:eqid0...
        2: {
          rel_apply refines_na_close. iFrame.
          iSplitL.
          {
            iFrame. iLeft. iFrame.
            iSplitR; first (iPureIntro; lia).
            iLeft; iFrame.
          }
          rel_vals.
        }
        rel_apply refines_is_plaintext_l...
        { iExists (#id, #r)%V. iExists _, _, _, _.
          repeat iSplit.
          1, 2 : iPureIntro; done.
          - iExists id. done.
          - iExists r. done. }
        rel_apply refines_is_key_l.
        { iExists kb'. iAssumption. }
        rel_load_l...
        rel_load_l; rel_store_l...
        rel_apply refines_na_close; iFrame.
        iSplitL.
        {
          iFrame. iLeft. iFrame.
          iSplitR; first done.
          iLeft. iFrame.
        }
        rewrite eqr.
        rel_apply refines_injr.
        repeat rel_apply refines_app.
        * rel_apply senc_sem_typed; last iAssumption.
          eexists. apply bi.equiv_entails; split; iIntros "[H1 H2]".
          -- iFrame. iAssumption.
          -- iFrame.
        * rel_vals.
        * rel_vals.
          -- iExists id. done.
          -- iExists nonce. iPureIntro; repeat split; lia.
        Unshelve.
        {
          clear.
          iIntros (x y) "[[%x' Hx] | [%x' Hx]] [[%y' Hy]|[%y' Hy]]";
          iDestruct "Hx" as "[%id1v [%id1v' [%m1 [%m1'
            [%Heq1 [%Heq2 [[%id1
            [%eqid1 %eqid2]] [%r1 [%eqr1 [%eqr2 %Hr1bound]]]]]]]]]]"; subst;
          iDestruct "Hy" as "[%id [%id' [%m [%m'
            [%Heq1 [%Heq2 [[%id2
            [%eqid1 %eqid2]] [%r2 [%eqr1 [%eqr2 %Hr2bound]]]]]]]]]]"; subst;
          iPureIntro; constructor; constructor.
        }
        {
          clear.
          iIntros (x y) "H";
          iDestruct "H" as "[%id1v [%id1v' [%m1 [%m1'
            [%Heq1 [%Heq2 [[%id1
            [%eqid1 %eqid2]] [%r1 [%eqr1 [%eqr2 %Hr1bound]]]]]]]]]]"; subst;
          done.
        }
      + rel_store_l; rel_store_r...
        rel_apply refines_is_ciphertext_l...
        { iExists c'; done. }
        rel_apply (refines_sdec_lr_l with "[HP]").
        {
          iSplit; first iAssumption.
          iSplit; first iAssumption.
          iAssumption.
        }
        iIntros (decrypted1 decrypted2) "[%iddest [%iddest' [%crecv [%crecv'
        [%Hinputeq1 [%Hinputeq2 [[%id_dest
          [%eqiddest1 %eqiddest2]] [%r [%eqr1 [%eqr2 %Hrbound]]]]]]]]]]
          Hiscipher"; subst...
        rel_load_l...
        rel_load_l... rel_store_l...
        rel_load_r...
        rel_apply "Hiscipher".
        iIntros "HP"...
        rel_apply (refines_elem_of_l lrel_msg with "
          [Hrun1 Hrun1' Hrun2 Hrun2' Hchannel
           Hcnt Hcntdec Hcntencgen H Hclose HP]
          [Hlst]
          []").
        2: iAssumption.
        2: {
          iSplit; first done.
          simpl.
          iLeft. iExists (#id_dest, #r)%V.
          iExists _, _, _, _. repeat iSplit.
          1, 2: iPureIntro; done.
          + iExists id_dest. iPureIntro. split;
            f_equal.
          + iExists r. iPureIntro; repeat split; lia. 
        }
        Unshelve.
        2: exact lrel_cipher.
        2: exact lrel_key.
        2: exact is_ciphertext.
        2: exact is_plaintext.
        2: apply refines_is_ciphertext_r.
        2: apply refines_is_ciphertext_l.
        2: apply refines_is_plaintext_r.
        2: apply refines_is_plaintext_l.
        4: apply refines_elem_eq_l.
        4: apply refines_elem_eq_r.
        2, 3: shelve.
        iIntros (b) "Hlst %eq".
        destruct b...
        {
          exfalso.
          destruct eq as [eq _].
          unshelve epose proof (eq _) as eq'; first done.
          apply elem_of_nil in eq'. assumption.
        }
        rel_apply refines_na_close; iFrame.
        iSplitL.
        {
          iFrame. iRight. iFrame.
          iLeft. iFrame.
        }
        rel_vals.
        Unshelve.
        {
          clear.
          iIntros (x y) "[[%x' Hx] | [%x' Hx]] [[%y' Hy]|[%y' Hy]]";
          iDestruct "Hx" as "[%id1v [%id1v' [%m1 [%m1'
            [%Heq1 [%Heq2 [[%id1
            [%eqid1 %eqid2]] [%r1 [%eqr1 [%eqr2 %Hr1bound]]]]]]]]]]"; subst;
          iDestruct "Hy" as "[%id [%id' [%m [%m'
            [%Heq1 [%Heq2 [[%id2
            [%eqid1 %eqid2]] [%r2 [%eqr1 [%eqr2 %Hr2bound]]]]]]]]]]"; subst;
          iPureIntro; constructor; constructor.
        }
        {
          clear.
          iIntros (x y) "H";
          iDestruct "H" as "[%id1v [%id1v' [%m1 [%m1'
            [%Heq1 [%Heq2 [[%id1
            [%eqid1 %eqid2]] [%r1 [%eqr1 [%eqr2 %Hr1bound]]]]]]]]]]"; subst;
          done.
        }
    - rel_arrow_val. iIntros (v1 v2) "#Hrelinput"...
      rel_apply refines_na_inv. iSplit; first iAssumption.
      iIntros "[
        [HP
          [[Hrun1 [Hrun1' [Hlst [Hcnt H]]]]|[Hrun1 [Hrun1' [[Hlst Hchannel] [Hcnt H]]]]]]
        Hclose]";
      iDestruct "H" as "[[Hrun2 [Hrun2' [Hcntdec [Hcntencgen H]]]] |
        [Hrun2 [Hrun2' [Hcntdec [Hcntencgen H]]]] ]";
        iDestruct "H" as "[[Hrun3 Hrun3'] | [Hrun3 Hrun3']]";
        rel_load_l; try rel_store_l;
        rel_load_r; try rel_store_r;
        rel_apply refines_na_close; iFrame;
        iSplitL;
        try_close_inv;
        rel_pures_l; rel_pures_r;
        rel_vals.
  Qed.

  Definition a_to_s_plain_and_cipher_channel : val :=
    λ:  "A" "B" "b" "plain_channel" "cipher_channel" "senc" "ka",
      let: "run" := ref #true in
      λ: "r_adv",
        if: ! "run" then
          "run" <- #false;;
          SOME
            (if: "b" then
              let: "nonce" := rand #N in
              "plain_channel" <- SOME ("B", "nonce");;
              let: "c" := "senc" "ka" ("B", "nonce") in
              "cipher_channel" <- SOME "c";;
              ("A", "c")
            else
              "plain_channel" <- SOME ("B", "r_adv");;
              let:m "c" := "senc" "ka" ("B", "r_adv") in
              "cipher_channel" <- SOME "c";;
              ("A", "c"))
        else NONE.

  Definition s_to_b_plain_and_cipher_channel : val :=
    λ: "A" "B" "b" "plain_channel" "cipher_channel" "senc" "sdec" "ka" "kb",
      let: "run" := ref #true in
      λ: "input",
        if: ! "run" then
          "run" <- #false;;
          let: "cipher" := Snd "input" in
          let:m "cipher_rec" := ! "cipher_channel" in
          let:m "plain_rec" := ! "plain_channel" in
          let: "decr" := if: "cipher" = "cipher_rec" then
              "plain_rec"
            else
              "sdec" "ka" (Snd "input")
            in
          if: elem_eq "decr" "plain_rec" then
            let: "sender" := Fst "input" in
            let: "dest" := Fst "plain_rec" in
            let: "nonce" := Snd "plain_rec" in
            if: "sender" = "A" `and` "dest" = "B" then
              SOME ("senc" "kb" ("sender", "nonce"))
            else NONE
          else NONE
        else NONE.

  Definition wmf_once_plain_cipher_channel : expr :=
    let: "B" := init_id #() in  
    let: "A" := Fst "B" in
    let: "B" := Snd "B" in
    let: "a_s__channel_plain" := ref NONE in 
    let: "a_s__channel_cipher" := ref NONE in 
    λ: "b" "enc_scheme",
      let: "ka" := keygen #() in
      let: "kb" := keygen #() in
        let: "a_to_s" := a_to_s_plain_and_cipher_channel "A" "B" "b"
          "a_s__channel_plain" "a_s__channel_cipher"
          (get_enc "enc_scheme") "ka" in
        let: "s_to_b" := s_to_b_plain_and_cipher_channel "A" "B" "b"
          "a_s__channel_plain" "a_s__channel_cipher"
          (get_enc "enc_scheme") (get_dec "enc_scheme") "ka" "kb" in
        let: "b_recv" := b_recv_once "A" "B" "b" "kb" in
      λ: "r_adv",
        ("a_to_s" "r_adv",
         "s_to_b",
         "b_recv").

  Hypothesis cipher_comparable : ∀ x y,
    half_lrel lrel_cipher x ∗ half_lrel lrel_cipher y ⊢ ⌜vals_compare_safe x y⌝.
  
  Hypothesis lrel_cipher_eq : ∀ x y, lrel_cipher x y ⊢ ⌜x = y⌝.

  Lemma refines_senc_lr_l2 :
    ∀ (lls rls : list loc) (msg msg' : val) (k k' : val) K K' E A,
    lrel_key k k' ∗ lrel_msg msg msg' ∗ Plr lls rls ⊢
      ((∀ (c c' : val),
        lrel_cipher c c'
      -∗ (@sym_is_cipher_lr_l lls rls msg c k ∧ Plr lls rls)
      -∗ refines E
          (fill K (Val c))
          (fill K' (Val c'))
          A)
    -∗ refines E
        (fill K  (senc lls k  msg ))
        (fill K' (senc rls k' msg'))
        A).
  Admitted.

  Lemma refines_sdec_l :
    ∀ (lls rls : list loc) (c : val) (k k' : val) K e' E A,
    lrel_key k k' ∗ half_lrel lrel_cipher c ∗ Plr lls rls ⊢
      ((∀ (msg : val),
        half_lrel lrel_msg msg
      -∗ Plr lls rls
      -∗ refines E
          (fill K (Val c))
          e'
          A)
    -∗ refines E
        (fill K  (sdec lls k  c))
        e'
        A).
  Admitted.

  Lemma wmf_private_channel_true__wmf_pctxt_channel_true (adv : val) :
    ⊢ REL
        (init_scheme (wmf_once_private_channel #true)) <<
        (init_scheme (wmf_once_plain_cipher_channel #true))
      : lrel_protocol.
  Proof with rel_pures_l; rel_pures_r.
    rewrite /init_scheme/wmf_protocol.init_scheme...
    rel_apply refines_init_scheme_l;
    iIntros (lls) "HP";
    rel_apply refines_init_scheme_r;
    iIntros (rls) "HP'"...
    rewrite /get_enc/get_dec/get_keygen...
    rewrite /init_id...
    rel_alloc_l ptxtchannel as "Hptxtchannel"...
    rel_alloc_r ptxtchannel' as "Hptxtchannel'"...
    rel_alloc_r ctxtchannel' as "Hctxtchannel'"...
    rel_apply refines_sym_keygen_couple.
    iIntros (ka ka') "#Hrelka"...
    rel_apply refines_sym_keygen_couple.
    iIntros (kb kb') "#Hrelkb"...
    rewrite /a_to_s_plain_and_cipher_channel/a_to_s_private_channel...
    rel_alloc_l run1 as "Hrun1";
    rel_alloc_r run1' as "Hrun1'"...
    rewrite /s_to_b_plain_and_cipher_channel/s_to_b_private_channel.
    rel_alloc_l run2 as "Hrun2";
    rel_alloc_r run2' as "Hrun2'"...
    rewrite /b_recv_once...
    rel_alloc_l run3 as "Hrun3";
    rel_alloc_r run3' as "Hrun3'"...
    set (P := (
          (
            (run1  ↦  #false
          ∗ run1' ↦ₛ #false
          ∗ ∃ (nonce : nat) (c c' : val),
              ( ptxtchannel ↦ SOMEV (#1, #nonce)
              ∗ ptxtchannel' ↦ₛ SOMEV (#1, #nonce)
              ∗ (lrel_cipher c c' ∗ ctxtchannel' ↦ₛ SOMEV c')
              ∗ ⌜nonce ≤ N⌝
              ∗ ( run2  ↦  #false
                ∗ run2' ↦ₛ #false
                ∗ Plr lls rls
                ∗ ( run3  ↦  #false
                  ∗ run3' ↦ₛ #false ∨
                    run3  ↦  #true
                  ∗ run3' ↦ₛ #true)
                ∨ run2  ↦  #true
                ∗ run2' ↦ₛ #true
                ∗ (@sym_is_cipher_lr_l lls rls (#1, #nonce)%V c ka ∧ Plr lls rls)
                ∗ ( run3  ↦  #false
                  ∗ run3' ↦ₛ #false ∨
                    run3  ↦  #true
                  ∗ run3' ↦ₛ #true))))
          ∨ (run1  ↦  #true
          ∗ run1' ↦ₛ #true
          ∗ Plr lls rls
          ∗ ptxtchannel ↦ NONEV
          ∗ ptxtchannel' ↦ₛ NONEV
          ∗ ctxtchannel' ↦ₛ NONEV
          ∗ ( run2  ↦  #false
            ∗ run2' ↦ₛ #false
            ∗ ( run3  ↦  #false
              ∗ run3' ↦ₛ #false ∨
                run3  ↦  #true
              ∗ run3' ↦ₛ #true)
            ∨ run2  ↦  #true
            ∗ run2' ↦ₛ #true
            ∗ ( run3  ↦  #false
              ∗ run3' ↦ₛ #false ∨
                run3  ↦  #true
              ∗ run3' ↦ₛ #true)))
        ))%I).
    rel_apply (refines_na_alloc P (nroot.@"wmf_channel__both_channel_true")).
    iPoseProof (P0lr_Plr with "HP HP'") as "HP".
    iSplitL.
    { iFrame. try_close_inv. }
    iIntros "#Inv".
    rel_arrow_val.
    iIntros (v1 v2) "[%r [%eq1 [%eq2 %Hrbound]]]"; subst...
    rel_apply refines_pair; first rel_apply refines_pair.
    - rel_apply refines_na_inv; iSplit; first iAssumption.
      iIntros "[
        [
          [Hrun1 [Hrun1' H]] |
          [Hrun1 [Hrun1' [HP [Hpchan [Hpchan' [Hcchan' H]]]]]]
        ] Hclose]".
      + rel_load_l; rel_load_r...
        rel_apply refines_na_close. iFrame.
        iSplitL.
        { try_close_inv. }
        rel_vals.
      + rel_load_l; rel_load_r...
        rel_store_l; rel_store_r...
        rel_apply refines_couple_UU; first done.
        iIntros (nonce) "%Hnoncebound"; iModIntro...
        rel_store_l.
        rel_store_r...
        rel_apply (refines_senc_lr_l2 with "[HP]").
        {
          iFrame. iSplitL; first iAssumption.
          iExists _, _, _, _. repeat iSplit.
          1, 2: done.
          - iExists 1. done.
          - iExists nonce. iPureIntro; repeat split; lia.
        }
        iIntros (c c') "#Hrelcipher Hcipher"...
        rel_store_r...
        rel_apply refines_na_close.
        iFrame. iSplitL.
        {
          rewrite /P. iLeft. iFrame.
          iExists c.
          iSplitR.
          { iAssumption. }
          iSplitR; first (iPureIntro; lia).
          iDestruct "H" as "[[Hrun2 [Hrun2' H]] | [Hrun2 [Hrun2' H]]]".
          - iLeft. iPoseProof (bi.and_elim_r with "Hcipher") as "Hcipher". iFrame.
          - iRight. iFrame.
        }
        rel_vals; last iAssumption.
        iExists 0. done.
    - rel_arrow_val.
      iIntros (input1 input2) "[%id_ [%id_' [%c [%c'
        [%Hinputeq1 [%Hinputeq2 [[%id [%eqid1 %eqid2]] #Hrelcipher]]]]]]]"; subst...
      rel_apply refines_na_inv. iSplitL; first iAssumption.
      iIntros "[
        [
          [Hrun1 [Hrun1'
            [%nonce [%c_rec [%c_rec'
              [
                Hpchan [Hpchan' [[#Hrelc Hcchan]
                  [>%Hnoncebound [[Hrun2 [Hrun2' H]] | [Hrun2 [Hrun2' H]]]]
                ]]
              ]
            ]]]
          ]] |
          [Hrun1 [Hrun1' [HP [Hpchan [Hpchan' [Hcchan'
            [[Hrun2 [Hrun2' H]] | [Hrun2 [Hrun2' H]]]
          ]]]]]]
        ] Hclose]".
      + rel_load_l; rel_load_r...
        rel_apply refines_na_close.
        iFrame. iSplitL. { iFrame. iLeft.
          iFrame. iExists c_rec.
          iSplitR; first iAssumption.
          iSplitR; first (iPureIntro; lia).
          iLeft. iFrame. }
        rel_vals.
      + rel_load_l; rel_load_r...
        rel_store_l; rel_store_r...
        rel_load_r...
        rel_load_r...
        iAssert (half_lrel lrel_cipher c') as "Hcipherc'". { iRight. iExists c. done. }
        iAssert (half_lrel lrel_cipher c_rec') as "Hciphercrec'". { iRight; iExists c_rec. done. }
        iPoseProof (cipher_comparable with "[Hcipherc' Hciphercrec']") as "%Hcomparable".
        { iSplit; first iApply "Hcipherc'". iApply "Hciphercrec'". }
        rel_pure_r. clear Hcomparable.
        destruct (bool_decide (c' = c_rec')) eqn:eqc...
        * iDestruct "H" as "[Hcipher H]".
          apply bool_decide_eq_true in eqc.
          iPoseProof (lrel_cipher_eq with "Hrelcipher") as "%eqcc'"; subst.
          iPoseProof (lrel_cipher_eq with "Hrelc") as "%eqcrec'"; subst.
          rel_apply "Hcipher".
          iIntros "HP"...
          rel_load_l... 
          rel_apply refines_elem_eq_l.
          iSplitR; last iSplitR.
          { iLeft. iExists (#1, #nonce)%V. iExists _, _ , _, _.
            repeat iSplit.
            1, 2: done.
            - iExists 1. done.
            - iExists nonce. iPureIntro; repeat split; lia. }
          { iLeft. iExists (#1, #nonce)%V. iExists _, _ , _, _.
            repeat iSplit.
            1, 2: done.
            - iExists 1. done.
            - iExists nonce. iPureIntro; repeat split; lia. }
          rel_apply refines_elem_eq_r.
          iSplitR; last iSplitR.
          { iLeft. iExists (#1, #nonce)%V. iExists _, _ , _, _.
            repeat iSplit.
            1, 2: done.
            - iExists 1. done.
            - iExists nonce. iPureIntro; repeat split; lia. }
          { iLeft. iExists (#1, #nonce)%V. iExists _, _ , _, _.
            repeat iSplit.
            1, 2: done.
            - iExists 1. done.
            - iExists nonce. iPureIntro; repeat split; lia. }
          destruct (bool_decide (#nonce = #nonce)) eqn:eqnonce...
          2: { exfalso. clear -eqnonce. apply bool_decide_eq_false in eqnonce.
            apply eqnonce. reflexivity. }
          destruct (bool_decide (#id = #0)) eqn:eqid...
          -- rel_apply (refines_senc_lr_l2 with "[HP]").
            { iFrame. iSplit; first iAssumption.
              iExists _, _, _, _.
              repeat iSplit.
              1, 2: done.
              { iExists id. done. }
              iExists nonce. iPureIntro; repeat split; lia.
            }
            iIntros (newc newc') "#Hrelnewc HP".
            iPoseProof (bi.and_elim_r with "HP") as "HP".
            rel_apply refines_na_close. iFrame.
            iSplitL.
            {
              iFrame. iLeft.
              iFrame. iExists _.
              iSplitR.
              - iApply "Hrelcipher".
              - iSplitR; first (iPureIntro; lia).
                iLeft. iFrame.
            }
            rel_pures_l; rel_pures_r.
            rel_vals.
          -- rel_apply refines_na_close. iFrame.
            iSplitL.
            {
              iFrame. iLeft.
              iFrame. iExists _.
              iSplitR.
              - iApply "Hrelcipher".
              - iSplitR; first (iPureIntro; lia).
                iLeft. iFrame.
            }
            rel_vals.
        * iDestruct "H" as "[Hcipher H]".
          rel_apply (refines_couple_sdec with "[Hcipher]").
          { iPoseProof (bi.and_elim_r with "Hcipher") as "Hcipher".
            iApply "Hcipher". }
          { iAssumption. }
          { iAssumption. }
          iIntros (decr decr') "#Hreldecr HP"...
          rel_load_l...
          rel_apply refines_elem_eq_l.
          iSplitR.
          { iLeft. iExists decr'. iAssumption. }
          iSplitR.
          { iLeft. iExists (#1, #nonce)%V.
            iExists _, _, _, _. repeat iSplit.
            1, 2: done.
            1: iExists 1; done.
            iExists nonce; iPureIntro; repeat split; lia. }
          rel_apply refines_elem_eq_r.
          iSplitR.
          { iRight. iExists decr. iAssumption. }
          iSplitR...
          { iLeft. iExists (#1, #nonce)%V.
            iExists _, _, _, _. repeat iSplit.
            1, 2: done.
            1: iExists 1; done.
            iExists nonce; iPureIntro; repeat split; lia. }
          simpl.
          iDestruct "Hreldecr" as "[%id_decr1 [%id_decr2 [%c_decr [%c_decr'
            [%Hinputeq1 [%Hinputeq2 [[%id_decr [%eqid1 %eqid2]] #Hreldecr]]]]]]]"; subst...
          simpl.
          iDestruct "Hreldecr" as "[%r_decr [%eqr1 [%eqr2 %Hr_decrbound]]]"; subst...
          destruct (bool_decide (#id_decr = #1)) eqn:eqid_decr;
          destruct (bool_decide (#r_decr = #nonce)) eqn:eqr_decr; simpl;
          try rewrite eqr_decr...
          2, 3, 4: 
            rel_apply refines_na_close; iFrame; iSplitL; last rel_vals;
            iLeft; iFrame; iExists c_rec;
            iSplitR; first iAssumption; iSplitR; first (iPureIntro; lia);
            iLeft; iFrame.
          destruct (bool_decide (#id = #0)) eqn:eqid...
          -- rel_apply (refines_senc_lr_l2 with "[HP]").
            { iFrame. iSplit; first iAssumption.
              iExists _, _, _, _.
              repeat iSplit.
              1, 2: done.
              { iExists id. done. }
              iExists nonce. iPureIntro; repeat split; lia.
            }
            iIntros (newc newc') "#Hrelnewc HP".
            iPoseProof (bi.and_elim_r with "HP") as "HP".
            rel_apply refines_na_close. iFrame.
            iSplitL.
            {
              iFrame. iLeft.
              iFrame. iExists _.
              iSplitR.
              - iApply "Hrelc".
              - iSplitR; first (iPureIntro; lia).
                iLeft. iFrame.
            }
            rel_pures_l; rel_pures_r.
            rel_vals.
          -- rel_apply refines_na_close. iFrame.
            iSplitL.
            {
              iFrame. iLeft.
              iFrame. iExists _.
              iSplitR.
              - iApply "Hrelc".
              - iSplitR; first (iPureIntro; lia).
                iLeft. iFrame.
            }
            rel_vals.
      + rel_load_l; rel_load_r...
        rel_apply refines_na_close.
        iFrame. iSplitL. { iFrame. iRight.
          iFrame.
          iLeft. iFrame. }
        rel_vals.
      + rel_load_l; rel_load_r...
        rel_store_l; rel_store_r...
        rel_load_r...
        rel_apply (refines_sdec_l with "[HP]").
        { iSplitR; last iSplitR; try iAssumption.
          iLeft. iExists c'. iAssumption. }
        iIntros (msg) "_ HP"...
        rel_load_l...
        rel_apply refines_na_close. iFrame. iSplitL.
        {
          iFrame. iRight.
          iFrame. iLeft. iFrame.
        }
        rel_vals.
    - rel_arrow_val.
      iIntros (v1 v2) "Hrelcipher"...
      rel_apply refines_na_inv. iSplitL; first iAssumption.
      iIntros "[
        [
          [Hrun1 [Hrun1'
            [%nonce [%c_rec [%c_rec'
              [
                Hpchan [Hpchan' [[#Hrelc Hcchan]
                  [>%Hnoncebound [[Hrun2 [Hrun2' H]] | [Hrun2 [Hrun2' H]]]]
                ]]
              ]
            ]]]
          ]] |
          [Hrun1 [Hrun1' [HP [Hpchan [Hpchan' [Hcchan'
            [[Hrun2 [Hrun2' H]] | [Hrun2 [Hrun2' H]]]
          ]]]]]]
        ] Hclose]".
      + iDestruct "H" as "[HP [[Hrun3 Hrun3'] | [Hrun3 Hrun3']]]";
        rel_load_l; rel_load_r; last (rel_store_l; rel_store_r)...
        all: rel_apply refines_na_close; iFrame; iSplitL; last rel_vals.
        all: iFrame; iLeft; iFrame; iExists c_rec;
          iSplitR; first iAssumption; iSplitR; first (iPureIntro; lia).
        all: iLeft; iFrame; iLeft; iFrame.
      + iDestruct "H" as "[HP [[Hrun3 Hrun3'] | [Hrun3 Hrun3']]]";
        rel_load_l; rel_load_r; last (rel_store_l; rel_store_r)...
        all: rel_apply refines_na_close; iFrame; iSplitL; last rel_vals.
        all: iFrame; iLeft; iFrame; iExists c_rec;
          iSplitR; first iAssumption; iSplitR; first (iPureIntro; lia).
        all: iRight; iFrame; iLeft; iFrame.
      + iDestruct "H" as "[[Hrun3 Hrun3'] | [Hrun3 Hrun3']]";
        rel_load_l; rel_load_r; last (rel_store_l; rel_store_r)...
        all: rel_apply refines_na_close; iFrame; iSplitL; last rel_vals.
        all: iFrame; iRight; iFrame.
        all: iLeft; iFrame; iLeft; iFrame.
      + iDestruct "H" as "[[Hrun3 Hrun3'] | [Hrun3 Hrun3']]";
        rel_load_l; rel_load_r; last (rel_store_l; rel_store_r)...
        all: rel_apply refines_na_close; iFrame; iSplitL; last rel_vals.
        all: iFrame; iRight; iFrame.
        all: iRight; iFrame; iLeft; iFrame.
  Qed.

  (* TODO now reduce to IND-CCA *)


End logrel.