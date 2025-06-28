(* CPA security of a PRF based symmetric encryption scheme. *)
From clutch.approxis Require Import approxis list.
From clutch.approxis.examples Require Import symmetric_init security_aux option xor.
Set Default Proof Using "Type*".

Section defs.

  (** We will prove one time CPA security of one time pad.

    References for the encryption scheme:
      Claim 2.7, Mike Rosulek, 2020, The Joy of Cryptography.
*)

  (** Upper bound of messages. *)
  Variable N : nat.

  Let Message := N.
  Let Key := N.
  Let Output := N.
  Let Cipher := N.

  Local Opaque INR.

  (** Parameters of the generic PRF-based encryption scheme. *)
  Variable xor_struct : XOR (Key := Message) (Support := Cipher).

  (** We specialize the construction to an idealized random function family. *)
  Definition otp_keygen : val := λ:<>, rand #Key.
  Definition otp_keygen_tape : val := λ: "α" <>, rand("α") #Key.
  Definition otp_enc : val :=
    λ: "key" "msg", xor "msg" "key".
  Definition otp_enc_delay : val :=
    λ: "α" <> "msg", let: "key" := rand("α") #Key in xor "msg" "key".
  Definition otp_rand_cipher : val :=
    λ: <>, rand #Output. (* let:"o" := rand #Output in "o". *)
  Definition otp_rand_cipher_tape : expr :=
    let: "β" := alloc #Output in
    λ: <>, rand("β") #Output. (* let:"o" := rand(#lbl:β) #Output in "o". *)
  Definition otp_dec : val :=
    λ: "key" "c", xor "c" "key".
  
  Definition otp_scheme : expr :=
    (otp_keygen, otp_enc, otp_dec).
  Definition otp_scheme_tape : expr :=
    let: "α" := alloc #Key in
    (otp_keygen_tape "α", otp_enc, otp_dec).
  Definition otp_scheme_delay : expr :=
    let: "α" := alloc #Key in
    (otp_keygen, otp_enc_delay "α", otp_dec).

  Local Instance SYM_otp_param : SYM_init_params :=
    {| card_key := Key ; card_message := Message ; card_cipher := Cipher |}.
  Local Instance SYM_otp_scheme : SYM_init :=
    {| enc_scheme := otp_scheme
      ; rand_cipher := otp_rand_cipher |}.

  Definition sym_scheme_tape : expr :=
    (sym_params, (λ: <>, otp_scheme_tape)%V, otp_rand_cipher_tape)%E.
  Definition sym_scheme_delay : expr :=
    (sym_params, (λ: <>, otp_scheme_delay)%V, otp_rand_cipher)%E.

  (** RandML types of the scheme. *)
  Definition TMessage := TInt.
  Definition TKey := TInt.
  Definition TInput := TInt.
  Definition TOutput := TInt.
  Definition TCipher := TOutput.

  Section Correctness.
    Context `{!approxisRGS Σ}.
    Variable xor_spec : XOR_spec.

    Theorem otp_scheme_correct :
      ⊢ refines top
        (let: "otp_scheme" := (get_enc_scheme sym_scheme) #() in
        let: "otp_enc" := get_enc "otp_scheme" in
        let: "otp_dec" := get_dec "otp_scheme" in
        let: "otp_keygen" := get_keygen "otp_scheme" in
        let: "k" := otp_keygen #() in
        λ: "msg",
          "otp_dec" "k" ("otp_enc" "k" "msg"))
        (λ: "msg", "msg") (lrel_int_bounded 0 Message → lrel_int_bounded 0 Output).
    Proof with rel_pures_l; rel_pures_r.
      rewrite /get_enc_scheme...
      rewrite /otp_scheme...
      rewrite /get_enc/get_dec/get_keygen...
      rewrite /otp_keygen...
      rel_apply refines_randU_l.
      iIntros (k Hkbound)...
      rewrite /otp_dec...
      rewrite /otp_enc...
      rel_arrow_val.
      iIntros (v1 v2 [msg [eq1 [eq2 Hxbound]]]); subst...
      rel_apply xor_correct_l; try lia...
      rel_apply xor_correct_l; try lia.
      { rewrite Nat2Z.id. apply xor_dom; lia. }
      rewrite Nat2Z.id. rewrite xor_sem_inverse_r; try lia.
      rewrite Z2Nat.id; last lia. rel_vals.
    Qed.

  End Correctness.

  (** We will prove CPA security of the scheme using the idealised random
      function. We assume that the adversaries are well-typed. *)
  Variable adv : val.
  Definition TAdv := ((TMessage → (TOption TCipher)) → TBool)%ty.
  Variable adv_typed : (∅ ⊢ₜ adv : TAdv).

  Section proofs.
    Context `{!approxisRGS Σ}.
    Variable xor_spec : XOR_spec.

    (* (* TODO Make it so that `iFrame "ε"` generates the obligation `ε = ε'`.
       Currently, one has to write the equation or apply ec_eq manually. *)
    Local Instance ec_frame_eq ε ε' :
      ε = ε' ->
      Frame false (↯ ε) (↯ ε') emp | 0.
    Proof.
      intros ->. simpl. iIntros "[??]". iFrame.
    Defined. *)

    Lemma otp_otp_delay (Q : nat) :
      ⊢ (REL (CPA #true adv sym_scheme #1) <<
        (CPA #true adv sym_scheme_delay #1) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
      rewrite /sym_scheme/sym_scheme_delay...
      rewrite /CPA...
      rewrite /get_enc_scheme...
      rewrite /otp_scheme/otp_scheme_delay...
      rewrite /get_keygen...
      rewrite /otp_keygen...
      rel_alloctape_r α as "Hα".
      rel_apply refines_couple_UT; first done; iFrame.
      iModIntro. iIntros (k Hkbound) "Hα". simpl...
      rewrite /otp_enc_delay...
      rel_apply refines_randU_r.
      iIntros (k_dummy Hkdummybound)...
      rewrite /get_enc...
      rewrite /otp_enc...
      rel_bind_l (q_calls _ _ _).
      rel_bind_r (q_calls _ _ _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_apply refines_app.
        - rel_arrow_val. iIntros (v1 v2) "Hrel"... rel_vals.
        - rel_apply (refines_app _ _ _ _ (interp (TMessage → (TOption TCipher)) [])).
          + iPoseProof refines_typed as "Hrel"; first apply adv_typed.
            Unshelve. 3: exact []. 2 : shelve.
            rel_apply "Hrel".
          + rel_vals. 
      }
      rewrite /get_card_message...
      rewrite /q_calls...
      rel_alloc_l cnt as "Hcnt".
      rel_alloc_r cnt' as "Hcnt'"...
      set (P := (
        cnt ↦ #0 ∗ cnt' ↦ₛ #0 ∗ α↪ₛN(Key;[k]) ∨
        cnt ↦ #1 ∗ cnt' ↦ₛ #1 ∗ α↪ₛN(Key;[])
      )%I).
      rel_apply (refines_na_alloc P (nroot.@"otp_is_OTCPA_tape")).
      iSplitL; first (iLeft; iFrame).
      iIntros "#Inv".
      rel_arrow_val. iIntros (v1 v2 [msg [eq1 eq2]]); subst...
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[[Hcnt [Hcnt' Hα]]|[Hcnt [Hcnt' Hα]]] Hclose]".
      - rel_load_l; rel_load_r...
        case_bool_decide as Hmsgpos; simpl; first case_bool_decide as Hmsgbound;
        [|rel_pures_l; rel_pures_r;
          rel_apply refines_na_close; iFrame; iSplitL; first (iLeft; iFrame);
          rel_vals
         |rel_pures_l; rel_pures_r;
          rel_apply refines_na_close; iFrame; iSplitL; first (iLeft; iFrame);
          rel_vals].
        rel_load_l; rel_load_r... replace (0+1)%Z with 1%Z by lia.
        rel_store_l; rel_store_r... rel_apply (refines_randT_r with "Hα").
        iIntros "Hα _"...
        rel_apply refines_na_close. iFrame. iSplitL; first (iRight; iFrame).
        rel_apply xor_correct_l; try lia.
        rel_apply xor_correct_r; try lia...
        rel_vals.
      - rel_load_l; rel_load_r... rel_apply refines_na_close; iFrame.
        iSplitL; first (iRight; iFrame). rel_vals.
    Qed.

    Theorem otp_is_OTCPA_tape (Q : nat) :
      ⊢ (REL (CPA #true adv sym_scheme_delay #1) <<
        (CPA #false adv sym_scheme_tape #1) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
      rewrite /sym_scheme_tape/sym_scheme_delay...
      rewrite /otp_rand_cipher_tape...
      rel_alloctape_r β as "Hβ".
      rewrite /CPA...
      rewrite /get_enc_scheme/get_keygen...
      rewrite /otp_scheme_tape/otp_scheme_delay...
      rel_alloctape_l α as "Hα"...
      rel_alloctape_r α' as "Hα'"...
      rewrite /otp_keygen_tape/otp_enc_delay/otp_keygen...
      rel_apply refines_randU_l... iIntros (kdummyl _).
      rel_apply refines_randT_empty_r. iFrame. iIntros (kdummyr) "Hα' _"...
      rewrite /get_enc... rewrite /otp_enc...
      rewrite /get_rand_cipher...
      rel_bind_l (q_calls _ _ _).
      rel_bind_r (q_calls _ _ _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_apply refines_app.
        - rel_arrow_val. iIntros (v1 v2) "Hrel"... rel_vals.
        - rel_apply (refines_app _ _ _ _ (interp (TMessage → (TOption TCipher)) [])).
          + iPoseProof refines_typed as "Hrel"; first apply adv_typed.
            Unshelve. 3: exact []. 2 : shelve.
            rel_apply "Hrel".
          + rel_vals. 
      }
      rewrite /get_card_message...
      rewrite /q_calls...
      rel_alloc_l cnt as "Hcnt".
      rel_alloc_r cnt' as "Hcnt'"...
      set (P := (
        cnt ↦ #0 ∗ cnt' ↦ₛ #0 ∗ α↪N(Output;[]) ∗ α'↪ₛN(Output;[]) ∗ β↪ₛN(Output;[]) ∨
        cnt ↦ #1 ∗ cnt' ↦ₛ #1 ∗ α↪N(Output;[]) ∗ α'↪ₛN(Output;[]) ∗ β↪ₛN(Output;[])
      )%I).
      rel_apply (refines_na_alloc P (nroot.@"otp_is_OTCPA_tape")).
      iSplitL; first (iLeft; iFrame).
      iIntros "#Inv".
      rel_arrow_val. iIntros (v1 v2 [msg [eq1 eq2]]); subst...
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[[Hcnt [Hcnt' [Hα [Hα' Hβ]]]]|[Hcnt [Hcnt' Htapes]]] Hclose]".
      - rel_load_l. rel_load_r...
        case_bool_decide as Hxpos; simpl; first (case_bool_decide as Hxbound);
        [|rel_pures_l; rel_pures_r; rel_apply refines_na_close;
          iFrame; iSplitL; first (iLeft; iFrame); rel_vals
         |rel_pures_l; rel_pures_r; rel_apply refines_na_close;
         iFrame; iSplitL; first (iLeft; iFrame); rel_vals].
        rel_load_l; rel_load_r... replace (0+1)%Z with 1%Z by lia.
        rel_store_l; rel_store_r...
        eremember (f_inv (xor_sem (Z.to_nat msg))) as xor_inv_l eqn:eqxorinv.
        Unshelve. 5: { eapply bij_surj. }
        Unshelve. 5: { apply xor_bij. }
        rel_apply (refines_couple_TT_frag N N xor_inv_l); first lia.
        { rewrite eqxorinv. eapply fin.f_inv_restr. intros * H. apply xor_dom; lia. }
        iSplitL "Hα"; first iApply "Hα".
        iSplitL "Hβ"; first iApply "Hβ".
        iIntros (k Hkbound).
        simpl.
        assert (∃ m : nat, (m ≤ N ∧ xor_inv_l m = k)).
        { exists (xor_sem (Z.to_nat msg) k). split.
          - apply le_S_n.
            apply (xor_dom (Z.to_nat msg)); lia.
          - rewrite eqxorinv. apply f_inv_cancel_l.
            eapply bij_inj.
            Unshelve. 
            + rewrite eqxorinv.
              rewrite /Inj. intros * Heq.    
              erewrite <- (f_inv_cancel_r (xor_sem (Z.to_nat msg))). symmetry.
              erewrite <- (f_inv_cancel_r (xor_sem (Z.to_nat msg))).
              Unshelve. 5: { eapply bij_surj. }
              8: { eapply bij_surj. }
              Unshelve. 8: { apply xor_bij. }
              5: { apply xor_bij. }
              rewrite -Heq. reflexivity.
            + apply xor_bij.
          }
        case_bool_decide as Hbool.
        2:{ exfalso. apply Hbool. apply H. }          
        iIntros (k') "[Hα [Hβ [%Hkbound' %Hk'bound]]]".
        rel_apply refines_randT_l; iFrame. iModIntro. iIntros "Hα _"...
        rel_apply (refines_randT_r with "Hβ"). iIntros "Hβ _"...
        rewrite eqxorinv.
        rel_apply xor_correct_l; try lia.
        { rewrite /Cipher. apply fin.f_inv_restr; last lia.
          intros n Htmp. apply xor_dom; lia. }
        rewrite f_inv_cancel_r.
        rel_apply refines_na_close. iFrame.
        iSplitL; first (iRight; iFrame)...
        rel_vals.
      - rel_load_l; rel_load_r...
        rel_apply refines_na_close. iFrame.
        iSplitL; first iRight; iFrame. rel_vals.
    Qed.

    (* Theorem otp_is_OTCPA' :
      ⊢ (REL (CPA #false adv sym_scheme #1) <<
        (CPA #true adv sym_scheme #1) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).

  Admitted. *)

    Lemma otp_tape_otp (Q : nat) :
        ⊢ (REL (CPA #false adv sym_scheme_tape #1) <<
          (CPA #false adv sym_scheme #1) : lrel_bool).
    Proof with (rel_pures_l ; rel_pures_r).
      rewrite /sym_scheme_tape/sym_scheme...
      rewrite /otp_rand_cipher_tape...
      rel_alloctape_l β as "Hβ".
      rewrite /CPA...
      rewrite /get_enc_scheme/get_keygen...
      rewrite /otp_scheme_tape/otp_scheme...
      rel_alloctape_l α as "Hα"...
      rewrite /otp_keygen_tape/otp_enc_delay/otp_keygen...
      rel_apply refines_randT_empty_l; iFrame.
      iModIntro. iIntros (kdummy1) "Hα %Hkdummy1bound"...
      rel_apply refines_randU_r; iFrame.
      iIntros (kdummy2 Hkdummy2bound)...
      rewrite /get_rand_cipher...
      rel_bind_l (q_calls _ _ _).
      rel_bind_r (q_calls _ _ _).
      rel_apply (refines_bind with "[-]").
      2:{
        iIntros (v v') "Hrel"...
        rel_apply refines_app.
        - rel_arrow_val. iIntros (v1 v2) "Hrel"... rel_vals.
        - rel_apply (refines_app _ _ _ _ (interp (TMessage → (TOption TCipher)) [])).
          + iPoseProof refines_typed as "Hrel"; first apply adv_typed.
            Unshelve. 3: exact []. 2 : shelve.
            rel_apply "Hrel".
          + rel_vals. 
      }
      rewrite /get_card_message...
      rewrite /q_calls...
      rel_alloc_l cnt as "Hcnt".
      rel_alloc_r cnt' as "Hcnt'"...
      set (P := (
        cnt ↦ #0 ∗ cnt' ↦ₛ #0 ∗ α↪N(Key;[]) ∗ β↪N(Output;[]) ∨
        cnt ↦ #1 ∗ cnt' ↦ₛ #1 ∗ α↪N(Key;[]) ∗ β↪N(Output;[])
      )%I).
      rel_apply (refines_na_alloc P (nroot.@"otp_is_OTCPA_tape")).
      iSplitL; first (iLeft; iFrame).
      iIntros "#Inv".
      rel_arrow_val. iIntros (v1 v2 [msg [eq1 eq2]]); subst...
      rel_apply refines_na_inv; iSplitL; first iAssumption.
      iIntros "[[[Hcnt [Hcnt' [Hα Hβ]]]|[Hcnt [Hcnt' Htapes]]] Hclose]".
      - rel_load_l. rel_load_r...
        case_bool_decide as Hxpos; simpl; first (case_bool_decide as Hxbound);
        [|rel_pures_l; rel_pures_r; rel_apply refines_na_close;
          iFrame; iSplitL; first (iLeft; iFrame); rel_vals
         |rel_pures_l; rel_pures_r; rel_apply refines_na_close;
         iFrame; iSplitL; first (iLeft; iFrame); rel_vals].
        rel_load_l; rel_load_r... replace (0+1)%Z with 1%Z by lia.
        rel_store_l; rel_store_r...
        rewrite /otp_rand_cipher...
        rel_apply refines_couple_TU; first done.
        iFrame.
        iIntros (r Hrbound) "Hβ"; simpl.
        rel_apply refines_randT_l; iFrame.
        iModIntro; iIntros "Hβ %Hbbound"...
        rel_apply refines_na_close. iFrame.
        iSplitL; first iRight; iFrame. rel_vals.
      - rel_load_l; rel_load_r...
        rel_apply refines_na_close. iFrame.
        iSplitL; first iRight; iFrame. rel_vals.
    Qed.

  End proofs.

End defs.