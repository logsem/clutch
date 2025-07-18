From clutch.approxis Require Import approxis map list linked_list.
From clutch.approxis Require Export bounded_oracle.
Set Default Proof Using "Type*".

Section symmetric.

  Context `{approxisRGS Σ}.

  (** A symmetric encryption [scheme] is given by three functions (keygen, encrypt, decrypt).

The set of keys, messages, and ciphertexts are modelled by finite sets of integers [0, Key], [0, Input], and [0, Output].
   *)

  Class SYM_init_params :=
    { card_key : nat
    ; card_message : nat
    ; card_cipher : nat
    ; sym_params : val := (#card_key, #card_message, #card_cipher) }.

  (* Variable Key Message Cipher : nat. *)

  (* Let keygen scheme : expr := Fst scheme.
     Let enc scheme : expr := Fst (Snd scheme).
     Let rand_cipher scheme : expr := Snd (Snd scheme). *)

  Definition get_param_card_key : val := λ:"sym_params", Fst (Fst "sym_params").
  Definition get_param_card_message : val := λ:"sym_params", Snd (Fst "sym_params").
  Definition get_param_card_cipher : val := λ:"sym_params", Snd "sym_params".

  (* rand_cipher is currently unused ; it would be useful if a SYM module had
   abstract types. *)
  (* enc_scheme can be any expression that reduces to a triplet of the form:
  `(keygen, (enc, dec))%V`. This way we can initialize a local state that can
  be shared between the three functions.
  We thunk `enc_scheme`, this way, it doesn't have to be evaluated every time
  we want to access a parameter or `rand_cipher`.
  For now, the state is also shared with `keygen`, we'll see if it's relevant.
  *)
  Class SYM_init `{SYM_init_params} :=
    { keygen : val
    ; enc_scheme : expr
    ; rand_cipher : val
    ; sym_scheme : val := (sym_params, (keygen, λ: <>, enc_scheme), rand_cipher)%V
    }.

  (* `get_keygen`, `get_enc` and `get_dec` shoudl now be called with an
   encryption scheme i.e. only the tuple of these three, this ensures
   the state is shared between them *)
  Definition get_params : val := λ:"sym_scheme", Fst (Fst "sym_scheme").
  Definition get_card_key : val := λ:"sym_scheme", Fst (Fst (Fst (Fst "sym_scheme"))).
  Definition get_card_message : val := λ:"sym_scheme", Snd (Fst (Fst (Fst "sym_scheme"))).
  Definition get_card_cipher : val := λ:"sym_scheme", Snd (Fst "sym_scheme").
  Definition get_enc_scheme : val := λ:"sym_scheme", Snd (Snd (Fst "sym_scheme")).
  Definition get_keygen : val := λ:"sym_scheme", Fst (Snd (Fst "sym_scheme")).
  Definition get_enc : val := λ:"enc_scheme", Fst "enc_scheme".
  Definition get_dec : val := λ:"enc_scheme", Snd "enc_scheme".
  Definition get_rand_cipher : val := λ:"sym_scheme", Snd "sym_scheme".

  Section CPA.

    (** Indistinguishability of Chosen Plaintext Attacks security
      for symmetric/private key encryption.

Real vs random variant (sometimes called "CPA$").

References:
- Definition 7.2, Mike Rosulek, 2020, The Joy of Cryptography.
- Definition 3.22, Jonathan Katz and Yehuda Lindell, 2021, Introduction to Modern Cryptography (3rd edition).

Our definition deviates from Rosulek's and Katz/Lindell in that we wrap the encryption oracle with [q_calls] to enforce the bound [Q] on the number of oracle calls, while loc. cit. rely on the assumption that the adversary runs in polynomial time in the security parameter.

Our definition further differs from Katz/Lindell in that, depending on the value of [b], the encryption oracle either encrypts the adversary's message or return a random ciphertext, whereas in Katz/Lindell, the encryption oracle encrypts one of two messages provided by the adversary. These two notions are equivalent by Claim 7.3 in Rosulek's book.
     *)

    Definition CPA : val :=
      λ:"b" "adv" "scheme" "Q",
        let: "rr_key_b" :=
          let: "enc_scheme" := get_enc_scheme "scheme" #() in
          let: "key" := get_keygen "scheme" #() in
          (* let: "enc_key" := enc "scheme" "key" in *)
          if: "b" then
            (* "enc_key" *)
            get_enc "enc_scheme" "key"
          else
            get_rand_cipher "scheme" in
        let: "oracle" := q_calls (get_card_message "scheme") "Q" "rr_key_b" in
        let: "b'" := "adv" "oracle" in
        "b'".

    Definition CPA_real : val :=
      λ:"scheme" "Q",
        let: "enc_scheme" := get_enc_scheme "scheme" #() in
        let: "key" := get_keygen "scheme" #() in
        q_calls (get_card_message "scheme") "Q" (get_enc "enc_scheme" "key").

    (* TODO this should just use `rand` instead of get_rand_cipher. *)
    Definition CPA_rand : val :=
      λ:"scheme" "Q",
        q_calls (get_card_message "scheme") "Q" (get_rand_cipher "scheme").

  End CPA.

End symmetric.

Module CPA_sem.

  Definition CPA_real : val :=
    λ:"scheme" "Q",
      let: "enc_scheme" := get_enc_scheme "scheme" #() in
      let: "key" := get_keygen "scheme" #() in
      q_calls_poly #() #() "Q" (get_enc "enc_scheme" "key").

  (* TODO this should just use `rand` instead of get_rand_cipher. *)
  Definition CPA_rand : val :=
    λ:"scheme" "Q",
      q_calls_poly #() #() "Q" (get_rand_cipher "scheme").

End CPA_sem.

Section INT_PTXT.

  (** Integrity of plaintexts game for symmetric encryption
    References:
    - Daniel Jost, 2018, Christian Badertscher, Fabio Banfi,
      A note on the equivalence of IND-CCA & INT-PTXT and IND-CCA & INT-CTXT 
    - Nicolas Klose, 2021, Characterizing Notions For Secure Cryptographic Channels
    - Mihir Bellare, Chanathip Namprempre, 2007,
      Authenticated Encryption: Relations among notions
      and analysis of the generic composition paradigm *)
  
  Variable is_plaintext : val.
  Variable is_ciphertext : val.

  Variable elem_eq : val.

  Definition PTXT : val :=
    λ: "b" "adv" "scheme" "Q_enc" "Q_dec" "Q_lr",
      let: "record_plaintext" := init_linked_list #() in
      let: "enc_scheme" := get_enc_scheme "scheme" #() in
      let: "enc" := get_enc "enc_scheme" in
      let: "dec" := get_dec "enc_scheme" in
      let: "key" := get_keygen "scheme" #() in
      let: "enc_key" := λ: "msg", add_list "record_plaintext" "msg";;
        "enc" "key" "msg" in
      let: "dec_key" := λ: "msg", "dec" "key" "msg" in
      let: "rr_key_b" :=
        if: "b" then
          λ: "c", 
          let: "decrypted'" := "dec" "key" "c" in
          elem_of_linked_list elem_eq "record_plaintext" "decrypted'"
        else
          λ: <>, #true in
      let: "oracle_enc" := q_calls_general_test is_plaintext "Q_enc" "enc_key" in
      let: "oracle_dec" := q_calls_general_test_eager is_ciphertext "Q_dec" "dec_key" in
      let: "oracle_lr" := q_calls_general_test is_ciphertext "Q_lr" "rr_key_b" in
      let: "b'" := "adv" "oracle_enc" "oracle_dec" "oracle_lr" in
      "b'".

  Context `{!approxisRGS Σ}.

  Section lrel_types_defs.

  Variable lrel_msg : lrel Σ.
  Variable lrel_cipher : lrel Σ.

  Definition lrel_enc_oracle : lrel Σ :=
    lrel_msg → (() + lrel_cipher).
    
  Definition lrel_dec_oracle : lrel Σ :=
    lrel_cipher → (() + lrel_msg).
    
  Definition lrel_oracle_lr : lrel Σ :=
    lrel_cipher → (() + lrel_bool).

  Definition lrel_adv : lrel Σ :=
    lrel_enc_oracle → lrel_dec_oracle → lrel_oracle_lr → lrel_bool.

  End lrel_types_defs.

End INT_PTXT.