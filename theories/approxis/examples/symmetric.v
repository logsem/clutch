From clutch.approxis Require Import approxis map list.
From clutch.approxis Require Export bounded_oracle.
Set Default Proof Using "Type*".

Section symmetric.

  (** A symmetric encryption [scheme] is given by three functions (keygen, encrypt, decrypt).

The set of keys, messages, and ciphertexts are modelled by finite sets of integers [0, Key], [0, Input], and [0, Output].
   *)

  Class SYM_params :=
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
  Class SYM `{SYM_params} :=
    { keygen : val
    ; enc : val
    ; dec : val
    ; rand_cipher : val
    ; sym_scheme : val := (sym_params, keygen, enc, dec, rand_cipher)%V
    }.

  Definition get_params : val := λ:"sym_scheme", Fst (Fst (Fst (Fst "sym_scheme"))).
  Definition get_card_key : val := λ:"sym_scheme", Fst (Fst (Fst (Fst (Fst (Fst "sym_scheme"))))).
  Definition get_card_message : val := λ:"sym_scheme", Snd (Fst (Fst (Fst (Fst (Fst "sym_scheme"))))).
  Definition get_card_cipher : val := λ:"sym_scheme", Snd (Fst (Fst (Fst (Fst "sym_scheme")))).
  Definition get_keygen : val := λ:"sym_scheme", Snd (Fst (Fst (Fst "sym_scheme"))).
  Definition get_enc : val := λ:"sym_scheme", Snd (Fst (Fst ("sym_scheme"))).
  Definition get_dec : val := λ:"sym_scheme", Snd (Fst "sym_scheme").
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
          let: "key" := get_keygen "scheme" #() in
          (* let: "enc_key" := enc "scheme" "key" in *)
          if: "b" then
            (* "enc_key" *)
            get_enc "scheme" "key"
          else
            get_rand_cipher "scheme" in
        let: "oracle" := q_calls (get_card_message "scheme") "Q" "rr_key_b" in
        let: "b'" := "adv" "oracle" in
        "b'".

    Definition CPA_real : val :=
      λ:"scheme" "Q",
        let: "key" := get_keygen "scheme" #() in
        q_calls (get_card_message "scheme") "Q" (get_enc "scheme" "key").

    (* TODO this should just use `rand` instead of get_rand_cipher. *)
    Definition CPA_rand : val :=
      λ:"scheme" "Q",
        q_calls (get_card_message "scheme") "Q" (get_rand_cipher "scheme").

  End CPA.

End symmetric.
