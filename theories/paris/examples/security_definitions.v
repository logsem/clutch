From clutch Require Import lib.flip.
From clutch.paris Require Import paris map list.
Set Default Proof Using "Type*".


Section bounded_oracle.
  Local Opaque INR.

  (** Bounded Oracles *)
  Definition q_calls (MAX : Z) : val :=
    λ:"Q" "f" "g",
      let: "counter" := ref #0 in
      λ:"x", if: (BinOp AndOp (! "counter" < "Q") (BinOp AndOp (#0 ≤ "x") ("x" < #MAX)))
             then ("counter" <- !"counter" + #1 ;; "f" "x")
             else "g" "x".
End bounded_oracle.


Section symmetric.

  (** A symmetric encryption [scheme] is given by three functions (keygen, encrypt, decrypt).

The set of keys, messages, and ciphertexts are modelled by finite sets of integers [0, Key], [0, Input], and [0, Output].
   *)

  Variable Key Message Cipher : nat.

  Let keygen scheme : expr := Fst scheme.
  Let enc scheme : expr := Fst (Snd scheme).
  Let rand_cipher scheme : expr := Snd (Snd scheme).

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


    Let q_calls := q_calls Message.
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

  End CPA.

End symmetric.

Section PRF.

  Variable Key Input Output : nat.

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

End PRF.
