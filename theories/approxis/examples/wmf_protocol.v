From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From clutch.prob_lang Require Import advantage typing.tychk.
From clutch.approxis Require Import map reltac2 approxis option.
From clutch.approxis.examples Require Import
  security_aux option symmetric_init
  bounded_oracle pubkey advantage_laws iterable_expression.
From clutch.approxis.examples Require
  kemdem_hybrid_cpa_generic.
From mathcomp Require Import ssrbool.
Set Default Proof Using "All".
Import map.

Section defs.

  (*
    A → S : (A,{B, n}_ka)
    S → B : {A, n}_kb
  *)
  (* security parameter *)
  Variable η : nat.

  Let N := 2^η - 1.

  Variable Key : nat.
  Variable Output : nat.

  #[local] Instance sym_params_wmf : SYM_init_params := {|
      card_key := Key
    ; card_message := N
    ; card_cipher := Output
  |}.

  Context `{sym : !SYM_init}.

  Definition init_scheme (e : expr) : expr :=
    let: "scheme" := symmetric_init.get_enc_scheme symmetric_init.sym_scheme
      #() in
    e "scheme".


  Definition is_plaintext_inst : val :=
    λ: "params" "x",
        (Fst "x" = #0 `or` Fst "x" = #1)
      `and` #0 ≤ Snd "x"
      `and` Snd "x" ≤ symmetric_init.get_card_cipher "params".

  Definition q_calls : val :=
    λ: "test_is_plaintext" "Q" "f",
      let: "counter" := ref #0 in
      λ:"x", if: (BinOp AndOp (! "counter" < "Q") ("test_is_plaintext" "x"))
            then ("counter" <- !"counter" + #1 ;; SOME ("f" "x"))
            else NONEV.

  Definition CPA' : val :=
    λ:"b" "adv" "scheme" "Q",
      let: "enc_scheme" := get_enc_scheme "scheme" #() in
      let: "enc" := get_enc "enc_scheme" in
      let: "rr_key_b" :=
        let: "key" := get_keygen "scheme" #() in
        (* let: "enc_key" := enc "scheme" "key" in *)
        if: "b" then
          (* "enc_key" *)
          λ: "msg", "enc" "key" "msg"
        else
          get_rand_cipher "scheme" in
      let: "oracle" := q_calls (is_plaintext_inst sym_params) "Q" "rr_key_b" in
      let: "b'" := "adv" "enc" "oracle" in
      "b'".

  Section SeveralSessionsAgents.

    (* agent name *)
    (* Variable A : val.
    Variable lrel_msg : lrel Σ.
    Hypothesis test : ⊢ (lrel_car (lrel_nat → lrel_nat → lrel_nat → lrel_msg)) A A. *)


    (* FIXME when considering it, remove argument `A` and de-comment `Variable` *)
    Definition a_to_s A : val := 
      λ: "b" "nonce_count" "senc",
      λ: "i" "j" "k",
        if: get "nonce_count" ("i", "j", "k") = #false then
          set "nonce_count" ("i", "j", "k") #true;;
          if: "b" then
            λ: "ka",
              ((A "i", "senc" ("ka" "i") (A "j", rand #N)), "r_adv")
          else
            λ: "ka",
              ((A "i", "senc" ("ka" "i") (A "j", "r_adv")), "r_adv")
        else #().
    Definition s_to_b A : val :=
      λ: "b" "nonce_count" "senc" "sdec",
      λ: "i" "j" "k",
        if: get "nonce_count" ("i", "j", "k") = #false then
          set "nonce_count" ("i", "j", "k") #true;;
          λ: "ka" "input",
            let: "nonce" := "sdec" "ka" (Snd "input") in
            let: "sender" := Fst "input" in
            let: "dest" := Fst "nonce" in
            let: "nonce" := Snd "nonce" in
            if: "sender" = A "i" `and` "dest" = A "j" then
              "senc" ("ka" "j") ("sender", "nonce")
            else #()
        else #().

    (* may not be correct *)
    Definition b_recv : val :=
      λ: "b" "nonce_count" "kb", (* parameters of the protocol *)
        λ: "input", #().
          (* let: "nonce" := "sdec" "kb" "input" in
          let: "sender" := Fst "nonce" in
          let: "nonce" := Snd "nonce" in
          if: "sender" = #0 then
            #()
          else #(). *)
  
  End SeveralSessionsAgents.

  Section Once.

    Definition a_to_s_once : val :=
      λ: "A" "B" "b" "senc" "ka", (* parameters of the protocol *)
        let: "run" := ref #true in
        λ: "r_adv", (* attacker provided random *)
          if: ! "run" then
          "run" <- #false;;
            SOME
              (if: "b" then
                ("A", "senc" "ka" ("B", rand #N))
              else
                ("A", "senc" "ka" ("B", "r_adv")))
          else
            NONE.

    Definition s_to_b_once : val :=
      λ: "A" "B" "b" "senc" "sdec" "ka" "kb", (* parameters of the protocol *)
        let: "run" := ref #true in
        λ: "input",
          if: ! "run" then
            "run" <- #false;;
            let: "nonce" := "sdec" "ka" (Snd "input") in
            let: "sender" := Fst "input" in
            let: "dest" := Fst "nonce" in
            let: "nonce" := Snd "nonce" in
            if: "sender" = "A" `and` "dest" = "B" then
              SOME ("senc" "kb" ("sender", "nonce"))
            else NONE
          else
            NONE.

    Definition b_recv_once : val :=
      λ: "A" "B" "b" "kb", (* parameters of the protocol *)
        let: "run" := ref #true in
        λ: "input",
          if: ! "run" then "run" <- #false;; SOME #() else NONE.
          (* let: "nonce" := "sdec" "kb" "input" in
          let: "sender" := Fst "nonce" in
          let: "nonce" := Snd "nonce" in
          if: "sender" = #0 then
            #()
          else #(). *)
  
  End Once.

  Section Dishonest.

    Definition s_to_b_maybe_d_once : val :=
      λ: "A" "B" "Bd" "b" "senc" "sdec" "ka" "kb" "kbd", (* parameters of the protocol *)
        let: "run" := ref #true in
        λ: "input",
          if: ! "run" then
            "run" <- #false;;
            let: "nonce" := "sdec" "ka" (Snd "input") in
            let: "sender" := Fst "input" in
            let: "dest" := Fst "nonce" in
            let: "nonce" := Snd "nonce" in
            if: "sender" = "A" `and` "dest" = "B" then
              SOME ("senc" "kb" ("sender", "nonce"))
            else if: "sender" = "A" `and` "dest" = "Bd" then
              SOME ("senc" "kbd" ("sender", "nonce"))
            else NONE
          else
            NONE.
  
  End Dishonest.

  Section Once_eav.

    Definition a_to_s_once_eav : val :=
      λ: "b" "senc" "ka", (* parameters of the protocol *)
        λ: "r_adv", (* attacker provided random *)
          if: "b" then
            (#0, "senc" "ka" (#1, rand #N))
          else
            (#0, "senc" "ka" (#1, "r_adv")).

    Definition s_to_b_once_eav : val :=
      λ: "b" "senc" "sdec" "ka" "kb", (* parameters of the protocol *)
        λ: "input",
          let: "nonce" := "sdec" "ka" (Snd "input") in
          let: "sender" := Fst "input" in
          let: "dest" := Fst "nonce" in
          let: "nonce" := Snd "nonce" in
          if: "sender" = #0 `and` "dest" = #1 then
            "senc" "kb" ("sender", "nonce")
          else #().

    Definition b_recv_once_eav : val :=
      λ: "b" "kb", (* parameters of the protocol *)
        λ: "input", #().
          (* let: "nonce" := "sdec" "kb" "input" in
          let: "sender" := Fst "nonce" in
          let: "nonce" := Snd "nonce" in
          if: "sender" = #0 then
            #()
          else #(). *)
  
  End Once_eav.

  Section protocols.

    Definition init_id : val :=
      λ: <>,
        let: "A" := #0 in
        let: "B" := #1 in
        ("A", "B").

    Definition wmf_once : expr :=
      let: "B" := init_id #() in
      let: "A" := Fst "B" in
      let: "B" := Snd "B" in
      λ: "b" "enc_scheme",
        let: "ka" := keygen #() in
        let: "kb" := keygen #() in
        let: "a_to_s" := a_to_s_once "A" "B" "b"
            (symmetric_init.get_enc "enc_scheme") "ka" in
        let: "s_to_b" := s_to_b_once "A" "B" "b"
            (symmetric_init.get_enc "enc_scheme")
            (symmetric_init.get_dec "enc_scheme")
            "ka" "kb" in
        let: "b_recv" := b_recv_once "A" "B" "b" "kb" in
        λ: "r_adv",
          ("a_to_s" "r_adv",
           "s_to_b",
           "b_recv").

    Definition wmf_eav : expr :=
      λ: "b" "enc_scheme",
        let: "r_adv" := rand #N in
        ("r_adv",
          let: "ka" := keygen #() in
          let: "kb" := keygen #() in
          let: "msg1" :=
            a_to_s_once_eav "b" (symmetric_init.get_enc "enc_scheme") "ka" "r_adv" in
          ("msg1",
            let: "msg2" :=
              s_to_b_once_eav "b"
                (symmetric_init.get_enc "enc_scheme")
                (symmetric_init.get_dec "enc_scheme")
                "ka" "kb" "msg1" in
            ("msg2",
            b_recv_once_eav "b" "kb" #())
          )
        ).

  End protocols.

End defs.