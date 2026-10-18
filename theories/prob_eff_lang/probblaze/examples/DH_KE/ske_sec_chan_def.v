From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Export def_dhke valgroup ske mask.
From clutch.prob_eff_lang.probblaze Require Export notation p_composition.

Import fingroup.

Import valgroup_notation.

Section schannel.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}. 
  #[local] Notation n := (S n'').
  Context {msg_card : nat}.
  Context {cipher_card : nat}.
  Local Instance ske_params : SYM_params := {
      card_key := n;
      card_message := msg_card;
      card_cipher := cipher_card }.
  Context {ske : @SYM_struct ske_params}.

  Definition F_OAUTH : val :=
    λ: "f" "LeakOp",
      let, ("doLeakSend", "doLeakRecv") := "LeakOp" in
      let: "message" := ref NONEV in
      effect "send"
        effect "recv"
        let: "doSend" := (λ: "m", do: "send" "m") in
        let: "doRecv" := (λ: "m", do: "recv" "m") in
        handle: handle: "f" ("doSend", "doRecv") with
    (*Send Auth*)
    | effect "send" "payload", rec "k" as multi =>
        let, ("m", "dst") := "payload" in
        match: !"message" with
        | NONE => "message" <- SOME "m" ;;
                  ("doLeakSend" ("m", "dst"));; "k" #()%V
        | SOME "message" => "k" #()%V
        end
    | return "y" => "y" end with
(* Receive Auth *)
| effect "recv" "from", rec "k" as multi =>
    let: "r" := ("doLeakRecv" "from") in
    match: "r" with
    | NONE => "k" NONEV
    | SOME "x" => "k" !"message"                         
    end
| return "y" => "y"
  end.


  (* Assumes a fixed direction from Alice to Bob, so the leak raised by CHAN doesnt need to send a destination with the argument Bob*)
  (* InjL arg represents the message being sent by Alice, and InjR <>, just represents that Bob is requesting a receive , so "doSecRecv" is now a genuine thunk, because it doesnt need any argument anymore*)
  Definition CHAN : val :=
    λ: "f" "ChanOp" "doGK",
      let, ("doSend", "doRecv") := "ChanOp" in
      let: "message" := ref NONEV in
      effect "ssend"
        effect "srecv"
        let: "doSecSend" := (λ: "m", do: "ssend" "m") in
        let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
        handle: handle: "f" ("doSecSend", "doSecRecv") with
    (*SendSecure*)
    | effect "ssend" "m", rec "k" as multi =>
        match: msg_of_int "m" with
        | NONE => "k" #()%V
        | SOME "m" => 
            match: !"message" with
            | NONE => "message" <- SOME "m";;
                      let: "key" := "doGK" (bob) in
                      match: "key" with
                      | NONE => "k" #()%V
                      | SOME "key" =>
                          let: "mg" := enc (int_of_vg "key") "m" in ("doSend" ("mg", bob));; "k" #()%V
                      end
            | SOME "m" => "k" #()%V
            end
        end 
    | return "y" => "y" end with
(*RecvSecure*)
| effect "srecv" "payload", rec "k" as multi =>
    let: "key" := "doGK" (alice) in
    match: "key" with
    | NONE => "k" NONEV
    | SOME "key" =>
        let: "r" := ("doRecv" bob) in
        match: "r" with
        | NONE => "k" NONEV
        | SOME "m" =>
            "k" (SOME (dec (int_of_vg "key") "m"))   
        end       
    end                              
| return "y" => "y"
  end.
  

  Definition RED_CHAN : val :=
    λ: "enc" "f" "ChanOp" "doGK", 
      let, ("doSend", "doRecv") := "ChanOp" in
      let: "message" := ref NONEV in
      effect "ssend"
        effect "srecv"
        let: "doSecSend" := (λ: "m", do: "ssend" "m") in
        let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
        handle: handle: "f" ("doSecSend", "doSecRecv") with
      (*SendSecure*)
    | effect "ssend" "m", rec "k" as multi =>
        match: msg_of_int "m" with
        | NONE => "k" #()%V
        | SOME "m" => 
            match: !"message" with
            | NONE => "message" <- SOME "m";;
                      let: "key" := "doGK" (bob) in
                      match: "key" with
                      | NONE => "k" #()%V
                      | SOME "key" =>
                          let: "mg" := "enc" "m" in ("doSend" ("mg", bob));; "k" #()%V
                      end
            | SOME "m" => "k" #()%V
            end
        end 
    | return "y" => "y" end with
(*RecvSecure*)
| effect "srecv" "payload", rec "k" as multi =>
    let: "key" := "doGK" (alice) in
    match: "key" with
    | NONE => "k" NONE
    | SOME "key" =>
        let: "r" := ("doRecv" bob) in
        match: "r" with
        | NONE => "k" NONE
        | SOME "m" =>
            "k" (!"message")   
        end       
    end                              
| return "y" => "y"
  end.


  (*reflecting the same change here as in the real functionality*)
  (* Ideal functionality of the ONE-MESSAGE secure channel *)
  Definition F_CHAN : val :=
    λ: "f" "LeakOp",
      let, ("doLeakSend", "doLeakRecv") := "LeakOp" in
      let: "message" := ref NONEV in
      effect "ssend"
        effect "srecv"
        let: "doSecSend" := (λ: "m", do: "ssend" "m")  in
        let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
        handle: handle: "f" ("doSecSend" ,"doSecRecv") with
    (*SendSecure*)
    | effect "ssend" "m", rec "k" as multi =>
        match: msg_of_int "m" with
        | NONE => "k" #()%V
        | SOME "m" => 
            match: !"message" with
            | NONE => "message" <- SOME "m";;
                      ("doLeakSend" alice);;
                      "k" #()%V 
            | SOME "x" => "k" #()%V
            end
        end
    | return "y" => "y" end with
(*ReceiveSecure*)
| effect "srecv" "payload", rec "k" as multi =>
    let: "r" := ("doLeakRecv" bob) in
    match: "r" with
    | NONE => "k" NONEV
    | SOME "x" => "k" (!"message")
    end              
| return "y" => "y"
  end.


  (*Simulator for the one message secure channel *)
  Definition CHAN_SIM : val :=
    λ: "f" "LeakAOp" "doKeyLeak",
      let, ("doLeakASend" , "doLeakARecv") := "LeakAOp" in
      let, ("doKeyLeakSnd", "doKeyLeakRecv") := "doKeyLeak" in
      let: "message" := ref NONEV in
      (* Mirrors [F_KE_lazy_alice]'s key cache [lc]: set as soon as a secure
         send has STARTED, i.e. before the key leaks are resolved.  The real
         side only reaches its authenticated-receive leak once a key has been
         established, so the simulator must gate its own on the same event --
         note that ["message"] is not a substitute, as it is only set when the
         key leak actually succeeded. *)
      let: "started" := ref NONEV in
      effect "lsend"
        effect "lrecv"
        let: "doLeakSecSend" := (λ: "m", do: "lsend" "m") in
        let: "doLeakSecRecv" := (λ: "m", do: "lrecv" "m") in
        handle: handle: "f" ("doLeakSecSend" , "doLeakSecRecv") with
    (*Broadcast a message*)
    | effect "lsend" "payload", rec "k" as multi =>
        "started" <- SOME #()%V ;;
        ("doKeyLeakSnd" (bob));;
        let: "r" := "doKeyLeakRecv" (bob) in
        match: "r" with
        | NONE =>
            "k" NONEV
        | SOME "x" =>
            match: !"message" with
            | NONE =>
                let: "mA" := rand_cipher #()%V in
                "message" <- SOME "mA";;
                ("doLeakASend" ("mA", bob));;
                "k" #()%V
            | SOME "m" => "k" #()%V
            end
        end
    | return "y" => "y" end with
| effect "lrecv" "payload", rec "k" as multi =>
            let: "r" := "doKeyLeakRecv" (alice) in
            match: "r" with
            | NONE =>
                "k" NONEV
            | SOME "x" =>
                ("doKeyLeakSnd" alice);;
                match: !"started" with
                | NONE => "k" NONEV
                | SOME "s" =>
                    let: "rla" := ("doLeakARecv" bob) in
                    match: "rla" with
                    | NONE => "k" NONEV
                    | SOME "x" => "k" !"message"
                    end
                end
            end           
| return "y" => "y" end.


  Definition sc_real : val := λ: "f", (F_KE_lazy_alice ||ᵣ F_OAUTH) (CHAN "f").

  Definition enc_real : expr := let: "ι" := alloc #n in λ: "m", let: "k" := rand("ι") #n in enc "k" "m". 
  Definition reduction : val := (λ: "enc" "f", (F_KE_lazy_alice ||ᵣ F_OAUTH) (RED_CHAN "enc" "f")).
  Definition game1 : expr := reduction enc_real.

  Definition enc_ideal : expr := λ: "m", rand_cipher #()%V.

  Definition game2 : expr := reduction enc_ideal.

  (* The ideal world: the one-message secure channel [F_CHAN] together with the
     simulator [CHAN_SIM] that fakes the authenticated-channel and key-exchange
     leaks the environment would otherwise see. *)
  Definition sc_ideal : val := λ: "f", CHAN_SIM (F_CHAN "f").


End schannel.
