From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Export def_dhke valgroup ske valgroup_finval fin_val_type.
From clutch.prob_eff_lang.probblaze Require Export notation p_composition.

Import fingroup.

Import valgroup_notation.

Section schannel.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}. 
  #[local] Notation n := (S n'').
  (* message and cipher spaces: abstract *)
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  (* key space is valgroup *)
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.


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
    λ: "f" "effs",
      let, ("doSend", "doRecv", "doGK") := "effs" in
      let: "message" := ref NONEV in
      effect "ssend"
        effect "srecv"
        let: "doSecSend" := (λ: "m", do: "ssend" "m") in
        let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
        handle: handle: "f" ("doSecSend", "doSecRecv") with
    (*SendSecure*)
    | effect "ssend" "m", rec "k" as multi =>
        match: ms.(fvt_of_int) "m" with
        | NONE => "k" #()%V
        | SOME "m" => 
            match: !"message" with
            | NONE => "message" <- SOME "m";;
                      let: "key" := "doGK" (bob) in
                      match: "key" with
                      | NONE => "k" #()%V
                      | SOME "key" =>
                          let: "mg" := ske.(enc) "key" "m" in ("doSend" ("mg", bob));; "k" #()%V
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
            "k" (SOME (ske.(dec) "key" "m"))   
        end       
    end                              
| return "y" => "y"
  end.
  

  Definition RED_CHAN : val :=
    λ: "enc" "f" "effs",
      let, ("doSend", "doRecv", "doGK") := "effs" in
      let: "message" := ref NONEV in
      effect "ssend"
        effect "srecv"
        let: "doSecSend" := (λ: "m", do: "ssend" "m") in
        let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
        handle: handle: "f" ("doSecSend", "doSecRecv") with
      (*SendSecure*)
    | effect "ssend" "m", rec "k" as multi =>
        match: ms.(fvt_of_int) "m" with
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
        match: ms.(fvt_of_int) "m" with
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
    λ: "f" "effs",
      let, ("LeakAOp", "doKeyLeak") := "effs" in
      let, ("doLeakASend" , "doLeakARecv") := "LeakAOp" in
      let, ("doKeyLeakSnd", "doKeyLeakRecv") := "doKeyLeak" in
      let: "message" := ref NONEV in
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
                let: "mA" := ske.(rand_cipher) #()%V in
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


  Definition sc_real : expr := (F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f CHAN.
  
  Definition reduction : expr := (λ: "enc", (F_KE_lazy_alice ||ᵣ F_OAUTH)  ∘f (RED_CHAN "enc")).

  Definition game1 : expr := reduction (enc_real_tape ske).

  Definition game2 : expr := reduction (enc_ideal ske).

  Definition sc_ideal : expr := CHAN_SIM ∘f F_CHAN.


End schannel.
