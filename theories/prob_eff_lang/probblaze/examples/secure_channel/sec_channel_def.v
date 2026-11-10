From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems.
From clutch.prob_eff_lang.probblaze Require Export dhke_def notation valgroup mask.
From clutch.prob_eff_lang.probblaze.uc Require Export comp_operators.

Import fingroup.

Import valgroup_notation.

Section schannel.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}. 
  Context {msk : @Mask (@vgG vg) vgval}.
  #[local] Notation n := (S n'').

  (* The functionalities allocate their state before taking the client, so all
     calls of an evaluated functionality share one session. *)
  Definition F_OAUTH : val := λ: <>,
    let: "message" := ref NONEV in
    λ: "f" "LeakOp",
      let, ("doLeakSend", "doLeakRecv") := "LeakOp" in
      effect "send"
        effect "recv"
        let: "doSend" := (λ: "m", do: "send" "m") in
        let: "doRecv" := (λ: "m", do: "recv" "m") in
        handle: handle: "f" ("doSend", "doRecv") with
    (*Send Auth*)
    | effect "send" "payload", rec "k" =>
        let, ("m", "dst") := "payload" in
        match: !"message" with
        | NONE => "message" <- SOME "m" ;;
                  ("doLeakSend" ("m", "dst"));; "k" #()%V
        | SOME "stored" => "k" #()%V
        end
    | return "y" => "y" end with
(* Receive Auth *)
| effect "recv" "from", rec "k" =>
    let: "r" := ("doLeakRecv" "from") in
    match: "r" with
    | NONE => "k" NONEV
    | SOME "x" => "k" !"message"                         
    end
| return "y" => "y"
  end.


  (* Assumes a fixed direction from Alice to Bob, so the leak raised by CHAN doesnt need to send a destination with the argument Bob*)
  (* InjL arg represents the message being sent by Alice, and InjR <>, just represents that Bob is requesting a receive , so "doSecRecv" is now a genuine thunk, because it doesnt need any argument anymore*)
  Definition CHAN : val := λ: <>,
    let: "message" := ref NONEV in
    (*λ: "f" "ChanOp" "doGK",*)
    λ: "f" "effs",
      let, ("ChanOp", "doGK") := "effs" in
      let, ("doSend", "doRecv") := "ChanOp" in
      effect "ssend"
        effect "srecv"
        let: "doSecSend" := (λ: "m", do: "ssend" "m") in
        let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
        handle: handle: "f" ("doSecSend", "doSecRecv") with
    (*SendSecure*)
    | effect "ssend" "m", rec "k" =>
        match: vg_of_int "m" with
        | NONE => "k" #()%V
        | SOME "m" => 
            match: !"message" with
            | NONE => "message" <- SOME "m";;
                      let: "key" := "doGK" (bob) in
                      match: "key" with
                      | NONE => "k" #()%V
                      | SOME "key" =>
                          let: "mg" := mask "key" "m" in ("doSend" ("mg", bob));; "k" #()%V
                      end
            | SOME "m" => "k" #()%V
            end
        end 
    | return "y" => "y" end with
(*RecvSecure*)
| effect "srecv" "payload", rec "k" =>
    let: "key" := "doGK" (alice) in
    match: "key" with
    | NONE => "k" NONEV
    | SOME "key" =>
        let: "r" := ("doRecv" bob) in
        match: "r" with
        | NONE => "k" NONEV
        | SOME "m" =>
            "k" (SOME (mask "key" "m"))   
        end       
    end                              
| return "y" => "y"
  end.
  
  (*reflecting the same change here as in the real functionality*)
  (* Ideal functionality of the ONE-MESSAGE secure channel *)
  Definition F_CHAN : val := λ: <>,
    let: "message" := ref NONEV in
    λ: "f" "LeakOp",
      let, ("doLeakSend", "doLeakRecv") := "LeakOp" in
      effect "ssend"
        effect "srecv"
        let: "doSecSend" := (λ: "m", do: "ssend" "m")  in
        let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
        handle: handle: "f" ("doSecSend" ,"doSecRecv") with
    (*SendSecure*)
    | effect "ssend" "m", rec "k" =>
        match: vg_of_int "m" with
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
| effect "srecv" "payload", rec "k" =>
    let: "r" := ("doLeakRecv" bob) in
    match: "r" with
    | NONE => "k" NONEV
    | SOME "x" => "k" (!"message")
    end              
| return "y" => "y"
  end.


  (*Simulator for the one message secure channel *)
  Definition CHAN_SIM_lazy : val := λ: <>,
    let: "message" := ref NONEV in
    let: "m'_opt" := ref NONEV in
    let: "sample_or_load" :=
      λ:<>, match: !"m'_opt" with
        | NONE =>
            let: "m'" := (sample #()%V) in
            "m'_opt" <- SOME "m'" ;;
            "m'"
        | SOME "m'" => "m'"
        end
    in
    λ: "f" "effs",
      let, ("LeakAOp", "doKeyLeak") := "effs" in
      let, ("doLeakASend" , "doLeakARecv") := "LeakAOp" in
      let, ("doKeyLeakSnd", "doKeyLeakRecv") := "doKeyLeak" in
      effect "lsend"
        effect "lrecv"
        let: "doLeakSecSend" := (λ: "m", do: "lsend" "m") in
        let: "doLeakSecRecv" := (λ: "m", do: "lrecv" "m") in
        handle: handle: "f" ("doLeakSecSend" , "doLeakSecRecv") with
    (*Broadcast a message*)
    | effect "lsend" "payload", rec "k" =>
        let: "m'" := "sample_or_load" #()%V in
        ("doKeyLeakSnd" (bob));;
        let: "r" := "doKeyLeakRecv" (bob) in
        match: "r" with
        | NONE =>
            "k" NONEV
        | SOME "x" =>
            match: !"message" with
            | NONE =>
                (* let: "m'" := (sample #()%V) in *)
                let: "mA" := g^"m'" in
                "message" <- SOME "m'";;
                ("doLeakASend" ("mA", bob));;
                "k" #()%V
            | SOME "m" => "k" #()%V
            end
        end
    | return "y" => "y" end with
| effect "lrecv" "payload", rec "k" =>
    (*("doKeyLeakRecv" (alice));;*)
    let: "r" := "doKeyLeakRecv" (alice) in
    match: "r" with
    | NONE =>
        (*(do: leakauth ("from"));;*)
        "k" NONEV
    | SOME "x" =>
        ("doKeyLeakSnd" alice);;
        match: !"m'_opt" with
        (* match: !"message" with*)
        | NONE => "k" NONEV
        | SOME "_" =>
            let: "rla" := ("doLeakARecv" bob) in
            match: "rla" with
            | NONE => "k" NONEV
            | SOME "x" => "k" !"message"
            end
        end

    end
| return "y" => "y" end.



  (* The systems are factories (uc/DESIGN.md): a call allocates the state of
     a fresh session and returns it. *)
  #[global] Instance F_OAUTH_as_recv : AsRecV F_OAUTH BAnon BAnon _ := eq_refl.
  #[global] Instance CHAN_as_recv : AsRecV CHAN BAnon BAnon _ := eq_refl.
  #[global] Instance F_CHAN_as_recv : AsRecV F_CHAN BAnon BAnon _ := eq_refl.
  #[global] Instance CHAN_SIM_lazy_as_recv : AsRecV CHAN_SIM_lazy BAnon BAnon _ := eq_refl.
  (* The real system: the protocol in the (F_KE_lazy_alice, F_OAUTH)-hybrid
     world; the ideal functionality; the simulator. *)
  Definition REAL_SCHAN : val := ((F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f CHAN)%fac.
  Definition IDEAL_SCHAN : val := F_CHAN.
  Definition SIM_SCHAN : val := CHAN_SIM_lazy.


End schannel.
