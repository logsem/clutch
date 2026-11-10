From clutch.prob_eff_lang.probblaze.examples Require Export dhke_def valgroup ske valgroup_finval fin_val_type.
From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems.
From clutch.prob_eff_lang.probblaze Require Export notation.
From clutch.prob_eff_lang.probblaze.uc Require Export comp_operators.

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
    λ: "f" "effs",
      let, ("chanOp", "doGK") := "effs" in
      let, ("doSend", "doRecv") := "chanOp" in
      effect "ssend"
        effect "srecv"
        let: "doSecSend" := (λ: "m", do: "ssend" "m") in
        let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
        handle: handle: "f" ("doSecSend", "doSecRecv") with
    (*SendSecure*)
    | effect "ssend" "m", rec "k" =>
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
| effect "srecv" "payload", rec "k" =>
    let: "key" := "doGK" (alice) in
    match: "key" with
    | NONE => "k" NONEV
    | SOME "key" =>
        let: "r" := ("doRecv" bob) in
        match: "r" with
        | NONE => "k" NONEV
        | SOME "m" =>
            "k" (ske.(dec) "key" "m")   
        end       
    end                              
| return "y" => "y"
  end.
  

  (* The encryption oracle is initialised once, at setup. *)
  Definition RED_CHAN_sess : val :=
    λ: "enc",
    let: "enc" := "enc" #()%V in
    let: "message" := ref NONEV in
    λ: "f" "effs",
      let, ("chanOp", "doGK") := "effs" in
      let, ("doSend", "doRecv") := "chanOp" in
      effect "ssend"
        effect "srecv"
        let: "doSecSend" := (λ: "m", do: "ssend" "m") in
        let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
        handle: handle: "f" ("doSecSend", "doSecRecv") with
      (*SendSecure*)
    | effect "ssend" "m", rec "k" =>
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
| effect "srecv" "payload", rec "k" =>
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
| effect "srecv" "payload", rec "k" =>
    let: "r" := ("doLeakRecv" bob) in
    match: "r" with
    | NONE => "k" NONEV
    | SOME "x" => "k" (!"message")
    end              
| return "y" => "y"
  end.


  (*Simulator for the one message secure channel *)
  Definition CHAN_SIM : val := λ: <>,
    let: "message" := ref NONEV in
    let: "started" := ref NONEV in
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
| effect "lrecv" "payload", rec "k" =>
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


  (* The factories: each system allocates its state when called.  [RED_CHAN]
     takes the encryption oracle (itself a thunk, called once at setup).
     [AsRecV] lets the pure-step tactics call them without unfolding. *)
  Definition RED_CHAN : val := (λ: "enc", λ: <>, RED_CHAN_sess "enc")%V.
  Definition C_ENC_real : val := (λ: <>, RED_CHAN_sess (enc_real_tape ske))%V.
  Definition C_ENC_ideal : val := (λ: <>, RED_CHAN_sess (enc_ideal ske))%V.
  #[global] Instance F_OAUTH_as_recv : AsRecV F_OAUTH BAnon BAnon _ := eq_refl.
  #[global] Instance CHAN_as_recv : AsRecV CHAN BAnon BAnon _ := eq_refl.
  #[global] Instance F_CHAN_as_recv : AsRecV F_CHAN BAnon BAnon _ := eq_refl.
  #[global] Instance CHAN_SIM_as_recv : AsRecV CHAN_SIM BAnon BAnon _ := eq_refl.
  #[global] Instance RED_CHAN_as_recv : AsRecV RED_CHAN BAnon "enc" _ := eq_refl.
  #[global] Instance RED_CHAN_sess_as_recv : AsRecV RED_CHAN_sess BAnon "enc" _ := eq_refl.
  #[global] Instance C_ENC_real_as_recv : AsRecV C_ENC_real BAnon BAnon _ := eq_refl.
  #[global] Instance C_ENC_ideal_as_recv : AsRecV C_ENC_ideal BAnon BAnon _ := eq_refl.

  (* The real system: the protocol in the (F_KE_lazy_alice, F_OAUTH)-hybrid
     world; the ideal functionality; the simulator. *)
  Definition REAL_SKE : val := ((F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f CHAN)%fac.
  Definition IDEAL_SKE : val := F_CHAN.
  Definition SIM_SKE : val := CHAN_SIM.
  (* The simulator on the ideal functionality, as one system (the relation
     files do not import the factory notations). *)
  Definition SIM_IDEAL_SKE : val := (SIM_SKE ∘f IDEAL_SKE)%fac.
  (* The hybrids: the protocol with the encryption replaced by the oracle. *)
  Definition GAME1 : val := ((F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f C_ENC_real)%fac.
  Definition GAME2 : val := ((F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f C_ENC_ideal)%fac.
  (* The reduction to the encryption scheme for an environment [A]. *)
  Definition RED_SKE (A : val) : val :=
    (λ: "v", A ((F_KE_lazy_alice ||ᵣ F_OAUTH) ∘fₚ (RED_CHAN "v"))%fac)%V.


End schannel.

(* The message struct is explicit where nothing else determines it: with both
   [ms] and [cs] in scope, typeclass resolution would otherwise pick the one
   declared last. *)
#[global] Arguments RED_CHAN_sess {mt} ms.
#[global] Arguments RED_CHAN {mt} ms.
#[global] Arguments F_CHAN {mt} ms.
#[global] Arguments IDEAL_SKE {mt} ms.
#[global] Arguments RED_SKE {vg cg vgg mt} ms A.
