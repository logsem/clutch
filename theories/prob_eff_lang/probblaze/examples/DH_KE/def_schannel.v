From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Export def_dhke.

Import fingroup.

Import fingroup.fingroup.

Import valgroup_notation.
Import valgroup_tactics.

Section def_schannel.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').
  
  (*In this implementation, we are not parametrizing by the party*)
  (*Unidirectional channel ideal functionality for sending ONE message *)
  Definition F_OAUTH : val :=
    λ: "f" "doLeakSend" "doLeakRecv",
      let: "message" := ref NONEV in
      effect "channel"
      let: "doSend" := (λ: "m", do: (EffName "channel") (Send "m")) in
      let: "doRecv" := (λ: "m", do: (EffName "channel") (Recv "m")) in
      handle: "f" "doSend" "doRecv" with
      | effect (EffName "channel") "payload", rec "k" as multi =>
      match: "payload" with
      (*Send Auth*)
      | InjL "payload" =>
          let, ("m", "dst") := "payload" in
          match: !"message" with
          | NONE => "message" <- SOME "m" ;;
                   ("doLeakSend" ("m", "dst"));; "k" #()%V
          | SOME "message" => "k" #()%V
          end
      (* Receive Auth *)
      | InjR "from" => 
          let: "r" := ("doLeakRecv" "from") in
          match: "r" with
          | NONE => "k" NONEV
          | SOME "x" => "k" !"message"                         
          end
      end
     | return "y" => #()%V
    end.

  (*placeholder for now*)
  Definition xor (e1 e2 : expr) : val := #()%V.

  Definition CHAN : val :=
    λ: "f" "doSend" "doRecv" "doGK",
      let: "message" := ref NONEV in
      effect "schannel"
      let: "doSecSend" := (λ: "m", do: (EffName "schannel") (Send "m")) in
      let: "doSecRecv" := (λ: "m", do: (EffName "schannel") (Recv "m")) in
      handle: "f" "doSecSend" "doSecRecv" with
      | effect (EffName "schannel") "payload", rec "k" as multi =>
        match: "payload" with
          (*SendSecure*)
        | InjL "payload" =>
            let, ("m", "dst") := "payload" in
            match: !"message" with
              | NONE => "message" <- SOME "m";;
                     let: "key" := "doGK" ("dst") in
                                     match: "key" with
                                     | NONE => "k" #()%V
                                     | SOME "x" =>
                                         let: "enc_m" := xor "x" "m" in
                                         ("doSend" (Send ("enc_m", bob)));;
                                         "k" #()%V
                                     end
              | SOME "m" => "k" #()%V
               end
          (*RecvSecure*)
        | InjR "from" =>
            let: "key" := "doGK" ("from") in
                            match: "key" with
                            | NONE => "k" NONEV
                            | SOME "key" =>
                                let: "r" := ("doRecv" (Recv "from")) in
                                match: "r" with
                                | NONE => "k" NONEV
                                | SOME "x" =>
                                    let: "enc_m" := xor "key" "x" in
                                    "k" (SOME "enc_m")
                                end       
                            end                              
        end
      | return "y" => #()%V
  end.

   (* Ideal functionality of the ONE-SHOT secure channel *)
   Definition F_CHAN : val :=
    λ: "f" "doLeakSend" "doLeakRecv",                           
      let: "message" := ref NONEV in
      effect "schannel"
      let: "doSecSend" := (λ: "m", do: (EffName "schannel") (Send "m"))  in
      let: "doSecRecv" := (λ: "m", do: (EffName "schannel") (Recv "m")) in
      handle: "f" "doSecSend" "doSecRecv" with
       | effect (EffName "schannel") "payload", rec "k" as multi =>
        match: "payload" with
          (*SendSecure*)
         | InjL "payload" =>
            let, ("m", "dst") := "payload" in
            match: !"message" with
            | NONE => "message" <- SOME "m";;
                     ("doLeakSend" (Send ("dst")));;
                     "k" #()%V 
            | SOME "x" => "k" #()%V
            end
          (*ReceiveSecure*)
         | InjR "from" =>
            let: "r" := ("doLeakRecv" (Recv "from")) in
            match: "r" with
            | NONE => "k" NONEV
            | SOME "x" => "k" (SOME "x")
            end              
         end
       | return "y" => #()%V
    end.

    (*Simulator for the one message secure channel *)
 (* Assumes a fixed direction from Alice to Bob *)       
  Definition CHAN_SIM : val :=
   λ: "f" "doKeyLeak" "doLeakASend" "doLeakARecv",                            
    let: "α" := alloc #n in
    let: "message" := ref NONEV in
    effect "leaksec"
    let: "doLeakSecSend" := (λ: "m", do: (EffName "leaksec") (Send "m")) in
    let: "doLeakSecRecv" := (λ: "m", do: (EffName "leaksec") (Recv "m")) in
    handle: "f" "doLeakSecSend" "doLeakSecRecv" with
    | effect (EffName "leaksec") "payload", rec "k" as multi =>
        match: "payload" with
          (*Broadcast a message*)
        | InjL "payload" =>
            (* assuming "dst" is alice for now *)
            (*let, ("m", "dst") := "payload" in*)
            ("doKeyLeak" (Send("payload")));;
            let: "r" := "doKeyLeak" (Recv bob) in
                          match: "r" with
                          | NONE =>
                              "k" NONEV
                          | SOME "x" =>
                              match: !"message" with
                              | NONE =>
                                  let: "m'" := (samplelbl "α" #()%V) in
                                  let: "mA" := g^"m'" in
                                  "message" <- SOME "m'";;
                                  ("doLeakASend" (Send ("mA", bob)));;
                                  "k" #()%V
                              | SOME "m" => "k" #()%V
                              end    
                          end                           
                        | InjR "from" =>
                            ("doKeyLeak" (Send "from"));;
             let: "r" := "doKeyLeak" (Recv "from") in
                           match: "r" with
                           | NONE =>
                               (*(do: leakauth ("from"));;*)
                               "k" NONEV
                           | SOME "x" =>
                               (*(do: keyleak (Send (bob)));;*)
                               let: "rla" := ("doLeakARecv" (Recv "from")) in
                               match: "rla" with
                               | NONE => "k" NONEV
                               | SOME "x" => "k" !"message"
                               end
                                 
                           end                             
        end
    | return "y" => "y" end.

  Definition F_KE_L : val :=
  λ: "f" "doKeyLeak",                           
    (* Magically share a presampled key *)
    let: "c" := (sample #()%V) in
    let: "key" := g ^ "c" in
    effect "getKey"
    let: "doGK" := (λ: "party", do: (EffName "getKey") "party") in
    handle: "f" "doGK" with
    | effect (EffName "getKey") "p", rec "k" as multi =>
        match: "p" with
          (* Alice *)
          InjL <> =>
            (* Send a dummy value *)
            ("doKeyLeak" (Send(bob)));;
            (* Receive a dummy value *)
            let: "r" := "doKeyLeak" (Recv bob) in
            match: "r" with
              NONE => "k" NONEV
            | SOME "w" => "k" (SOME "key")
            end
        (* Bob  *)
        | InjR <> =>
            let: "r" := "doKeyLeak" (Recv alice) in
            match: "r" with
              NONE => "k" NONEV
            | SOME "w" => 
                ("doKeyLeak" (Send alice));;
                "k" (SOME "key")
            end
       end
    | return "y" => "y" end.



End def_schannel.
