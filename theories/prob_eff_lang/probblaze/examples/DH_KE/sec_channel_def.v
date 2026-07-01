From clutch.prob_eff_lang.probblaze Require Export notation valgroup p_composition.
From clutch.prob_eff_lang.probblaze Require Export def_dhke.

Import fingroup.

Import fingroup.fingroup.

Import valgroup_notation.
Import valgroup_tactics.

Section schannel.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}. 
  (*Context (channel leaksec getKey1 getKey2 leakauth1 leakauth2 schannel1 schannel2 : label).*)
  Variable xor_sem : val -> val -> val.
  Variable xor : val.
  #[local] Notation n := (S n'').


   Definition F_OAUTH : val :=
     λ: "f" "LeakOp",
      let, ("doLeakSend", "doLeakRecv") := "LeakOp" in
      let: "message" := ref NONEV in
      effect "channel"
      let: "doSend" := (λ: "m", do: (EffName "channel") (Send "m")) in
      let: "doRecv" := (λ: "m", do: (EffName "channel") (Recv "m")) in
      handle: "f" ("doSend", "doRecv") with
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
     | return "y" => "y"
  end.


   Definition G_XOR : val :=
    λ: "a" "b",
      vg_of_int (xor (int_of_vg "a") (int_of_vg "b")).


    Definition CHAN : val :=
     λ: "f" "ChanOp" "doGK",
      let, ("doSend", "doRecv") := "ChanOp" in
      let: "message" := ref NONEV in
      effect "schannel"
      let: "doSecSend" := (λ: "m", do: (EffName "schannel") (Send "m")) in
      let: "doSecRecv" := (λ: "from", do: (EffName "schannel") (Recv "from")) in
      handle: "f" ("doSecSend", "doSecRecv") with
      | effect (EffName "schannel") "payload", rec "k" as multi =>
        match: "payload" with
          (*SendSecure*)
        | InjL "payload" =>
            let, ("m", "dst") := "payload" in
            match: !"message" with
              | NONE => "message" <- SOME "m";;
                     let: "key" := "doGK" (bob) in
                                     match: "key" with
                                     | NONE => "k" #()%V
                                     | SOME "x" =>
                                         match: G_XOR "m" "x" with
                                         | SOME "mg" =>
                                             ("doSend" ("mg" , bob));;
                                             "k" #()%V
                                         | NONE => "k" #()%V
                                         end
                                     end
              | SOME "m" => "k" #()%V
               end
          (*RecvSecure*)
        | InjR <> =>
            let: "key" := "doGK" (alice) in
                            match: "key" with
                            | NONE => "k" NONEV
                            | SOME "key" =>
                                let: "r" := ("doRecv" bob) in
                                match: "r" with
                                | NONE => "k" NONEV
                                | SOME "x" =>
                                    match: G_XOR "x" "key" with
                                    | SOME "mg" => "k" (SOME "mg")
                                    | NONE => "k" NONE
                                    end                           
                                end       
                            end                              
        end
      | return "y" => "y"
  end.

   (* Ideal functionality of the ONE-SHOT secure channel *)
   Definition F_CHAN : val :=
     λ: "f" "LeakOp",
      let, ("doLeakSend", "doLeakRecv") := "LeakOp" in
      let: "message" := ref NONEV in
      effect "schannel"
      let: "doSecSend" := (λ: "m", do: (EffName "schannel") (Send "m"))  in
      let: "doSecRecv" := (λ: "from", do: (EffName "schannel") (Recv "from")) in
      handle: "f" ("doSecSend" ,"doSecRecv") with
       | effect (EffName "schannel") "payload", rec "k" as multi =>
        match: "payload" with
          (*SendSecure*)
         | InjL "payload" =>
            let, ("m", "dst") := "payload" in
            match: !"message" with
            | NONE => "message" <- SOME "m";;
                     ("doLeakSend" alice);;
                     "k" #()%V 
            | SOME "x" => "k" #()%V
            end
          (*ReceiveSecure*)
         | InjR <> =>
            let: "r" := ("doLeakRecv" bob) in
            match: "r" with
            | NONE => "k" NONEV
            | SOME "x" => "k" (SOME !"message")
            end              
         end
       | return "y" => "y"
  end.

  Print alice.

  (*a function for requesting messages from the other party *)
  Definition ASK_KEY : val :=
    λ: "party",
      match: "party" with
      | InjL <> => InjR #()%V
      | InjR <> => InjL #()%V
      end.

   (*Simulator for the one message secure channel *)      
  Definition CHAN_SIM : val :=
    λ: "f" "LeakAOp" "doKeyLeak",
    let, ("doLeakASend" , "doLeakARecv") := "LeakAOp" in
    let, ("doKeyLeakSnd", "doKeyLeakRecv") := "doKeyLeak" in  
    (*let: "α" := alloc #n in*)
    let: "message" := ref NONEV in
    effect "leaksec"
    let: "doLeakSecSend" := (λ: "m", do: (EffName "leaksec") (Send "m")) in
    let: "doLeakSecRecv" := (λ: "m", do: (EffName "leaksec") (Recv "m")) in
    handle: "f" ("doLeakSecSend" , "doLeakSecRecv") with
    | effect (EffName "leaksec") "payload", rec "k" as multi =>
        match: "payload" with
          (*Broadcast a message*)
        | InjL <> =>
            (* assuming "dst" is alice for now *)
            (*let, ("m", "dst") := "payload" in*)
            (*("doKeyLeak" (Send("payload")));;*)
            ("doKeyLeakSnd" (bob));;
            let: "r" := "doKeyLeakRecv" (bob) in
                          match: "r" with
                          | NONE =>
                              "k" NONEV
                          | SOME "x" =>
                              match: !"message" with
                              | NONE =>
                                  let: "m'" := (sample #()%V) in
                                  let: "mA" := g^"m'" in
                                  "message" <- SOME "m'";;
                                  ("doLeakASend" ("mA", bob));;
                                  "k" #()%V
                              | SOME "m" => "k" #()%V
                              end    
                          end                           
       | InjR <> =>
                            (*("doKeyLeakRecv" (alice));;*)
                            let: "r" := "doKeyLeakRecv" (alice) in
                            match: "r" with
                             | NONE =>
                               (*(do: leakauth ("from"));;*)
                               "k" NONEV
                             | SOME "x" =>
                               ("doKeyLeakSnd" alice);;
                               let: "rla" := ("doLeakARecv" bob) in
                               match: "rla" with
                               | NONE => "k" NONEV
                               | SOME "x" => "k" !"message"
                               end
                                 
                           end                             
        end
    | return "y" => "y" end.


   (*Simulator for the one message secure channel *)
  Definition CHAN_SIM_lazy : val :=
    λ: "f" "LeakAOp" "doKeyLeak",
    let, ("doLeakASend" , "doLeakARecv") := "LeakAOp" in
    let, ("doKeyLeakSnd", "doKeyLeakRecv") := "doKeyLeak" in
    let: "message" := ref NONEV in
    let: "m'_opt" := ref NONEV in
    let: "sample_or_load" :=
      λ:<>, match: !"m'_opt" with
        | NONE =>
            let: "m'" := (sample #()%V) in
            "m'_opt" <- SOME "m'" ;;
            "key"
        | SOME "m'" => "m'"
        end
    in
    effect "leaksec"
    let: "doLeakSecSend" := (λ: "m", do: (EffName "leaksec") (Send "m")) in
    let: "doLeakSecRecv" := (λ: "m", do: (EffName "leaksec") (Recv "m")) in
    handle: "f" ("doLeakSecSend" , "doLeakSecRecv") with
    | effect (EffName "leaksec") "payload", rec "k" as multi =>
        match: "payload" with
          (*Broadcast a message*)
        | InjL <> =>
            (* assuming "dst" is alice for now *)
            (*let, ("m", "dst") := "payload" in*)
            (*("doKeyLeak" (Send("payload")));;*)
            let: "m'" := "sample_or_load" #() in
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
       | InjR <> =>
                            (*("doKeyLeakRecv" (alice));;*)
                            let: "r" := "doKeyLeakRecv" (alice) in
                            match: "r" with
                             | NONE =>
                               (*(do: leakauth ("from"));;*)
                               "k" NONEV
                             | SOME "x" =>
                               ("doKeyLeakSnd" alice);;
                               match: !"message" with
                               | NONE => "k" NONEV
                               | SOME "_" =>
                                   let: "rla" := ("doLeakARecv" bob) in
                                   match: "rla" with
                                   | NONE => "k" NONEV
                                   | SOME "x" => "k" !"message"
                                   end
                               end

                           end
        end
    | return "y" => "y" end.

End schannel.
