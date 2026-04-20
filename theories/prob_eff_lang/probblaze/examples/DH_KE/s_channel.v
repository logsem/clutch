From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Export definition.

Import fingroup.

Import fingroup.fingroup.

Import valgroup_notation.
Import valgroup_tactics.

Section sec_channel.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').

  Definition SendSecure (e : expr) := InjL e.
  Definition RecvSecure (e : expr) := InjR e.

  (*In this implementation, we are not parametrizing by the party*)
  (*Unidirectional channel ideal functionality for sending ONE message *)
  Definition F_OAUTH (leak' channel : label) f : expr :=
     let: "message" := ref NONEV in
     handle: f with
     | effect channel "payload", rec "k" as multi =>
      match: "payload" with
      (*Send Auth*)
      | InjL "payload" =>
          let, ("m", "dst") := "payload" in
          match: !"message" with
          | NONE => "message" <- SOME "m" ;;
                   (do: leak' (Send ("m", "dst")));; "k" #()%V
          | SOME "message" => "k" #()%V
          end
      (* Receive Auth *)
      | InjR "from" => 
          let: "r" := (do: leak' (Recv "from")) in
          match: "r" with
          | NONE => "k" NONEV
          | SOME "x" => "k" !"message"                         
          end
      end
     | return "y" => #()%V
    end.

            
  (*placeholder for now *)
  Definition xor (e1 e2 : expr) : expr := #()%V.  

  (*ONE message unidirectional secure channel functionality.
    Assume a fixed direction of sending the message, from Alice to Bob *)
  Definition CHAN (getKey schannel channel : label) f : expr :=
    let: "message" := ref NONEV in
    handle: f with
    | effect schannel "payload", rec "k" as multi =>
        match: "payload" with
          (*SendSecure*)
        | InjL "payload" =>
            let, ("m", "dst") := "payload" in
            match: !"message" with
            | NONE => "message" <- SOME "m";;
                     let: "key" := do: getKey ("dst") in
                                     match: "key" with
                                     | NONE => "k" NONEV
                                     | SOME "x" =>
                                         let: "enc_m" := xor "x" "m" in
                                         (do: channel (Send ("enc_m", bob)));;
                                         "k" #()%V
                                     end
                                       
            | SOME "message" => "k" NONEV
            end
          (*RecvSecure*)
        | InjR "from" =>
            let: "key" := do: getKey ("from") in
                            match: "key" with
                            | NONE => "k" NONEV
                            | SOME "key" =>
                                let: "r" := (do: channel (Recv "from")) in
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
  Definition F_CHAN (schannel channel : label) f : expr :=
    let: "message" := ref NONEV in
    handle: f with
    | effect schannel "payload", rec "k" as multi =>
        match: "payload" with
          (*SendSecure*)
        | InjL "payload" =>
            let, ("m", "dst") := "payload" in
            match: !"message" with
            | NONE => "message" <- SOME "m";;
                     (do: channel (Send (#0, "dst")));;
                     "k" #()%V 
            | SOME "x" => "k" #()%V
            end
          (*ReceiveSecure*)
        | InjR "from" =>
            let: "r" := (do: channel (Recv "from")) in
            match: "r" with
            | NONE => "k" NONEV
            | SOME "x" => "k" !"message"
            end              
        end
    | return "y" => #()%V
    end.
                        
 (*Simulator for the one message secure channel *)
 (* Assumes a fixed direction from Alice to Bob *)       
  Definition CHAN_SIM (leak' leak channel : label) (f : expr) : expr :=
    let: "α" := alloc #n in
    let: "message" := ref NONEV in
    handle: f with
    | effect channel "payload", rec "k" as multi =>
        match: "payload" with
          (*Broadcast a message*)
        | InjL "payload" =>
            (* assuming "dst" is alice for now *)
            let, ("m", "dst") := "payload" in
            (do: leak ("dst"));;
            let: "r" := do: channel (Recv bob) in
                          match: "r" with
                          | NONE => "k" NONE
                          | SOME "x" =>
                              let: "m" :=
                                (match: !"message" with
                                     | NONE =>
                                         let:
                                           "m":= (samplelbl "α" #()%V) in "message" <- SOME "m";; "m"
                                     | SOME "m" => "m"
                                     end) in
                              let: "mA" := g^"m" in
                              (do: leak' (Send ("mA", alice)));;
                              "k" #()%V
                          end
                            
         | InjR "from " =>
             let: "r" := do: leak' (Recv "from") in
                           match: "r" with
                           | NONE => "k" NONE
                           | SOME "x" =>
                               (do: leak ("from"));;
                               "k" (SOME #0)
                           end                             
        end
     | return "y" => #()%V end.

                           
    (*Definition CHAN_SIM (channel leak : label) (f : expr) : expr :=
      let: "α" := alloc #n in
      let: "message" := ref NONEV in
      handle: f with
      | effect channel "payload", rec "k" as multi =>
          match: "payload" with
          | InjL "payload" =>
              let, ("m", "dst") := "payload" in
              
          | InjR "from" =>
          end
      | return "y" => #()%V end.*)


    Definition F_KE_L (getKey channel leak : label) f : expr :=
    (* Magically share a presampled key *)
    let: "c" := (sample #()%V) in
    let: "key" := g ^ "c" in

    handle: f with
    | effect getKey "p", rec "k" as multi =>
        match: "p" with
          (* Alice *)
          InjL <> =>
            (* Send a dummy value *)
            (do: leak (bob));;
            (* Receive a dummy value *)
            let: "r" := do: channel Recv bob in
            match: "r" with
              NONE => "k" NONEV
            | SOME "w" => "k" (SOME "key")
            end
        (* Bob  *)
        | InjR <> =>
            let: "r" := do: channel Recv alice in
            match: "r" with
              NONE => "k" NONEV
            | SOME "w" => 
                (do: leak (alice));;
                "k" (SOME "key")
            end
       end
    | return "y" => "y" end.


End sec_channel.
