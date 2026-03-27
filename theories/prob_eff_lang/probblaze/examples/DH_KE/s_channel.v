From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import definition.

Import fingroup.

Import fingroup.fingroup.

Import valgroup_notation.
Import valgroup_tactics.


Section secure_channel.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.


  #[local] Notation n := (S n'').

  Definition SendSecure (e : expr) := InjL e.
  Definition RecvSecure (e : expr) := InjR e.

  (*ONE-SHOT auhtneticated channel ideal functionality*)
  (*Definition F_OAUTH*)

  (*placeholder for now *)
  Definition xor (e1 e2 : expr) : expr := #()%V.  

  
  (*ONE-SHOT Secure channel functionality*)
  Definition CHAN (channel : label) f : expr :=
    let: "message" := ref NONEV in
    handle: f with
    | effect channel "payload", rec "k" as multi =>
        match: "payload" with
          (*SendSecure*)
        | InjL "payload" =>
            let, ("m", "dst") := "payload" in
            match: "dst" with
            (*Alice *)
            | InjL <> => match: !"message" with
                       | NONE => "message" <- SOME "m";;
                                let: "key" := do: "getKey" ("dst") in
                                              match: "key" with
                                                (*is this correct?*)
                                              | NONE => "k" NONEV
                                              | SOME "x" =>
                                                  let: "enc_m" := xor "x" "m" in
                                                  (do: channel (Send ("enc_m", bob)));; "k" #()%V
                                              end    
                        | SOME "message" => "k" NONEV (*is this correct? *)
                      end                              
         (*Bob*)                        
             | InjR <> => match: !"message" with
                       | NONE => "message" <- SOME "m";;
                                let: "key" := do: "getKey" ("dst") in
                                              match: "key" with
                                                (*is this correct?*)
                                              | NONE => "k" NONEV
                                              | SOME "x" =>
                                                  let: "enc_m" := xor "x" "m" in
                                                  (do: channel (Send ("enc_m", alice)));; "k" #()%V
                                              end
                      | SOME "message" => "k" NONEV (*is this correct? *)
                      end                                                           
            end
              
            (*ReceiveSecure*)
                                            |InjR "from" =>
                                               let: "key" := do: "getKey" ("from") in
                                                             match: "key" with
                                                               (*is this correct?*)
                                                             | NONE => "k" NONEV
                                                             | SOME "x" =>
                                                                 let: "r" := (do: channel (Recv "from")) in
                                                                 match: "r" with
                                                                 | NONE => "k" NONEV
                                                                 | SOME "x'" =>
                                                                     let: "enc_m" := xor "x" "x'" in
                                                                     "k" (SOME "enc_m")
                                                                 end
                                                              end                
                                               
                                               
        end
    | return "y" => #()%V end.
  


  
  (* Ideal functionality of the ONE-SHOT secure channel*)
  Definition F_CHAN (channel : label) f : expr :=
    let: "message" := ref NONEV in
    handle: f with
    | effect channel "payload", rec "k" as multi =>
        match: "payload" with
        (*SendSecure *)
        | InjL "payload" =>
            let, ("m", "dst") := "payload" in
            match: !"message" with
            | NONE => "message" <- SOME "m";;
                     (do: channel (Send (#0, "dst")));;
                     "k" #()%V
            | SOME "x" => "k" #()%V
            end
        (*ReceiveSecure*)
        |InjR "from" =>
           let: "r" := (do: channel (Recv "from")) in
           match: "r" with
           | NONE => "k" NONEV
           | SOME "x" => "k" !"message"
           end
        end
              
    | return "y" => #()%V end.
  
    
  Definition CHAN_SIM (channel : label) (f : expr) : expr :=
      let: "message" := ref NONEV in
      
    handle: f with
    | effect channel "payload", rec "k" as multi =>
        match: "payload" with
          (*Leak effect for sending a message *)
        | InjL "payload" => (*"k" NONE*)
            let, ("m", "dst") := "payload" in
            match: "dst" with
              (*Alice *)
             | InjL <> =>
                (do: channel (Send (#0, alice)));;
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
                                  (do: channel (Send ("mA", alice)));;
                                  "k" #()%V
                              end                                   
               (*Bob*)
             | InjR <> =>
                (do: channel (Send (#0, bob)));;
                let: "r" := do: channel (Recv alice) in
                              match: "r" with
                              | NONE => "k" NONE
                              | SOME "x" =>
                                  let: "m" :=
                                    (match: !"message" with
                                     | NONE =>
                                         let:
                                           "m":= (samplelbl "β" #()%V) in "message" <- SOME "m";; "m"
                                     | SOME "m" => "m"
                                     end) in
                                  let: "mB" := g^"m" in
                                  (do: channel (Send ("mB", bob)));;
                                  "k" #()%V
                              end                      
            end
          (*Leak effect for receiving a message *)
         | InjR "from" =>
            let: "r" := do: channel (Recv "from") in
                         match: "r" with
                          | NONE => "k" NONE
                          | SOME "x" => "k" (SOME #0)
                         end
        end
    | return "y" => "y" end.

                          
End secure_channel.
