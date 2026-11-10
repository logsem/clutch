(** * Environments for the authenticated channel ([auth_def])

    The client gets [(send, recv)] as for [F_AUTH]: [send (m, dst)] and
    [recv from].  The ports are the raw network [(doSend, doRecv)]: the
    environment sees every tagged pair and decides what is delivered.
    Messages with destination [InjL] are read by the receiver [InjR]. *)
From clutch.prob_eff_lang.probblaze Require Import syntax notation.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup dhke_def auth_def.
From clutch_exec Require Import exec_common.

Section env_auth.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Import valgroup_notation.
  #[local] Notation n := (S n'').

  (** A raw network that stores the pair sent in each direction and, on
      [recv from], delivers [forge] applied to the stored pair. *)
  Definition net_ports (obs : string → val) (slot1 slot2 forge : expr) : expr :=
    ((λ: "p", (obs "net.send") "p" ;;
              let, ("mt", "dst") := "p" in
              match: "dst" with InjL <> => slot1 <- SOME "mt" | InjR <> => slot2 <- SOME "mt" end),
     (λ: "from", (obs "net.recv") "from" ;;
                 let: "r" := match: "from" with InjL <> => !slot2 | InjR <> => !slot1 end in
                 match: "r" with NONE => NONE | SOME "mt" => SOME (forge "mt") end))%E.

  (** Alice sends a uniformly chosen group element to Bob, who receives it.
      True iff Bob gets it. *)
  Definition env_auth_honest (obs : string → val) : val :=
    λ: "X",
      let: "m" := g ^ (rand #n) in
      let: "slot1" := ref NONE in
      let: "slot2" := ref NONE in
      let: "got" := ref NONE in
      let: "s" := "X" #()%V in
      "s" (λ: "ops", let, ("snd", "rcv") := "ops" in
                     "snd" ("m", InjLV #()%V) ;; "got" <- "rcv" (InjRV #()%V))
          (net_ports obs "slot1" "slot2" (λ: "mt", "mt")) ;;
      (obs "received") !"got" ;;
      match: !"got" with NONE => #false | SOME "x" => veq "x" "m" end.

  (** A forger: delivers [(m · g, t)] for the tagged pair [(m, t)].  The
      real MAC accepts it iff its key exponent [k1] is 0; the ideal MAC
      never does.  True iff Bob accepts. *)
  Definition env_auth_forge (obs : string → val) : val :=
    λ: "X",
      let: "m" := g ^ (rand #n) in
      let: "slot1" := ref NONE in
      let: "slot2" := ref NONE in
      let: "got" := ref NONE in
      let: "s" := "X" #()%V in
      "s" (λ: "ops", let, ("snd", "rcv") := "ops" in
                     "snd" ("m", InjLV #()%V) ;; "got" <- "rcv" (InjRV #()%V))
          (net_ports obs "slot1" "slot2" (λ: "mt", let, ("x", "t") := "mt" in ("x" · g, "t"))) ;;
      (obs "received") !"got" ;;
      match: !"got" with NONE => #false | SOME <> => #true end.
End env_auth.
