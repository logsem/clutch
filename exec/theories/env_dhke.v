(** * Environments for the Diffie–Hellman key exchange ([dhke_def])

    The systems take a client and the authenticated channel's leak ports
    [(doLeakSend, doLeakRecv)].  The client gets [doGK]; in [DH_KE] the
    party [InjL ()] is Alice and [InjR ()] is Bob. *)
From clutch.prob_eff_lang.probblaze Require Import syntax notation.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup dhke_def.
From clutch_exec Require Import exec_common.

Section env_dhke.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Import valgroup_notation.

  Definition partyA : val := InjLV #()%V.
  Definition partyB : val := InjRV #()%V.

  (** Leak ports that deliver everything and observe each call. *)
  Definition dh_ports (obs : string → val) : expr :=
    ((λ: "m", (obs "leakSend") "m"),
     (λ: "from", (obs "leakRecv") "from" ;; SOME #()%V))%E.

  (** Honest run.  Alice's first query cannot complete, since Bob has not
      sent yet; Bob's query completes the exchange and Alice's second query
      reads Bob's half.  True iff Bob's key and Alice's second key agree. *)
  Definition env_dhke_honest (obs : string → val) : val :=
    λ: "X",
      let: "ka1" := ref NONE in
      let: "kb" := ref NONE in
      let: "ka2" := ref NONE in
      let: "s" := "X" #()%V in
      "s" (λ: "doGK", "ka1" <- "doGK" partyA ;;
                      "kb" <- "doGK" partyB ;;
                      "ka2" <- "doGK" partyA)
          (dh_ports obs) ;;
      (obs "keys") (!"ka1", !"kb", !"ka2") ;;
      match: !"kb" with
        NONE => #false
      | SOME "k" => match: !"ka2" with
                      NONE => #false
                    | SOME "k2" => veq "k" "k2"
                    end
      end.

  (** A distinguisher that solves the discrete logarithm of Alice's half,
      which is feasible in a toy group: it accepts iff Bob's key is
      [gB^(log gA)].  It always accepts the real protocol; in the ideal
      world the key is independent of the simulated halves. *)
  Definition env_dhke_dlog (obs : string → val) : val :=
    λ: "X",
      let: "gA" := ref NONE in
      let: "gB" := ref NONE in
      let: "kb" := ref NONE in
      let: "s" := "X" #()%V in
      "s" (λ: "doGK", "doGK" partyA ;; "kb" <- "doGK" partyB ;; #()%V)
          ((λ: "m", (obs "leakSend") "m" ;;
                    let, ("x", "dst") := "m" in
                    match: "dst" with
                      InjL <> => "gA" <- SOME "x"
                    | InjR <> => "gB" <- SOME "x"
                    end),
           (λ: "from", (obs "leakRecv") "from" ;; SOME #()%V)) ;;
      match: !"kb" with
        NONE => #false
      | SOME "k" =>
          match: !"gA" with
            NONE => #false
          | SOME "ga" =>
              match: !"gB" with
                NONE => #false
              | SOME "gb" =>
                  let: "a" := dlog "ga" in
                  (obs "dlog") ("ga", "a") ;;
                  veq "k" ("gb" ^ "a")
              end
          end
      end.

  (** Delivers nothing: every receive is refused.  No party gets a key. *)
  Definition env_dhke_block (obs : string → val) : val :=
    λ: "X",
      let: "ka" := ref NONE in
      let: "kb" := ref NONE in
      let: "s" := "X" #()%V in
      "s" (λ: "doGK", "ka" <- "doGK" partyA ;; "kb" <- "doGK" partyB)
          ((λ: "m", (obs "leakSend") "m"),
           (λ: "from", (obs "leakRecv") "from" ;; NONE)) ;;
      (obs "keys") (!"ka", !"kb") ;;
      match: !"ka" with
        NONE => match: !"kb" with NONE => #true | SOME <> => #false end
      | SOME <> => #false
      end.
End env_dhke.
