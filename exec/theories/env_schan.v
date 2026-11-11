(** * Environments for the one-message secure channel ([sec_channel_def])
    and its composition with DHKE ([advantage_dhke_sec_channel])

    The client gets [(doSecSend, doSecRecv)]; [doSecSend m] sends the group
    element with index [m], [doSecRecv ()] returns what Bob received.  The
    ports are [(oauth, ke)]: the leak ports of the authenticated channel
    and of the key exchange (of [F_KE_lazy_alice], or of [REAL_DHKE]'s
    [F_AUTH] in the composition). *)
From clutch.prob_eff_lang.probblaze Require Import syntax notation.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup dhke_def sec_channel_def.
From clutch_exec Require Import exec_common env_dhke.

Import fingroup.
#[local] Open Scope factory_scope.

Section env_schan.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {msk : @Mask (@vgG vg) vgval}.
  Import valgroup_notation.
  #[local] Notation n := (S n'').

  (** The composite systems of [advantage_dhke_sec_channel], restated here
      to avoid depending on the proofs in that file. *)
  Definition REAL_DHKE_CHAN : val := ((REAL_DHKE ||ᵣ F_OAUTH) ∘f CHAN)%fac.
  Definition SIM_DHKE_CHAN : val := (SIM_DHKE ∘F SIM_SCHAN)%fac.
  Definition RED_DHKE_CHAN (A : val) : val :=
    RED_DHKE (λ: "v", A (("v" ||ᵣₚ F_OAUTH) ∘fₚ CHAN))%V.

  (** Is [r] the option of the group element with index [m]? *)
  Definition is_some_elem : val :=
    λ: "r" "m",
      match: "r" with
        NONE => #false
      | SOME "x" => match: vg_of_int "m" with NONE => #false | SOME "y" => veq "x" "y" end
      end.

  (** Honest run: Alice sends a uniformly chosen message, Bob receives it,
      every leak is delivered.  True iff Bob gets Alice's message. *)
  Definition env_chan_honest (obs : string → val) : val :=
    λ: "X",
      let: "m" := rand #n in
      let: "out" := ref NONE in
      let: "s" := "X" #()%V in
      "s" (λ: "ops", let, ("snd", "rcv") := "ops" in "snd" "m" ;; "out" <- "rcv" #()%V)
          (deliver_ports obs "oauth", deliver_ports obs "ke") ;;
      (obs "received") ("m", !"out") ;;
      is_some_elem !"out" "m".

  (** As [env_chan_honest], but the client alternates receive and send
      attempts: receive, send, receive, send, receive.  True iff some
      receive returns Alice's message. *)
  Definition env_chan_retry (obs : string → val) : val :=
    λ: "X",
      let: "m" := rand #n in
      let: "ok" := ref #false in
      let: "s" := "X" #()%V in
      "s" (λ: "ops",
             let, ("snd", "rcv") := "ops" in
             let: "try" := (λ: <>, let: "r" := "rcv" #()%V in
                                   (obs "received") "r" ;;
                                   if: is_some_elem "r" "m" then "ok" <- #true else #()%V) in
             "try" #()%V ;; "snd" "m" ;; "try" #()%V ;; "snd" "m" ;; "try" #()%V)
          (deliver_ports obs "oauth", deliver_ports obs "ke") ;;
      !"ok".

  (** True iff the ciphertext on the authenticated channel is the message
      itself.  The mask makes the ciphertext uniform, in both worlds. *)
  Definition env_chan_peek (obs : string → val) : val :=
    λ: "X",
      let: "m" := rand #n in
      let: "ct" := ref NONE in
      let: "s" := "X" #()%V in
      "s" (λ: "ops", let, ("snd", "rcv") := "ops" in "snd" "m" ;; "rcv" #()%V ;; #()%V)
          (((λ: "p", (obs "oauth.send") "p" ;; let, ("c", "dst") := "p" in "ct" <- SOME "c"),
            (λ: "from", (obs "oauth.recv") "from" ;; SOME #()%V)),
           deliver_ports obs "ke") ;;
      is_some_elem !"ct" "m".

  (** For the composition with DHKE: recover the key from the leaked halves
      by a discrete logarithm and unmask the ciphertext.  Always true in the
      real world; in the ideal world the halves are simulated. *)
  Definition env_dhke_chan_dlog (obs : string → val) : val :=
    λ: "X",
      let: "m" := rand #n in
      let: "ct" := ref NONE in
      let: "gA" := ref NONE in
      let: "gB" := ref NONE in
      let: "s" := "X" #()%V in
      "s" (λ: "ops", let, ("snd", "rcv") := "ops" in "snd" "m" ;; "rcv" #()%V ;; #()%V)
          (((λ: "p", (obs "oauth.send") "p" ;; let, ("c", "dst") := "p" in "ct" <- SOME "c"),
            (λ: "from", (obs "oauth.recv") "from" ;; SOME #()%V)),
           ((λ: "p", (obs "auth.send") "p" ;;
                     let, ("x", "dst") := "p" in
                     match: "dst" with InjL <> => "gA" <- SOME "x" | InjR <> => "gB" <- SOME "x" end),
            (λ: "from", (obs "auth.recv") "from" ;; SOME #()%V))) ;;
      match: !"ct" with
        NONE => #false
      | SOME "c" =>
          match: !"gA" with
            NONE => #false
          | SOME "ga" =>
              match: !"gB" with
                NONE => #false
              | SOME "gb" =>
                  let: "key" := "gb" ^ (dlog "ga") in
                  is_some_elem (SOME (mask "key" "c")) "m"
              end
          end
      end.

  (** The scheduler of [dhke_chan_delivery.sched_prog]: when the key
      exchange leaks a share (Alice's, the first time), Bob is activated
      before the leak returns, by a nested call of the same session whose
      client receives once.  The session takes a client any number of times
      ([τ__F], since e74cf72e on prob_eff_lang), and the calls share its
      state.  True iff the main client's receive gets Alice's message. *)
  Definition env_chan_sched (obs : string → val) : val :=
    λ: "X",
      let: "m" := rand #n in
      let: "res" := ref NONE in
      let: "s" := "X" #()%V in
      let: "scheduler" := (λ: "x",
         (obs "ke.send") "x" ;;
         "s" (λ: "ops", let, ("ssend", "srecv") := "ops" in (obs "bob received") ("srecv" #()%V))
             (deliver_ports obs "oauth", deliver_ports obs "ke")) in
      "s" (λ: "ops", let, ("ssend", "srecv") := "ops" in "ssend" "m" ;; "res" <- "srecv" #()%V)
          (deliver_ports obs "oauth",
           ("scheduler", (λ: "from", (obs "ke.recv") "from" ;; SOME #()%V))) ;;
      (obs "received") ("m", !"res") ;;
      is_some_elem !"res" "m".
End env_schan.
