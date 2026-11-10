(** * Environments for the secure channel with a symmetric scheme
    ([ske_sec_chan_def]), instantiated with the PRF-based scheme
    ([prf/ske_prf], [prf/prf_results])

    The interface is that of the mask channel ([env_schan]): the client
    gets [(doSecSend, doSecRecv)], the ports are [(oauth, ke)]; messages
    are indices into the message type [ms]. *)
From clutch.prob_eff_lang.probblaze Require Import syntax notation.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup fin_val_type fin_val_type_prod ske ske_prf.
From clutch.prob_eff_lang.probblaze.examples Require ske_sec_chan_def.
From clutch_exec Require Import exec_common.

Section env_ske.
  Context {mt : fin_val_type} {ms : @fin_val_type_struct mt}.

  #[local] Notation N := (fin_val_type.card (fin_val_type := mt)).

  Definition is_some_msg : val :=
    λ: "r" "m",
      match: "r" with
        NONE => #false
      | SOME "x" => match: ms.(fvt_of_int) "m" with NONE => #false | SOME "y" => "x" = "y" end
      end.

  (** Alice sends a uniformly chosen message, Bob receives it.  True iff
      Bob gets it. *)
  Definition env_ske_honest (obs : string → val) : val :=
    λ: "X",
      let: "m" := rand #(N - 1) in
      let: "out" := ref NONE in
      let: "s" := "X" #()%V in
      "s" (λ: "ops", let, ("snd", "rcv") := "ops" in "snd" "m" ;; "out" <- "rcv" #()%V)
          (deliver_ports obs "oauth", deliver_ports obs "ke") ;;
      (obs "received") ("m", !"out") ;;
      is_some_msg !"out" "m".

  (** True iff the second component of the ciphertext [(r, c)] is the
      message: the pad [prf k r] is then zero. *)
  Definition env_ske_peek (obs : string → val) : val :=
    λ: "X",
      let: "m" := rand #(N - 1) in
      let: "ct" := ref NONE in
      let: "s" := "X" #()%V in
      "s" (λ: "ops", let, ("snd", "rcv") := "ops" in "snd" "m" ;; "rcv" #()%V ;; #()%V)
          (((λ: "p", (obs "oauth.send") "p" ;; let, ("c", "dst") := "p" in "ct" <- SOME "c"),
            (λ: "from", (obs "oauth.recv") "from" ;; SOME #()%V)),
           deliver_ports obs "ke") ;;
      match: !"ct" with
        NONE => #false
      | SOME "c" => is_some_msg (SOME (Snd "c")) "m"
      end.
End env_ske.

Section reductions.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {nt mt : fin_val_type} {ns : @fin_val_type_struct nt} {ms : @fin_val_type_struct mt}.

  (** The environment of [adv_schan_prf] against the PRF games. *)
  Definition RED_SKE_PRF (A : val) : val :=
    (λ: "F", @ske_sec_chan_def.RED_SKE vg cg vgg mt ms A (@red_prf nt mt ns ms "F"))%V.
End reductions.
