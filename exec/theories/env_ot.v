(** * Environments for oblivious transfer with a corrupt receiver
    ([ot/definition_thunk_receiver_corrupt], [ot/advantage_ot])

    The systems are sessions (this case study predates factories).  The
    client gets [(doCRS, doSender)]; the ports are [(doSend, doRecv)] of the
    corrupt receiver: [doRecv ()] answers the receiver's first message
    [(u, v)] (as indices), [doSend (e0, e1)] receives the encryptions. *)
From clutch.prob_eff_lang.probblaze Require Import syntax notation.
From clutch.prob_eff_lang.probblaze.examples Require Import valgroup definition_thunk_receiver_corrupt.
From clutch_exec Require Import exec_common.

Section env_ot.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Import valgroup_notation.
  #[local] Notation n := (S n'').

  (** The real world of [adv_ot_rc]. *)
  Definition OT_REAL_RC : val :=
    (λ: "f" "effs", F_CRS (λ: "doCRS", OT_Real_Receiver_Corrupted "f" ("effs", "doCRS"))%E)%V.

  (** The receiver follows the protocol with choice bit [b]: it reads the
      CRS, sends [(g_b^x, h_b^x)] for a nonzero [x], and decrypts [e_b].
      True iff it recovers the sender's message [m_b], or the sender
      aborted. *)
  Definition env_ot_receiver (b : bool) (obs : string → val) : val :=
    λ: "X",
      let: "m0" := rand #n in
      let: "m1" := rand #n in
      let: "crs" := ref NONE in
      let: "x" := ref #0 in
      let: "got" := ref NONE in
      "X" (λ: "ops", let, ("doCRS", "doSender") := "ops" in
                     "crs" <- SOME ("doCRS" #()%V) ;; "doSender" ("m0", "m1"))
          ((λ: "e", (obs "send") "e" ;; "got" <- SOME "e"),
           (λ: <>,
              match: !"crs" with
                NONE => NONE
              | SOME "c" =>
                  let, ("h1", "h0", "g1", "g0") := "c" in
                  let: "xx" := (rand #(n - 1)) + #1 in
                  "x" <- "xx" ;;
                  let: "u" := (if: #b then "g1" else "g0") ^ "xx" in
                  let: "v" := (if: #b then "h1" else "h0") ^ "xx" in
                  (obs "recv") ("u", "v") ;;
                  SOME (int_of_vg "u", int_of_vg "v")
              end)) ;;
      match: !"got" with
        NONE => #true
      | SOME "e" =>
          let, ("e0", "e1") := "e" in
          let: "mb" := dec !"x" (if: #b then "e1" else "e0") in
          (obs "decrypted") "mb" ;;
          match: vg_of_int (if: #b then "m1" else "m0") with
            NONE => #false
          | SOME "y" => veq "mb" "y"
          end
      end.
End env_ot.
