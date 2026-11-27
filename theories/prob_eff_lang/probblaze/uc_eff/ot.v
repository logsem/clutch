(* Oblivious transfer in the CRS model, as modules: the protocol, and the
   case where both parties are honest.

   The protocol is that of [examples/ot] (1-out-of-2 OT in the CRS model);
   the choice bit [b] selects the message [m_b].  The parties take the
   reference string and their network operations.  The same code is used
   in every corruption case: with both honest the network operations are
   the endpoints of two one-way authenticated channels [F_OAUTH]
   (auth.v); when the other party is corrupted, they are operations of
   the adversary, who plays that party.  The corruption cases are in
   [ot_corrupted_receiver.v] and [ot_corrupted_sender.v].

     module REAL_OT_H (Adv : sig module Crs : CRS.adv  module RS : AUTH.adv  module SR : AUTH.adv end) =
       struct
         module Crs = F_CRS (Adv.Crs)
         module RS = F_OAUTH (Adv.RS)       (* receiver to sender *)
         module SR = F_OAUTH (Adv.SR)       (* sender to receiver *)
         module S = OT_S (Crs) (struct let recv = RS.recv let send = SR.send end)
         module R = OT_R (Crs) (struct let send = RS.send let recv = SR.recv end)
       end

   The sender's port has two phases, [λ (). … λ (m0, m1). …]: the first
   waits for the receiver's message (and so fixes the receiver's choice),
   the second takes the sender's messages.  The textbook functionality
   instead takes the sender's messages at once and leaves the order of
   the inputs open.  The two phases are there for the clients' proofs:

   - In OT reversal ([ot_rev.v]) the client samples a mask [r], and the
     proof couples it with the simulator's sample along
     [ρ = r ⊕ (s ∧ c)], which depends on the receiver's choice [s].  A
     coupling is fixed when the first of the two samples is taken, so [s]
     must be known by then: the client samples after the first phase.
     With a one-phase port the client would sample before the choice, and
     the argument that the mask is independent of everything the
     adversary has seen has no counterpart among the coupling rules.
   - The real protocol has this shape anyway (the receiver speaks first),
     and a client that does not need it calls the two phases one after
     the other.

   With both parties honest the ideal functionality [F_OT_H] hands control
   to the adversary for a whole party's run, with one operation per party
   ([run_s], [run_r]), and the simulator runs the real parties on dummy
   inputs.  The environment schedules the parties by handling the network
   operations, so neither the functionality nor the simulator keeps track
   of how far a party is.  The proof is in [ot_proof.v]. *)

From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze Require Import logic adequacy sem_def sem_types sem_row sem_judgement.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules auth.
From Stdlib Require Import Reals.

Import fingroup.
Import valgroup_notation.

Section ot.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').

  Definition sample : val := λ: <>, rand #n.

  (* Encryption of [m] under the key [(g, h, u, v)] with randomness [r], [s]. *)
  Definition enc : val :=
    λ: "pk" "m" "r" "s",
      let, ("g", "h", "u", "v") := "pk" in
      ("g"^"r" · "h"^"s", "m" · ("u"^"r") · ("v"^"s")).

  (* Decryption of a ciphertext [(c, d)] with the secret [x]. *)
  Definition dec : val := λ: "x" "e", let, ("c", "d") := "e" in "d" · ("c" ^- "x").

  (* ---------------------------------------------------------------- *)
  (* The decisional Diffie-Hellman problem.                             *)
  (* ---------------------------------------------------------------- *)

  (* The generator [g] of the group is a public parameter, fixed in
     advance.  A DDH tuple [(g^y, g^x, g^(y x))] against a random tuple
     [(g^y, g^x, g^z)], each in the shape of a reference string
     [(h1, h0, g1, g0)] with [g0 = g]: [(g^(y x), g^x, g^y, g)] and
     [(g^z, g^x, g^y, g)].  Each call samples a fresh tuple. *)
  Definition DDH_real : val :=
    λ: <>,
      let: "y" := sample #()%V in
      let: "x" := sample #()%V in
      let: "g1" := g^"y" in
      ("g1"^"x", g^"x", "g1", g).

  Definition DDH_rand : val :=
    λ: <>,
      let: "y" := sample #()%V in
      let: "x" := sample #()%V in
      let: "z" := sample #()%V in
      (g^"z", g^"x", g^"y", g).

  (* ---------------------------------------------------------------- *)
  (* The common reference string.                                       *)
  (* ---------------------------------------------------------------- *)

  (* The reference string taken from a DDH sampler [dh]: the functionality
     samples it when it is set up, sends it to the adversary (push), and
     gives the parties a port to request it (pull).  The string is the same
     for every request; sampling it at the first request instead would make
     no observable difference.  This is the [F_crs] of the UC literature,
     which hands the string to the parties of the protocol and to the
     adversary.

       module F_CRS_DH (Dh : DDH) (Adv : sig val publish : crs -> unit end) =
         struct
           let crs = Dh.sample () ;; Adv.publish crs
           let get () = crs
         end *)
  Definition F_CRS_DH (dh : val) : val :=
    λ: "publish",
      let: "crs" := dh #()%V in
      "publish" "crs";;
      λ: <>, "crs".

  (* The reference string of the protocol: [(h1, h0, g1, g)] for three
     random group elements, i.e. a random DDH tuple. *)
  Definition F_CRS : val := F_CRS_DH DDH_rand.

  Definition F_CRS_DH_app : val :=
    λ: "dh" "publish",
      let: "crs" := "dh" #()%V in
      "publish" "crs";;
      λ: <>, "crs".

  Lemma F_CRS_DH_app_pure (dh : val) : rtc pure_step (F_CRS_DH_app dh) (F_CRS_DH dh).
  Proof.
    rewrite /F_CRS_DH_app /F_CRS_DH.
    eapply rtc_l.
    { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
    simpl. eapply rtc_l.
    { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
    done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The protocol: the sender.                                          *)
  (* ---------------------------------------------------------------- *)

  (* It takes the reference string's port and its network: [recv] returns
     the receiver's message, [send] takes the sender's reply.  It returns
     the sender's port, in two phases: the first requests the reference
     string and takes the receiver's message, the second the sender's
     messages. *)
  Definition OT_S : val :=
    λ: "res",
      let, ("crs", "net") := "res" in
      let, ("recv", "send") := "net" in

      λ: <>,
        let, ("h1", "h0", "g1", "g0") := "crs" #()%V in
        let, ("u", "v") := "recv" #()%V in
        λ: "mm",
          let, ("m0", "m1") := "mm" in
          if: veq "u" vunit then #()%V else
            let: "pk0" := ("g0", "h0", "u", "v") in
            let: "pk1" := ("g1", "h1", "u", "v") in
            let, ("r0", "s0", "r1", "s1") :=
              (sample #()%V, sample #()%V, sample #()%V, sample #()%V) in
            let: "e0" := enc "pk0" "m0" "r0" "s0" in
            let: "e1" := enc "pk1" "m1" "r1" "s1" in
            "send" ("e0", "e1").

  (* ---------------------------------------------------------------- *)
  (* The protocol: the receiver.                                        *)
  (* ---------------------------------------------------------------- *)

  (* It takes the reference string's port and its network: [send] takes
     the receiver's message, [recv] returns the sender's reply.  Its port
     takes the choice [b], requests the reference string, and returns
     [m_b]. *)
  Definition OT_R : val :=
    λ: "res",
      let, ("crs", "net") := "res" in
      let, ("send", "recv") := "net" in

      λ: "b",
        let, ("h1", "h0", "g1", "g0") := "crs" #()%V in
        let: "x" := sample #()%V in
        let, ("gb", "hb") := if: "b" then ("g1", "h1") else ("g0", "h0") in
        "send" ("gb"^"x", "hb"^"x");;
        let, ("e0", "e1") := "recv" #()%V in
        dec "x" (if: "b" then "e1" else "e0").

  (* ---------------------------------------------------------------- *)
  (* The ideal oblivious transfer, both parties honest.                 *)
  (* ---------------------------------------------------------------- *)

  (* It takes the adversary's operations [run_s] and [run_r], one per
     party, and returns the sender's and the receiver's port.  A port
     records the party's input and hands control to the adversary for the
     whole of that party's run (UC's delayed output); [run_s] returns the
     operation for the sender's second phase.  The sender's first phase
     returns only if the receiver has chosen, and the receiver gets [m_b]
     only if the sender has given its messages; otherwise the port never
     returns. *)
  Definition F_OT_H : val :=
    λ: "adv",
      let, ("run_s", "run_r") := "adv" in

      (* state: whether the receiver has chosen, and the messages *)
      let: "ch" := ref #false in
      let: "mm" := ref NONE in

      (* the sender *)
      (λ: <>,
         let: "run_s2" := "run_s" #()%V in
         if: !"ch" then (λ: "mm'", "mm" <- SOME "mm'";; "run_s2" #()%V) else loop #()%V,

      (* the receiver *)
       λ: "b",
         "ch" <- #true;;
         "run_r" #()%V;;
         match: !"mm" with
           NONE => loop #()%V
         | SOME "m" => let, ("m0", "m1") := "m" in if: "b" then "m1" else "m0"
         end).

  (* ---------------------------------------------------------------- *)
  (* The real module, both parties honest.                              *)
  (* ---------------------------------------------------------------- *)

  (* The two parties on the reference string and the two channels:
     [res = (crs, ((send_rs, recv_rs), (send_sr, recv_sr)))]. *)
  Definition PARTIES_OT : val :=
    λ: "res",
      let, ("crs", "chans") := "res" in
      let, ("rs", "sr") := "chans" in
      let, ("send_rs", "recv_rs") := "rs" in
      let, ("send_sr", "recv_sr") := "sr" in
      (OT_S ("crs", ("recv_rs", "send_sr")), OT_R ("crs", ("send_rs", "recv_sr"))).

  Definition REAL_OT_H : val := (PARTIES_OT ⊳ (F_CRS ⊗ (F_OAUTH ⊗ F_OAUTH)))%md.

  (* ---------------------------------------------------------------- *)
  (* The hybrids and the reductions.                                    *)
  (* ---------------------------------------------------------------- *)

  (* The real parties on a reference string from a DDH sampler [dh]; the
     real module is [HYB1_OT_H DDH_rand]. *)
  Definition HYB1_OT_H (dh : val) : val := (PARTIES_OT ⊳ (F_CRS_DH dh ⊗ (F_OAUTH ⊗ F_OAUTH)))%md.

  (* ---------------------------------------------------------------- *)
  (* The simulator, both parties honest.                                *)
  (* ---------------------------------------------------------------- *)

  (* The real parties on dummy inputs: [run_s] runs the sender's first
     phase and returns its second phase on the messages [(1, 1)]; [run_r]
     runs the receiver with choice [false] and drops its output.  As usual
     in the CRS model, the simulator chooses the reference string: a DDH
     tuple (decryption mode), so that the receiver's message hides its
     choice and both ciphertexts are encryptions. *)
  Definition DUMMY_OT : val :=
    λ: "ports",
      let, ("sport", "rport") := "ports" in
      (λ: <>, let: "k" := "sport" #()%V in λ: <>, "k" (vunit, vunit),
       λ: <>, "rport" #false;; #()%V).

  Definition S_OT_H : val := (DUMMY_OT ⊳ HYB1_OT_H DDH_real)%md.
  Definition IDEAL_OT_H : val := (F_OT_H ⊳ S_OT_H)%md.

  (* The parties with a reference string in decryption mode, whose
     receiver's message and ciphertexts are built from one tuple of the
     sampler [dh = (C, B, A, g)], taken when the receiver chooses, by
     rerandomisation: [u = A], and slot [i] is
     [((B^α_i · g^β_i)^(y_i), m_i · C^α_i · A^β_i)].  For a DDH tuple
     these are honest encryptions under [u]; for a random one, of random
     elements.  The parties share the sender's messages: the receiver
     outputs the chosen one. *)
  Definition HYB2_body (dh : expr) : expr :=
      let, ("publish", "nets") := "adv" in
      let, ("rs", "sr") := "nets" in

      (* a reference string in decryption mode *)
      let: "y" := sample #()%V in
      let: "x" := sample #()%V in
      let: "g1" := g^"y" in
      let: "crs" := ("g1"^"x", g^"x", "g1", g) in
      "publish" "crs";;

      (* the two channels *)
      let, ("send_rs", "recv_rs") := F_OAUTH "rs" in
      let, ("send_sr", "recv_sr") := F_OAUTH "sr" in

      (* state: the tuple, and the sender's messages *)
      let: "tup" := ref NONE in
      let: "mm" := ref NONE in

      (* the sender *)
      (λ: <>,
         let, ("u", "v") := "recv_rs" #()%V in
         λ: "mm'",
           let, ("m0", "m1") := "mm'" in
           "mm" <- SOME "mm'";;
           if: veq "u" vunit then #()%V else
             match: !"tup" with
               NONE => #()%V
             | SOME "t" =>
                 let, ("C", "B", "A") := "t" in
                 let, ("b0", "a0", "b1", "a1") :=
                   (sample #()%V, sample #()%V, sample #()%V, sample #()%V) in
                 let: "e0" := ("B"^"a0" · g^"b0", "m0" · ("C"^"a0" · "A"^"b0")) in
                 let: "e1" := (("B"^"a1" · g^"b1")^"y", "m1" · ("C"^"a1" · "A"^"b1")) in
                 "send_sr" ("e0", "e1")
             end,

      (* the receiver *)
       λ: "b",
         let, ("C", "B", "A", <>) := dh #()%V in
         "tup" <- SOME ("C", "B", "A");;
         "send_rs" ("A", "A"^"x");;
         "recv_sr" #()%V;;
         match: !"mm" with
           NONE => g
         | SOME "mm'" => let, ("m0", "m1") := "mm'" in if: "b" then "m1" else "m0"
         end).

  Definition HYB2_OT_H (dh : val) : val := (λ: "adv", HYB2_body dh)%V.
  Definition HYB2_app : val := (λ: "dh" "adv", HYB2_body "dh")%V.

  (* The environment with the rest of the world around the sampler, an
     adversary against DDH, for each of the two steps. *)
  Definition RED1_OT_H (A : val) : val :=
    λ: "v", A (comp_app PARTIES_OT (tens_app (F_CRS_DH_app "v") (F_OAUTH ⊗ F_OAUTH)%md)).
  Definition RED2_OT_H (A : val) : val := λ: "v", A (HYB2_app "v").

  (* The environment with the functionality and the dummy inputs in front:
     the hybrid steps are taken again on the ideal side, under it. *)
  Definition DENV_OT_H (A : val) : val :=
    λ: "v", (λ: "v", A (comp_app F_OT_H "v"))%V (comp_app DUMMY_OT "v").

End ot.

Section ot_types.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* The reference string, the operation that publishes it to the
     adversary, and the parties' port that requests it. *)
  Definition Crs : sem_ty Σ := (𝔾 × 𝔾 × 𝔾 × 𝔾)%T.
  Definition Pub (θ : sem_row Σ) : sem_ty Σ := (Crs → 𝟙)%T.
  Definition CrsPort (θ : sem_row Σ) : sem_ty Σ := (𝟙 → Crs)%T.
  (* The sender's port, in two phases: the first fixes the receiver's
     choice, the second takes the sender's messages (see the comment at the
     top of the file). *)
  Definition SPort (θ : sem_row Σ) : sem_ty Σ :=
    (𝟙 -{ ¡ θ }-∘ ((𝔾 × 𝔾) -{ ¡ θ }-∘ 𝟙))%T.
  (* The receiver's port: the choice, and the chosen message. *)
  Definition RPort (θ : sem_row Σ) : sem_ty Σ := (𝔹 -{ ¡ θ }-∘ 𝔾)%T.

  (* The adversarial interface of a one-way channel carrying [τ]. *)
  Definition LNet (τ : sem_ty Σ) (θ : sem_row Σ) : sem_ty Σ :=
    ((τ -{ θ }-> 𝟙) × (𝟙 -{ θ }-> 𝟙))%T.
  (* Both honest.  The real adversarial interface: the reference string,
     the channel of the receiver's message, the channel of the
     ciphertexts. *)
  Definition OTHNet (θ : sem_row Σ) : sem_ty Σ :=
    (Pub θ × (LNet (𝔾 × 𝔾) θ × LNet ((𝔾 × 𝔾) × (𝔾 × 𝔾)) θ))%T.
  (* The adversarial interface of the ideal transfer: one operation per
     party, which runs it (the sender's returns its second phase).
     One-shot: only the functionality calls them. *)
  Definition OTHAdv (θ : sem_row Σ) : sem_ty Σ :=
    ((𝟙 -{ ¡ θ }-∘ (𝟙 -{ ¡ θ }-∘ 𝟙)) × (𝟙 -{ ¡ θ }-∘ 𝟙))%T.
  (* Both ports. *)
  Definition OTPorts (θ : sem_row Σ) : sem_ty Σ := (SPort θ × RPort θ)%T.

End ot_types.

(* The security statement, both parties honest, for a group of order [n]:
   an environment that instantiates the module once tells the real from
   the ideal module with at most the DDH advantages of three reductions
   (the second step twice: for the real inputs, and for the dummy ones
   under the functionality) plus [3/n]. *)
Definition ot_h_secure `{!probblazeRGpreS Σ}
    {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg} : Prop :=
  ∀ A : val,
    (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModA OTHNet OTPorts → 𝔹)%T) →
    (advantage A REAL_OT_H IDEAL_OT_H #true
       <= advantage (RED1_OT_H A) DDH_rand DDH_real #true
          + advantage (RED2_OT_H A) DDH_real DDH_rand #true
          + advantage (RED2_OT_H (DENV_OT_H A)) DDH_real DDH_rand #true + 3 / S (S n''))%R.
