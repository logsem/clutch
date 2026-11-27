(* Oblivious transfer in the CRS model, as modules (uc_eff/DESIGN.md,
   section 6): the protocol, and the case where both parties are honest.

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
   the second takes the sender's messages.  This is not the textbook
   functionality, whose sender port takes the messages at once and leaves
   the order of the inputs open.  The two-phase port is a concession to
   the proof method of the clients, not a property of OT:

   - In OT reversal (DESIGN.md, section 6) the client samples a mask [r]
     and the proof couples it with the simulator's sample along
     [ρ = r ⊕ (s ∧ c)], which depends on the receiver's choice [s].  The
     couplings of the logic are fixed when the earlier sample is taken, so
     [s] has to be known by then: the client must sample after the first
     phase.  With the textbook port the client samples before the choice,
     and the paper argument (the mask is independent of everything the
     adversary has seen) has no counterpart among the coupling rules.
   - The real protocol already has this shape (the receiver speaks first),
     and a one-phase client calls the two phases one after the other, so
     nothing a client could do with the textbook port is lost.

   The right thing would be the textbook port together with a rule that
   moves a sample past a call to the adversary that does not receive it,
   for one-shot rows; see DESIGN.md, section 10.

   With both parties honest the ideal functionality [F_OT_H] gives the
   adversary one operation per party, [yield_s] and [yield_r], which the
   party calls wherever the real party calls the network: "this party is
   at a scheduling point; resume it when you like" (UC's delayed output,
   for blocking ports).  The ideal functionality has to keep the real
   party's waiting points, because when a port returns is observable to
   the environment.  Its security proof is not done: it needs two DDH
   steps (DESIGN.md, section 6). *)

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
     publishes it to the adversary and returns it.

       module F_CRS_DH (Dh : DDH) (Adv : sig val publish : crs -> unit end) =
         struct let crs = Dh.sample () ;; Adv.publish crs end *)
  Definition F_CRS_DH (dh : val) : val :=
    λ: "publish",
      let: "crs" := dh #()%V in
      "publish" "crs";;
      "crs".

  (* The reference string of the protocol: [(h1, h0, g1, g)] for three
     random group elements, i.e. a random DDH tuple. *)
  Definition F_CRS : val := F_CRS_DH DDH_rand.

  Definition F_CRS_DH_app : val :=
    λ: "dh" "publish",
      let: "crs" := "dh" #()%V in
      "publish" "crs";;
      "crs".

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

  (* It takes the reference string and its network: [recv] returns the
     receiver's message, [send] takes the sender's reply.  It returns the
     sender's port, in two phases: the first takes the receiver's message,
     the second the sender's messages. *)
  Definition OT_S : val :=
    λ: "res",
      let, ("crs", "net") := "res" in
      let, ("recv", "send") := "net" in
      let, ("h1", "h0", "g1", "g0") := "crs" in

      λ: <>,
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

  (* It takes the reference string and its network: [send] takes the
     receiver's message, [recv] returns the sender's reply.  Its port
     takes the choice [b] and returns [m_b]. *)
  Definition OT_R : val :=
    λ: "res",
      let, ("crs", "net") := "res" in
      let, ("send", "recv") := "net" in
      let, ("h1", "h0", "g1", "g0") := "crs" in

      λ: "b",
        let: "x" := sample #()%V in
        let, ("gb", "hb") := if: "b" then ("g1", "h1") else ("g0", "h0") in
        "send" ("gb"^"x", "hb"^"x");;
        let, ("e0", "e1") := "recv" #()%V in
        dec "x" (if: "b" then "e1" else "e0").

  (* ---------------------------------------------------------------- *)
  (* The ideal oblivious transfer, both parties honest.                 *)
  (* ---------------------------------------------------------------- *)

  (* It takes the adversary's operations [yield_s] and [yield_r], one per
     party, and returns the sender's and the receiver's port. *)
  Definition F_OT_H : val :=
    λ: "adv",
      let, ("yield_s", "yield_r") := "adv" in

      (* state: whether the receiver has chosen, and the messages *)
      let: "ch" := ref #false in
      let: "mm" := ref NONE in

      (* the sender: wait for the receiver's choice, then take the
         messages *)
      (λ: <>,
         (rec: "wait" <> :=
            "yield_s" #()%V;;
            if: !"ch" then #()%V else "wait" #()%V) #()%V;;
         λ: "mm'",
           "mm" <- SOME "mm'";;
           "yield_s" #()%V,

      (* the receiver: choose, wait for the messages, take the chosen one *)
       λ: "b",
         "ch" <- #true;;
         let, ("m0", "m1") :=
           (rec: "wait" <> :=
              "yield_r" #()%V;;
              match: !"mm" with NONE => "wait" #()%V | SOME "m" => "m" end) #()%V in
         if: "b" then "m1" else "m0").

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
  (* The simulator, both parties honest.                                *)
  (* ---------------------------------------------------------------- *)

  (* It publishes a reference string in decryption mode and maps each
     party's yields to that party's next move in the real world: for the
     receiver, its message [(g^a, h0^a)] for a fresh [a] and then
     [deliver] of the ciphertexts' channel; for the sender, [deliver] of
     the receiver's channel until the receiver has sent, then encryptions
     of random elements [g^d_i] under [u]. *)
  Definition S_OT_H : val :=
    λ: "adv",
      let, ("publish", "nets") := "adv" in
      let, ("rs", "sr") := "nets" in
      let, ("leak_rs", "deliver_rs") := "rs" in
      let, ("leak_sr", "deliver_sr") := "sr" in

      (* a reference string in decryption mode *)
      let: "y" := sample #()%V in
      let: "x" := sample #()%V in
      let: "g1" := g^"y" in
      let, ("h1", "h0") := ("g1"^"x", g^"x") in
      "publish" ("h1", "h0", "g1", g);;

      (* state: the receiver's message, and whether the sender is in its
         second phase *)
      let: "uu" := ref NONE in
      let: "s_go" := ref #false in

      (* the sender *)
      (λ: <>,
         if: !"s_go" then
           match: !"uu" with
             NONE => #()%V
           | SOME "u" =>
               let, ("t0", "d0", "t1", "d1") :=
                 (sample #()%V, sample #()%V, sample #()%V, sample #()%V) in
               "leak_sr" ((g^"t0", g^"d0" · "u"^"t0"), ("g1"^"t1", g^"d1" · "u"^"t1"))
           end
         else
           ("deliver_rs" #()%V;;
            match: !"uu" with NONE => #()%V | SOME <> => "s_go" <- #true end),

      (* the receiver *)
       λ: <>,
         match: !"uu" with
           NONE =>
             let: "a" := sample #()%V in
             "uu" <- SOME (g^"a");;
             "leak_rs" (g^"a", "h0"^"a");;
             "deliver_sr" #()%V
         | SOME <> => "deliver_sr" #()%V
         end).

  Definition IDEAL_OT_H : val := (F_OT_H ⊳ S_OT_H)%md.

  (* ---------------------------------------------------------------- *)
  (* The hybrids and the reductions.                                    *)
  (* ---------------------------------------------------------------- *)

  (* The real parties on a reference string from a DDH sampler [dh]; the
     real module is [HYB1_OT_H DDH_rand]. *)
  Definition HYB1_OT_H (dh : val) : val := (PARTIES_OT ⊳ (F_CRS_DH dh ⊗ (F_OAUTH ⊗ F_OAUTH)))%md.

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

End ot.

Section ot_types.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* The reference string, and the operation that publishes it. *)
  Definition Crs : sem_ty Σ := (𝔾 × 𝔾 × 𝔾 × 𝔾)%T.
  Definition Pub (θ : sem_row Σ) : sem_ty Σ := (Crs → 𝟙)%T.
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
  (* The adversarial interface of the ideal transfer: one scheduling
     operation per party. *)
  Definition OTHAdv (θ : sem_row Σ) : sem_ty Σ := ((𝟙 -{ θ }-> 𝟙) × (𝟙 -{ θ }-> 𝟙))%T.
  (* Both ports. *)
  Definition OTPorts (θ : sem_row Σ) : sem_ty Σ := (SPort θ × RPort θ)%T.

End ot_types.

(* The security statement, both parties honest, for a group of order [n]:
   an environment that instantiates the module once tells the real from
   the ideal module with at most the DDH advantages of the two reductions
   plus [3/n]. *)
Definition ot_h_secure `{!probblazeRGpreS Σ}
    {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg} : Prop :=
  ∀ A : val,
    (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModA OTHNet OTPorts → 𝔹)%T) →
    (advantage A REAL_OT_H IDEAL_OT_H #true
       <= advantage (RED1_OT_H A) DDH_rand DDH_real #true
          + advantage (RED2_OT_H A) DDH_real DDH_rand #true + 3 / S (S n''))%R.
