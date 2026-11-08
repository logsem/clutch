(* Realising the authenticated channel [F_AUTH] over the raw network with a
   preshared one-time MAC.

   The protocol [AUTH] runs both parties.  Its ports [effs = (doSend, doRecv)]
   are the raw network, i.e. the environment: every pair it sends is seen by
   the environment, and what it receives is whatever the environment injects.
   Each direction has its own one-time MAC instance, created at setup: the
   first message in a direction is sent as the pair [(m, tag m)], and the
   receiver accepts the first pair whose tag checks.

   A MAC instance is a pair of closures [(tag, verify)] over its own state
   ([MAC], below): [tag m] tags the first message and refuses later ones;
   [verify (m', t')] decides the first pair it is given and repeats that
   verdict afterwards.  The key [(k1, k2)] is sampled at first use, from
   tapes, with [tag k1 k2 m = m^k1 · g^k2].

   The security proof swaps the MAC instance for two others with the same
   interface ([MAC_pad], [MAC_ideal]); [AUTH_of M] is the protocol over the
   instance [M], and [AUTH = AUTH_of MAC].  The simulator [S_AUTH] runs the
   ideal instance: it turns [F_AUTH]'s leak-and-permit interface into the raw
   network's by tagging the leaked message, and permits delivery iff the
   environment injects exactly the tagged pair.

   Slots follow [F_AUTH]: messages with destination [InjL] live in slot 1 and
   are read by a receiver [InjR], and symmetrically. *)

From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.common Require Import locations.
From clutch.prob_eff_lang.probblaze Require Import metatheory class_instances.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

Section auth_def.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').

  (* [tag k1 k2 m = m^k1 · g^k2] *)
  Definition tag : val := λ: "k1" "k2" "m", "m" ^ "k1" · g ^ "k2".

  (* ------------------------------------------------------------------ *)
  (* The one-time MAC instances.                                         *)
  (* ------------------------------------------------------------------ *)

  (* The MAC: the key is sampled at first use. *)
  Definition MAC : val := λ: <>,
    let: "α" := alloc #n in let: "β" := alloc #n in
    let: "key" := ref NONEV in
    let: "getkey" := λ: <>,
      match: !"key" with
        NONE => let: "k1" := rand("α") #n in let: "k2" := rand("β") #n in
                "key" <- SOME ("k1", "k2");; ("k1", "k2")
      | SOME "k" => "k"
      end in
    let: "tagged" := ref #false in
    let: "verdict" := ref NONEV in
    ((λ: "m",
        if: !"tagged" then NONEV
        else "tagged" <- #true;;
             let, ("k1", "k2") := "getkey" #()%V in SOME (tag "k1" "k2" "m")),
     (λ: "p",
        match: !"verdict" with
          SOME "b" => "b"
        | NONE =>
            let, ("m'", "t'") := "p" in
            let, ("k1", "k2") := "getkey" #()%V in
            let: "b" := veq "t'" (tag "k1" "k2" "m'") in
            "verdict" <- SOME "b";; "b"
        end)).

  (* The MAC with the tag reparametrised: when the tag comes first it is a
     uniform group element [g^r], and the exponent [k1] is only sampled when
     a different message is verified against it.  When a pair is verified
     before anything is tagged, the key is sampled then and used by the tag. *)
  Definition MAC_pad : val := λ: <>,
    let: "α" := alloc #n in let: "β" := alloc #n in
    let: "key" := ref NONEV in
    let: "tg" := ref NONEV in
    let: "verdict" := ref NONEV in
    ((λ: "m",
        match: !"tg" with
          SOME <> => NONEV
        | NONE =>
            let: "t" := match: !"key" with
                          SOME "k" => let, ("k1", "k2") := "k" in tag "k1" "k2" "m"
                        | NONE => g ^ (rand("β") #n)
                        end in
            "tg" <- SOME ("m", "t");; SOME "t"
        end),
     (λ: "p",
        match: !"verdict" with
          SOME "b" => "b"
        | NONE =>
            let, ("m'", "t'") := "p" in
            let: "b" := match: !"tg" with
                          NONE => let: "k1" := rand("α") #n in let: "k2" := rand("β") #n in
                                  "key" <- SOME ("k1", "k2");; veq "t'" (tag "k1" "k2" "m'")
                        | SOME "q" => let, ("m", "t") := "q" in
                                      if: veq "m'" "m" then veq "t'" "t"
                                      else let: "k1" := rand("α") #n in
                                           veq "t'" ("t" · ("m'" · "m"^-1) ^ "k1")
                        end in
            "verdict" <- SOME "b";; "b"
        end)).

  (* The ideal MAC: it accepts exactly the pair it tagged.  (Its tag is that
     of [MAC_pad]; the key sampled by a verification that comes first is kept
     for the tag, so that [MAC_pad] and [MAC_ideal] differ in nothing but
     the verdict.) *)
  (* The ideal MAC, with its state as parameters: [tag] (with "m" free) and
     [verify] (with "p" free). *)
  Definition ideal_tag_b (β key tg : expr) : expr :=
    match: !tg with
      SOME <> => NONEV
    | NONE =>
        let: "t" := match: !key with
                      SOME "k" => let, ("k1", "k2") := "k" in tag "k1" "k2" "m"
                    | NONE => g ^ (rand(β) #n)
                    end in
        tg <- SOME ("m", "t");; SOME "t"
    end.

  Definition ideal_verify_b (α β key tg verdict : expr) : expr :=
    match: !verdict with
      SOME "b" => "b"
    | NONE =>
        let, ("m'", "t'") := "p" in
        let: "b" := match: !tg with
                      NONE => let: "k1" := rand(α) #n in let: "k2" := rand(β) #n in
                              key <- SOME ("k1", "k2");; #false
                    | SOME "q" => let, ("m", "t") := "q" in
                                  veq "m'" "m" && veq "t'" "t"
                    end in
        verdict <- SOME "b";; "b"
    end.

  Definition MAC_ideal : val := λ: <>,
    let: "α" := alloc #n in let: "β" := alloc #n in
    let: "key" := ref NONEV in
    let: "tg" := ref NONEV in
    let: "verdict" := ref NONEV in
    ((λ: "m", ideal_tag_b "β" "key" "tg"), (λ: "p", ideal_verify_b "α" "β" "key" "tg" "verdict")).

  (* An instance of the ideal MAC, over its state. *)
  Definition mac_ideal_v (α β key tg verdict : loc) : val :=
    ((λ: "m", ideal_tag_b #lbl:β #key #tg)%V, (λ: "p", ideal_verify_b #lbl:α #lbl:β #key #tg #verdict)%V)%V.

  (* ------------------------------------------------------------------ *)
  (* The protocol.                                                       *)
  (* ------------------------------------------------------------------ *)

  (* The skeleton of a session: the client's [send]/[recv] are handled by
     [hs]/[hr], which see the outside ports as [doLeakSend]/[doLeakRecv].
     This is literally the shape of [F_AUTH]'s session, so that the two can
     be related by relating their handler bodies. *)
  Definition auth_skel' (hs hr : expr) : expr :=
    effect "send"
      effect "recv"
      let: "doSend" := (λ: "m", do: "send" "m") in
      let: "doRecv" := (λ: "m", do: "recv" "m") in
      handle: handle: "f" ("doSend", "doRecv") with
    | effect "send" "message", rec "k" => hs
    | return "y" => #()%V end with
    | effect "recv" "from", rec "k" => hr
    | return "y" => #()%V end.
  Definition auth_skel (hs hr : expr) : expr :=
    let, ("doLeakSend", "doLeakRecv") := "effs" in auth_skel' hs hr.

  (* [send]: tag the first message of each direction and put it on the network. *)
  Definition auth_send_h (maca macb : expr) : expr :=
    let, ("m", "dst") := "message" in
    let: "mac" := match: "dst" with InjL <> => maca | InjR <> => macb end in
    (match: (Fst "mac") "m" with
       NONE => #()%V
     | SOME "t" => "doLeakSend" (("m", "t"), "dst")
     end);;
    "k" #()%V.

  (* [recv]: verify the first pair delivered in a direction, and repeat the
     verdict afterwards.  A receiver [InjL] reads slot 2, a receiver [InjR]
     reads slot 1. *)
  Definition auth_recv_h (maca macb dec1 dec2 res1 res2 : expr) : expr :=
    let: "mac" := match: "from" with InjL <> => macb | InjR <> => maca end in
    let: "dec" := match: "from" with InjL <> => dec2 | InjR <> => dec1 end in
    let: "res" := match: "from" with InjL <> => res2 | InjR <> => res1 end in
    if: !"dec" then "k" !"res"
    else
      match: "doLeakRecv" "from" with
        NONE => "k" NONEV
      | SOME "p" =>
          (* decided meanwhile? *)
          if: !"dec" then "k" !"res"
          else
            let, ("m'", "t'") := "p" in
            let: "r" := if: (Snd "mac") ("m'", "t'") then SOME "m'" else NONEV in
            "dec" <- #true;; "res" <- "r";; "k" "r"
      end.

  (* One session, over the MAC instances [maca] (slot 1) and [macb] (slot 2)
     and the receivers' state. *)
  Definition auth_sess (maca macb dec1 dec2 res1 res2 : expr) : expr :=
    λ: "f" "effs", auth_skel (auth_send_h maca macb) (auth_recv_h maca macb dec1 dec2 res1 res2).

  (* The protocol over the MAC instance [M]: a factory. *)
  Definition AUTH_of (M : val) : val := λ: <>,
    let: "maca" := M #()%V in let: "macb" := M #()%V in
    let: "dec1" := ref #false in let: "dec2" := ref #false in
    let: "res1" := ref NONEV in let: "res2" := ref NONEV in
    auth_sess "maca" "macb" "dec1" "dec2" "res1" "res2".

  Definition AUTH : val := AUTH_of MAC.
  (* The two intermediate systems of the security proof. *)
  Definition AUTH_pad : val := AUTH_of MAC_pad.
  Definition AUTH_ideal : val := AUTH_of MAC_ideal.

  (* ------------------------------------------------------------------ *)
  (* The simulator.                                                      *)
  (* ------------------------------------------------------------------ *)

  (* The simulator's two ports towards [F_AUTH]: the leaked message is tagged
     and put on the raw network; delivery is permitted iff the pair injected
     by the network verifies. *)
  Definition sauth_send_b (maca macb doSend : expr) : expr :=
    let, ("m", "dst") := "payload" in
    let: "mac" := match: "dst" with InjL <> => maca | InjR <> => macb end in
    match: (Fst "mac") "m" with
      NONE => #()%V
    | SOME "t" => doSend (("m", "t"), "dst")
    end.

  Definition sauth_recv_b (maca macb dec1 dec2 acc1 acc2 doRecv : expr) : expr :=
    let: "mac" := match: "from" with InjL <> => macb | InjR <> => maca end in
    let: "dec" := match: "from" with InjL <> => dec2 | InjR <> => dec1 end in
    let: "acc" := match: "from" with InjL <> => acc2 | InjR <> => acc1 end in
    if: !"dec" then (if: !"acc" then SOME #(0%nat) else NONEV)
    else
      match: doRecv "from" with
        NONE => NONEV
      | SOME "p" =>
          if: !"dec" then (if: !"acc" then SOME #(0%nat) else NONEV)
          else
            let: "ok" := (Snd "mac") "p" in
            "dec" <- #true;; "acc" <- "ok";;
            (if: "ok" then SOME #(0%nat) else NONEV)
      end.

  Definition S_AUTH : val := λ: <>,
    let: "maca" := MAC_ideal #()%V in let: "macb" := MAC_ideal #()%V in
    let: "dec1" := ref #false in let: "dec2" := ref #false in
    let: "acc1" := ref #false in let: "acc2" := ref #false in
    λ: "f" "effs",
      let, ("doSend", "doRecv") := "effs" in
      "f" ((λ: "payload", sauth_send_b "maca" "macb" "doSend"),
           (λ: "from", sauth_recv_b "maca" "macb" "dec1" "dec2" "acc1" "acc2" "doRecv")).

  (* [F_AUTH]'s handler bodies, over its two message slots; [F_AUTH]'s
     session is [auth_skel] of these ([F_AUTH_eq]). *)
  Definition fauth_send_h (m1 m2 : expr) : expr :=
    let, ("m", "dst") := "message" in
    match: "dst" with
      InjL <> => match: !m1 with
                   NONE => m1 <- SOME "m";; ("doLeakSend" ("m", "dst"));; "k" #()%V
                 | SOME "x" => "k" #()%V
                 end
    | InjR <> => match: !m2 with
                   NONE => m2 <- SOME "m";; ("doLeakSend" ("m", "dst"));; "k" #()%V
                 | SOME "x" => "k" #()%V
                 end
    end.

  Definition fauth_recv_h (m1 m2 : expr) : expr :=
    let: "r" := ("doLeakRecv" "from") in
    match: "r" with
      NONE => "k" NONEV
    | SOME "x" => match: "from" with
                    InjL <> => match: !m2 with
                                 NONE => "k" NONEV
                               | SOME "m" => "k" (SOME "m")
                               end
                  | InjR <> => match: !m1 with
                                 NONE => "k" NONEV
                               | SOME "m" => "k" (SOME "m")
                               end
                  end
    end.

  Lemma F_AUTH_eq :
    F_AUTH = (λ: <>, let: "m1" := ref NONEV in let: "m2" := ref NONEV in
                     λ: "f" "effs", auth_skel (fauth_send_h "m1" "m2") (fauth_recv_h "m1" "m2"))%V.
  Proof. reflexivity. Qed.

  (* The MAC instances, the protocols and the simulator are factories: they
     allocate their state when called.  [AsRecV] lets the pure-step tactics
     call them without unfolding. *)
  #[global] Instance MAC_as_recv : AsRecV MAC BAnon BAnon _ := eq_refl.
  #[global] Instance MAC_pad_as_recv : AsRecV MAC_pad BAnon BAnon _ := eq_refl.
  #[global] Instance MAC_ideal_as_recv : AsRecV MAC_ideal BAnon BAnon _ := eq_refl.
  #[global] Instance AUTH_of_as_recv M : AsRecV (AUTH_of M) BAnon BAnon _ := eq_refl.
  #[global] Instance AUTH_as_recv : AsRecV AUTH BAnon BAnon _ := eq_refl.
  #[global] Instance AUTH_pad_as_recv : AsRecV AUTH_pad BAnon BAnon _ := eq_refl.
  #[global] Instance AUTH_ideal_as_recv : AsRecV AUTH_ideal BAnon BAnon _ := eq_refl.
  #[global] Instance S_AUTH_as_recv : AsRecV S_AUTH BAnon BAnon _ := eq_refl.

End auth_def.
