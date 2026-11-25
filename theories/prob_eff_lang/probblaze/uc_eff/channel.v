(* A one-time secure channel from a key and an authenticated channel, as
   modules (uc_eff/DESIGN.md).

   The sender masks its message with the key and sends it over a one-way
   authenticated channel; the receiver unmasks.  The protocol [CHAN] uses
   the key ports of the ideal key exchange [F_KE] and the endpoints of
   [F_OAUTH], and realises the ideal secure channel [F_CHAN] with the
   simulator [S_CHAN].  The statement is [chan_secure], proved in
   [channel_proof.v]; the composition with Diffie-Hellman key exchange is
   in [channel_dhke.v].

   The sender's and the receiver's ports are one-shot (affine). *)

From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze Require Import logic adequacy sem_def sem_types sem_row sem_judgement.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules dhke.
From Stdlib Require Import Reals.

Import fingroup.
Import valgroup_notation.

Section channel.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').

  (* ---------------------------------------------------------------- *)
  (* The one-way authenticated channel.                                 *)
  (* ---------------------------------------------------------------- *)

  (* It takes the adversary's operations [leak] and [deliver] and returns
     the sender's and the receiver's endpoint. *)
  Definition F_OAUTH : val :=
    λ: "adv",
      let, ("leak", "deliver") := "adv" in

      (* state: the message *)
      let: "box" := ref NONE in

      (* send: store the message and leak it *)
      (λ: "x", "box" <- SOME "x";; "leak" "x",

      (* recv: ask the adversary to deliver, and read the message *)
       λ: <>, if: "deliver" #()%V then !"box" else NONE).

  (* ---------------------------------------------------------------- *)
  (* The protocol.                                                      *)
  (* ---------------------------------------------------------------- *)

  (* It takes the key ports and the endpoints of the authenticated channel
     and returns the sender's and the receiver's port. *)
  Definition CHAN : val :=
    λ: "ports",
      let, ("keys", "ep") := "ports" in
      let, ("keyA", "keyB") := "keys" in
      let, ("send", "recv") := "ep" in

      (* the sender: get the key and send the masked message *)
      (λ: "m",
         match: "keyA" #()%V with
           NONE => #()%V
         | SOME "k" => "send" ("m" · "k")
         end,

      (* the receiver: get the key, receive, and unmask *)
       λ: <>,
         match: "keyB" #()%V with
           NONE => NONE
         | SOME "k" => match: "recv" #()%V with
                         NONE => NONE
                       | SOME "c" => SOME ("c" · ("k"^-1))
                       end
         end).

  (* ---------------------------------------------------------------- *)
  (* The ideal secure channel.                                          *)
  (* ---------------------------------------------------------------- *)

  (* It takes the adversary's operations [notify] (a message was sent) and
     [allow] (may the receiver get it?) and returns the sender's and the
     receiver's port. *)
  Definition F_CHAN : val :=
    λ: "adv",
      let, ("notify", "allow") := "adv" in

      (* state: the message *)
      let: "box" := ref NONE in

      (* the sender: the adversary only learns that there is a message *)
      (λ: "m", "box" <- SOME "m";; "notify" #()%V,

      (* the receiver: gets the message if the adversary allows it *)
       λ: <>, if: "allow" #()%V then !"box" else NONE).

  (* ---------------------------------------------------------------- *)
  (* The simulator.                                                     *)
  (* ---------------------------------------------------------------- *)

  (* It takes the operations of the adversaries of the key exchange,
     [notify] and [allow], and of the authenticated channel, [leak] and
     [deliver], and returns those of the secure channel's. *)
  Definition S_CHAN : val :=
    λ: "adv",
      let, ("ctl", "net") := "adv" in
      let, ("notify", "allow") := "ctl" in
      let, ("leak", "deliver") := "net" in

      (* state: has the sender started, is the fake ciphertext out, and the
         tape of the fake ciphertext *)
      let: "started" := ref #false in
      let: "sent" := ref #false in
      let: "ρ" := alloc #n in

      (* notify: a message was sent; play the initiator of the key exchange
         and, if it gets a key, show the adversary a random group element *)
      (λ: <>,
         "started" <- #true;;
         "notify" #true;;
         if: "allow" #true
         then "sent" <- #true;; "leak" (g^(samplelbl "ρ" #()%V))
         else #()%V,

      (* allow: may the receiver get the message?  play the responder of
         the key exchange and, if it gets a key, ask the adversary to
         deliver; agree only if the fake ciphertext is out *)
       λ: <>,
         if: "allow" #false then
           let: "s" := !"started" in
           "notify" #false;;
           if: "s" then (let: "d" := "deliver" #()%V in "d" && !"sent") else #false
         else #false).

  (* The protocol on its two functionalities, and the ideal module. *)
  Definition HYB_CHAN : val := (CHAN ⊳ (F_KE ⊗ F_OAUTH))%md.
  Definition IDEAL_CHAN : val := (F_CHAN ⊳ S_CHAN)%md.

End channel.

Section channel_types.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* The adversarial interface of the one-way authenticated channel. *)
  Definition ONet (θ : sem_row Σ) : sem_ty Σ :=
    ((𝔾 -{ θ }-> 𝟙) × (𝟙 -{ θ }-> 𝔹))%T.
  (* Its endpoints: the sender's and the receiver's. *)
  Definition OEp (θ : sem_row Σ) : sem_ty Σ :=
    ((𝔾 -{ ¡ θ }-∘ 𝟙) × (𝟙 -{ ¡ θ }-∘ Option 𝔾))%T.
  (* The adversarial interface of the secure channel. *)
  Definition CAdv (θ : sem_row Σ) : sem_ty Σ :=
    ((𝟙 -{ θ }-> 𝟙) × (𝟙 -{ θ }-> 𝔹))%T.
  (* The ports of the secure channel: the sender's and the receiver's. *)
  Definition SChan (θ : sem_row Σ) : sem_ty Σ :=
    ((𝔾 -{ ¡ θ }-∘ 𝟙) × (𝟙 -{ ¡ θ }-∘ Option 𝔾))%T.

  (* The typings of the components ([channel_typing.v]):
       F_OAUTH : Mod ONet OEp
       CHAN    : Mod (IProd Keys OEp) SChan
       F_CHAN  : Mod CAdv SChan
       S_CHAN  : Mod (IProd Ctl ONet) CAdv
     so that  HYB_CHAN, IDEAL_CHAN : Mod (IProd Ctl ONet) SChan. *)

End channel_types.

(* The security statement: the masking is perfect, so no environment
   distinguishes the protocol on its functionalities from the ideal
   module. *)
Definition chan_secure `{!probblazeRGpreS Σ}
    {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg} : Prop :=
  ∀ A : val,
    (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (Mod (IProd Ctl ONet) SChan → 𝔹)%T) →
    (advantage A HYB_CHAN IDEAL_CHAN #true <= 0)%R.
