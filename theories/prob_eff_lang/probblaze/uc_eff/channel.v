(* A one-time secure channel from a key and an authenticated channel, as
   modules (uc_eff/DESIGN.md).

   The sender masks its message with the key and sends it over a one-way
   authenticated channel; the receiver unmasks.  The protocol [CHAN] uses
   the key ports of the ideal key exchange [F_KE] and the endpoints of
   [F_OAUTH], and realises the ideal secure channel [F_CHAN] with the
   simulator [S_CHAN].  The statement is [chan_secure], proved in
   [channel_proof.v]; the composition with Diffie-Hellman key exchange is
   in [channel_dhke.v].

   The sender's and the receiver's ports are one-shot (affine), and the
   receiver's blocks until the message is there. *)

From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze Require Import logic adequacy sem_def sem_types sem_row sem_judgement.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules auth dhke.
From Stdlib Require Import Reals.

Import fingroup.
Import valgroup_notation.

Section channel.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').

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
         let: "k" := "keyA" #()%V in
         "send" ("m" · "k"),

      (* the receiver: get the key, receive, and unmask *)
       λ: <>,
         let: "k" := "keyB" #()%V in
         let: "c" := "recv" #()%V in
         "c" · ("k"^-1)).

  (* ---------------------------------------------------------------- *)
  (* The ideal secure channel.                                          *)
  (* ---------------------------------------------------------------- *)

  (* It takes the adversary's operations [notify] (a message was sent) and
     [allow] (the receiver gets the message when this returns) and returns
     the sender's and the receiver's port. *)
  Definition F_CHAN : val :=
    λ: "adv",
      let, ("notify", "allow") := "adv" in

      (* state: the message *)
      let: "box" := ref NONE in

      (* the sender: the adversary only learns that there is a message *)
      (λ: "m", "box" <- SOME "m";; "notify" #()%V,

      (* the receiver: call [allow] until the message is there *)
       rec: "recv" <> :=
         "allow" #()%V;;
         match: !"box" with NONE => "recv" #()%V | SOME "m" => "m" end).

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

      (* notify: a message was sent; play the initiator of the key
         exchange, then show the adversary a random group element *)
      (λ: <>,
         "started" <- #true;;
         "notify" #true;;
         "allow" #true;;
         "sent" <- #true;;
         "leak" (g^(samplelbl "ρ" #()%V)),

      (* allow: play the receiver; wait for the key as the responder of the
         key exchange does, then for the fake ciphertext *)
       λ: <>,
         (rec: "wait" <> :=
            "allow" #false;;
            if: !"started" then #()%V else "wait" #()%V) #()%V;;
         "notify" #false;;
         (rec: "wait" <> :=
            "deliver" #()%V;;
            if: !"sent" then #()%V else "wait" #()%V) #()%V).

  (* The protocol on its two functionalities, and the ideal module. *)
  Definition HYB_CHAN : val := (CHAN ⊳ (F_KE ⊗ F_OAUTH))%md.
  Definition IDEAL_CHAN : val := (F_CHAN ⊳ S_CHAN)%md.

End channel.

Section channel_types.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* The adversarial interface of the secure channel. *)
  Definition CAdv (θ : sem_row Σ) : sem_ty Σ :=
    ((𝟙 -{ θ }-> 𝟙) × (𝟙 -{ θ }-> 𝟙))%T.
  (* The ports of the secure channel: the sender's and the receiver's. *)
  Definition SChan (θ : sem_row Σ) : sem_ty Σ :=
    ((𝔾 -{ ¡ θ }-∘ 𝟙) × (𝟙 -{ ¡ θ }-∘ 𝔾))%T.

  (* The typings of the components ([channel_typing.v]):
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
