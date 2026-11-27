(* Oblivious transfer with a corrupted sender, as modules
   (uc_eff/DESIGN.md, section 6).

   The protocol is in [ot.v]; here the sender is corrupted, so its code is
   absent and the adversary plays it.  In the real world the
   receiver talks to the adversary directly: [send] takes the receiver's
   message, [recv] returns the sender's reply.  In the ideal world the
   functionality asks the adversary for the sender's messages when the
   receiver chooses.

   The simulator publishes a reference string in decryption mode, a DDH
   tuple, whose trapdoor [y] lets it compute one receiver's message that
   opens both slots, and so extract both messages.  The real reference
   string is a random tuple [(h1, h0, g1, g)]; telling it from a DDH tuple
   is the DDH problem.  The security statement [ot_s_secure] therefore bounds the
   advantage by the DDH advantage of a reduction plus [1/n]; it is proved
   in [ot_corrupted_sender_proof.v].  The DDH samplers and the reference
   string taken from one, [F_CRS_DH], are in [ot.v]. *)

From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze Require Import logic adequacy sem_def sem_types sem_row sem_judgement.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules ot.
From Stdlib Require Import Reals.

Import fingroup.
Import valgroup_notation.

Section ot_corrupted_sender.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* ---------------------------------------------------------------- *)
  (* The ideal oblivious transfer, sender corrupted.                    *)
  (* ---------------------------------------------------------------- *)

  (* It takes the adversary's operation [input] (the sender's messages)
     and returns the receiver's port. *)
  Definition F_OT_S : val :=
    λ: "input",
      λ: "b",
        let, ("m0", "m1") := "input" #()%V in
        if: "b" then "m1" else "m0".

  (* ---------------------------------------------------------------- *)
  (* The simulator.                                                     *)
  (* ---------------------------------------------------------------- *)

  (* It publishes a reference string in decryption mode, with the
     trapdoor [y] ([g1 = g0^y]), sends the receiver's message
     [(g0^a0, h0^a0) = (g1^a1, h1^a1)] for [a0 = a1 y], and decrypts both
     ciphertexts.  This is the real receiver on the dummy choice [false]
     (secret [a0]), except that it also opens slot [1], with [a1]: it
     cannot run [OT_R] itself, which keeps its secret. *)
  Definition S_OT_S : val :=
    λ: "adv",
      let, ("publish", "net") := "adv" in
      let, ("send", "recv") := "net" in

      (* a reference string in decryption mode, with the trapdoor [y] *)
      let: "y" := sample #()%V in
      let: "x" := sample #()%V in
      let: "g1" := g^"y" in
      let, ("h1", "h0") := ("g1"^"x", g^"x") in
      "publish" ("h1", "h0", "g1", g);;

      (* input: a receiver's message that opens both slots *)
      λ: <>,
        let: "a1" := sample #()%V in
        let: "a0" := "a1" * "y" in
        "send" (g^"a0", "h0"^"a0");;
        let, ("e0", "e1") := "recv" #()%V in
        (dec "a0" "e0", dec "a1" "e1").

  (* The real and the ideal module. *)
  Definition REAL_OT_S : val := (OT_R ⊳ (F_CRS ⊗ id_mod))%md.
  Definition IDEAL_OT_S : val := (F_OT_S ⊳ S_OT_S)%md.

  (* The real module with the reference string from a DDH sampler, and the
     reduction: an environment of the OT modules as an adversary against
     DDH. *)
  Definition HYB_OT_S (dh : val) : val := (OT_R ⊳ (F_CRS_DH dh ⊗ id_mod))%md.
  Definition DDH_RED (A : val) : val :=
    λ: "v", A (comp_app OT_R (tens_app (F_CRS_DH_app "v") id_mod)).

End ot_corrupted_sender.

Section ot_corrupted_sender_types.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* The network of the corrupted sender: the receiver's message to it,
     and its reply. *)
  Definition SNet (θ : sem_row Σ) : sem_ty Σ :=
    (((𝔾 × 𝔾) -{ θ }-> 𝟙) × (𝟙 -{ θ }-> (𝔾 × 𝔾) × (𝔾 × 𝔾)))%T.
  (* The adversarial interface of the ideal oblivious transfer: the
     sender's messages. *)
  Definition OTSAdv (θ : sem_row Σ) : sem_ty Σ := (𝟙 -{ θ }-> 𝔾 × 𝔾)%T.

  (* The typings of the components:
       F_CRS  : Mod Pub CrsPort           OT_R   : Mod (IProd CrsPort SNet) RPort
       F_OT_S : Mod OTSAdv RPort          S_OT_S : Mod (IProd Pub SNet) OTSAdv
     so that  REAL_OT_S, IDEAL_OT_S : Mod (IProd Pub SNet) RPort. *)

End ot_corrupted_sender_types.

(* The security statement, for a group of order [n]: an environment that
   instantiates the module once tells the real from the ideal module with
   at most the DDH advantage of the reduction plus [1/n]. *)
Definition ot_s_secure `{!probblazeRGpreS Σ}
    {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg} : Prop :=
  ∀ A : val,
    (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModA (IProd Pub SNet) RPort → 𝔹)%T) →
    (advantage A REAL_OT_S IDEAL_OT_S #true
       <= advantage (DDH_RED A) DDH_rand DDH_real #true + 1 / S (S n''))%R.
