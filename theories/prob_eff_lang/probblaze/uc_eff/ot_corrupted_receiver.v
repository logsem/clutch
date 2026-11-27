(* Oblivious transfer with a corrupted receiver, as modules
   (uc_eff/DESIGN.md, section 6).

   The protocol is in [ot.v].  The receiver is corrupted, so its code is
   absent and the adversary plays it.  In the real world the sender talks
   to the adversary directly: a channel with a corrupted end adds nothing
   to what the adversary can do.  In the ideal world the functionality
   asks the adversary for the receiver's choice and hands it the chosen
   message.

   The components, their interfaces, the real and ideal modules, and the
   security statement [ot_r_secure], which is proved in
   [ot_corrupted_receiver_proof.v]. *)

From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze Require Import logic adequacy sem_def sem_types sem_row sem_judgement.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules ot.
From Stdlib Require Import Reals.

Import fingroup.
Import valgroup_notation.

Section ot_corrupted_receiver.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* ---------------------------------------------------------------- *)
  (* The ideal oblivious transfer, receiver corrupted.                  *)
  (* ---------------------------------------------------------------- *)

  (* It takes the adversary's operations [choose] (the receiver's choice)
     and [output] (the receiver's message) and returns the sender's port:
     the first phase fixes the choice, the second takes the messages. *)
  Definition F_OT_R : val :=
    λ: "adv",
      let, ("choose", "output") := "adv" in

      λ: <>,
        let: "b" := "choose" #()%V in
        λ: "mm",
          let, ("m0", "m1") := "mm" in
          "output" (if: "b" then "m1" else "m0").

  (* ---------------------------------------------------------------- *)
  (* The simulator.                                                     *)
  (* ---------------------------------------------------------------- *)

  (* It publishes a reference string with a trapdoor [(t1, t0)], extracts
     the choice from the receiver's message with [t0], and encrypts the
     chosen message under its key and a dummy under the other. *)
  Definition S_OT_R : val :=
    λ: "adv",
      let, ("publish", "net") := "adv" in
      let, ("recv", "send") := "net" in

      (* a reference string with a trapdoor *)
      let: "g1" := g^(sample #()%V) in
      let: "t0" := sample #()%V in
      let: "t1" := sample #()%V in
      let, ("h0", "h1") := (g^"t0", "g1"^"t1") in
      let: "crs" := ("h1", "h0", "g1", g) in
      "publish" "crs";;

      (* state: the receiver's message *)
      let: "st" := ref NONE in

      (* choose: take the receiver's message and extract the choice *)
      (λ: <>,
         let: "uv" := "recv" #()%V in
         "st" <- SOME "uv";;
         let, ("u", "v") := "uv" in
         ~ (veq "v" ("u"^"t0")),

      (* output: encrypt the chosen message, and a dummy *)
       λ: "m",
         match: !"st" with
           NONE => #()%V
         | SOME "uv" =>
             let, ("u", "v") := "uv" in
             if: veq "u" vunit then #()%V else
               let, ("m0", "m1") :=
                 if: veq "v" ("u"^"t0") then ("m", g ^ #(Z.of_nat 1)) else (g ^ #(Z.of_nat 1), "m") in
               let: "pk0" := (g, "h0", "u", "v") in
               let: "pk1" := ("g1", "h1", "u", "v") in
               let, ("r0", "s0", "r1", "s1") :=
                 (sample #()%V, sample #()%V, sample #()%V, sample #()%V) in
               let: "e0" := enc "pk0" "m0" "r0" "s0" in
               let: "e1" := enc "pk1" "m1" "r1" "s1" in
               "send" ("e0", "e1")
         end).

  (* The real and the ideal module. *)
  Definition REAL_OT_R : val := (OT_S ⊳ (F_CRS ⊗ id_mod))%md.
  Definition IDEAL_OT_R : val := (F_OT_R ⊳ S_OT_R)%md.

End ot_corrupted_receiver.

Section ot_corrupted_receiver_types.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* The network of the corrupted receiver: its message to the sender, and
     the sender's reply. *)
  Definition RNet (θ : sem_row Σ) : sem_ty Σ :=
    ((𝟙 -{ θ }-> 𝔾 × 𝔾) × (((𝔾 × 𝔾) × (𝔾 × 𝔾)) -{ θ }-> 𝟙))%T.
  (* The adversarial interface of the ideal oblivious transfer. *)
  Definition OTAdv (θ : sem_row Σ) : sem_ty Σ :=
    ((𝟙 -{ θ }-> 𝔹) × (𝔾 -{ θ }-> 𝟙))%T.

  (* The typings of the components:
       F_CRS  : Mod Pub (λ _, Crs)        OT_S   : Mod (IProd (λ _, Crs) RNet) SPort
       F_OT_R : Mod OTAdv SPort           S_OT_R : Mod (IProd Pub RNet) OTAdv
     so that  REAL_OT_R, IDEAL_OT_R : Mod (IProd Pub RNet) SPort. *)

End ot_corrupted_receiver_types.

(* The security statement, for a group of order [n]: an environment that
   instantiates the module once tells the real from the ideal module with
   advantage at most [2/n]. *)
Definition ot_r_secure `{!probblazeRGpreS Σ}
    {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg} : Prop :=
  ∀ A : val,
    (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (ModA (IProd Pub RNet) SPort → 𝔹)%T) →
    (advantage A REAL_OT_R IDEAL_OT_R #true <= 2 / S (S n''))%R.
