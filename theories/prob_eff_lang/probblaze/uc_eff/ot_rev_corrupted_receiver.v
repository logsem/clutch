(* Oblivious transfer reversal with the receiver (Bob) corrupted.

   The protocol is in [ot_rev.v].  Bob's code is absent: Alice uses the OT
   with a corrupted sender ([F_OT_S], ot_corrupted_sender.v), and her
   message goes to the adversary.  The statement [to_r_secure] is proved
   in [ot_rev_corrupted_receiver_proof.v]. *)

From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze Require Import logic adequacy sem_def sem_types sem_row sem_judgement.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules ot ot_corrupted_sender ot_rev.
From Stdlib Require Import Reals.

Import fingroup.
Import valgroup_notation.

Section ot_rev_corrupted_receiver.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* ---------------------------------------------------------------- *)
  (* The ideal transfer, receiver (Bob) corrupted.                      *)
  (* ---------------------------------------------------------------- *)

  (* It asks the adversary for Bob's choice and hands it the chosen bit. *)
  Definition F_TO_R : val :=
    λ: "choose",
      λ: "xx",
        let, ("x0", "x1") := "xx" in
        let, ("c", "output") := "choose" #()%V in
        "output" (if: "c" then "x1" else "x0").

  (* ---------------------------------------------------------------- *)
  (* The simulator.                                                     *)
  (* ---------------------------------------------------------------- *)

  (* The hybrid world: Alice on the ideal OT with Bob corrupted, her
     message to the adversary. *)
  Definition HYB_TO_R : val := (TO_S ⊳ (F_OT_S ⊗ id_mod))%md.

  (* It reads Bob's choice [c = r ⊕ r1] off his OT messages
     [(u0, u1) = (gbit r, gbit r1)], and runs Alice on the bits
     [(x_c, x_c)], replaying his messages to the OT. *)
  Definition S_TO_R : val :=
    λ: "adv",
      let, ("input", "send") := "adv" in
      λ: <>,
        let, ("u0", "u1") := "input" #()%V in
        (bxor (ungbit "u0") (ungbit "u1"),
         λ: "x", HYB_TO_R ((λ: <>, ("u0", "u1")), "send") ("x", "x")).

  Definition IDEAL_TO_R : val := (F_TO_R ⊳ S_TO_R)%md.

End ot_rev_corrupted_receiver.

Section ot_rev_corrupted_receiver_types.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* Alice's message, to the adversary. *)
  Definition ASend (θ : sem_row Σ) : sem_ty Σ := (𝔹 -{ θ }-> 𝟙)%T.
  (* The adversarial interface of the ideal transfer with Bob corrupted:
     his choice, and the operation that delivers the chosen bit.  One-shot:
     only the functionality calls it. *)
  Definition TORAdv (θ : sem_row Σ) : sem_ty Σ := (𝟙 -{ ¡ θ }-∘ (𝔹 × (𝔹 -{ ¡ θ }-∘ 𝟙)))%T.

  (* The typings of the components:
       TO_S   : Mod (IProd RPort ASend) TSPort    F_OT_S ⊗ id : Mod (IProd OTSAdv ASend) (IProd RPort ASend)
       S_TO_R : Mod (IProd OTSAdv ASend) TORAdv   F_TO_R      : Mod TORAdv TSPort
     so that  HYB_TO_R, IDEAL_TO_R : Mod (IProd OTSAdv ASend) TSPort. *)

End ot_rev_corrupted_receiver_types.

(* Reversal is perfect: no environment tells Alice on the ideal OT from the
   ideal transfer with the simulator. *)
Definition to_r_secure `{!probblazeRGpreS Σ}
    {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg} : Prop :=
  ∀ A : val,
    (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (Mod (IProd OTSAdv ASend) TSPort → 𝔹)%T) →
    (advantage A HYB_TO_R IDEAL_TO_R #true <= 0)%R.
