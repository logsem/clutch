(* Oblivious transfer reversal with the sender (Alice) corrupted
   (uc_eff/DESIGN.md, section 6).

   The protocol is in [ot_rev.v].  Alice's code is absent: her message is
   an adversarial operation [recv], and Bob uses the OT with a corrupted
   receiver ([F_OT_R], ot_corrupted_receiver.v).  The statement
   [to_s_secure] is proved in [ot_rev_corrupted_sender_proof.v]. *)

From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze Require Import logic adequacy sem_def sem_types sem_row sem_judgement.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules ot ot_corrupted_receiver ot_rev.
From Stdlib Require Import Reals.

Import fingroup.
Import valgroup_notation.

Section ot_rev_corrupted_sender.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* ---------------------------------------------------------------- *)
  (* The ideal transfer, sender (Alice) corrupted.                      *)
  (* ---------------------------------------------------------------- *)

  (* It asks the adversary for Alice's bits when Bob chooses. *)
  Definition F_TO_S : val :=
    λ: "input",
      λ: "c",
        let, ("x0", "x1") := "input" #()%V in
        if: "c" then "x1" else "x0".

  (* ---------------------------------------------------------------- *)
  (* The simulator.                                                     *)
  (* ---------------------------------------------------------------- *)

  (* It plays the OT with Alice: takes her choice [s = x0 ⊕ x1], hands her
     a random bit [ρ] (her OT output [r ⊕ (s ∧ c)]), and reads her inputs
     off her message [m = x0 ⊕ ρ]. *)
  Definition S_TO_S : val :=
    λ: "adv",
      let, ("ot", "recv") := "adv" in
      let, ("choose", "output") := "ot" in

      λ: <>,
        let: "s" := "choose" #()%V in
        let: "ρ" := flip #()%V in
        "output" (gbit "ρ");;
        let: "m" := "recv" #()%V in
        let: "x0" := bxor "m" "ρ" in
        ("x0", bxor "x0" "s").

  (* The hybrid world (Bob on the ideal OT, Alice's message beside it) and
     the ideal world. *)
  Definition HYB_TO_S : val := (TO_R ⊳ (F_OT_R ⊗ id_mod))%md.
  Definition IDEAL_TO_S : val := (F_TO_S ⊳ S_TO_S)%md.

End ot_rev_corrupted_sender.

Section ot_rev_corrupted_sender_types.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* Alice's message, from the adversary. *)
  Definition ARecv (θ : sem_row Σ) : sem_ty Σ := (𝟙 -{ θ }-> 𝔹)%T.
  (* The adversarial interface of the ideal transfer with Alice
     corrupted: her bits. *)
  Definition TOSAdv (θ : sem_row Σ) : sem_ty Σ := (𝟙 -{ θ }-> 𝔹 × 𝔹)%T.

  (* The typings of the components:
       TO_R   : Mod (IProd SPort ARecv) TPort    F_OT_R ⊗ id : Mod (IProd OTAdv ARecv) (IProd SPort ARecv)
       S_TO_S : Mod (IProd OTAdv ARecv) TOSAdv   F_TO_S      : Mod TOSAdv TPort
     so that  HYB_TO_S, IDEAL_TO_S : Mod (IProd OTAdv ARecv) TPort. *)

End ot_rev_corrupted_sender_types.

(* Reversal is perfect: no environment tells Bob on the ideal OT from the
   ideal transfer with the simulator. *)
Definition to_s_secure `{!probblazeRGpreS Σ}
    {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg} : Prop :=
  ∀ A : val,
    (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (Mod (IProd OTAdv ARecv) TPort → 𝔹)%T) →
    (advantage A HYB_TO_S IDEAL_TO_S #true <= 0)%R.
