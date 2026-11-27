(* Oblivious transfer reversal: a transfer the other way round (TO) from
   one oblivious transfer and one message (uc_eff/DESIGN.md, section 6):
   the protocol, and the case where both parties are honest.

   In the OT, Bob is the sender and Alice the receiver.  In the TO, Alice
   is the sender, with two bits [(x0, x1)], and Bob the receiver, with a
   choice bit [c].  Bob offers [(r, r ⊕ c)] for a random mask [r]; Alice
   chooses [s = x0 ⊕ x1], learns [r ⊕ (s ∧ c)] and sends
   [m = x0 ⊕ r ⊕ (s ∧ c)]; Bob outputs [m ⊕ r = x_c].  Bits go through the
   group OT as [gbit b = if b then g else 1].

   The parties [TO_R] (Bob) and [TO_S] (Alice) are the same code in every
   case.  With both honest they use the honest OT [F_OT_H] (ot.v) and an
   authenticated channel from Alice to Bob; when one of them is corrupted,
   its code is absent, the OT is the one with that party corrupted, and
   Alice's message comes from or goes to the adversary.  The corruption
   cases are in [ot_rev_corrupted_sender.v] (Alice corrupted) and
   [ot_rev_corrupted_receiver.v] (Bob corrupted).

     module TO_R (Ot : OT.sender) (Net : sig val recv : unit -> bool end) = struct
       let transfer c =
         let snd = Ot.choose () in            (* Alice's OT choice is fixed *)
         let r = flip () in
         snd (gbit r, gbit (r ⊕ c));
         Net.recv () ⊕ r
     end

     module TO_S (Ot : OT.receiver) (Net : sig val send : bool -> unit end) = struct
       let transfer (x0, x1) =
         let z = ungbit (Ot.transfer (x0 ⊕ x1)) in   (* r ⊕ (s ∧ c) *)
         Net.send (x0 ⊕ z)
     end *)

From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze Require Import logic adequacy sem_def sem_types sem_row sem_judgement.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules auth ot.
From Stdlib Require Import Reals.

Import fingroup.
Import valgroup_notation.

(* The coupling of two bits sampled as [rand 1]: the identity, or the swap
   of [0] and [1]. *)
Definition swap01 (k : nat) : nat := match k with 0 => 1 | 1 => 0 | _ => k end.
Definition bmask (b : bool) (k : nat) : nat := if b then swap01 k else k.

#[global] Instance bmask_bij b : Bij (bmask b).
Proof.
  split.
  - intros x y. destruct b; last done. destruct x as [|[|x]], y as [|[|y]]; simpl; lia.
  - intros y. exists (bmask b y). by destruct b, y as [|[|y]].
Qed.

Lemma bmask_lt b (k : nat) : (k < 2)%nat → (bmask b k < 2)%nat.
Proof. destruct b, k as [|[|k]]; simpl; lia. Qed.

Section ot_rev.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* Bits. *)
  Definition flip : val := λ: <>, rand #1 = #1.
  Definition bxor : val := λ: "a" "b", if: "a" then ~ "b" else "b".
  Definition gbit : val := λ: "b", if: "b" then g else vunit.

  (* A group element as a bit. *)
  Definition ungbit : val := λ: "z", veq "z" g.

  (* ---------------------------------------------------------------- *)
  (* The protocol: Bob, the receiver of the transfer.                   *)
  (* ---------------------------------------------------------------- *)

  (* It takes the sender's port of the OT and Alice's message, which the
     adversary provides.  Its port takes the choice [c] and returns
     [x_c]. *)
  Definition TO_R : val :=
    λ: "res",
      let, ("sport", "recv") := "res" in

      λ: "c",
        let: "snd" := "sport" #()%V in
        let: "r" := flip #()%V in
        "snd" (gbit "r", gbit (bxor "r" "c"));;
        let: "m" := "recv" #()%V in
        bxor "m" "r".

  (* ---------------------------------------------------------------- *)
  (* The protocol: Alice, the sender of the transfer.                   *)
  (* ---------------------------------------------------------------- *)

  Definition TO_S : val :=
    λ: "res",
      let, ("rport", "send") := "res" in

      λ: "xx",
        let, ("x0", "x1") := "xx" in
        let: "z" := ungbit ("rport" (bxor "x0" "x1")) in
        "send" (bxor "x0" "z").

  (* ================================================================ *)
  (* Both honest.                                                       *)
  (* ================================================================ *)

  (* Alice and Bob are [TO_S] and [TO_R], on the honest OT [F_OT_H]
     (ot.v) and an authenticated channel from Alice to Bob.

       module PARTIES_TO (Ot : OT.ports) (Ab : AUTH.endpoints) = struct
         module Alice = TO_S (Ot.receiver) (struct let send = Ab.send end)
         module Bob = TO_R (Ot.sender) (struct let recv = Ab.recv end)
       end *)
  Definition PARTIES_TO : val :=
    λ: "res",
      let, ("ot", "ab") := "res" in
      let, ("sport", "rport") := "ot" in
      let, ("send", "recv") := "ab" in
      (TO_S ("rport", "send"), TO_R ("sport", "recv")).

  (* ---------------------------------------------------------------- *)
  (* The ideal transfer, both honest.                                   *)
  (* ---------------------------------------------------------------- *)

  (* It takes the adversary's operations [yield_a] and [yield_b], one per
     party, which the party calls wherever the real party calls the
     network (ot.v: UC's delayed output, for blocking ports). *)
  Definition F_TO_H : val :=
    λ: "adv",
      let, ("yield_a", "yield_b") := "adv" in

      (* state: Alice's bits, whether Bob has chosen, whether Alice is
         done *)
      let: "xs" := ref NONE in
      let: "cs" := ref #false in
      let: "fin" := ref #false in

      (* Alice: wait for Bob's input, then finish *)
      (λ: "xx",
         "xs" <- SOME "xx";;
         (rec: "wait" <> :=
            "yield_a" #()%V;;
            if: !"cs" then #()%V else "wait" #()%V) #()%V;;
         "fin" <- #true;;
         "yield_a" #()%V,

      (* Bob: wait for Alice's input, choose, wait for Alice to finish *)
       λ: "c",
         let, ("x0", "x1") :=
           (rec: "wait" <> :=
              "yield_b" #()%V;;
              match: !"xs" with NONE => "wait" #()%V | SOME "xx" => "xx" end) #()%V in
         "cs" <- #true;;
         "yield_b" #()%V;;
         (rec: "wait" <> :=
            "yield_b" #()%V;;
            if: !"fin" then #()%V else "wait" #()%V) #()%V;;
         if: "c" then "x1" else "x0").

  (* ---------------------------------------------------------------- *)
  (* The simulator.                                                     *)
  (* ---------------------------------------------------------------- *)

  (* It maps each party's yields to that party's next move in the real
     world: for Alice, [yield_r] of the OT until Bob has sent, then the
     leak of her message, a random bit; for Bob, [yield_s] of the OT until
     Alice has her input, then sending (it samples the bit then, when Bob
     samples his mask), then [deliver] of the channel.  It decides the
     next move after each real move returns, which is where the
     functionality checks its condition. *)
  Definition S_TO_H : val :=
    λ: "adv",
      let, ("ot", "net") := "adv" in
      let, ("yield_s", "yield_r") := "ot" in
      let, ("leak", "deliver") := "net" in

      (* state: Alice's message, and how far each party is *)
      let: "rho" := ref #false in
      let: "a_in" := ref #false in
      let: "a_last" := ref #false in
      let: "b_go" := ref #false in
      let: "b_sent" := ref #false in

      (* Alice *)
      (λ: <>,
         if: !"a_last" then "leak" !"rho" else
           ("a_in" <- #true;;
            "yield_r" #()%V;;
            if: !"b_sent" then "a_last" <- #true else #()%V),

      (* Bob *)
       λ: <>,
         if: !"b_sent" then "deliver" #()%V else
         if: !"b_go" then
           ("rho" <- flip #()%V;;
            "b_sent" <- #true;;
            "yield_s" #()%V)
         else
           ("yield_s" #()%V;;
            if: !"a_in" then "b_go" <- #true else #()%V)).

  Definition HYB_TO_H : val := (PARTIES_TO ⊳ (F_OT_H ⊗ F_OAUTH))%md.
  Definition IDEAL_TO_H : val := (F_TO_H ⊳ S_TO_H)%md.

End ot_rev.

Section ot_rev_types.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* Bob's port: the choice, and the chosen bit. *)
  Definition TPort (θ : sem_row Σ) : sem_ty Σ := (𝔹 -{ ¡ θ }-∘ 𝔹)%T.
  (* Alice's port: her two bits. *)
  Definition TSPort (θ : sem_row Σ) : sem_ty Σ := ((𝔹 × 𝔹) -{ ¡ θ }-∘ 𝟙)%T.

  (* Both honest: the hybrid adversarial interface (the honest OT's and
     the channel's), the ideal one, and both ports. *)
  Definition TOHNet (θ : sem_row Σ) : sem_ty Σ := (OTHAdv θ × LNet 𝔹 θ)%T.
  Definition TOHAdv (θ : sem_row Σ) : sem_ty Σ := ((𝟙 -{ θ }-> 𝟙) × (𝟙 -{ θ }-> 𝟙))%T.
  Definition TPorts (θ : sem_row Σ) : sem_ty Σ := (TSPort θ × TPort θ)%T.

End ot_rev_types.

(* Reversal is perfect: no environment tells the parties on the ideal OT
   from the ideal transfer with the simulator. *)
Definition to_h_secure `{!probblazeRGpreS Σ}
    {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg} : Prop :=
  ∀ A : val,
    (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (Mod TOHNet TPorts → 𝔹)%T) →
    (advantage A HYB_TO_H IDEAL_TO_H #true <= 0)%R.
