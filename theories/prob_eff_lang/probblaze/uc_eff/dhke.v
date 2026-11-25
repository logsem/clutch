(* Diffie-Hellman key exchange over the two-way authenticated channel of
   [auth.v], as modules (uc_eff/DESIGN.md).

   The components, their interfaces, the real and ideal modules, the
   reduction, and the security statement [dhke_secure], which is proved in
   [dhke_proof.v].

   Every component is a closed value that takes the operations it uses and
   returns the operations it offers.  The parties' ports are one-shot
   (affine), so there is no "first call only" bookkeeping, and they block:
   a party that waits for a message calls the adversary until the message
   is there.  The initiator
   (Alice) is [#true], the responder (Bob) is [#false].  The tapes in
   [DH_KE] and [S_DHKE] are proof devices. *)

From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze Require Import logic adequacy sem_def sem_types sem_row sem_judgement.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules auth.
From Stdlib Require Import Reals.

Import fingroup.
Import valgroup_notation.

Section dhke.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').

  (* ---------------------------------------------------------------- *)
  (* The protocol.                                                      *)
  (* ---------------------------------------------------------------- *)

  (* It takes the endpoints of the two-way authenticated channel, those of
     the direction A to B first, and returns one key port per party. *)
  Definition DH_KE : val :=
    λ: "eps",
      let, ("epAB", "epBA") := "eps" in
      let, ("sendAB", "recvAB") := "epAB" in
      let, ("sendBA", "recvBA") := "epBA" in

      (* state: the tapes of the two exponents *)
      let: "α" := alloc #n in
      let: "β" := alloc #n in

      (* the initiator *)
      (λ: <>,
         let: "a" := samplelbl "α" #()%V in
         "sendAB" (g^"a");;
         let: "B" := "recvBA" #()%V in
         "B"^"a",

      (* the responder *)
       λ: <>,
         let: "A" := "recvAB" #()%V in
         let: "b" := samplelbl "β" #()%V in
         "sendBA" (g^"b");;
         "A"^"b").

  (* ---------------------------------------------------------------- *)
  (* The ideal key exchange.                                            *)
  (* ---------------------------------------------------------------- *)

  (* It takes the adversary's operations [notify] (a party has started) and
     [allow] (a party gets the key when this returns) and returns one key
     port per party.  The key is sampled when the initiator starts; the
     responder blocks until then. *)
  Definition F_KE : val :=
    λ: "adv",
      let, ("notify", "allow") := "adv" in

      (* state: the key's tape, and the key once sampled *)
      let: "γ" := alloc #n in
      let: "kr" := ref NONE in

      (* the initiator *)
      (λ: <>,
         let: "key" := g^(samplelbl "γ" #()%V) in
         "kr" <- SOME "key";;
         "notify" #true;;
         "allow" #true;;
         "key",

      (* the responder *)
       rec: "resp" <> :=
         "allow" #false;;
         match: !"kr" with
           NONE => "resp" #()%V
         | SOME "k" => "notify" #false;; "k"
         end).

  (* ---------------------------------------------------------------- *)
  (* The simulator.                                                     *)
  (* ---------------------------------------------------------------- *)

  (* It takes the operations of the adversary of the two-way channel,
     [leak] and [deliver] for each direction, and returns those of the key
     exchange's, [notify] and [allow]. *)
  Definition S_DHKE : val :=
    λ: "adv",
      let, ("netAB", "netBA") := "adv" in
      let, ("leakAB", "deliverAB") := "netAB" in
      let, ("leakBA", "deliverBA") := "netBA" in

      (* state: which parties have started, and the tapes of the fake
         halves *)
      let: "sentA" := ref #false in
      let: "sentB" := ref #false in
      let: "α" := alloc #n in
      let: "β" := alloc #n in

      (* notify: party [p] has started; record it, then show the adversary
         a fake half on the party's outgoing direction *)
      (λ: "p",
         if: "p"
         then "sentA" <- #true;; "leakAB" (g^(samplelbl "α" #()%V))
         else "sentB" <- #true;; "leakBA" (g^(samplelbl "β" #()%V)),

      (* allow: party [p] waits for its peer's half; ask the adversary to
         deliver on the incoming direction until the peer's fake half is
         out *)
       λ: "p",
         if: "p"
         then (rec: "wait" <> :=
                 "deliverBA" #()%V;;
                 if: !"sentB" then #()%V else "wait" #()%V) #()%V
         else (rec: "wait" <> :=
                 "deliverAB" #()%V;;
                 if: !"sentA" then #()%V else "wait" #()%V) #()%V).

  (* ---------------------------------------------------------------- *)
  (* The reduction to DDH.                                              *)
  (* ---------------------------------------------------------------- *)

  (* The protocol with its exponentiations replaced by a DDH oracle.  [C_DH]
     is the program, [C_DH_v d] the value it evaluates to on the oracle [d]. *)
  Definition C_DH_of (DH : expr) : expr :=
      let, ("ga", "gb", "gc") := DH #()%V in
      let, ("epAB", "epBA") := "eps" in
      let, ("sendAB", "recvAB") := "epAB" in
      let, ("sendBA", "recvBA") := "epBA" in

      (* the initiator *)
      (λ: <>,
         "sendAB" "ga";;
         "recvBA" #()%V;;
         "gc",

      (* the responder *)
       λ: <>,
         "recvAB" #()%V;;
         "sendBA" "gb";;
         "gc").
  Definition C_DH : val := λ: "DH" "eps", C_DH_of "DH".
  Definition C_DH_v (d : val) : val := λ: "eps", C_DH_of d.

  (* The real and the ideal module. *)
  Definition REAL_DHKE : val := (DH_KE ⊳ F_AUTH)%md.
  Definition IDEAL_DHKE : val := (F_KE ⊳ S_DHKE)%md.

  (* The DDH reduction for an environment [A]. *)
  Definition RED_DHKE (A : val) : val :=
    (λ: "v", A (comp_app (C_DH "v") F_AUTH))%V.

End dhke.

Section dhke_types.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  (* The adversarial interface of the key exchange. *)
  Definition Ctl (θ : sem_row Σ) : sem_ty Σ :=
    ((𝔹 -{ θ }-> 𝟙) × (𝔹 -{ θ }-> 𝟙))%T.
  (* The key ports of the two parties.  The row is one-shot: the adversary
     resumes a suspended party at most once. *)
  Definition Keys (θ : sem_row Σ) : sem_ty Σ :=
    ((𝟙 -{ ¡ θ }-∘ 𝔾) × (𝟙 -{ ¡ θ }-∘ 𝔾))%T.

  (* The typings of the components:
       DH_KE  : Mod Eps Keys      F_KE   : Mod Ctl Keys
       S_DHKE : Mod Net Ctl
       C_DH d : Mod Eps Keys      for a DDH oracle d
     so that  REAL_DHKE, IDEAL_DHKE : Mod Net Keys.  Those of [F_KE] and
     [S_DHKE] are proved in [dhke_typing.v]; the security proof relates the
     composed modules directly and does not go through the others. *)

End dhke_types.

(* The security statement: the advantage of an environment against the
   real and the ideal module is at most that of the reduction against the
   two DDH oracles. *)
Definition dhke_secure `{!probblazeRGpreS Σ}
    {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg} : Prop :=
  ∀ A : val,
    (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (Mod Net Keys → 𝔹)%T) →
    (advantage A REAL_DHKE IDEAL_DHKE #true <= advantage (RED_DHKE A) DH_real DH_rand #true)%R.
