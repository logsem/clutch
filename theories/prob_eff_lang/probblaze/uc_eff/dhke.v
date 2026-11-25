(* Diffie-Hellman key exchange as modules (uc_eff/DESIGN.md).

   The components, their interfaces, the real and ideal modules, the
   reduction, and the security statement [dhke_secure], which is proved in
   [dhke_proof.v].

   Every component is a closed value that takes the operations it uses and
   returns the operations it offers.  The parties' ports are one-shot
   (affine), so there is no "first call only" bookkeeping.  The initiator
   (Alice) is [#true], the responder (Bob) is [#false].  The tapes in
   [DH_KE] and [S_DHKE] are proof devices. *)

From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze Require Import logic adequacy sem_def sem_types sem_row sem_judgement.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules.
From Stdlib Require Import Reals.

Import fingroup.
Import valgroup_notation.

Section dhke.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').

  (* ---------------------------------------------------------------- *)
  (* The authenticated channel.                                         *)
  (* ---------------------------------------------------------------- *)

  (* It takes the adversary's operations [leak] and [deliver] and returns
     one endpoint (send, recv) per party. *)
  Definition F_AUTH : val :=
    λ: "adv",
      let, ("leak", "deliver") := "adv" in

      (* state: one message slot per direction *)
      let: "mA" := ref NONE in
      let: "mB" := ref NONE in

      (* the initiator's endpoint *)
      ((λ: "m", "mA" <- SOME "m";; "leak" (#true, "m"),
        λ: <>, if: "deliver" #true then !"mB" else NONE),

      (* the responder's endpoint *)
       (λ: "m", "mB" <- SOME "m";; "leak" (#false, "m"),
        λ: <>, if: "deliver" #false then !"mA" else NONE)).

  (* ---------------------------------------------------------------- *)
  (* The protocol.                                                      *)
  (* ---------------------------------------------------------------- *)

  (* It takes the two endpoints and returns one key port per party. *)
  Definition DH_KE : val :=
    λ: "eps",
      let, ("epA", "epB") := "eps" in

      (* state: the tapes of the two exponents *)
      let: "α" := alloc #n in
      let: "β" := alloc #n in

      (* the initiator *)
      (λ: <>,
         let, ("send", "recv") := "epA" in
         let: "a" := samplelbl "α" #()%V in
         "send" (g^"a");;
         match: "recv" #()%V with
           NONE => NONE
         | SOME "B" => SOME ("B"^"a")
         end,

      (* the responder *)
       λ: <>,
         let, ("send", "recv") := "epB" in
         match: "recv" #()%V with
           NONE => NONE
         | SOME "A" => let: "b" := samplelbl "β" #()%V in
                       "send" (g^"b");;
                       SOME ("A"^"b")
         end).

  (* ---------------------------------------------------------------- *)
  (* The ideal key exchange.                                            *)
  (* ---------------------------------------------------------------- *)

  (* It takes the adversary's operations [notify] (a party has started) and
     [allow] (may a party get the key?) and returns one key port per party.
     The key is sampled when the initiator starts. *)
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
         if: "allow" #true then SOME "key" else NONE,

      (* the responder *)
       λ: <>,
         if: "allow" #false
         then (let: "k" := !"kr" in "notify" #false;; "k")
         else NONE).

  (* ---------------------------------------------------------------- *)
  (* The simulator.                                                     *)
  (* ---------------------------------------------------------------- *)

  (* It takes the operations of the channel's adversary, [leak] and
     [deliver], and returns those of the key exchange's, [notify] and
     [allow]. *)
  Definition S_DHKE : val :=
    λ: "adv",
      let, ("leak", "deliver") := "adv" in

      (* state: which parties have started, and the tapes of the fake
         halves *)
      let: "sentA" := ref #false in
      let: "sentB" := ref #false in
      let: "α" := alloc #n in
      let: "β" := alloc #n in

      (* notify: party [p] has started; record it, then show the adversary
         a fake half *)
      (λ: "p",
         (if: "p" then "sentA" else "sentB") <- #true;;
         "leak" ("p", g^(if: "p" then samplelbl "α" #()%V else samplelbl "β" #()%V)),

      (* allow: may party [p] get the key?  ask the adversary to deliver,
         and agree only if the peer's fake half is out *)
       λ: "p",
         let: "d" := "deliver" "p" in
         "d" && !(if: "p" then "sentB" else "sentA")).

  (* ---------------------------------------------------------------- *)
  (* The reduction to DDH.                                              *)
  (* ---------------------------------------------------------------- *)

  (* The protocol with its exponentiations replaced by a DDH oracle.  [C_DH]
     is the program, [C_DH_v d] the value it evaluates to on the oracle [d]. *)
  Definition C_DH_of (DH : expr) : expr :=
      let, ("ga", "gb", "gc") := DH #()%V in
      let, ("epA", "epB") := "eps" in

      (* the initiator *)
      (λ: <>,
         let, ("send", "recv") := "epA" in
         "send" "ga";;
         match: "recv" #()%V with
           NONE => NONE
         | SOME <> => SOME "gc"
         end,

      (* the responder *)
       λ: <>,
         let, ("send", "recv") := "epB" in
         match: "recv" #()%V with
           NONE => NONE
         | SOME <> => "send" "gb";; SOME "gc"
         end).
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

  (* The adversarial interface of the authenticated channel. *)
  Definition Net (θ : sem_row Σ) : sem_ty Σ :=
    (((𝔹 × 𝔾) -{ θ }-> 𝟙) × (𝔹 -{ θ }-> 𝔹))%T.
  (* One endpoint of the channel; the two endpoints. *)
  Definition Ep (θ : sem_row Σ) : sem_ty Σ :=
    ((𝔾 -{ ¡ θ }-∘ 𝟙) × (𝟙 -{ ¡ θ }-∘ Option 𝔾))%T.
  Definition Eps (θ : sem_row Σ) : sem_ty Σ := (Ep θ × Ep θ)%T.
  (* The adversarial interface of the key exchange. *)
  Definition Ctl (θ : sem_row Σ) : sem_ty Σ :=
    ((𝔹 -{ θ }-> 𝟙) × (𝔹 -{ θ }-> 𝔹))%T.
  (* The key ports of the two parties.  The row is one-shot: the adversary
     resumes a suspended party at most once. *)
  Definition Keys (θ : sem_row Σ) : sem_ty Σ :=
    ((𝟙 -{ ¡ θ }-∘ Option 𝔾) × (𝟙 -{ ¡ θ }-∘ Option 𝔾))%T.

  (* The typings of the components:
       F_AUTH : Mod Net Eps       DH_KE  : Mod Eps Keys
       F_KE   : Mod Ctl Keys      S_DHKE : Mod Net Ctl
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
