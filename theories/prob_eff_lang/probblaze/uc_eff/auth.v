(* Authenticated channels as modules (uc_eff/DESIGN.md).

   The one-way authenticated channel [F_OAUTH] carries one message from a
   sender to a receiver.  The adversary sees the message and decides when
   it is delivered.  The two-way channel [F_AUTH] is two one-way channels
   side by side, one per direction. *)

From clutch.prob_eff_lang.probblaze Require Export notation valgroup.
From clutch.prob_eff_lang.probblaze Require Import class_instances.
From clutch.prob_eff_lang.probblaze Require Import logic adequacy sem_def sem_types sem_row sem_judgement.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules.

Import valgroup_notation.

(* It takes the adversary's operations [leak] and [deliver] and returns the
   sender's and the receiver's endpoint. *)
Definition F_OAUTH : val :=
  λ: "adv",
    let, ("leak", "deliver") := "adv" in

    (* state: the message *)
    let: "box" := ref NONE in

    (* send: store the message and leak it *)
    (λ: "x", "box" <- SOME "x";; "leak" "x",

    (* recv: call [deliver] until the message is there *)
     rec: "recv" <> :=
       "deliver" #()%V;;
       match: !"box" with NONE => "recv" #()%V | SOME "x" => "x" end).

(* The two-way channel between an initiator A and a responder B: the
   channel from A to B beside the channel from B to A. *)
Definition F_AUTH : val := (F_OAUTH ⊗ F_OAUTH)%md.

Section auth_types.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.

  (* The adversarial interface of the one-way channel: [leak], [deliver]. *)
  Definition ONet (θ : sem_row Σ) : sem_ty Σ :=
    ((𝔾 -{ θ }-> 𝟙) × (𝟙 -{ θ }-> 𝟙))%T.
  (* Its endpoints: [send] for the sender, [recv] for the receiver.  The
     row is one-shot: the adversary resumes a suspended party at most
     once. *)
  Definition OEp (θ : sem_row Σ) : sem_ty Σ :=
    ((𝔾 -{ ¡ θ }-∘ 𝟙) × (𝟙 -{ ¡ θ }-∘ 𝔾))%T.

  (* The same, for messages of type [τ]; [ONet] and [OEp] are the
     instances at [𝔾]. *)
  Definition ONetT (τ : sem_ty Σ) (θ : sem_row Σ) : sem_ty Σ :=
    ((τ -{ θ }-> 𝟙) × (𝟙 -{ θ }-> 𝟙))%T.
  Definition OEpT (τ : sem_ty Σ) (θ : sem_row Σ) : sem_ty Σ :=
    ((τ -{ ¡ θ }-∘ 𝟙) × (𝟙 -{ ¡ θ }-∘ τ))%T.

  (* The two-way channel: one of each per direction, A to B first. *)
  Definition Net : sem_row Σ → sem_ty Σ := IProd ONet ONet.
  Definition Eps : sem_row Σ → sem_ty Σ := IProd OEp OEp.

  (* F_OAUTH : Mod (ONetT τ) (OEpT τ) for a first-order [τ] ([auth_typing.v]),
     hence F_AUTH : Mod Net Eps. *)

End auth_types.
