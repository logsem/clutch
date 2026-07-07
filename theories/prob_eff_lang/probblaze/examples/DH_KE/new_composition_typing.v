From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import
  logic primitive_laws proofmode
  spec_rules spec_ra class_instances tactics notation valgroup metatheory
  sem_types sem_row sem_sig sem_judgement sem_def
  def_dhke sec_channel_def xor sec_channel_prf dhke_channel_lazy_results dhke_channel_lazy_authchan.
From clutch.prob_eff_lang.probblaze.typing Require Import fundamental.

Import fingroup.
Import fingroup.fingroup.

Import valgroup_tactics.

(* ------------------------------------------------------------------ *)
(* Semantic typing of the building blocks.                            *)
(*                                                                    *)
(* Each of these is a term related to itself at a semantic type.  All *)
(* the types below are meant to be in the image of the interpretation *)
(* ⟦·⟧ of the syntactic types, so each lemma can (in a later step) be *)
(* discharged by applying the fundamental lemma of the logical        *)
(* relation to a syntactic typing derivation:                         *)
(*   - 𝔾 = ⟦τG⟧ (the clutch-group syntactic type),                    *)
(*   - Option = sem_ty_option,                                        *)
(*   - the row parameters range over ⟦row-variables⟧,                 *)
(*   - products/sums/arrows/∀ᵣ/row-unions all have syntactic formers. *)
(*                                                                    *)
(* For now they are admitted; the interface definitions below may     *)
(* need minor adjustments once the proofs are carried out.  This file *)
(* only imports the base theory, so it can be iterated on quickly.    *)
(* ------------------------------------------------------------------ *)

Section new_comp_verification.
  Context `{probblazeRGS Σ}.
  Context (channel leaksec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 keyleak1 keyleak2 schannel1 schannel2 l1 l2 l2': label).
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.
  Let Key := S (S n'').
  Let Support := S (S n'').
  Variable xor_struct : XOR (Key := Key) (Support := Support).
  Context `{!XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}.

  Notation "'𝔾'" := sem_ty_group.

  (* Interface families (each parametrised by the effect row of its ops).*)
  (* [chan]   : authenticated channel — group send, group recv.          *)
  (* [oaleak] : F_OAUTH's leak — group send, recv only leaks presence.    *)
  (* [leakI]  : direction-only send/recv (unit messages).                 *)
  (* [gk]     : the getKey operation.                                     *)
  (* [cli]    : the top-level secure-channel client interface.            *)
  Definition chan (θ : sem_row Σ) : sem_ty Σ :=
    (((𝔾 × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝔾))%T.
  Definition oaleak (θ : sem_row Σ) : sem_ty Σ :=
    (((𝔾 × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝟙))%T.
  Definition leakI (θ : sem_row Σ) : sem_ty Σ :=
    (((𝟙 + 𝟙) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝟙))%T.
  Definition gk (θ : sem_row Σ) : sem_ty Σ := ((𝟙 + 𝟙) -{ θ }-> Option 𝔾)%T.
  Definition cli (θ : sem_row Σ) : sem_ty Σ :=
    ((𝔾 -{ θ }-> 𝟙) × (𝟙 -{ θ }-> Option 𝔾))%T.
  (* the handler consuming an interface I, polymorphic over I's row *)
  Definition hdl (I : sem_row Σ -> sem_ty Σ) (θ : sem_row Σ) : sem_ty Σ :=
    (∀ᵣ θ', I θ' -{ sem_row_union θ' θ }-∘ 𝟙)%T.

  (* Atomic functionalities, as effect-handler transformers (τ__F τ τ' takes
     a τ'-consuming handler to a τ-consuming handler). *)
  Lemma F_OAUTH_typed :
    ⊢ sem_val_typed F_OAUTH F_OAUTH (τ__F oaleak chan).
  Proof using Type*. Admitted.

  Lemma F_AUTH_typed :
    ⊢ sem_val_typed F_AUTH F_AUTH (τ__F chan chan).
  Proof using Type*. Admitted.

  Lemma DH_SIM_typed :
    ⊢ sem_val_typed DH_SIM DH_SIM (τ__F chan leakI).
  Proof using Type*. Admitted.

  Lemma F_KE_lazy_alice_typed :
    ⊢ sem_val_typed F_KE_lazy_alice F_KE_lazy_alice (τ__F leakI gk).
  Proof using Type*. Admitted.

  Lemma CHAN_typed :
    ⊢ ∀ θ, sem_val_typed (CHAN xor) (CHAN xor) ((hdl cli θ ⊸ τ__f θ chan gk)%T).
  Proof using Type*. Admitted.

  (* [F_AUTH ∘f DH_SIM], in both value and open (sem_typed) presentations. *)
  Lemma F_AUTH_DH_SIM_typed_val :
    ⊢ sem_val_typed (F_AUTH ∘f DH_SIM) (F_AUTH ∘f DH_SIM) (τ__F chan leakI).
  Proof using Type*. Admitted.

  Lemma F_AUTH_DH_SIM_typed :
    ⊢ sem_typed [] (F_AUTH ∘f DH_SIM) (F_AUTH ∘f DH_SIM) ⊥ (τ__F chan leakI) [].
  Proof using Type*. Admitted.

  Lemma F_KE_F_OAUTH_typed :
    ⊢ sem_typed [] (F_KE_lazy_alice ||ᵣ F_OAUTH) (F_KE_lazy_alice ||ᵣ F_OAUTH) ⊥
        ((∀ᵣ θ, hdl chan θ ⊸
            (∀ᵣ θ1, oaleak θ1 ⊸ ∀ᵣ θ2, leakI θ2
                    -{ sem_row_union θ1 (sem_row_union θ2 θ) }-∘ 𝟙))%T) [].
  Proof using Type*. Admitted.

  (* Open bodies of [F_KE_lazy_alice] and [CHAN xor], needed as the [G]/[J]
     premises of the (functionality-)composition-associativity lemmas.
     [F_KE_body] is free in "f","effs"; [CHAN_body] is free in "f","ChanOp".
     These are copied verbatim from the source definitions
     ([def_dhke.F_KE_lazy_alice] and [sec_channel_def.CHAN]). *)
  Definition F_KE_body : expr :=
    (let, ("doLeakSend", "doLeakRecv") := "effs" in
     let: "γ" := alloc #(S n'') in
     let: "key_opt" := ref NONEV in
     let: "sample_or_load" :=
       λ:<>, match: !"key_opt" with
         | NONE =>
             let: "c" := (samplelbl "γ" #()%V) in
             let: "key" := vexp g "c" in
             "key_opt" <- SOME "key" ;;
             "key"
         | SOME "key" => "key"
         end
     in
     effect "getKey"
       let: "doGK" := (λ: "party", do: (EffName "getKey") "party") in
       handle: "f" "doGK" with
     | effect (EffName "getKey") "p", rec "k" as multi =>
         match: "p" with
           InjL <> =>
             let: "key" := "sample_or_load" #()%V in
             ("doLeakSend" bob);;
             let: "r" := ("doLeakRecv" bob) in
             match: "r" with
               NONE => "k" NONEV
             | SOME "w" => "k" (SOME "key")
             end
         | InjR <> =>
             let: "r" := ("doLeakRecv" alice) in
             match: "r" with
               NONE => "k" NONEV
             | SOME "w" =>
                 ("doLeakSend" alice);;
                 match: !"key_opt" with
                 | NONE => "k" NONEV
                 | SOME "key" => "k" (SOME "key")
                 end
             end
         end
     | return "y" => "y" end)%E.

  Definition CHAN_body : expr :=
    (λ: "doGK",
      let, ("doSend", "doRecv") := "ChanOp" in
      let: "message" := ref NONEV in
      effect "schannel"
      let: "doSecSend" := (λ: "m", do: (EffName "schannel") (Send "m")) in
      let: "doSecRecv" := (λ: <>, do: (EffName "schannel") (Recv bob)) in
      handle: "f" ("doSecSend", "doSecRecv") with
      | effect (EffName "schannel") "payload", rec "k" as multi =>
        match: "payload" with
          | InjL "m" =>
            match: !"message" with
              | NONE => "message" <- SOME "m";;
                     let: "key" := "doGK" (bob) in
                     match: "key" with
                     | NONE => "k" #()%V
                     | SOME "x" =>
                         match: G_XOR xor "m" "x" with
                         | SOME "mg" => ("doSend" ("mg", bob));; "k" #()%V
                         | NONE => "k" #()%V
                         end
                     end
              | SOME "m" => "k" #()%V
            end
        | InjR <> =>
            let: "key" := "doGK" (alice) in
            match: "key" with
            | NONE => "k" NONEV
            | SOME "key" =>
                let: "r" := ("doRecv" bob) in
                match: "r" with
                | NONE => "k" NONEV
                | SOME "x" =>
                    match: G_XOR xor "x" "key" with
                    | SOME "mg" => "k" (SOME "mg")
                    | NONE => "k" NONE
                    end
                end
            end
        end
      | return "y" => "y"
    end)%E.

  Lemma F_KE_body_typed :
    ⊢ ∀ (θ θG : sem_row Σ),
      sem_typed [("f", τ__f' θ gk); ("effs", leakI θG)]
        F_KE_body F_KE_body (sem_row_union θG θ) (𝟙)%T [].
  Proof using Type*. Admitted.

  Lemma CHAN_body_typed :
    ⊢ ∀ (θ θJ : sem_row Σ),
      sem_typed [("f", hdl cli θ); ("ChanOp", chan θJ)]
        CHAN_body CHAN_body (sem_row_union θJ θ) (𝟙)%T [].
  Proof using Type*. Admitted.

End new_comp_verification.
