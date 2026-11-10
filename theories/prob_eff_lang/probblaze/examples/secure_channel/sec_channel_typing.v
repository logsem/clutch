From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze.uc Require Import comp_operators.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_common sec_channel_def sec_channel_prf dhke_authchan mask.
From clutch.prob_eff_lang.probblaze.examples Require Export dhke_typing.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems.

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
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.
  Context {msk : Mask vgG vgval}.
  Context `{!Mask_struc}.

  Import valgroup_notation valgroup_tactics fingroup.

  (* Interface families (each parametrised by the effect row of its ops).
     [chan], [aleak], [leakI] and [gk] come from [dhke_typing].           *)
  (* [oaleak] : F_OAUTH's leak — group send, recv only leaks presence.    *)
  (* [cli]    : the top-level secure-channel client interface.            *)
  Definition oaleak (θ : sem_row Σ) : sem_ty Σ :=
    (((𝔾 × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝟙))%T.
  Definition cli (θ : sem_row Σ) : sem_ty Σ :=
    ((ℕ -{ θ }-> 𝟙) × (𝟙 -{ θ }-> Option 𝔾))%T.
  (* the handler consuming an interface I, polymorphic over I's row *)
  Definition hdl (I : sem_row Σ -> sem_ty Σ) (θ : sem_row Σ) : sem_ty Σ :=
    (∀ᵣ θ', I θ' -{ sem_row_union θ' θ }-∘ 𝟙)%T.

  (* Atomic functionalities, as effect-handler transformers (τ__F τ τ' takes
     a τ'-consuming handler to a τ-consuming handler). *)

  (* ----------------------------------------------------------------- *)
  (* [F_OAUTH_typed], derived from the compatibility lemmas.            *)
  (*                                                                    *)
  (* [τ__F] puts the leak rows under [¡]: in both handlers the one-shot *)
  (* continuation [k] is still live when F_OAUTH calls the leak         *)
  (* functions ([doLeakSend (m,dst);; k ()], [let r := doLeakRecv from  *)
  (* in … k …]).  Without [¡] a context could handle the leak effect    *)
  (* multi-shot and make [k] run twice; under [τ__F] the body runs at   *)
  (* [¡θ₂ ∪ θ], and [¡θ₂] is OnceR, so [k] may be held across the call. *)
  (* ----------------------------------------------------------------- *)

  (* A nested section, so the local instance and hint modes below do not
     reach the BREL proofs further down. *)
  Section f_oauth.

    #[local] Existing Instance multi_ty_group.

    (* See the tactics at the end of [compatibility.v]. *)
    Import typed_hint_modes.

    Lemma oauth_send_handler_typed (θ₂ ρh : sem_row Σ) :
      ⊢ (¡ θ₂)%R ≤ᵣ ρh -∗
      sem_typed [("payload", (𝔾 × (𝟙 + 𝟙))%T); ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T);
                 ("message", Refᶜ (Option 𝔾)); ("doLeakSend", ((𝔾 × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙)%T)]
        (let, ("m", "dst") := "payload" in
         match: !"message" with
         | NONE => "message" <- SOME "m" ;; ("doLeakSend" ("m", "dst"));; "k" #()%V
         | SOME "stored" => "k" #()%V
         end)%E
        (let, ("m", "dst") := "payload" in
         match: !"message" with
         | NONE => "message" <- SOME "m" ;; ("doLeakSend" ("m", "dst"));; "k" #()%V
         | SOME "stored" => "k" #()%V
         end)%E
        ρh 𝟙 [("message", Refᶜ (Option 𝔾)); ("doLeakSend", ((𝔾 × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙)%T)].
    Proof.
      iIntros "#Hρ".
      iApplyT sem_typed_pair_elim; first typed_var.
      (* The [SOME "stored"] binder is unused; the [message] entry is routed
       around that branch, as the [NONE] branch and the output need it. *)
      iApplyT (sem_typed_match_split [] [("message", _)]).
      - iApplyT sem_typed_load_cpy. typed_var_copy.
      - iApply env_le_refl.
      - iApplyT sem_typed_seq.
        { iApplyT sem_typed_store_cpy_gen.
          2: { iApplyT sem_typed_injr. typed_var_copy. }
          typed_var_copy. }
        iApplyT sem_typed_seq.
        { (* [k] is live across the leak call: fine because [¡θ₂] is OnceR. *)
          iApplyT sem_typed_app_fun_nil; first iApply "Hρ".
          - iApplyT sem_typed_pair; typed_var.
          - typed_leak_fun. }
        iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|].
        typed_cont.
      - iApply env_le_refl.
      - env_pick. iApply env_le_refl.
      - (* Drop the unused binder [stored]; [m] and [dst] are dropped by the
         output split. *)
        iApplyT sem_typed_sub_env; first iApply env_le_weaken.
        iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|].
        typed_cont.
      - env_solve.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma oauth_recv_handler_typed (θ₂ ρh : sem_row Σ) :
      ⊢ (¡ θ₂)%R ≤ᵣ ρh -∗
      sem_typed [("from", (𝟙 + 𝟙)%T); ("k", (Option 𝔾 -{ ρh }-[OS]-> 𝟙)%T);
                 ("message", Refᶜ (Option 𝔾)); ("doLeakRecv", ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙)%T)]
        (let: "r" := ("doLeakRecv" "from") in
         match: "r" with
         | NONE => "k" NONEV
         | SOME "x" => "k" !"message"
         end)%E
        (let: "r" := ("doLeakRecv" "from") in
         match: "r" with
         | NONE => "k" NONEV
         | SOME "x" => "k" !"message"
         end)%E
        ρh 𝟙 [("message", Refᶜ (Option 𝔾)); ("doLeakRecv", ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙)%T)].
    Proof.
      iIntros "#Hρ".
      iApplyT sem_typed_let.
      { (* [k] is live across the leak call: fine because [¡θ₂] is OnceR. *)
        iApplyT sem_typed_app_fun_nil; [iApply "Hρ"|typed_var|].
        typed_leak_fun. }
      iApplyT (sem_typed_match_split [] []).
      - typed_var.
      - iApply env_le_refl.
      - iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|].
        typed_cont.
      - iApply env_le_refl.
      - iApply env_le_refl.
      - (* Drop the binder [x] from the output. *)
        iApplyT sem_typed_sub_env_final; first iApply env_le_weaken.
        iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
        + iApplyT sem_typed_load_cpy. typed_var_copy.
        + typed_cont.
      - iApply env_le_refl.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma F_OAUTH_typed_u m : ⊢ ⊨ᵥ F_OAUTH ≤ F_OAUTH : fac m (τ__Fu oaleak chan).
    Proof using Type*.
      iApply fac_closure.
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
      iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_]). iApply sem_typed_RLam. iIntros (θ).
      (* the copyable reference is the only captured state *)
      iApplyT sem_oval_typed_ufun.
      iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ₂).
      iApplyT sem_oval_typed_afun.
      iApplyT sem_typed_pair_elim; first typed_var.
      iApply sem_typed_effect_gen. iIntros (ls1 ls2).
      iApply sem_typed_effect_gen. iIntros (lr1 lr2). simpl.
      (* The client's [doSend]/[doRecv]: their signatures fix the client row
       [θ₁ := σs · σr · ⟨⟩]. *)
      iApplyT sem_typed_let.
      { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
        iApplyT sem_oval_typed_ufun.
        iApply (sem_typed_do_const OS _ (ls1, ls2) (𝔾 × (𝟙 + 𝟙))%T 𝟙%T).
        iApply sem_typed_sub_nil. iApply sem_typed_var. }
      iApplyT sem_typed_let.
      { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
        iApplyT sem_oval_typed_ufun.
        iApplyT sem_typed_sub_row; first iApply row_le_cons_extend.
        iApply (sem_typed_do_const OS ⟨⟩%R (lr1, lr2) (𝟙 + 𝟙)%T (Option 𝔾)%T).
        iApply sem_typed_sub_nil. iApply sem_typed_var. }
      (* Each handler keeps its own copy of [message] (plus its leak function)
       in its persistent context; [f] and the two closures are consumed by
       the inner handled expression. *)
      iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT (sem_typed_sub_env _ ([("doRecv", _); ("doSend", _); ("f", _); ("message", _); ("doLeakSend", _)]
                                      ++ [("message", _); ("doLeakRecv", _)])).
      { simpl. env_solve. }
      (* Outer handler: recv. *)
      iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option 𝔾)%T).
      - (* Inner handler: send.  Its result row needs [send]'s bottom
         signature at the head. *)
        iApplyT sem_typed_sub_row; first iApply row_le_swap_second.
        iApplyT (sem_typed_sub_env _ ([_; _; _] ++ [_; _])); first iApply env_le_refl.
        iApplyT (sem_typed_deep_handler_OS (ls1, ls2) (λ _, 𝔾 × (𝟙 + 𝟙))%T (λ _, 𝟙)%T).
        + (* The client call [f (doSend, doRecv)], at [¡θ₁ ∪ θ ≤ θ₁ ∪ θ]. *)
          iApplyT sem_typed_app_fun_nil.
          2: { iApplyT sem_typed_pair; typed_var. }
          2: { iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst. }
          iApply row_le_trans; first iApplyT row_le_union'.
          * iApply row_le_mfbang_elim.
          * iApply row_le_refl.
          * row_le_submseteq.
        + iIntros (?). iApply oauth_send_handler_typed. row_le_submseteq.
        + typed_var.
      - iIntros (?). iApply oauth_recv_handler_typed. row_le_submseteq.
      - iApplyT sem_typed_sub_env_final; last typed_var. env_solve.
        Unshelve. all: solve_typed_side.
    Qed.

    Corollary F_OAUTH_typed m : ⊢ ⊨ᵥ F_OAUTH ≤ F_OAUTH : fac m (τ__F oaleak chan).
    Proof using All.
      iApply sem_val_typed_sub; [iApply fac_le; iApply τ__Fu_le_τ__F|iApply F_OAUTH_typed_u].
    Qed.
      
  End f_oauth.

  (* [CHAN], derived from the compatibility lemmas.  As for F_OAUTH, its
     one-shot handlers call [doGK]/[doSend]/[doRecv] while holding the
     continuation, so [τ__f] puts the interface rows under [¡]. *)
  Section chan.
    Import typed_hint_modes.
    #[local] Existing Instance multi_ty_group.

    Lemma sem_typed_vg_of_int Γ1 Γ2 e e' ρ :
      ⊢ sem_typed Γ1 e e' ρ ℕ Γ2 -∗
      sem_typed Γ1 (vg_of_int e) (vg_of_int e') ρ (Option 𝔾) Γ2.
    Proof using G.
      iIntros "#He !# %γ HΓ1 /=".
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ1]"); first by iApply "He".
      iIntros "!# % % (Hn & HΓ2) /=".
      iDestruct "Hn" as (n) "(-> & ->)".
      destruct (vg_of_int_sem n) as [g|] eqn:Hg.
      - iApply (brel_vg_of_int_correct_l _ []); first done.
        iApply (brel_vg_of_int_correct_r _ []); first done.
        iApply brel_value. iIntros "$ !>". iFrame. iExists _, _. iRight. iSplit; [done|]. iSplit; [done|]. by iExists g.
      - iApply (brel_vg_of_int_none_l _ []); first done.
        iApply (brel_vg_of_int_none_r _ []); first done.
        iApply brel_value. iIntros "$ !>". iFrame. iExists _, _. iLeft. done.
    Qed.

    Lemma sem_typed_mask Γ1 Γ2 Γ3 e1 e1' e2 e2' ρ :
      ⊢ sem_typed Γ1 e2 e2' ρ 𝔾 Γ2 -∗ sem_typed Γ2 e1 e1' ρ 𝔾 Γ3 -∗
      sem_typed Γ1 (mask e1 e2) (mask e1' e2') ρ 𝔾 Γ3.
    Proof using All.
      iIntros "#He2 #He1 !# %γ HΓ1 /=".
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ1]"); first by iApply "He2".
      iIntros "!# % % (Hm & HΓ2) /=". iDestruct "Hm" as (m) "(-> & ->)".
      iApply (brel_bind [AppLCtx _; AppRCtx _] [AppLCtx _; AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ2]"); first by iApply "He1".
      iIntros "!# % % (Hk & HΓ3) /=". iDestruct "Hk" as (k) "(-> & ->)".
      iApply (mask_correct_l _ []). iApply (mask_correct_r _ []).
      iApply brel_value. iIntros "$ !>". iFrame. by iExists _.
    Qed.

    Lemma chan_send_handler_typed (θ1 θ2 ρh : sem_row Σ) :
      ⊢ (¡ θ1)%R ≤ᵣ ρh -∗ (¡ θ2)%R ≤ᵣ ρh -∗
      sem_typed [("m", ℕ); ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T);
                 ("message", Refᶜ (Option 𝔾)); ("doGK", gk θ2); ("doSend", ((𝔾 × (𝟙 + 𝟙)) -{ θ1 }-> 𝟙)%T)]
        (match: vg_of_int "m" with
         | NONE => "k" #()%V
         | SOME "m" =>
             match: !"message" with
             | NONE => "message" <- SOME "m";;
                       let: "key" := "doGK" (bob) in
                       match: "key" with
                       | NONE => "k" #()%V
                       | SOME "key" =>
                           let: "mg" := mask "key" "m" in ("doSend" ("mg", bob));; "k" #()%V
                       end
             | SOME "m" => "k" #()%V
             end
         end)%E
        (match: vg_of_int "m" with
         | NONE => "k" #()%V
         | SOME "m" =>
             match: !"message" with
             | NONE => "message" <- SOME "m";;
                       let: "key" := "doGK" (bob) in
                       match: "key" with
                       | NONE => "k" #()%V
                       | SOME "key" =>
                           let: "mg" := mask "key" "m" in ("doSend" ("mg", bob));; "k" #()%V
                       end
             | SOME "m" => "k" #()%V
             end
         end)%E
        ρh 𝟙 [("message", Refᶜ (Option 𝔾)); ("doGK", gk θ2); ("doSend", ((𝔾 × (𝟙 + 𝟙)) -{ θ1 }-> 𝟙)%T)].
    Proof using All.
      iIntros "#Hρ1 #Hρ2".
      iApplyT (sem_typed_match_split [] []).
      - iApplyT sem_typed_vg_of_int. typed_var.
      - iApply env_le_refl.
      - iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|].
        typed_cont.
      - iApply env_le_refl.
      - iApply env_le_refl.
      - (* The inner [SOME "m"] shadows the group element [m]. *)
        iApplyT (sem_typed_match_split [] [("m", _)]).
        + iApplyT sem_typed_load_cpy. typed_var_copy.
        + iApply env_le_refl.
        + iApplyT sem_typed_seq.
          { iApplyT sem_typed_store_cpy_gen.
            2: { iApplyT sem_typed_injr. typed_var_copy. }
            typed_var_copy. }
          iApplyT sem_typed_let.
          { (* [k] is live across the key request: fine because [¡θ2] is OnceR. *)
            iApplyT sem_typed_app_fun_nil; [iApply "Hρ2"|iApply (sem_typed_party true)|].
            typed_leak_fun. }
          iApplyT (sem_typed_match_split [] []).
          * typed_var.
          * iApply env_le_refl.
          * iApplyT sem_typed_sub_env; first iApply env_le_weaken.
            iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|].
            typed_cont.
          * iApply env_le_refl.
          * iApply env_le_refl.
          * iApplyT sem_typed_let.
            { iApplyT sem_typed_mask; typed_var. }
            iApplyT sem_typed_seq.
            { iApplyT sem_typed_app_fun_nil; first iApply "Hρ1".
              - iApplyT sem_typed_pair; [iApply (sem_typed_party true)|typed_var].
              - typed_leak_fun. }
            iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|].
            typed_cont.
          * iApply env_le_refl.
        + iApply env_le_refl.
        + env_pick. iApply env_le_refl.
        + iApplyT sem_typed_sub_env; first iApply env_le_weaken.
          iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|].
          typed_cont.
        + env_solve.
      - iApply env_le_refl.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma chan_recv_handler_typed (θ1 θ2 ρh : sem_row Σ) :
      ⊢ (¡ θ1)%R ≤ᵣ ρh -∗ (¡ θ2)%R ≤ᵣ ρh -∗
      sem_typed [("payload", (𝟙 + 𝟙)%T); ("k", (Option 𝔾 -{ ρh }-[OS]-> 𝟙)%T);
                 ("doGK", gk θ2); ("doRecv", ((𝟙 + 𝟙) -{ θ1 }-> Option 𝔾)%T)]
        (let: "key" := "doGK" (alice) in
         match: "key" with
         | NONE => "k" NONEV
         | SOME "key" =>
             let: "r" := ("doRecv" bob) in
             match: "r" with
             | NONE => "k" NONEV
             | SOME "m" => "k" (SOME (mask "key" "m"))
             end
         end)%E
        (let: "key" := "doGK" (alice) in
         match: "key" with
         | NONE => "k" NONEV
         | SOME "key" =>
             let: "r" := ("doRecv" bob) in
             match: "r" with
             | NONE => "k" NONEV
             | SOME "m" => "k" (SOME (mask "key" "m"))
             end
         end)%E
        ρh 𝟙 [("doGK", gk θ2); ("doRecv", ((𝟙 + 𝟙) -{ θ1 }-> Option 𝔾)%T)].
    Proof using All.
      iIntros "#Hρ1 #Hρ2".
      (* The payload (Bob's direction) is not used. *)
      iApplyT sem_typed_sub_env; first iApply env_le_weaken.
      iApplyT sem_typed_let.
      { (* [k] is live across the key request: fine because [¡θ2] is OnceR. *)
        iApplyT sem_typed_app_fun_nil; [iApply "Hρ2"|iApply (sem_typed_party false)|].
        typed_leak_fun. }
      iApplyT (sem_typed_match_split [] []).
      - typed_var.
      - iApply env_le_refl.
      - iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|].
        typed_cont.
      - iApply env_le_refl.
      - iApply env_le_refl.
      - iApplyT sem_typed_let.
        { iApplyT sem_typed_app_fun_nil; [iApply "Hρ1"|iApply (sem_typed_party true)|].
          typed_leak_fun. }
        iApplyT (sem_typed_match_split [] []).
        + typed_var.
        + iApply env_le_refl.
        + iApplyT sem_typed_sub_env; first iApply env_le_weaken.
          iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|].
          typed_cont.
        + iApply env_le_refl.
        + iApply env_le_refl.
        + iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
          * iApplyT sem_typed_injr. iApplyT sem_typed_mask; typed_var.
          * typed_cont.
        + iApply env_le_refl.
      - iApply env_le_refl.
        Unshelve. all: solve_typed_side.
    Qed.


    (* The body of [CHAN] (free in "f", "effs" and the hoisted "message"),
     copied verbatim from [sec_channel_def.CHAN], so that [CHAN] is
     [let: "message" := ref NONEV in λ: "f" "effs", CHAN_body]. *)
    Definition CHAN_body : expr :=
      (let, ("ChanOp", "doGK") := "effs" in
       let, ("doSend", "doRecv") := "ChanOp" in
       effect "ssend"
         effect "srecv"
         let: "doSecSend" := (λ: "m", do: "ssend" "m") in
         let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
         handle: handle: "f" ("doSecSend", "doSecRecv") with
      (*SendSecure*)
      | effect "ssend" "m", rec "k" =>
          match: vg_of_int "m" with
          | NONE => "k" #()%V
          | SOME "m" => 
              match: !"message" with
              | NONE => "message" <- SOME "m";;
                        let: "key" := "doGK" (bob) in
                        match: "key" with
                        | NONE => "k" #()%V
                        | SOME "key" =>
                            let: "mg" := mask "key" "m" in ("doSend" ("mg", bob));; "k" #()%V
                        end
              | SOME "m" => "k" #()%V
              end
          end 
      | return "y" => "y" end with
      (*RecvSecure*)
      | effect "srecv" "payload", rec "k" =>
          let: "key" := "doGK" (alice) in
          match: "key" with
          | NONE => "k" NONEV
          | SOME "key" =>
              let: "r" := ("doRecv" bob) in
              match: "r" with
              | NONE => "k" NONEV
              | SOME "m" =>
                  "k" (SOME (mask "key" "m"))   
              end       
          end                              
      | return "y" => "y"
       end)%E.

    Lemma CHAN_body_typed (θ θ1 θ2 : sem_row Σ) :
      ⊢ sem_typed [("f", hdl cli θ); ("effs", (chan θ1 × gk θ2)%T); ("message", Refᶜ (Option 𝔾))]
          CHAN_body CHAN_body (sem_row_union (¡ θ1) (sem_row_union (¡ θ2) θ)) 𝟙 [].
    Proof using All.
      iApply sem_typed_swap_second.
      iApplyT sem_typed_pair_elim; first typed_var.
      iApplyT sem_typed_pair_elim; first typed_var.
      iApply sem_typed_effect_gen. iIntros (ls1 ls2).
      iApply sem_typed_effect_gen. iIntros (lr1 lr2). simpl.
      (* The client's [doSecSend]/[doSecRecv]: their signatures fix the client
       row [θc := σs · σr · ⟨⟩]. *)
      iApplyT sem_typed_let.
      { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
        iApplyT sem_oval_typed_ufun.
        iApply (sem_typed_do_const OS _ (ls1, ls2) ℕ 𝟙%T).
        iApply sem_typed_sub_nil. iApply sem_typed_var. }
      iApplyT sem_typed_let.
      { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
        iApplyT sem_oval_typed_ufun.
        iApplyT sem_typed_sub_row; first iApply row_le_cons_extend.
        iApply (sem_typed_do_const OS ⟨⟩%R (lr1, lr2) (𝟙 + 𝟙)%T (Option 𝔾)%T).
        iApply (sem_typed_party true). }
      (* The send handler keeps [message], [doGK] and [doSend]; the receive
       handler keeps [doGK] and [doRecv]. *)
      iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT (sem_typed_sub_env _ ([("doSecRecv", _); ("doSecSend", _); ("f", _);
                                     ("message", _); ("doGK", _); ("doSend", _)]
                                      ++ [("doGK", _); ("doRecv", _)])).
      { simpl. env_solve. }
      (* Outer handler: srecv. *)
      iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option 𝔾)%T).
      - (* Inner handler: ssend. *)
        iApplyT sem_typed_sub_row; first iApply row_le_swap_second.
        iApplyT (sem_typed_sub_env _ ([_; _; _] ++ [_; _; _])); first iApply env_le_refl.
        iApplyT (sem_typed_deep_handler_OS (ls1, ls2) (λ _, ℕ) (λ _, 𝟙)%T).
        + (* The client call [f (doSecSend, doSecRecv)]. *)
          iApplyT sem_typed_app_fun_nil.
          2: { iApplyT sem_typed_pair; typed_var. }
          2: { iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst. }
          row_le_submseteq.
        + iIntros (?). iApply chan_send_handler_typed;
            row_le_submseteq.
        + typed_var.
      - iIntros (?). iApply chan_recv_handler_typed;
          row_le_submseteq.
      - iApplyT sem_typed_sub_env_final; last typed_var. env_solve.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma CHAN_typed_u m :
      ⊢ ⊨ᵥ CHAN ≤ CHAN : fac m (∀ᵣ θ, hdl cli θ → τ__f θ chan gk).
    Proof using All.
      iApply fac_closure.
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
      iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_]). iApply sem_typed_RLam. iIntros (θ).
      (* the copyable reference is the only captured state *)
      iApplyT sem_oval_typed_ufun.
      iApply (sem_typed_oval _ [_; _]).
      iApply sem_typed_RLam. iIntros (θ1). iApply sem_typed_RLam. iIntros (θ2).
      iApplyT sem_oval_typed_afun. simpl.
      iApply sem_typed_swap_second. iApply CHAN_body_typed.
      Unshelve. all: solve_typed_side.
    Qed.

    Lemma CHAN_typed m :
      ⊢ ⊨ᵥ CHAN ≤ CHAN : fac m (∀ᵣ θ, hdl cli θ ⊸ τ__f θ chan gk).
    Proof using All.
      iApply sem_val_typed_sub; last iApply CHAN_typed_u.
      iApply fac_le. iApply ty_le_row_forall. iIntros (θ). iApply (ty_le_mbang_elim MS).
    Qed.

  End chan.


End new_comp_verification.
