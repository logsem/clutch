From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import p_composition primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_common sec_channel_def sec_channel_prf 
  dhke_channel_lazy_results dhke_channel_authchan_new
  new_composition_defs mask.

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
  Definition aleak (θ : sem_row Σ) : sem_ty Σ :=
    (((𝔾 × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option ℕ))%T.
  Definition leakI (θ : sem_row Σ) : sem_ty Σ :=
    (((𝟙 + 𝟙) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝟙))%T.
  Definition gk (θ : sem_row Σ) : sem_ty Σ := ((𝟙 + 𝟙) -{ θ }-> Option 𝔾)%T.
  Definition cli (θ : sem_row Σ) : sem_ty Σ :=
    ((ℕ -{ θ }-> 𝟙) × (𝟙 -{ θ }-> Option 𝔾))%T.
  (* the handler consuming an interface I, polymorphic over I's row *)
  Definition hdl (I : sem_row Σ -> sem_ty Σ) (θ : sem_row Σ) : sem_ty Σ :=
    (∀ᵣ θ', I θ' -{ sem_row_union θ' θ }-∘ 𝟙)%T.
  (* [τ__f] with the interface rows flipped: the client's operations may be
     handled by one-shot handlers that call the environment while holding a
     continuation (cf. [τ__FO]). *)
  Definition τ__f_once (θ : sem_row Σ) (τ1' τ2' : sem_row Σ → sem_ty Σ) : sem_ty Σ :=
    (∀ᵣ θ1, ∀ᵣ θ2, (τ1' θ1 × τ2' θ2) -{ sem_row_union (¡ θ1) (sem_row_union (¡ θ2) θ) }-∘ 𝟙)%T.

  Lemma τFO_le_τFC ι κ :
    ⊢ τ__FO ι κ ≤ₜ τ__FC ι κ.
  Proof. 
    iApply ty_le_row_forall. iIntros (θ).
    iApply ty_le_arr; [iApply row_le_refl | | iApply ty_le_refl].
    iApply ty_le_row_forall. iIntros (θ1).
    iApply ty_le_arr; [|iApply ty_le_refl|iApply ty_le_refl].
    iApply row_le_union'; rewrite ?iThyIfMono_iLblSig_to_iThyIfMono ?labels_l_to_iThyIfMono ?labels_r_to_iThyIfMono; try done.
    - iApply row_le_mfbang_intro.
    - iApply row_le_refl.
  Qed. 

  (* Atomic functionalities, as effect-handler transformers (τ__F τ τ' takes
     a τ'-consuming handler to a τ-consuming handler). *)

  (* ----------------------------------------------------------------- *)
  (* [F_OAUTH_typed], derived from the compatibility lemmas.            *)
  (*                                                                    *)
  (* The type is [τ__FO], not [τ__F]: in both handlers the one-shot     *)
  (* continuation [k] is still live when F_OAUTH calls the leak         *)
  (* functions ([doLeakSend (m,dst);; k ()], [let r := doLeakRecv from  *)
  (* in … k …]).  Under [τ__F] a context could handle the leak effect   *)
  (* multi-shot and make [k] run twice; under [τ__FO] the body runs at  *)
  (* [¡θ₂ ∪ θ], and [¡θ₂] is OnceR, so [k] may be held across the call. *)
  (* ----------------------------------------------------------------- *)

  (* A nested section, so the local instance and hint modes below do not
     reach the BREL proofs further down. *)
  Section f_oauth.

    #[local] Instance multi_ty_group : MultiT (𝔾 : sem_ty Σ).
    Proof.
      constructor. iIntros "!#" (v1 v2) "(%g & -> & ->)".
      rewrite /sem_ty_mbang /=. iModIntro. by iExists g.
    Qed.

    (* See the tactics at the end of [compatibility.v]. *)
    Import typed_hint_modes.

    Lemma oauth_send_handler_typed (θ₂ ρh : sem_row Σ) :
      ⊢ (¡ θ₂)%R ≤ᵣ ρh -∗
      sem_typed [("payload", (𝔾 × (𝟙 + 𝟙))%T); ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T);
                 ("message", Refᶜ (Option 𝔾)); ("doLeakSend", ((𝔾 × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙)%T)]
        (let, ("m", "dst") := "payload" in
         match: !"message" with
         | NONE => "message" <- SOME "m" ;; ("doLeakSend" ("m", "dst"));; "k" #()%V
         | SOME "message" => "k" #()%V
         end)%E
        (let, ("m", "dst") := "payload" in
         match: !"message" with
         | NONE => "message" <- SOME "m" ;; ("doLeakSend" ("m", "dst"));; "k" #()%V
         | SOME "message" => "k" #()%V
         end)%E
        ρh 𝟙 [("message", Refᶜ (Option 𝔾)); ("doLeakSend", ((𝔾 × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙)%T)].
    Proof.
      iIntros "#Hρ".
      iApplyT sem_typed_pair_elim; first typed_var.
      (* The [SOME "message"] branch shadows the reference, so it sets the
       [message] entry aside; the [NONE] branch needs it. *)
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
      - (* Drop the shadowing [message : 𝔾]; [m] and [dst] are dropped by the
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

    Lemma F_OAUTH_val_typed :
      ⊢ sem_val_typed F_OAUTH F_OAUTH (τ__FO oaleak chan).
    Proof using Type*.
      iApply sem_typed_Rclosure. iIntros (θ).
      iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
      iApply sem_typed_closure; first done.
      iApply (sem_typed_oval _ [_]). iApply sem_typed_RLam. iIntros (θ₂).
      iApplyT sem_oval_typed_afun.
      iApplyT sem_typed_pair_elim; first typed_var.
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
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

    Corollary F_OAUTH_typed : ⊢ sem_typed [] F_OAUTH F_OAUTH ⊥ (τ__FO oaleak chan) [].
    Proof using All. 
      iApply sem_typed_val.
      iApply F_OAUTH_val_typed.
    Qed. 

    Corollary F_OAUTH_FC_typed : ⊢ sem_typed [] F_OAUTH F_OAUTH ⊥ (τ__FC oaleak chan) [].
    Proof using All. 
      iApply sem_typed_val.
      iApply sem_val_typed_sub; last iApply F_OAUTH_val_typed.
      iApply τFO_le_τFC.
    Qed. 
      
  End f_oauth.


  (* [F_AUTH], derived from the compatibility lemmas: F_OAUTH's shape with
     one message reference per direction. *)
  Section f_auth.
    Import typed_hint_modes.
    #[local] Existing Instance multi_ty_group.

    Lemma fauth_send_handler_typed (θ₂ ρh : sem_row Σ) :
      ⊢ (¡ θ₂)%R ≤ᵣ ρh -∗
      sem_typed [("message", (𝔾 × (𝟙 + 𝟙))%T); ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T);
                 ("m1", Refᶜ (Option 𝔾)); ("m2", Refᶜ (Option 𝔾));
                 ("doLeakSend", ((𝔾 × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙)%T)]
        (let, ("m", "dst") := "message" in
         match: "dst" with
           
           InjL <> => match: !"m1" with 
                        NONE => "m1" <- SOME "m";; ("doLeakSend" ("m", "dst"));; "k" #()%V
                      | SOME "x" => "k" #()%V 
                      end
                        
         | InjR <> => match: !"m2" with
                        NONE => "m2" <- SOME "m";; ("doLeakSend" ("m", "dst"));; "k" #()%V
                      | SOME "x" => "k" #()%V 
                      end
         end)%E
        (let, ("m", "dst") := "message" in
         match: "dst" with
           
           InjL <> => match: !"m1" with 
                        NONE => "m1" <- SOME "m";; ("doLeakSend" ("m", "dst"));; "k" #()%V
                      | SOME "x" => "k" #()%V 
                      end
                        
         | InjR <> => match: !"m2" with
                        NONE => "m2" <- SOME "m";; ("doLeakSend" ("m", "dst"));; "k" #()%V
                      | SOME "x" => "k" #()%V 
                      end
         end)%E
        ρh 𝟙 [("m1", Refᶜ (Option 𝔾)); ("m2", Refᶜ (Option 𝔾));
              ("doLeakSend", ((𝔾 × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙)%T)].
    Proof.
      iIntros "#Hρ".
      iApplyT sem_typed_pair_elim; first typed_var.
      (* [dst] is matched on and then leaked, so the scrutinee copies it. *)
      iApplyT (sem_typed_match_split [] []).
      - typed_var_copy.
      - iApply env_le_refl.
      - iApplyT (sem_typed_match_split [] []).
        + iApplyT sem_typed_load_cpy. typed_var_copy.
        + iApply env_le_refl.
        + iApplyT sem_typed_seq.
          { iApplyT sem_typed_store_cpy_gen.
            2: { iApplyT sem_typed_injr. typed_var_copy. }
            typed_var_copy. }
          iApplyT sem_typed_seq.
          { iApplyT sem_typed_app_fun_nil; [iApply "Hρ"|iApplyT sem_typed_pair; typed_var|typed_leak_fun]. }
          iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|typed_cont].
        + iApply env_le_refl.
        + iApply env_le_refl.
        + iApplyT sem_typed_sub_env; first iApply env_le_weaken.
          iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|typed_cont].
        + env_solve.
      - iApply env_le_refl.
      - iApply env_le_refl.
      - iApplyT (sem_typed_match_split [] []).
        + iApplyT sem_typed_load_cpy. typed_var_copy.
        + iApply env_le_refl.
        + iApplyT sem_typed_seq.
          { iApplyT sem_typed_store_cpy_gen.
            2: { iApplyT sem_typed_injr. typed_var_copy. }
            typed_var_copy. }
          iApplyT sem_typed_seq.
          { iApplyT sem_typed_app_fun_nil; [iApply "Hρ"|iApplyT sem_typed_pair; typed_var|typed_leak_fun]. }
          iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|typed_cont].
        + iApply env_le_refl.
        + iApply env_le_refl.
        + iApplyT sem_typed_sub_env; first iApply env_le_weaken.
          iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|typed_cont].
        + env_solve.
      - iApply env_le_refl.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma fauth_recv_handler_typed (θ₂ ρh : sem_row Σ) :
      ⊢ (¡ θ₂)%R ≤ᵣ ρh -∗
      sem_typed [("from", (𝟙 + 𝟙)%T); ("k", (Option 𝔾 -{ ρh }-[OS]-> 𝟙)%T);
                 ("m1", Refᶜ (Option 𝔾)); ("m2", Refᶜ (Option 𝔾));
                 ("doLeakRecv", ((𝟙 + 𝟙) -{ θ₂ }-> Option ℕ)%T)]
        (let: "r" := ("doLeakRecv" "from") in
         match: "r" with
           NONE => "k" NONEV
         | SOME "x" => match: "from" with
                         
                         InjL <> => match: !"m2" with
                                      NONE => "k" NONEV
                                    | SOME "m" => "k" (SOME "m")
                                    end
                                      
                       | InjR <> => match: !"m1" with
                                      NONE => "k" NONEV
                                    | SOME "m" => "k" (SOME "m")
                                    end
                       end
         end)%E
        (let: "r" := ("doLeakRecv" "from") in
         match: "r" with
           NONE => "k" NONEV
         | SOME "x" => match: "from" with
                         
                         InjL <> => match: !"m2" with
                                      NONE => "k" NONEV
                                    | SOME "m" => "k" (SOME "m")
                                    end
                                      
                       | InjR <> => match: !"m1" with
                                      NONE => "k" NONEV
                                    | SOME "m" => "k" (SOME "m")
                                    end
                       end
         end)%E
        ρh 𝟙 [("m1", Refᶜ (Option 𝔾)); ("m2", Refᶜ (Option 𝔾));
              ("doLeakRecv", ((𝟙 + 𝟙) -{ θ₂ }-> Option ℕ)%T)].
    Proof.
      iIntros "#Hρ".
      (* [from] is leaked and then matched on, so the leak call copies it. *)
      iApplyT sem_typed_let.
      { iApplyT sem_typed_app_fun_nil; [iApply "Hρ"|typed_var_copy|typed_leak_fun]. }
      iApplyT (sem_typed_match_split [] []).
      - typed_var.
      - iApply env_le_refl.
      - iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|typed_cont].
      - env_solve.
      - iApply env_le_refl.
      - iApplyT sem_typed_sub_env; first iApply env_le_weaken.
        iApplyT (sem_typed_match_split [] []).
        + typed_var.
        + iApply env_le_refl.
        + iApplyT (sem_typed_match_split [] []).
          * iApplyT sem_typed_load_cpy. typed_var_copy.
          * iApply env_le_refl.
          * iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|typed_cont].
          * iApply env_le_refl.
          * iApply env_le_refl.
          * iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injr; typed_var|typed_cont].
          * iApply env_le_refl.
        + iApply env_le_refl.
        + iApply env_le_refl.
        + iApplyT (sem_typed_match_split [] []).
          * iApplyT sem_typed_load_cpy. typed_var_copy.
          * iApply env_le_refl.
          * iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|typed_cont].
          * iApply env_le_refl.
          * iApply env_le_refl.
          * iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injr; typed_var|typed_cont].
          * iApply env_le_refl.
        + iApply env_le_refl.
      - iApply env_le_refl.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma F_AUTH_val_typed :
      ⊢ sem_val_typed F_AUTH F_AUTH (τ__FO aleak chan).
    Proof using Type*.
      iApply sem_typed_Rclosure. iIntros (θ).
      iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
      iApply sem_typed_closure; first done.
      iApply (sem_typed_oval _ [_]). iApply sem_typed_RLam. iIntros (θ₂).
      iApplyT sem_oval_typed_afun.
      iApplyT sem_typed_pair_elim; first typed_var.
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
      iApply sem_typed_effect_gen. iIntros (ls1 ls2).
      iApply sem_typed_effect_gen. iIntros (lr1 lr2). simpl.
      (* The client's [doSend]/[doRecv]: their signatures fix the client row. *)
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
      (* Each handler keeps its own copies of the two references. *)
      iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT (sem_typed_sub_env _ ([("doRecv", _); ("doSend", _); ("f", _); ("m1", _); ("m2", _); ("doLeakSend", _)]
                                      ++ [("m1", _); ("m2", _); ("doLeakRecv", _)])).
      { simpl. env_solve. }
      (* Outer handler: recv. *)
      iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option 𝔾)%T).
      - (* Inner handler: send. *)
        iApplyT sem_typed_sub_row; first iApply row_le_swap_second.
        iApplyT (sem_typed_sub_env _ ([_; _; _] ++ [_; _; _])); first iApply env_le_refl.
        iApplyT (sem_typed_deep_handler_OS (ls1, ls2) (λ _, 𝔾 × (𝟙 + 𝟙))%T (λ _, 𝟙)%T).
        + (* The client call [f (doSend, doRecv)], at [¡θ₁ ∪ θ ≤ θ₁ ∪ θ]. *)
          iApplyT sem_typed_app_fun_nil.
          2: { iApplyT sem_typed_pair; typed_var. }
          2: { iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst. }
          iApply row_le_trans; first iApplyT row_le_union'.
          * iApply row_le_mfbang_elim.
          * iApply row_le_refl.
          * row_le_submseteq.
        + iIntros (?). iApply fauth_send_handler_typed. row_le_submseteq.
        + iApplyT sem_typed_sub_env_final; last iApplyT sem_typed_unit'. env_solve.
      - iIntros (?). iApply fauth_recv_handler_typed. row_le_submseteq.
      - iApplyT sem_typed_sub_env_final; last iApplyT sem_typed_unit'. env_solve.
        Unshelve. all: solve_typed_side.
    Qed.

    Corollary F_AUTH_typed : ⊢ sem_typed [] F_AUTH F_AUTH ⊥  (τ__FO aleak chan) [].
    Proof using All. 
      iApply sem_typed_val.
      iApply F_AUTH_val_typed.
    Qed. 

    Corollary F_AUTH_FC_typed : ⊢ sem_typed [] F_AUTH F_AUTH ⊥ (τ__FC aleak chan) [].
    Proof using All. 
      iApply sem_typed_val.
      iApply sem_val_typed_sub; last iApply F_AUTH_val_typed.
      iApply τFO_le_τFC.
    Qed. 

  End f_auth.

  (* [DH_SIM], derived from the compatibility lemmas.  The two exponents are
     drawn lazily from tapes ([sem_ty_tape]: the identity coupling makes both
     sides draw the same value) and cached in [Refᶜ (Option ℕ)]. *)
  Section dh_sim.
    Import typed_hint_modes.
    #[local] Existing Instance multi_ty_group.

    Lemma sem_typed_party (b : bool) Γ ρ :
      ⊢ sem_typed Γ (if b then bob else alice) (if b then bob else alice) ρ (𝟙 + 𝟙)%T Γ.
    Proof.
      iApply sem_typed_sub_nil. iApply sem_typed_val. iIntros "!>".
      destruct b; iExists _, _; [iLeft|iRight]; done.
    Qed.

    Lemma sem_typed_vexp (b : vgG) Γ1 Γ2 e e' ρ :
      ⊢ sem_typed Γ1 e e' ρ ℕ Γ2 -∗
      sem_typed Γ1 (vexp (vgval b) e) (vexp (vgval b) e') ρ 𝔾 Γ2.
    Proof using All.
      iIntros "#He !# %γ HΓ1 /=".
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ1]"); first by iApply "He".
      iIntros "!# % % (Hn & HΓ2) /=". iDestruct "Hn" as (n) "(-> & ->)".
      iApply (brel_exp_l []). iApply (brel_exp_r []).
      iApply brel_value. iIntros "$ !>". iFrame. by iExists _.
    Qed.

    Lemma dh_sim_send_handler_typed (θ₂ ρh : sem_row Σ) :
      ⊢ (¡ θ₂)%R ≤ᵣ ρh -∗
      sem_typed [("dst", (𝟙 + 𝟙)%T); ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T);
                 ("α", sem_ty_tape); ("l1", Refᶜ (Option ℕ)); ("β", sem_ty_tape); ("l2", Refᶜ (Option ℕ));
                 ("doSend", ((𝔾 × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙)%T)]
        (match: "dst" with
           InjL <> => let: "c" := 
                        (match: !"l1" with
                           NONE => let: "c" := (samplelbl "α" #()%V) in "l1" <- SOME "c";; "c"
                         | SOME "c" => "c"
                         end) in
                      let: "gC" := g^"c" in
                      "doSend" ("gC",bob);;
                      "k" #()%V
         | InjR <> => let: "c" :=
                        (match: !"l2" with
                           NONE => let: "c" := (samplelbl "β" #()%V) in "l2" <- SOME "c";; "c"
                         | SOME "c" => "c"
                         end) in
                      let: "gC" := g^"c" in
                      "doSend" ("gC", alice);;
                      "k" #()%V
         end)%E
        (match: "dst" with
           InjL <> => let: "c" := 
                        (match: !"l1" with
                           NONE => let: "c" := (samplelbl "α" #()%V) in "l1" <- SOME "c";; "c"
                         | SOME "c" => "c"
                         end) in
                      let: "gC" := g^"c" in
                      "doSend" ("gC",bob);;
                      "k" #()%V
         | InjR <> => let: "c" :=
                        (match: !"l2" with
                           NONE => let: "c" := (samplelbl "β" #()%V) in "l2" <- SOME "c";; "c"
                         | SOME "c" => "c"
                         end) in
                      let: "gC" := g^"c" in
                      "doSend" ("gC", alice);;
                      "k" #()%V
         end)%E
        ρh 𝟙 [("α", sem_ty_tape); ("l1", Refᶜ (Option ℕ)); ("β", sem_ty_tape); ("l2", Refᶜ (Option ℕ));
              ("doSend", ((𝔾 × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙)%T)].
    Proof using All.
      iIntros "#Hρ". rewrite /samplelbl.
      (* Each branch draws its exponent from its tape at most once (cached in
       [l1]/[l2]) and sends [g^c]. *)
      iApplyT (sem_typed_match_split [] []).
      - typed_var.
      - iApply env_le_refl.
      - iApplyT sem_typed_let.
        { iApplyT (sem_typed_match_split [] []).
          + iApplyT sem_typed_load_cpy. typed_var_copy.
          + iApply env_le_refl.
          + iApplyT sem_typed_let.
            { iApplyT sem_typed_let; first iApplyT sem_typed_unit'.
              iApplyT sem_typed_rand; [typed_var_copy|iApplyT sem_typed_int']. }
            iApplyT sem_typed_seq.
            { iApplyT sem_typed_store_cpy_gen.
              2: { iApplyT sem_typed_injr. typed_var_copy. }
              typed_var_copy. }
            typed_var.
          + iApply env_le_refl.
          + iApply env_le_refl.
          + typed_var.
          + iApply env_le_refl. }
        iApplyT sem_typed_let; first (iApplyT sem_typed_vexp; typed_var).
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_app_fun_nil; [iApply "Hρ"|iApplyT sem_typed_pair; [iApply (sem_typed_party true)|typed_var]|typed_leak_fun]. }
        iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|typed_cont].
      - iApply env_le_refl.
      - iApply env_le_refl.
      - iApplyT sem_typed_let.
        { iApplyT (sem_typed_match_split [] []).
          + iApplyT sem_typed_load_cpy. typed_var_copy.
          + iApply env_le_refl.
          + iApplyT sem_typed_let.
            { iApplyT sem_typed_let; first iApplyT sem_typed_unit'.
              iApplyT sem_typed_rand; [typed_var_copy|iApplyT sem_typed_int']. }
            iApplyT sem_typed_seq.
            { iApplyT sem_typed_store_cpy_gen.
              2: { iApplyT sem_typed_injr. typed_var_copy. }
              typed_var_copy. }
            typed_var.
          + iApply env_le_refl.
          + iApply env_le_refl.
          + typed_var.
          + iApply env_le_refl. }
        iApplyT sem_typed_let; first (iApplyT sem_typed_vexp; typed_var).
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_app_fun_nil; [iApply "Hρ"|iApplyT sem_typed_pair; [iApply (sem_typed_party false)|typed_var]|typed_leak_fun]. }
        iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|typed_cont].
      - iApply env_le_refl.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma dh_sim_recv_handler_typed (θ₂ ρh : sem_row Σ) :
      ⊢ (¡ θ₂)%R ≤ᵣ ρh -∗
      sem_typed [("from", (𝟙 + 𝟙)%T); ("k", (Option 𝟙 -{ ρh }-[OS]-> 𝟙)%T);
                 ("doRecv", ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝔾)%T)]
        (let: "r" := "doRecv" "from" in
         match: "r" with
           NONE => "k" NONE
         | SOME "x" => "k" (SOME #()%V)
         end)%E
        (let: "r" := "doRecv" "from" in
         match: "r" with
           NONE => "k" NONE
         | SOME "x" => "k" (SOME #()%V)
         end)%E
        ρh 𝟙 [("doRecv", ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝔾)%T)].
    Proof.
      iIntros "#Hρ".
      iApplyT sem_typed_let.
      { iApplyT sem_typed_app_fun_nil; [iApply "Hρ"|typed_var|typed_leak_fun]. }
      iApplyT (sem_typed_match_split [] []).
      - typed_var.
      - iApply env_le_refl.
      - iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injl; iApplyT sem_typed_unit'|typed_cont].
      - iApply env_le_refl.
      - iApply env_le_refl.
      - iApplyT sem_typed_sub_env; first iApply env_le_weaken.
        iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injr; iApplyT sem_typed_unit'|typed_cont].
      - iApply env_le_refl.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma DH_SIM_val_typed :
      ⊢ sem_val_typed DH_SIM DH_SIM (τ__FO chan leakI).
    Proof using All.
      iApply sem_typed_Rclosure. iIntros (θ).
      iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
      iApply sem_typed_closure; first done.
      iApply (sem_typed_oval _ [_]). iApply sem_typed_RLam. iIntros (θ₂).
      iApplyT sem_oval_typed_afun.
      iApplyT sem_typed_pair_elim; first typed_var.
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloctape; iApplyT sem_typed_int').
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloctape; iApplyT sem_typed_int').
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
      iApply sem_typed_effect_gen. iIntros (ls1 ls2).
      iApply sem_typed_effect_gen. iIntros (lr1 lr2). simpl.
      (* The client's [doLeakSend]/[doLeakRecv]: their signatures fix the
       client row. *)
      iApplyT sem_typed_let.
      { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
        iApplyT sem_oval_typed_ufun.
        iApply (sem_typed_do_const OS _ (ls1, ls2) (𝟙 + 𝟙)%T 𝟙%T).
        iApply sem_typed_sub_nil. iApply sem_typed_var. }
      iApplyT sem_typed_let.
      { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
        iApplyT sem_oval_typed_ufun.
        iApplyT sem_typed_sub_row; first iApply row_le_cons_extend.
        iApply (sem_typed_do_const OS ⟨⟩%R (lr1, lr2) (𝟙 + 𝟙)%T (Option 𝟙)%T).
        iApply sem_typed_sub_nil. iApply sem_typed_var. }
      (* The send handler keeps the tapes, caches and [doSend]; the receive
       handler keeps [doRecv]. *)
      iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT (sem_typed_sub_env _ ([("doLeakRecv", _); ("doLeakSend", _); ("f", _);
                                     ("α", _); ("l1", _); ("β", _); ("l2", _); ("doSend", _)]
                                      ++ [("doRecv", _)])).
      { simpl. env_solve. }
      (* Outer handler: leakRecv. *)
      iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option 𝟙)%T).
      - (* Inner handler: leakSend. *)
        iApplyT sem_typed_sub_row; first iApply row_le_swap_second.
        iApplyT (sem_typed_sub_env _ ([_; _; _] ++ [_; _; _; _; _])); first iApply env_le_refl.
        iApplyT (sem_typed_deep_handler_OS (ls1, ls2) (λ _, 𝟙 + 𝟙)%T (λ _, 𝟙)%T).
        + (* The client call [f (doLeakSend, doLeakRecv)], at [¡θ₁ ∪ θ ≤ θ₁ ∪ θ]. *)
          iApplyT sem_typed_app_fun_nil.
          2: { iApplyT sem_typed_pair; typed_var. }
          2: { iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst. }
          iApply row_le_trans; first iApplyT row_le_union'.
          * iApply row_le_mfbang_elim.
          * iApply row_le_refl.
          * row_le_submseteq.
        + iIntros (?). iApply dh_sim_send_handler_typed. row_le_submseteq.
        + typed_var.
      - iIntros (?). iApply dh_sim_recv_handler_typed. row_le_submseteq.
      - iApplyT sem_typed_sub_env_final; last typed_var. env_solve.
        Unshelve. all: solve_typed_side.
    Qed.

    Corollary DH_SIM_typed : ⊢ sem_typed [] DH_SIM DH_SIM ⊥ (τ__FO chan leakI) [].
      iApply sem_typed_val. iApply DH_SIM_val_typed.
    Qed. 

    Corollary DH_SIM_FC_typed : ⊢ sem_typed [] DH_SIM DH_SIM ⊥ (τ__FC chan leakI) [].
      iApply sem_typed_val.
      iApply sem_val_typed_sub; last iApply DH_SIM_val_typed.
      iApply τFO_le_τFC.
    Qed. 


  End dh_sim.

  (* The body of [F_KE_lazy_alice] (free in "f","effs"), copied verbatim
     from [def_dhke.F_KE_lazy_alice], so that [F_KE_lazy_alice] is
     [λ: "f" "effs", F_KE_body]. *)
  Definition F_KE_body : expr :=
    (let, ("doLeakSend", "doLeakRecv") := "effs" in
     let: "γ" := alloc #(S n'') in
     let: "lc" := ref NONEV in
     let: "sample_or_load" :=
       λ:<>, match: !"lc" with
         | NONE =>
             let: "c" := (samplelbl "γ" #()%V) in
             "lc" <- SOME "c" ;;
             "c"
         | SOME "c" => "c"
         end
     in

     effect "getKey"
       let: "doGK" := (λ: "party", do: (EffName "getKey") "party") in
       handle: "f" "doGK" with
    | effect (EffName "getKey") "p", rec "k" =>
        match: "p" with
          (* Alice *)
          InjL <> =>
            let: "c" := "sample_or_load" #()%V in
            let: "key" := g^"c" in
            (* Leak a send *)
            ("doLeakSend" bob);;
            (* Receive a dummy value *)
            let: "r" := ("doLeakRecv" bob) in
            match: "r" with
              NONE => "k" NONEV
            | SOME "w" =>
                "k" (SOME "key")
            end
        (* Bob  *)
        | InjR <> =>
            let: "r" := ("doLeakRecv" alice) in
            match: "r" with
              NONE => "k" NONEV
            | SOME "w" =>
                ("doLeakSend" alice);;
                match: !"lc" with
                | NONE => "k" NONEV
                | SOME "c" =>
                    let: "key" := g^"c" in
                    "k" (SOME "key")
                end
            end
        end
    | return "y" => "y" end).

  Section f_ke.
    Import typed_hint_modes.
    #[local] Existing Instance multi_ty_group.

    (* Like [C_lazy]: [sample_or_load] captures copies of the tape and the
     cache, and Bob reads the cache directly. *)
    Lemma F_KE_body_typed :
      ⊢ ∀ (θ θG : sem_row Σ),
          sem_typed [("f", (∀ᵣ θ₁, gk θ₁ -{ sem_row_union (¡ θ₁) θ }-∘ 𝟙)%T); ("effs", leakI θG)]
            F_KE_body F_KE_body (sem_row_union (¡θG)%R θ) (𝟙)%T [].
    Proof using All.
      iIntros (θ θG). rewrite /F_KE_body /samplelbl.
      iApplyT sem_typed_pair_elim; first typed_var.
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloctape; iApplyT sem_typed_int').
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
      (* [sample_or_load] captures copies of the tape and the cache. *)
      iApplyT sem_typed_let.
      { iApplyT (sem_typed_sub_env _ ([("γ", _); ("lc", _)] ++ [("lc", _); ("γ", _); ("doLeakSend", _); ("doLeakRecv", _); ("f", _)])).
        { simpl. env_solve. }
        iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _]).
        iApplyT sem_oval_typed_ufun. simpl.
        iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
        iApplyT (sem_typed_match_split [] []).
        - iApplyT sem_typed_load_cpy. typed_var_copy.
        - iApply env_le_refl.
        - iApplyT sem_typed_let.
          { iApplyT sem_typed_let; first iApplyT sem_typed_unit'.
            iApplyT sem_typed_rand; [typed_var_copy|iApplyT sem_typed_int']. }
          iApplyT sem_typed_seq.
          { iApplyT sem_typed_store_cpy_gen.
            2: { iApplyT sem_typed_injr. typed_var_copy. }
            typed_var_copy. }
          typed_var.
        - iApply env_le_refl.
        - iApply env_le_refl.
        - typed_var.
        - iApply env_le_refl. }
      iApply sem_typed_effect_gen. iIntros (l1 l2). simpl.
      iApplyT sem_typed_let.
      { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
        iApplyT sem_oval_typed_ufun.
        iApply (sem_typed_do_const OS ⟨⟩%R (l1, l2) (𝟙 + 𝟙)%T (Option 𝔾)%T).
        iApply sem_typed_sub_nil. iApply sem_typed_var. }
      iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT (sem_typed_sub_env _ ([("doGK", _); ("f", _)]
                                      ++ [("sample_or_load", _); ("lc", _); ("doLeakSend", _); ("doLeakRecv", _)])).
      { simpl. env_solve. }
      iApplyT (sem_typed_deep_handler_OS (l1, l2) (λ _, 𝟙 + 𝟙)%T (λ _, Option 𝔾)%T).
      - (* The client call [f doGK], at [¡θ₁ ∪ θ ≤ θ₁ ∪ θ]. *)
        iApplyT sem_typed_app_fun_nil.
        2: typed_var.
        2: { iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst. }
        iApply row_le_trans; first iApplyT row_le_union'.
        + iApply row_le_mfbang_elim.
        + iApply row_le_refl.
        + row_le_submseteq.
      - iIntros (?). simpl.
        iApplyT (sem_typed_match_split [] []).
        + typed_var.
        + iApply env_le_refl.
        + (* Alice: draw (or load) the exponent, leak a send and a receive. *)
          iApplyT sem_typed_let.
          { iApplyT sem_typed_app_fun_nil; [iApply row_le_nil|iApplyT sem_typed_unit'|].
            iApplyT sem_typed_sub_ty; [iApply ty_le_u2aarr|typed_var_copy]. }
          iApplyT sem_typed_let; first (iApplyT sem_typed_vexp; typed_var).
          iApplyT sem_typed_seq.
          { iApplyT sem_typed_app_fun_nil; [row_le_submseteq|iApply (sem_typed_party true)|typed_leak_fun]. }
          iApplyT sem_typed_let.
          { iApplyT sem_typed_app_fun_nil; [row_le_submseteq|iApply (sem_typed_party true)|typed_leak_fun]. }
          iApplyT (sem_typed_match_split [] []).
          * typed_var.
          * iApply env_le_refl.
          * iApplyT sem_typed_sub_env; first iApply env_le_weaken.
            iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|typed_cont].
          * iApply env_le_refl.
          * iApply env_le_refl.
          * iApplyT sem_typed_sub_env; first iApply env_le_weaken.
            iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injr; typed_var|typed_cont].
          * iApply env_le_refl.
        + iApply env_le_refl.
        + iApply env_le_refl.
        + (* Bob: leak a receive and a send, then read the cached exponent. *)
          iApplyT sem_typed_let.
          { iApplyT sem_typed_app_fun_nil; [row_le_submseteq|iApply (sem_typed_party false)|typed_leak_fun]. }
          iApplyT (sem_typed_match_split [] []).
          * typed_var.
          * iApply env_le_refl.
          * iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|typed_cont].
          * iApply env_le_refl.
          * iApply env_le_refl.
          * iApplyT sem_typed_sub_env; first iApply env_le_weaken.
            iApplyT sem_typed_seq.
            { iApplyT sem_typed_app_fun_nil; [row_le_submseteq|iApply (sem_typed_party false)|typed_leak_fun]. }
            iApplyT (sem_typed_match_split [] []).
            -- iApplyT sem_typed_load_cpy. typed_var_copy.
            -- iApply env_le_refl.
            -- iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|typed_cont].
            -- iApply env_le_refl.
            -- iApply env_le_refl.
            -- iApplyT sem_typed_let; first (iApplyT sem_typed_vexp; typed_var).
               iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injr; typed_var|typed_cont].
            -- iApply env_le_refl.
          * iApply env_le_refl.
        + iApply env_le_refl.
      - typed_var.
        Unshelve. all: solve_typed_side.
    Qed.


    Lemma F_KE_lazy_alice_val_typed :
      ⊢ sem_val_typed F_KE_lazy_alice F_KE_lazy_alice (τ__FO leakI gk).
    Proof using Type*.
      iApply sem_typed_Rclosure. iIntros (θ).
      iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
      iApply sem_typed_closure; first done.
      iApply (sem_typed_oval _ [_]). iApply sem_typed_RLam. iIntros (θ₂).
      iApplyT sem_oval_typed_afun. simpl.
      iApply sem_typed_swap_second. iApply F_KE_body_typed.
      Unshelve. all: solve_typed_side.
    Qed.

    Corollary F_KE_lazy_alice_typed : ⊢ sem_typed [] F_KE_lazy_alice F_KE_lazy_alice ⊥ (τ__FO leakI gk) [].
    Proof using All.
      iApply sem_typed_val.
      iApply F_KE_lazy_alice_val_typed.
    Qed. 

    Corollary F_KE_lazy_alice_FC_typed : ⊢ sem_typed [] F_KE_lazy_alice F_KE_lazy_alice ⊥ (τ__FC leakI gk) [].
    Proof using All.
      iApply sem_typed_val.
      iApply sem_val_typed_sub; last iApply F_KE_lazy_alice_val_typed.
      iApply τFO_le_τFC.
    Qed. 

  End f_ke.

  (* [CHAN], derived from the compatibility lemmas.  As for F_OAUTH, its
     one-shot handlers call [doGK]/[doSend]/[doRecv] while holding the
     continuation, so the interface rows are flipped ([τ__f_once]). *)
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


    (* The body of [CHAN] (free in "f","effs"), copied verbatim from
     [sec_channel_def.CHAN], so that [CHAN] is [λ: "f" "effs", CHAN_body]. *)
    Definition CHAN_body : expr :=
      (let, ("ChanOp", "doGK") := "effs" in 
       let, ("doSend", "doRecv") := "ChanOp" in
       let: "message" := ref NONEV in
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
      ⊢ sem_typed [("f", hdl cli θ); ("effs", (chan θ1 × gk θ2)%T)] CHAN_body CHAN_body
          (sem_row_union (¡ θ1) (sem_row_union (¡ θ2) θ)) 𝟙 [].
    Proof using All.
      iApply sem_typed_swap_second.
      iApplyT sem_typed_pair_elim; first typed_var.
      iApplyT sem_typed_pair_elim; first typed_var.
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
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

    Lemma CHAN_typed :
      ⊢ sem_typed [] CHAN CHAN ⊥ (∀ᵣ θ, hdl cli θ ⊸ τ__fu θ chan gk)%T [].
    Proof using All.
      iApply sem_typed_val. iApply sem_typed_Rclosure. iIntros (θ).
      iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
      iApply sem_typed_closure; first done.
      iApply (sem_typed_oval _ [_]).
      iApply sem_typed_RLam. iIntros (θ1). iApply sem_typed_RLam. iIntros (θ2).
      iApplyT sem_oval_typed_afun. simpl.
      iApply sem_typed_swap_second. iApply CHAN_body_typed.
      Unshelve. all: solve_typed_side.
    Qed.

  End chan.


  (* Generic composition of two functionality transformers:
     [F : τ__FO A B] and [J : τ__FO B B'] compose to [F ∘f J : τ__FO A B'],
     an instance of the typing of the [func_comp] closure. *)
  Section func_comp.
    Import typed_hint_modes.

    Lemma func_comp_val_typed (T1 T2 T3 : sem_row Σ → sem_ty Σ) :
      ⊢ ⊨ᵥ func_comp ≤ func_comp :
        ((∀ᵣ θ, T2 θ ⊸ T3 θ) ⊸ (∀ᵣ θ, T1 θ ⊸ T2 θ) ⊸ (∀ᵣ θ, T1 θ ⊸ T3 θ))%T.
    Proof.
      iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
      iApply sem_typed_closure; first done.
      iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_afun.
      iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
      iApplyT sem_oval_typed_afun. simpl.
      iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
      - iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|typed_var|].
        iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst.
      - iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma func_comp_OS_typed (F J : expr) (A B B' : sem_row Σ → sem_ty Σ) :
      ⊢ sem_typed [] F F ⊥ (τ__FO A B) [] -∗ sem_typed [] J J ⊥ (τ__FO B B') []-∗
      sem_typed [] (F ∘f J) (F ∘f J) ⊥ (τ__FO A B') [].
    Proof.
      iIntros "#HF #HJ".
      iApplyT sem_typed_app_nil; last iApply "HJ".
      iApplyT sem_typed_app_nil; last iApply "HF".
      iApply sem_typed_val. iApply func_comp_val_typed.
    Qed.

  End func_comp.

  (* [F_AUTH ∘f DH_SIM]. *)
  Lemma F_AUTH_DH_SIM_FO_typed :
    ⊢ sem_typed [] (F_AUTH ∘f DH_SIM) (F_AUTH ∘f DH_SIM) ⊥ (τ__FO aleak leakI) [].
  Proof using All.
    iApply func_comp_OS_typed; iApply sem_typed_val; [iApply F_AUTH_val_typed|iApply DH_SIM_val_typed].
  Qed.

  Corollary F_AUTH_DH_SIM_typed : ⊢ sem_typed [] (F_AUTH ∘f DH_SIM) (F_AUTH ∘f DH_SIM) ⊥ (τ__FC aleak leakI) [].
  Proof using All.
    iApply sem_typed_sub.
    - iApply env_le_refl.
    - iApply env_le_refl.
    - iApply row_le_refl.    
    - iApply τFO_le_τFC.
    - iApply F_AUTH_DH_SIM_FO_typed.
  Qed. 

  Section right_comp.
    Import typed_hint_modes.

    (* [F₁ ||ᵣ F₂] for two [τ__FO] functionalities: [F₁] is instantiated at
     [¡θ1 ∪ θ] and [F₂] at [¡θh ∪ θ], where [θh] is [F₁]'s client row, so
     that every row step is a permutation of union components. *)
    Lemma right_comp_val_typed (τ1 τ1' τ2 τ2' : sem_row Σ → sem_ty Σ) :
      ⊢ ⊨ᵥ right_composition ≤ right_composition :
        (τ__FO τ2 τ2' ⊸ τ__FO τ1 τ1' ⊸ ∀ᵣ θ, τ__fu θ τ1' τ2' ⊸ τ__fu θ τ1 τ2)%T.
    Proof.
      iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
      iApply sem_typed_closure; first done.
      iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_afun.
      iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
      iApplyT sem_oval_typed_afun.
      iApply (sem_typed_oval _ [_; _; _]). iApply sem_typed_RLam. iIntros (θ1).
      iApply sem_typed_RLam. iIntros (θ2).
      iApplyT sem_oval_typed_afun. simpl.
      iApplyT sem_typed_pair_elim; first typed_var.
      iApplyT sem_typed_app_fun_nil.
      2: typed_var.
      2: { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply (sem_typed_oval _ [_; _; _])|].
           2: { iApplyT sem_typed_sub_ty; last typed_var.
                iApply ty_le_trans; first iApply (ty_le_row_forall_inst _ (sem_row_union (¡ θ1) θ)).
                iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_row_forall_inst]. }
           iApply sem_typed_RLam. iIntros (θh). iApplyT sem_oval_typed_afun. simpl.
           iApplyT sem_typed_app_fun_nil.
           2: typed_var.
           2: { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply (sem_typed_oval _ [_; _])|].
                2: { iApplyT sem_typed_sub_ty; last typed_var.
                     iApply ty_le_trans; first iApply (ty_le_row_forall_inst _ (sem_row_union (¡ θh) θ)).
                     iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_row_forall_inst]. }
                iApply sem_typed_RLam. iIntros (θh2). iApplyT sem_oval_typed_afun. simpl.
                (* The client call [f (h₂, h₁)]. *)
                iApplyT sem_typed_app_fun_nil.
                2: { iApply sem_typed_sub_nil. iApplyT sem_typed_pair; typed_var. }
                2: { iApplyT sem_typed_sub_ty; last typed_var.
                     iApply ty_le_trans; first iApply ty_le_row_forall_inst. iApply ty_le_row_forall_inst. }
                iApply row_le_refl. }
           row_le_submseteq. }
      row_le_submseteq.
      Unshelve. all: solve_typed_side.
    Qed.

  End right_comp.

  Lemma F_KE_F_OAUTH_typed :
    ⊢ sem_typed [] (F_KE_lazy_alice ||ᵣ F_OAUTH) (F_KE_lazy_alice ||ᵣ F_OAUTH) ⊥
        (∀ᵣ θ, τ__fu θ chan gk ⊸ τ__fu θ oaleak leakI)%T [].
  Proof using All.
    iApply sem_typed_app_nil; last (iApply sem_typed_val; iApply F_OAUTH_val_typed).
    iApply sem_typed_app_nil; last (iApply sem_typed_val; iApply F_KE_lazy_alice_val_typed).
    iApply sem_typed_val. iApply right_comp_val_typed.
  Qed.


  (* [C_lazy], the DH-based key exchange, derived from the compatibility
     lemmas.  Like F_OAUTH it holds the one-shot continuation across the
     leak calls, so it is a [τ__FO] functionality. *)
  Section c_lazy.
    Import typed_hint_modes.
    #[local] Existing Instance multi_ty_group.

    Lemma C_lazy_val_typed :
      ⊢ ⊨ᵥ C_lazy ≤ C_lazy : ((𝟙 ⊸ ((𝔾 × 𝔾) × 𝔾)) ⊸ τ__FO chan gk)%T.
    Proof.
      iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
      iApply sem_typed_closure; first done.
      iApply (sem_typed_oval _ [_]). iApply sem_typed_RLam. iIntros (θ).
      iApplyT sem_oval_typed_afun.
      iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ₂).
      iApplyT sem_oval_typed_afun. simpl.
      iApplyT sem_typed_pair_elim; first typed_var.
      (* [let, ("ga", "gb", "gc") := "DH" #()]: bind the triple to "ga", copy
       out "gb" and "gc", then consume it for "ga". *)
      iApplyT sem_typed_let.
      { iApplyT sem_typed_app_fun_nil; [iApply row_le_nil|iApplyT sem_typed_unit'|typed_var]. }
      iApplyT sem_typed_let; first (iApplyT sem_typed_snd_gen; iApplyT sem_typed_fst_gen; typed_var_copy).
      iApplyT sem_typed_let; first (iApplyT sem_typed_snd_gen; typed_var_copy).
      iApplyT sem_typed_let; first (iApplyT sem_typed_fst_gen; iApplyT sem_typed_fst_gen; typed_var).
      simpl.
      iApplyT sem_typed_let.
      { iApplyT sem_typed_alloc_cpy. iApplyT sem_typed_injl. iApplyT sem_typed_unit'. }
      (* [store_if_none] captures copies of "lc" and "gc". *)
      iApplyT sem_typed_let.
      { iApplyT (sem_typed_sub_env _ ([("lc", _); ("gc", _)] ++ [("lc", _); ("ga", _); ("gc", _); ("gb", _); ("doSend", _); ("doRecv", _); ("f", _)])).
        { simpl. env_solve. }
        iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _]).
        iApplyT sem_oval_typed_ufun. simpl.
        iApplyT (sem_typed_match_split [] []).
        - iApplyT sem_typed_load_cpy. typed_var_copy.
        - iApply env_le_refl.
        - iApplyT sem_typed_store_cpy_gen.
          2: { iApplyT sem_typed_injr. typed_var_copy. }
          typed_var_copy.
        - iApply env_le_nil.
        - iApply env_le_refl.
        - iApplyT sem_typed_sub_env; first iApply env_le_weaken. iApplyT sem_typed_unit'.
        - iApply env_le_nil. }
      iApply sem_typed_effect_gen. iIntros (l1 l2). simpl.
      iApplyT sem_typed_let.
      { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
        iApplyT sem_oval_typed_ufun.
        iApply (sem_typed_do_const OS ⟨⟩%R (l1, l2) (𝟙 + 𝟙)%T (Option 𝔾)%T).
        iApply sem_typed_sub_nil. iApply sem_typed_var. }
      iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT (sem_typed_sub_env _ ([("doGK", _); ("f", _)]
                                      ++ [("store_if_none", _); ("doSend", _); ("doRecv", _); ("ga", _); ("gb", _); ("gc", _); ("lc", _)])).
      { simpl. env_solve. }
      iApplyT (sem_typed_deep_handler_OS (l1, l2) (λ _, 𝟙 + 𝟙)%T (λ _, Option 𝔾)%T).
      - (* The client call [f doGK], at [¡θ₁ ∪ θ ≤ θ₁ ∪ θ]. *)
        iApplyT sem_typed_app_fun_nil.
        2: typed_var.
        2: { iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst. }
        iApply row_le_trans; first iApplyT row_le_union'.
        + iApply row_le_mfbang_elim.
        + iApply row_le_refl.
        + row_le_submseteq.
      - iIntros (?). simpl.
        iApplyT (sem_typed_match_split [] []).
        + typed_var.
        + iApply env_le_refl.
        + (* Alice. *)
          iApplyT sem_typed_seq.
          { iApplyT sem_typed_app_fun_nil; [iApply row_le_nil|iApplyT sem_typed_unit'|].
            iApplyT sem_typed_sub_ty; [iApply ty_le_u2aarr|typed_var_copy]. }
          iApplyT sem_typed_seq.
          { iApplyT sem_typed_app_fun_nil; first row_le_submseteq.
            - iApplyT sem_typed_pair; [iApply (sem_typed_party true)|typed_var_copy].
            - typed_leak_fun. }
          iApplyT sem_typed_let.
          { iApplyT sem_typed_app_fun_nil; [row_le_submseteq|iApply (sem_typed_party true)|typed_leak_fun]. }
          iApplyT (sem_typed_match_split [] []).
          * typed_var.
          * iApply env_le_refl.
          * iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injl; iApplyT sem_typed_unit'|typed_cont].
          * iApply env_le_refl.
          * iApply env_le_refl.
          * iApplyT sem_typed_sub_env; first iApply env_le_weaken.
            iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injr; typed_var_copy|typed_cont].
          * iApply env_le_refl.
        + iApply env_le_refl.
        + iApply env_le_refl.
        + (* Bob. *)
          iApplyT sem_typed_let.
          { iApplyT sem_typed_app_fun_nil; [row_le_submseteq|iApply (sem_typed_party false)|typed_leak_fun]. }
          iApplyT (sem_typed_match_split [] []).
          * typed_var.
          * iApply env_le_refl.
          * iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injl; iApplyT sem_typed_unit'|typed_cont].
          * iApply env_le_refl.
          * iApply env_le_refl.
          * iApplyT sem_typed_sub_env; first iApply env_le_weaken.
            iApplyT sem_typed_seq.
            { iApplyT sem_typed_app_fun_nil; first row_le_submseteq.
              - iApplyT sem_typed_pair; [iApply (sem_typed_party false)|typed_var_copy].
              - typed_leak_fun. }
            iApplyT (sem_typed_match_split [] []).
            -- iApplyT sem_typed_load_cpy. typed_var_copy.
            -- iApply env_le_refl.
            -- iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injl; iApplyT sem_typed_unit'|typed_cont].
            -- iApply env_le_refl.
            -- iApply env_le_refl.
            -- iApplyT sem_typed_sub_env; first iApply env_le_weaken.
               iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injr; typed_var_copy|typed_cont].
            -- iApply env_le_refl.
          * iApply env_le_refl.
        + iApply env_le_refl.
      - typed_var.
        Unshelve. all: solve_typed_side.
    Qed.

  End c_lazy.

  Section real_chan.
    Import typed_hint_modes.

    Lemma REAL_CHAN_DH_RED_unfolded_typed :
      ⊢ sem_typed ((BNamed "DH", (𝟙 ⊸ (sem_ty_group × sem_ty_group) × sem_ty_group)) ::? []) (((F_AUTH ∘f (λ: "f", C_lazy "DH" "f")) ||ᵣ F_OAUTH) ∘f CHAN)%E (((F_AUTH ∘f (λ: "f", C_lazy "DH" "f")) ||ᵣ F_OAUTH) ∘f CHAN)%E  ⊥ τ [].
    Proof using All.
      (* [G ∘f CHAN] with [G := (F_AUTH ∘f C) ||ᵣ F_OAUTH]; arguments first. *)
      iApplyT sem_typed_app_nil; last first.
      { iApply (sem_typed_frame_env_gen _ [_]). iApply CHAN_typed. }
      iApplyT sem_typed_app_nil; last first.
      - iApplyT sem_typed_app_nil; last first.
        { iApply (sem_typed_frame_env_gen _ [_]). iApply sem_typed_val. iApply F_OAUTH_val_typed. }
        iApplyT sem_typed_app_nil; last first.
        + (* [F_AUTH ∘f C], with [C := λ: "f", C_lazy "DH" "f"]. *)
          iApplyT sem_typed_app_nil; last first.
          * iApply (sem_typed_oval _ [_]). iApply sem_typed_RLam. iIntros (θ).
            iApplyT sem_oval_typed_afun. simpl.
            iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|typed_var|].
            iApplyT sem_typed_sub_ty; last first.
            { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|typed_var|].
              iApply sem_typed_val. iApply C_lazy_val_typed. }
            iApply ty_le_row_forall_inst.
          * iApplyT sem_typed_app_nil; last (iApply sem_typed_val; iApply F_AUTH_val_typed).
            iApply sem_typed_val. iApply func_comp_val_typed.
        + iApply sem_typed_val. iApply right_comp_val_typed.
      - iApply sem_typed_val. iApply func_comp_val_typed.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma REAL_CHAN_DH_RED_sem_typed :
      ⊢ sem_typed [] REAL_CHAN_DH_RED REAL_CHAN_DH_RED ⊥ ((𝟙 ⊸ (sem_ty_group × sem_ty_group) × sem_ty_group) → τ)%T [].
    Proof using All.
      iApply (sem_typed_oval _ [] []). iApplyT sem_oval_typed_ufun.
      iApply REAL_CHAN_DH_RED_unfolded_typed.
      Unshelve. all: solve_typed_side.
    Qed.

  End real_chan.
  

  


End new_comp_verification.
