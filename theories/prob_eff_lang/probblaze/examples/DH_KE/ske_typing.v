From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import p_composition primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import dhke_common ske ske_sec_chan_def
  ske_sec_chan_common.

Import fingroup.
Import fingroup.fingroup.

Import valgroup_tactics.

(* Semantic typing of the programs of the SKE secure channel
   ([sc_real], [reduction], [enc_real_tape], [enc_ideal]). *)

Section ske_typing.
  Context `{probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.
  Context {msg : @fin_val Σ _ mt ms} {cipher : @fin_val Σ _ ct cs}.
  Context {SKE : @SYM Σ _ vg_fvt mt ct vg_fvts ms cs vg_fv msg cipher ske}.

  #[local] Notation Msg := (@sem_τFT Σ _ mt ms msg).
  #[local] Notation Cph := (@sem_τFT Σ _ ct cs cipher).

  Import valgroup_notation valgroup_tactics fingroup.

  (* Interface families (each parametrised by the effect row of its ops).*)
  (* [cchan]  : authenticated channel — cipher send, cipher recv.        *)
  (* [oaleak] : F_OAUTH's leak — cipher send, recv only leaks presence.   *)
  (* [leakI]  : direction-only send/recv (unit messages).                 *)
  (* [gk]     : the getKey operation.                                     *)
  (* [cli]    : the top-level secure-channel client interface.            *)
  Definition cchan (θ : sem_row Σ) : sem_ty Σ :=
    (((Cph × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option Cph))%T.
  Definition oaleak (θ : sem_row Σ) : sem_ty Σ :=
    (((Cph × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝟙))%T.
  Definition leakI (θ : sem_row Σ) : sem_ty Σ :=
    (((𝟙 + 𝟙) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝟙))%T.
  Definition gk (θ : sem_row Σ) : sem_ty Σ := ((𝟙 + 𝟙) -{ θ }-> Option 𝔾)%T.
  Definition cli (θ : sem_row Σ) : sem_ty Σ :=
    ((ℕ -{ θ }-> 𝟙) × (𝟙 -{ θ }-> Option Msg))%T.
  (* the handler consuming an interface I, polymorphic over I's row *)
  Definition hdl (I : sem_row Σ -> sem_ty Σ) (θ : sem_row Σ) : sem_ty Σ :=
    (∀ᵣ θ', I θ' -{ sem_row_union θ' θ }-∘ 𝟙)%T.

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

    #[local] Existing Instance multi_ty_fvt.

    Lemma oauth_send_handler_typed (θ₂ ρh : sem_row Σ) :
      ⊢ (¡ θ₂)%R ≤ᵣ ρh -∗
      sem_typed [("payload", (Cph × (𝟙 + 𝟙))%T); ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T);
                 ("message", Refᶜ (Option Cph)); ("doLeakSend", ((Cph × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙)%T)]
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
        ρh 𝟙 [("message", Refᶜ (Option Cph)); ("doLeakSend", ((Cph × (𝟙 + 𝟙)) -{ θ₂ }-> 𝟙)%T)].
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
        { iApplyT sem_typed_app_fun_nil; first iApply "Hρ".
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
      sem_typed [("from", (𝟙 + 𝟙)%T); ("k", (Option Cph -{ ρh }-[OS]-> 𝟙)%T);
                 ("message", Refᶜ (Option Cph)); ("doLeakRecv", ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙)%T)]
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
        ρh 𝟙 [("message", Refᶜ (Option Cph)); ("doLeakRecv", ((𝟙 + 𝟙) -{ θ₂ }-> Option 𝟙)%T)].
    Proof.
      iIntros "#Hρ".
      iApplyT sem_typed_let.
      { iApplyT sem_typed_app_fun_nil; [iApply "Hρ"|typed_var|].
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
      ⊢ sem_val_typed F_OAUTH F_OAUTH (τ__FO oaleak cchan).
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
        iApply (sem_typed_do_const OS _ (ls1, ls2) (Cph × (𝟙 + 𝟙))%T 𝟙%T).
        iApply sem_typed_sub_nil. iApply sem_typed_var. }
      iApplyT sem_typed_let.
      { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
        iApplyT sem_oval_typed_ufun.
        iApplyT sem_typed_sub_row; first iApply row_le_cons_extend.
        iApply (sem_typed_do_const OS ⟨⟩%R (lr1, lr2) (𝟙 + 𝟙)%T (Option Cph)%T).
        iApply sem_typed_sub_nil. iApply sem_typed_var. }
      (* Each handler keeps its own copy of [message] (plus its leak function)
       in its persistent context; [f] and the two closures are consumed by
       the inner handled expression. *)
      iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT (sem_typed_sub_env _ ([("doRecv", _); ("doSend", _); ("f", _); ("message", _); ("doLeakSend", _)]
                                      ++ [("message", _); ("doLeakRecv", _)])).
      { simpl. env_solve. }
      (* Outer handler: recv. *)
      iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option Cph)%T).
      - (* Inner handler: send.  Its result row needs [send]'s bottom
         signature at the head. *)
        iApplyT sem_typed_sub_row; first iApply row_le_swap_second.
        iApplyT (sem_typed_sub_env _ ([_; _; _] ++ [_; _])); first iApply env_le_refl.
        iApplyT (sem_typed_deep_handler_OS (ls1, ls2) (λ _, Cph × (𝟙 + 𝟙))%T (λ _, 𝟙)%T).
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

    Corollary F_OAUTH_typed : ⊢ sem_typed [] F_OAUTH F_OAUTH ⊥ (τ__FO oaleak cchan) [].
    Proof using All.
      iApply sem_typed_val.
      iApply F_OAUTH_val_typed.
    Qed.

  End f_oauth.

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

    Lemma sem_typed_party (b : bool) Γ ρ :
      ⊢ sem_typed Γ (if b then bob else alice) (if b then bob else alice) ρ (𝟙 + 𝟙)%T Γ.
    Proof.
      iApply sem_typed_sub_nil. iApply sem_typed_val. iIntros "!>".
      destruct b; iExists _, _; [iLeft|iRight]; done.
    Qed.

    Lemma sem_typed_vexp (b : vgG) Γ1 Γ2 e e' ρ :
      ⊢ sem_typed Γ1 e e' ρ ℕ Γ2 -∗
      sem_typed Γ1 (vexp (vgval b) e) (vexp (vgval b) e') ρ 𝔾 Γ2.
    Proof using G vgg.
      iIntros "#He !# %γ HΓ1 /=".
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ1]"); first by iApply "He".
      iIntros "!# % % (Hn & HΓ2) /=". iDestruct "Hn" as (n) "(-> & ->)".
      iApply (brel_exp_l []). iApply (brel_exp_r []).
      iApply brel_value. iIntros "$ !>". iFrame. by iExists _.
    Qed.


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


  End f_ke.

  (* [CHAN], derived from the compatibility lemmas.  As for F_OAUTH, its
     one-shot handlers call [doGK]/[doSend]/[doRecv] while holding the
     continuation, so the interface rows are flipped ([τ__f_once]). *)
  Section chan.
    Import typed_hint_modes.
    #[local] Existing Instance multi_ty_group.
    #[local] Existing Instance multi_ty_fvt.

    Lemma sem_typed_fvt_of_int Γ1 Γ2 e e' ρ :
      ⊢ sem_typed Γ1 e e' ρ ℕ Γ2 -∗
      sem_typed Γ1 (ms.(fvt_of_int) e) (ms.(fvt_of_int) e') ρ (Option Msg) Γ2.
    Proof.
      iIntros "#He !# %γ HΓ1 /=".
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ1]"); first by iApply "He".
      iIntros "!# % % (Hn & HΓ2) /=".
      iDestruct "Hn" as (n) "(-> & ->)".
      destruct (fvt_of_int_sem (fin_val := msg) n) as [x|] eqn:Hx.
      - iApply (brel_fvt_of_int_correct_l (fin_val := msg) _ []); first done.
        iApply (brel_fvt_of_int_correct_r (fin_val := msg) _ []); first done.
        iApply brel_value. iIntros "$ !>". iFrame. iExists _, _. iRight. iSplit; [done|]. iSplit; [done|]. by iExists x.
      - iApply (brel_fvt_of_int_none_l (fin_val := msg) _ []); first done.
        iApply (brel_fvt_of_int_none_r (fin_val := msg) _ []); first done.
        iApply brel_value. iIntros "$ !>". iFrame. iExists _, _. iLeft. done.
    Qed.

    Lemma sem_typed_enc Γ1 Γ2 Γ3 e1 e1' e2 e2' ρ :
      ⊢ sem_typed Γ1 e2 e2' ρ Msg Γ2 -∗ sem_typed Γ2 e1 e1' ρ 𝔾 Γ3 -∗
      sem_typed Γ1 (ske.(enc) e1 e2) (ske.(enc) e1' e2') ρ Cph Γ3.
    Proof using All.
      iIntros "#He2 #He1 !# %γ HΓ1 /=".
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ1]"); first by iApply "He2".
      iIntros "!# % % (Hm & HΓ2) /=". iDestruct "Hm" as (m) "(-> & ->)".
      iApply (brel_bind [AppLCtx _; AppRCtx _] [AppLCtx _; AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ2]"); first by iApply "He1".
      iIntros "!# % % (Hk & HΓ3) /=". iDestruct "Hk" as (k) "(-> & ->)".
      iApply (brel_bind [] [] ⊤ []); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
      assert (to_iThyIfMono OS [] = []) as <- by done.
      iApply brel_mono; first iApply to_iThy_le_refl.
      { iApply (brel_enc_couple (key := vg_fv) (msg := msg) k m). }
      simpl. iIntros "% % (%c & -> & -> & _) /=".
      iApply brel_value. iIntros "$ !>". iFrame. by iExists c.
    Qed.

    Lemma sem_typed_dec Γ1 Γ2 Γ3 e1 e1' e2 e2' ρ :
      ⊢ sem_typed Γ1 e2 e2' ρ Cph Γ2 -∗ sem_typed Γ2 e1 e1' ρ 𝔾 Γ3 -∗
      sem_typed Γ1 (ske.(dec) e1 e2) (ske.(dec) e1' e2') ρ (Option Msg) Γ3.
    Proof using All.
      iIntros "#He2 #He1".
      iApplyT (sem_typed_app_gen Cph ρ ρ ⊥); [iApply row_le_refl|iApply row_le_nil| |iApply "He2"].
      iApplyT (sem_typed_app_gen 𝔾 ⟨⟩%R ρ ⊥); [iApply row_le_nil|iApply row_le_nil| |iApply "He1"].
      iApply sem_typed_sub_nil. iApply sem_typed_val.
      iApply sem_val_typed_sub; last iApply (dec_typed (SYM := SKE)).
      iApply ty_le_trans; first iApply ty_le_mbang_elim.
      iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply ty_le_mbang_elim].
      Unshelve. all: try solve_typed_side.
    Qed.

    Lemma chan_send_handler_typed (θ1 θ2 ρh : sem_row Σ) :
      ⊢ (¡ θ1)%R ≤ᵣ ρh -∗ (¡ θ2)%R ≤ᵣ ρh -∗
      sem_typed [("m", ℕ); ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T);
                 ("message", Refᶜ (Option Msg)); ("doGK", gk θ2); ("doSend", ((Cph × (𝟙 + 𝟙)) -{ θ1 }-> 𝟙)%T)]
        (match: ms.(fvt_of_int) "m" with
         | NONE => "k" #()%V
         | SOME "m" =>
             match: !"message" with
             | NONE => "message" <- SOME "m";;
                       let: "key" := "doGK" (bob) in
                       match: "key" with
                       | NONE => "k" #()%V
                       | SOME "key" =>
                           let: "mg" := ske.(enc) "key" "m" in ("doSend" ("mg", bob));; "k" #()%V
                       end
             | SOME "m" => "k" #()%V
             end
         end)%E
        (match: ms.(fvt_of_int) "m" with
         | NONE => "k" #()%V
         | SOME "m" =>
             match: !"message" with
             | NONE => "message" <- SOME "m";;
                       let: "key" := "doGK" (bob) in
                       match: "key" with
                       | NONE => "k" #()%V
                       | SOME "key" =>
                           let: "mg" := ske.(enc) "key" "m" in ("doSend" ("mg", bob));; "k" #()%V
                       end
             | SOME "m" => "k" #()%V
             end
         end)%E
        ρh 𝟙 [("message", Refᶜ (Option Msg)); ("doGK", gk θ2); ("doSend", ((Cph × (𝟙 + 𝟙)) -{ θ1 }-> 𝟙)%T)].
    Proof using All.
      iIntros "#Hρ1 #Hρ2".
      iApplyT (sem_typed_match_split [] []).
      - iApplyT sem_typed_fvt_of_int. typed_var.
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
            { iApplyT sem_typed_enc; typed_var. }
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
      sem_typed [("payload", (𝟙 + 𝟙)%T); ("k", (Option Msg -{ ρh }-[OS]-> 𝟙)%T);
                 ("doGK", gk θ2); ("doRecv", ((𝟙 + 𝟙) -{ θ1 }-> Option Cph)%T)]
        (let: "key" := "doGK" (alice) in
         match: "key" with
         | NONE => "k" NONEV
         | SOME "key" =>
             let: "r" := ("doRecv" bob) in
             match: "r" with
             | NONE => "k" NONEV
             | SOME "m" => "k" (ske.(dec) "key" "m")
             end
         end)%E
        (let: "key" := "doGK" (alice) in
         match: "key" with
         | NONE => "k" NONEV
         | SOME "key" =>
             let: "r" := ("doRecv" bob) in
             match: "r" with
             | NONE => "k" NONEV
             | SOME "m" => "k" (ske.(dec) "key" "m")
             end
         end)%E
        ρh 𝟙 [("doGK", gk θ2); ("doRecv", ((𝟙 + 𝟙) -{ θ1 }-> Option Cph)%T)].
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
          * iApplyT sem_typed_dec; typed_var.
          * typed_cont.
        + iApply env_le_refl.
      - iApply env_le_refl.
        Unshelve. all: solve_typed_side.
    Qed.


    (* The body of [CHAN] (free in "f","effs"), copied verbatim from
     [sec_channel_def.CHAN], so that [CHAN] is [λ: "f" "effs", CHAN_body]. *)
    Definition CHAN_body : expr :=
      (let, ("chanOp", "doGK") := "effs" in
       let, ("doSend", "doRecv") := "chanOp" in
       let: "message" := ref NONEV in
       effect "ssend"
         effect "srecv"
         let: "doSecSend" := (λ: "m", do: "ssend" "m") in
         let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
         handle: handle: "f" ("doSecSend", "doSecRecv") with
      (*SendSecure*)
      | effect "ssend" "m", rec "k" =>
          match: ms.(fvt_of_int) "m" with
          | NONE => "k" #()%V
          | SOME "m" =>
              match: !"message" with
              | NONE => "message" <- SOME "m";;
                        let: "key" := "doGK" (bob) in
                        match: "key" with
                        | NONE => "k" #()%V
                        | SOME "key" =>
                            let: "mg" := ske.(enc) "key" "m" in ("doSend" ("mg", bob));; "k" #()%V
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
                  "k" (ske.(dec) "key" "m")
              end
          end
      | return "y" => "y"
       end)%E.

    Lemma CHAN_body_typed (θ θ1 θ2 : sem_row Σ) :
      ⊢ sem_typed [("f", hdl cli θ); ("effs", (cchan θ1 × gk θ2)%T)] CHAN_body CHAN_body
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
        iApply (sem_typed_do_const OS ⟨⟩%R (lr1, lr2) (𝟙 + 𝟙)%T (Option Msg)%T).
        iApply (sem_typed_party true). }
      (* The send handler keeps [message], [doGK] and [doSend]; the receive
       handler keeps [doGK] and [doRecv]. *)
      iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT (sem_typed_sub_env _ ([("doSecRecv", _); ("doSecSend", _); ("f", _);
                                     ("message", _); ("doGK", _); ("doSend", _)]
                                      ++ [("doGK", _); ("doRecv", _)])).
      { simpl. env_solve. }
      (* Outer handler: srecv. *)
      iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option Msg)%T).
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
      ⊢ sem_typed [] CHAN CHAN ⊥ (∀ᵣ θ, hdl cli θ ⊸ τ__fu θ cchan gk)%T [].
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
        (∀ᵣ θ, τ__fu θ cchan gk ⊸ τ__fu θ oaleak leakI)%T [].
  Proof using All.
    iApply sem_typed_app_nil; last (iApply sem_typed_val; iApply F_OAUTH_val_typed).
    iApply sem_typed_app_nil; last (iApply sem_typed_val; iApply F_KE_lazy_alice_val_typed).
    iApply sem_typed_val. iApply right_comp_val_typed.
  Qed.

  Section reduction.
    Import typed_hint_modes.
    #[local] Existing Instance multi_ty_group.
    #[local] Existing Instance multi_ty_fvt.

    Lemma red_send_handler_typed (θ1 θ2 ρh : sem_row Σ) :
      ⊢ (¡ θ1)%R ≤ᵣ ρh -∗ (¡ θ2)%R ≤ᵣ ρh -∗
      sem_typed [("m", ℕ); ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T);
                 ("message", Refᶜ (Option Msg)); ("doGK", gk θ2); ("doSend", ((Cph × (𝟙 + 𝟙)) -{ θ1 }-> 𝟙)%T);
                 ("enc", (Msg -{ ⊥ }-> Cph)%T)]
        (match: ms.(fvt_of_int) "m" with
         | NONE => "k" #()%V
         | SOME "m" =>
             match: !"message" with
             | NONE => "message" <- SOME "m";;
                       let: "key" := "doGK" (bob) in
                       match: "key" with
                       | NONE => "k" #()%V
                       | SOME "key" =>
                           let: "mg" := "enc" "m" in ("doSend" ("mg", bob));; "k" #()%V
                       end
             | SOME "m" => "k" #()%V
             end
         end)%E
        (match: ms.(fvt_of_int) "m" with
         | NONE => "k" #()%V
         | SOME "m" =>
             match: !"message" with
             | NONE => "message" <- SOME "m";;
                       let: "key" := "doGK" (bob) in
                       match: "key" with
                       | NONE => "k" #()%V
                       | SOME "key" =>
                           let: "mg" := "enc" "m" in ("doSend" ("mg", bob));; "k" #()%V
                       end
             | SOME "m" => "k" #()%V
             end
         end)%E
        ρh 𝟙 [("message", Refᶜ (Option Msg)); ("doGK", gk θ2); ("doSend", ((Cph × (𝟙 + 𝟙)) -{ θ1 }-> 𝟙)%T);
              ("enc", (Msg -{ ⊥ }-> Cph)%T)].
    Proof using All.
      iIntros "#Hρ1 #Hρ2".
      iApplyT (sem_typed_match_split [] []).
      - iApplyT sem_typed_fvt_of_int. typed_var.
      - iApply env_le_refl.
      - iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|].
        typed_cont.
      - iApply env_le_refl.
      - iApply env_le_refl.
      - iApplyT (sem_typed_match_split [] [("m", _)]).
        + iApplyT sem_typed_load_cpy. typed_var_copy.
        + iApply env_le_refl.
        + iApplyT sem_typed_seq.
          { iApplyT sem_typed_store_cpy_gen.
            2: { iApplyT sem_typed_injr. typed_var_copy. }
            typed_var_copy. }
          iApplyT sem_typed_let.
          { iApplyT sem_typed_app_fun_nil; [iApply "Hρ2"|iApply (sem_typed_party true)|].
            typed_leak_fun. }
          iApplyT (sem_typed_match_split [] []).
          * typed_var.
          * iApply env_le_refl.
          * iApplyT sem_typed_sub_env; first iApply env_le_weaken.
            iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|].
            typed_cont.
          * iApply env_le_refl.
          * iApply env_le_refl.
          * iApplyT sem_typed_sub_env; first iApply env_le_weaken.
            iApplyT sem_typed_let.
            { iApplyT sem_typed_app_fun_nil;
                [iApply row_le_nil|typed_var|iApplyT sem_typed_sub_ty; [iApply ty_le_mbang_elim|typed_var_copy]]. }
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

    Lemma red_recv_handler_typed (θ1 θ2 ρh : sem_row Σ) :
      ⊢ (¡ θ1)%R ≤ᵣ ρh -∗ (¡ θ2)%R ≤ᵣ ρh -∗
      sem_typed [("payload", (𝟙 + 𝟙)%T); ("k", (Option Msg -{ ρh }-[OS]-> 𝟙)%T);
                 ("doGK", gk θ2); ("doRecv", ((𝟙 + 𝟙) -{ θ1 }-> Option Cph)%T); ("message", Refᶜ (Option Msg))]
        (let: "key" := "doGK" (alice) in
         match: "key" with
         | NONE => "k" NONE
         | SOME "key" =>
             let: "r" := ("doRecv" bob) in
             match: "r" with
             | NONE => "k" NONE
             | SOME "m" => "k" (!"message")
             end
         end)%E
        (let: "key" := "doGK" (alice) in
         match: "key" with
         | NONE => "k" NONE
         | SOME "key" =>
             let: "r" := ("doRecv" bob) in
             match: "r" with
             | NONE => "k" NONE
             | SOME "m" => "k" (!"message")
             end
         end)%E
        ρh 𝟙 [("doGK", gk θ2); ("doRecv", ((𝟙 + 𝟙) -{ θ1 }-> Option Cph)%T); ("message", Refᶜ (Option Msg))].
    Proof using All.
      iIntros "#Hρ1 #Hρ2".
      iApplyT sem_typed_sub_env; first iApply env_le_weaken.
      iApplyT sem_typed_let.
      { iApplyT sem_typed_app_fun_nil; [iApply "Hρ2"|iApply (sem_typed_party false)|].
        typed_leak_fun. }
      iApplyT (sem_typed_match_split [] []).
      - typed_var.
      - iApply env_le_refl.
      - iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injl; iApplyT sem_typed_unit'|].
        typed_cont.
      - iApply env_le_refl.
      - iApply env_le_refl.
      - iApplyT sem_typed_sub_env; first iApply env_le_weaken.
        iApplyT sem_typed_let.
        { iApplyT sem_typed_app_fun_nil; [iApply "Hρ1"|iApply (sem_typed_party true)|].
          typed_leak_fun. }
        iApplyT (sem_typed_match_split [] []).
        + typed_var.
        + iApply env_le_refl.
        + iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injl; iApplyT sem_typed_unit'|].
          typed_cont.
        + iApply env_le_refl.
        + iApply env_le_refl.
        + iApplyT sem_typed_sub_env; first iApply env_le_weaken.
          iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
          * iApplyT sem_typed_load_cpy. typed_var_copy.
          * typed_cont.
        + iApply env_le_refl.
      - iApply env_le_refl.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma RED_CHAN_val_typed :
      ⊢ ⊨ᵥ (@RED_CHAN mt ms) ≤ (@RED_CHAN mt ms) : ((𝟙 ⊸ (Msg -{ ⊥ }-> Cph)) ⊸ ∀ᵣ θ, hdl cli θ ⊸ τ__fu θ cchan gk)%T.
    Proof using All.
      iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
      iApply sem_typed_closure; first done.
      iApply (sem_typed_oval _ [_]). iApply sem_typed_RLam. iIntros (θ).
      iApplyT sem_oval_typed_afun.
      iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ1).
      iApply sem_typed_RLam. iIntros (θ2).
      iApplyT sem_oval_typed_afun. simpl.
      iApplyT sem_typed_let.
      { iApplyT sem_typed_app_fun_nil; [iApply row_le_nil|iApplyT sem_typed_unit'|typed_var]. }
      iApplyT sem_typed_pair_elim; first typed_var.
      iApplyT sem_typed_pair_elim; first typed_var.
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApply (sem_typed_none Msg)).
      iApply sem_typed_effect_gen. iIntros (ls1 ls2).
      iApply sem_typed_effect_gen. iIntros (lr1 lr2). simpl.
      iApplyT sem_typed_let.
      { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
        iApplyT sem_oval_typed_ufun.
        iApply (sem_typed_do_const OS _ (ls1, ls2) ℕ 𝟙%T).
        iApply sem_typed_sub_nil. iApply sem_typed_var. }
      iApplyT sem_typed_let.
      { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
        iApplyT sem_oval_typed_ufun.
        iApplyT sem_typed_sub_row; first iApply row_le_cons_extend.
        iApply (sem_typed_do_const OS ⟨⟩%R (lr1, lr2) (𝟙 + 𝟙)%T (Option Msg)%T).
        iApply (sem_typed_party true). }
      iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT (sem_typed_sub_env _ ([("doSecRecv", _); ("doSecSend", _); ("f", _);
                                     ("message", _); ("doGK", _); ("doSend", _); ("enc", _)]
                                      ++ [("doGK", _); ("doRecv", _); ("message", _)])).
      { simpl. env_solve. }
      iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option Msg)%T).
      - iApplyT sem_typed_sub_row; first iApply row_le_swap_second.
        iApplyT (sem_typed_sub_env _ ([_; _; _] ++ [_; _; _; _])); first iApply env_le_refl.
        iApplyT (sem_typed_deep_handler_OS (ls1, ls2) (λ _, ℕ) (λ _, 𝟙)%T).
        + iApplyT sem_typed_app_fun_nil.
          2: { iApplyT sem_typed_pair; typed_var. }
          2: { iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst. }
          row_le_submseteq.
        + iIntros (?). iApply red_send_handler_typed;
            row_le_submseteq.
        + typed_var.
      - iIntros (?). iApply red_recv_handler_typed;
          row_le_submseteq.
      - iApplyT sem_typed_sub_env_final; last typed_var. env_solve.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma reduction_val_typed :
      ⊢ ⊨ᵥ (@reduction vg cg vgg mt ms) ≤ (@reduction vg cg vgg mt ms) :
        ((𝟙 ⊸ (Msg -{ ⊥ }-> Cph)) → ∀ᵣ θ, hdl cli θ ⊸ τ__fu θ oaleak leakI)%T.
    Proof using All.
      iApply sem_typed_closure; first done. simpl.
      iApplyT sem_typed_app_nil; last first.
      { iApplyT sem_typed_app_nil; last typed_var.
        iApply sem_typed_val. iApply RED_CHAN_val_typed. }
      iApplyT sem_typed_app_nil; last iApply F_KE_F_OAUTH_typed.
      iApply sem_typed_val. iApply func_comp_val_typed.
      Unshelve. all: solve_typed_side.
    Qed.

    Lemma sem_typed_rand_cipher Γ ρ :
      ⊢ sem_typed Γ (ske.(rand_cipher) #()%V) (ske.(rand_cipher) #()%V) ρ Cph Γ.
    Proof using All.
      iIntros "!# %γ HΓ /=".
      iApply (@rand_cipher_coupl Σ _ vg_fvt mt ct vg_fvts ms cs vg_fv msg cipher ske SKE ⊤ [] []).
      iIntros (c). iApply brel_value. iIntros "$ !>". iFrame. by iExists c.
    Qed.

    Lemma enc_ideal_val_typed :
      ⊢ ⊨ᵥ enc_ideal ske ≤ enc_ideal ske : (𝟙 ⊸ (Msg -{ ⊥ }-> Cph))%T.
    Proof using All.
      iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
      iApply sem_typed_closure; first done. simpl.
      iApply (sem_typed_oval _ []). iApplyT sem_oval_typed_ufun. simpl.
      iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApply sem_typed_rand_cipher.
      Unshelve. all: solve_typed_side.
    Qed.

    Lemma sem_typed_key_of_int Γ1 Γ2 e e' ρ :
      ⊢ sem_typed Γ1 e e' ρ ℕ Γ2 -∗
      sem_typed Γ1 (vg_fvts.(fvt_of_int) e) (vg_fvts.(fvt_of_int) e') ρ (Option 𝔾) Γ2.
    Proof using All.
      iIntros "#He !# %γ HΓ1 /=".
      iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
      iApply (brel_wand with "[HΓ1]"); first by iApply "He".
      iIntros "!# % % (Hn & HΓ2) /=".
      iDestruct "Hn" as (n) "(-> & ->)".
      destruct (fvt_of_int_sem (fin_val := vg_fv) n) as [x|] eqn:Hx.
      - iApply (brel_fvt_of_int_correct_l (fin_val := vg_fv) _ []); first done.
        iApply (brel_fvt_of_int_correct_r (fin_val := vg_fv) _ []); first done.
        iApply brel_value. iIntros "$ !>". iFrame. iExists _, _. iRight. iSplit; [done|]. iSplit; [done|]. by iExists x.
      - iApply (brel_fvt_of_int_none_l (fin_val := vg_fv) _ []); first done.
        iApply (brel_fvt_of_int_none_r (fin_val := vg_fv) _ []); first done.
        iApply brel_value. iIntros "$ !>". iFrame. iExists _, _. iLeft. done.
    Qed.

    Lemma enc_real_tape_val_typed :
      ⊢ ⊨ᵥ enc_real_tape ske ≤ enc_real_tape ske : (𝟙 ⊸ (Msg -{ ⊥ }-> Cph))%T.
    Proof using All.
      iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
      iApply sem_typed_closure; first done. simpl.
      iApplyT sem_typed_let; first (iApplyT sem_typed_alloctape; iApplyT sem_typed_int').
      iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_ufun. simpl.
      iApplyT sem_typed_let.
      { iApplyT sem_typed_rand; [typed_var_copy|iApplyT sem_typed_int']. }
      iApplyT (sem_typed_match_split [] []).
      - iApplyT sem_typed_key_of_int. typed_var.
      - iApply env_le_refl.
      - iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
        iApply sem_typed_val. by iExists _.
      - iApply env_le_refl.
      - iApply env_le_refl.
      - iApplyT sem_typed_enc; typed_var.
      - iApply env_le_nil.
        Unshelve. all: try solve_typed_side.
    Qed.

  End reduction.

  Lemma sem_typed_adv_red (A red : val) (α β : sem_ty Σ) :
    ⊢ ⊨ᵥ A ≤ A : (β → 𝔹) -∗ ⊨ᵥ red ≤ red : (α → β) -∗
      sem_typed [] (λ: "enc", A (red "enc"))%E (λ: "enc", A (red "enc"))%E ⊥ (α → 𝔹)%T [].
  Proof.
    iIntros "#HA #Hr".
    iApply (sem_typed_oval _ []). iApplyT sem_oval_typed_ufun. simpl.
    iApplyT sem_typed_app_nil; last first.
    { iApplyT sem_typed_app_nil; last typed_var. iApply sem_typed_val.
      iApply sem_val_typed_sub; [iApply ty_le_mbang_elim|iApply "Hr"]. }
    iApply sem_typed_val. iApply sem_val_typed_sub; [iApply ty_le_mbang_elim|iApply "HA"].
    Unshelve. all: solve_typed_side.
  Qed.

  Lemma sem_typed_adv_red_expr (s : string) (A : val) (red : expr) (α β : sem_ty Σ) :
    ⊢ ⊨ᵥ A ≤ A : (β → 𝔹) -∗ sem_typed [] red red ⊥ (α → β)%T [] -∗
      sem_typed [] (λ: s, A (red s))%E (λ: s, A (red s))%E ⊥ (α → 𝔹)%T [].
  Proof.
    iIntros "#HA #Hr".
    iApply (sem_typed_oval _ []). iApplyT sem_oval_typed_ufun. simpl.
    iApplyT sem_typed_app_nil; last first.
    { iApplyT sem_typed_app_nil; last typed_var.
      iApply sem_typed_sub_ty; [iApply ty_le_mbang_elim|iApply "Hr"]. }
    iApply sem_typed_val. iApply sem_val_typed_sub; [iApply ty_le_mbang_elim|iApply "HA"].
    Unshelve. all: solve_typed_side.
  Qed.

End ske_typing.
