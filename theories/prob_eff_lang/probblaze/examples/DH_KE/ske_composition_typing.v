From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import p_composition primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Import dhke_common ske ske_sec_chan_common
  ske_composition_defs.
From clutch.prob_eff_lang.probblaze.examples.DH_KE Require Export ske_typing.

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

Section ske_comp_verification.
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
  #[local] Notation τ := (@ske_composition_defs.τ Σ _ vg mt ct ms cs msg cipher).

  Import valgroup_notation valgroup_tactics fingroup.

  (* [chan] : authenticated channel — group send, group recv. *)
  Definition chan (θ : sem_row Σ) : sem_ty Σ :=
    (((𝔾 × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝔾))%T.
  Definition aleak (θ : sem_row Σ) : sem_ty Σ :=
    (((𝔾 × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option ℕ))%T.

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


  End f_auth.

  (* [DH_SIM], derived from the compatibility lemmas.  The two exponents are
     drawn lazily from tapes ([sem_ty_tape]: the identity coupling makes both
     sides draw the same value) and cached in [Refᶜ (Option ℕ)]. *)
  Section dh_sim.
    Import typed_hint_modes.
    #[local] Existing Instance multi_ty_group.

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


  End dh_sim.

  (* [F_AUTH ∘f DH_SIM]. *)
  Lemma F_AUTH_DH_SIM_FO_typed :
    ⊢ sem_typed [] (F_AUTH ∘f DH_SIM) (F_AUTH ∘f DH_SIM) ⊥ (τ__FO aleak leakI) [].
  Proof using All.
    iApply func_comp_OS_typed; iApply sem_typed_val; [iApply F_AUTH_val_typed|iApply DH_SIM_val_typed].
  Qed.

  Section reduction.
    Import typed_hint_modes.
    #[local] Existing Instance multi_ty_group.
    #[local] Existing Instance multi_ty_fvt.

    Lemma functionality_comp_val_typed (τ1' τ1 τF τ2 : sem_row Σ → sem_ty Σ) :
      ⊢ ⊨ᵥ functionality_composition ≤ functionality_composition :
        (τ__FO τ2 τF ⊸ (∀ᵣ θ, τ1' θ ⊸ τ__fu θ τ1 τF) ⊸ ∀ᵣ θ, τ1' θ ⊸ τ__fu θ τ1 τ2)%T.
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
           iApply sem_typed_RLam. iIntros (θF). iApplyT sem_oval_typed_afun. simpl.
           iApplyT sem_typed_app_fun_nil.
           2: { iApply sem_typed_sub_nil. iApplyT sem_typed_pair; typed_var. }
           2: { iApplyT sem_typed_sub_ty; last first.
                { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|typed_var|].
                  iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst. }
                rewrite /τ__fu. iApply ty_le_trans; first iApply (ty_le_row_forall_inst _ θ1).
                iApply (ty_le_row_forall_inst _ θF). }
           row_le_submseteq. }
      row_le_submseteq.
      Unshelve. all: solve_typed_side.
    Qed.

    Lemma DHSIM_FKE_RED_unfolded_typed :
      ⊢ sem_typed ((BNamed "enc", (𝟙 ⊸ (Msg -{ ⊥ }-> Cph))%T) ::? [])
          ((F_AUTH ∘f DH_SIM) ∘F (@reduction vg cg vgg mt ms "enc"))%E
          ((F_AUTH ∘f DH_SIM) ∘F (@reduction vg cg vgg mt ms "enc"))%E ⊥ τ [].
    Proof using All.
      iApplyT sem_typed_app_nil; last first.
      { iApplyT sem_typed_app_nil; last typed_var.
        iApply sem_typed_val. iApply sem_val_typed_sub; first iApply ty_le_mbang_elim.
        iApply (reduction_val_typed (SKE := SKE)). }
      iApplyT sem_typed_app_nil; last iApply F_AUTH_DH_SIM_FO_typed.
      iApply sem_typed_val. iApply functionality_comp_val_typed.
      Unshelve. all: solve_typed_side.
    Qed.

  End reduction.

End ske_comp_verification.
