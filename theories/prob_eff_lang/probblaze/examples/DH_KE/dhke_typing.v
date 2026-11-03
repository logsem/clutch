From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import p_composition primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_common.

Import fingroup.
Import fingroup.fingroup.

Import valgroup_tactics.

Section dhke_typing.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  Import valgroup_notation.

  Definition chan (θ : sem_row Σ) : sem_ty Σ :=
    (((𝔾 × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝔾))%T.
  Definition aleak (θ : sem_row Σ) : sem_ty Σ :=
    (((𝔾 × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option ℕ))%T.
  Definition gk (θ : sem_row Σ) : sem_ty Σ := ((𝟙 + 𝟙) -{ θ }-> Option 𝔾)%T.

  Import typed_hint_modes.

  #[local] Instance multi_ty_group : MultiT (𝔾 : sem_ty Σ).
  Proof.
    constructor. iIntros "!#" (v1 v2) "(%g & -> & ->)".
    rewrite /sem_ty_mbang /=. iModIntro. by iExists g.
  Qed.

  Lemma sem_typed_party (b : bool) Γ ρ :
    ⊢ sem_typed Γ (if b then bob else alice) (if b then bob else alice) ρ (𝟙 + 𝟙)%T Γ.
  Proof.
    iApply sem_typed_sub_nil. iApply sem_typed_val. iIntros "!>".
    destruct b; iExists _, _; [iLeft|iRight]; done.
  Qed.

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

  Lemma F_AUTH_typed : ⊢ sem_typed [] F_AUTH F_AUTH ⊥ (τ__FO aleak chan) [].
  Proof using Type*.
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _; _]). iApply sem_typed_RLam. iIntros (θ₂).
    iApplyT sem_oval_typed_afun.
    iApplyT sem_typed_pair_elim; first typed_var.
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

  Lemma C_lazy_val_typed :
    ⊢ sem_val_typed C_lazy C_lazy ((𝟙 ⊸ (𝔾 × 𝔾 × 𝔾)) → τ__FO chan gk)%T.
  Proof using Type*.
    iApply sem_typed_closure; first done. simpl.
    iApplyT sem_typed_let.
    { iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|typed_var]. }
    iApplyT sem_typed_let; first (iApplyT sem_typed_snd_gen; iApplyT sem_typed_fst_gen; typed_var_copy).
    iApplyT sem_typed_let; first (iApplyT sem_typed_snd_gen; typed_var_copy).
    iApplyT sem_typed_let; first (iApplyT sem_typed_fst_gen; iApplyT sem_typed_fst_gen; typed_var).
    simpl. iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_injl; iApplyT sem_typed_unit').
    iApplyT sem_typed_let.
    { iApplyT (sem_typed_sub_env _ ([("lc", _); ("gc", _)] ++ [("lc", _); ("ga", _); ("gc", _); ("gb", _)])).
      { simpl. env_solve. }
      iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _]).
      iApplyT sem_oval_typed_ufun. simpl.
      iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT (sem_typed_match_split [] []).
      - iApplyT sem_typed_load_cpy. typed_var_copy.
      - iApply env_le_refl.
      - iApplyT sem_typed_store_cpy_gen.
        2: { iApplyT sem_typed_injr. typed_var_copy. }
        typed_var_copy.
      - iApply env_le_refl.
      - iApply env_le_refl.
      - iApplyT sem_typed_sub_env; first iApply env_le_weaken.
        iApplyT sem_typed_unit'.
      - iApply env_le_refl. }
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _; _; _; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _; _; _; _; _]). iApply sem_typed_RLam. iIntros (θ₂).
    iApplyT sem_oval_typed_afun. simpl.
    iApplyT sem_typed_pair_elim; first typed_var.
    iApply sem_typed_effect_gen. iIntros (l1 l2). simpl.
    iApplyT sem_typed_let.
    { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
      iApplyT sem_oval_typed_ufun.
      iApply (sem_typed_do_const OS ⟨⟩%R (l1, l2) (𝟙 + 𝟙)%T (Option 𝔾)%T).
      iApply sem_typed_sub_nil. iApply sem_typed_var. }
    iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
    iApplyT (sem_typed_sub_env _ ([("doGK", _); ("f", _)]
                                    ++ [("store_if_none", _); ("lc", _); ("ga", _); ("gb", _); ("gc", _); ("doSend", _); ("doRecv", _)])).
    { simpl. env_solve. }
    iApplyT (sem_typed_deep_handler_OS (l1, l2) (λ _, 𝟙 + 𝟙)%T (λ _, Option 𝔾)%T).
    - iApplyT sem_typed_app_fun_nil.
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
      + iApplyT sem_typed_seq.
        { iApplyT sem_typed_app_fun_nil; [iApply row_le_nil|iApplyT sem_typed_unit'|].
          iApplyT sem_typed_sub_ty; [iApply ty_le_u2aarr|typed_var_copy]. }
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_app_fun_nil; [row_le_submseteq|iApplyT sem_typed_pair; [iApply (sem_typed_party true)|typed_var_copy]|typed_leak_fun]. }
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
      + iApplyT sem_typed_let.
        { iApplyT sem_typed_app_fun_nil; [row_le_submseteq|iApply (sem_typed_party false)|typed_leak_fun]. }
        iApplyT (sem_typed_match_split [] []).
        * typed_var.
        * iApply env_le_refl.
        * iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_injl; iApplyT sem_typed_unit'|typed_cont].
        * iApply env_le_refl.
        * iApply env_le_refl.
        * iApplyT sem_typed_sub_env; first iApply env_le_weaken.
          iApplyT sem_typed_seq.
          { iApplyT sem_typed_app_fun_nil; [row_le_submseteq|iApplyT sem_typed_pair; [iApply (sem_typed_party false)|typed_var_copy]|typed_leak_fun]. }
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

  Lemma red_self :
    ⊢ sem_typed [] (λ: "DH", F_AUTH ∘f (λ: "f", C_lazy "DH" "f"))
                    (λ: "DH", F_AUTH ∘f (λ: "f", C_lazy "DH" "f")) ⊥
        ((𝟙 ⊸ (𝔾 × 𝔾 × 𝔾)) → τ_DH)%T [].
  Proof using Type*.
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []). iApplyT sem_oval_typed_ufun. simpl.
    iApplyT sem_typed_app_nil.
    - iApplyT sem_typed_app_nil; last iApply F_AUTH_typed.
      iApply sem_typed_val. iApply func_comp_val_typed.
    - iApply (sem_typed_oval _ [_]). iApply sem_typed_RLam. iIntros (θ).
      iApplyT sem_oval_typed_afun. simpl.
      iApplyT sem_typed_app_nil; last typed_var.
      iApplyT sem_typed_sub_ty.
      2: { iApplyT sem_typed_app_nil; last typed_var.
           iApplyT sem_typed_sub_ty; first iApply ty_le_mbang_elim.
           iApply sem_typed_val. iApply C_lazy_val_typed. }
      iApply ty_le_row_forall_inst.
      Unshelve. all: solve_typed_side.
  Qed.

End dhke_typing.
