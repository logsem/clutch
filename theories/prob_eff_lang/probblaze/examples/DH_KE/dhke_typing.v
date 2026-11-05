From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import comp_operators primitive_laws proofmode.
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
  Definition leakI (θ : sem_row Σ) : sem_ty Σ :=
    (((𝟙 + 𝟙) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option 𝟙))%T.

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

  (* [func_comp] hands [F] the client [λ r, G f r]: the application [G f] is
     delayed behind an η-expansion. [EtaT τ] says that this delay preserves
     [τ]. It holds for one-shot arrows and is closed under [∀ᵣ], so it covers
     both [τ__F]'s client (one row binder) and [τ__f] (two row binders). *)
  Class EtaT (τ : sem_ty Σ) := {
    eta_ty : ⊢ ∀ g1 g2 x1 x2 : val,
      BREL g1 x1 ≤ g2 x2 <| [] |> {{ τ }} -∗ τ (λ: "r", g1 x1 "r")%V (λ: "r", g2 x2 "r")%V
  }.

  Global Instance eta_ty_arr ρ τ κ : EtaT (τ -{ ρ }-∘ κ).
  Proof.
    constructor. iIntros (g1 g2 x1 x2) "Hg". rewrite /sem_ty_arr /=.
    iIntros (w1 w2) "Hw". brel_pures_l; brel_pures_r.
    iApply (brel_bind [AppLCtx _] [AppLCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS _ _ [] [] with "[] Hg"); first iApply to_iThy_le_refl.
    simpl. iIntros (v1 v2) "Hv". by iApply "Hv".
  Qed.

  Global Instance eta_ty_row_forall (C : sem_row Σ → sem_ty Σ) `{!∀ θ, EtaT (C θ)} :
    EtaT (∀ᵣ θ, C θ).
  Proof.
    constructor. iIntros (g1 g2 x1 x2) "Hg". rewrite /sem_ty_row_forall /=. iIntros (θ).
    iApply eta_ty. iApply (brel_wand with "Hg"). iIntros "!# % % H". iApply "H".
  Qed.

  Lemma sem_oval_typed_eta (g x : string) τ M `{!EtaT M} :
    g ≠ "r" → x ≠ "r" →
    ⊢ sem_oval_typed [(x, τ); (g, τ ⊸ M)] (λ: "r", g x "r") (λ: "r", g x "r") M.
  Proof.
    iIntros (Hg Hx) "!# %vs HΓ /=".
    rewrite !env_sem_typed_cons env_sem_typed_empty.
    iDestruct "HΓ" as "([%x1 [%x2 [%Hvx Hx]]] & [%g1 [%g2 [%Hvg Hg]]] & _)".
    simplify_map_eq. rewrite /pure_weakestpre.prel /=. iExists _, _, 1%nat, 1%nat.
    iSplit; first (iPureIntro; repeat split; by apply pure_recc).
    iApply eta_ty. by iApply "Hg".
  Qed.

  Lemma func_comp_val_typed (T1 M T4 : sem_row Σ → sem_ty Σ) `{!∀ θ, EtaT (M θ)} :
    ⊢ ⊨ᵥ func_comp ≤ func_comp :
      ((∀ᵣ θ, M θ ⊸ T4 θ) ⊸ (∀ᵣ θ, T1 θ ⊸ M θ) ⊸ (∀ᵣ θ, T1 θ ⊸ T4 θ))%T.
  Proof.
    iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
    iApply sem_typed_closure; first done.
    iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_afun. simpl.
    iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
    - iApplyT (sem_typed_sub_env _ [("f", T1 θ); ("G", T1 θ ⊸ M θ); ("F", _)]).
      { iApply env_le_cons; last iApply ty_le_refl.
        iApply env_le_cons; [iApply env_le_refl|iApply ty_le_row_forall_inst]. }
      iApply (sem_typed_oval _ [("f", _); ("G", _)] [("F", _)]).
      by iApply sem_oval_typed_eta.
    - iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst.
      Unshelve. all: solve_typed_side.
  Qed.

  (* Unrestricted variant of [τ__F]: the functionality can be given a client multiple times *)
  Definition τ__Fu (τ τ' : sem_row Σ → sem_ty Σ) :=
    (∀ᵣ θ, (∀ᵣ θ₁, τ' θ₁ -{ sem_row_union (¡θ₁) θ}-∘ 𝟙) → (∀ᵣ θ₂, τ θ₂ -{ sem_row_union (¡θ₂) θ }-∘ 𝟙))%T.

  Lemma τ__Fu_le_τ__F τ τ' : ⊢ τ__Fu τ τ' ≤ₜ τ__F τ τ'.
  Proof. iApply ty_le_row_forall. iIntros (θ). iApply ty_le_mbang_elim. Qed.

  (* Only the closure taking the client is unrestricted, so [F] and [G] must be *)
  Lemma func_comp_val_typed_u (T1 M T4 : sem_row Σ → sem_ty Σ) `{!∀ θ, EtaT (M θ)} :
    ⊢ ⊨ᵥ func_comp ≤ func_comp :
      ((∀ᵣ θ, M θ → T4 θ) ⊸ (∀ᵣ θ, T1 θ → M θ) ⊸ (∀ᵣ θ, T1 θ → T4 θ))%T.
  Proof.
    iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
    iApply sem_typed_closure; first done.
    iApply (sem_typed_oval _ [_]). iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_ufun. simpl.
    iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
    - iApplyT (sem_typed_sub_env _ [("f", T1 θ); ("G", T1 θ ⊸ M θ); ("F", _)]).
      { iApply env_le_cons; last iApply ty_le_refl.
        iApply env_le_cons; [iApply env_le_refl|].
        iApply ty_le_trans; [iApply ty_le_row_forall_inst|iApply ty_le_mbang_elim]. }
      iApply (sem_typed_oval _ [("f", _); ("G", _)] [("F", _)]).
      by iApply sem_oval_typed_eta.
    - iApplyT sem_typed_sub_ty; last typed_var.
      iApply ty_le_trans; [iApply ty_le_row_forall_inst|iApply ty_le_mbang_elim].
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

  Lemma F_AUTH_typed_u : ⊢ sem_typed [] F_AUTH F_AUTH ⊥ (τ__Fu aleak chan) [].
  Proof using Type*.
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
    (* the copyable references are the only captured state *)
    iApplyT sem_oval_typed_ufun.
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

  Lemma F_AUTH_typed : ⊢ sem_typed [] F_AUTH F_AUTH ⊥ (τ__F aleak chan) [].
  Proof using Type*.
    iApply sem_typed_sub_ty; [iApply τ__Fu_le_τ__F|iApply F_AUTH_typed_u].
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

  Lemma DH_SIM_typed : ⊢ sem_typed [] DH_SIM DH_SIM ⊥ (τ__F chan leakI) [].
  Proof using All.
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloctape; iApplyT sem_typed_int').
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloctape; iApplyT sem_typed_int').
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _; _; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _; _; _; _]). iApply sem_typed_RLam. iIntros (θ₂).
    iApplyT sem_oval_typed_afun.
    iApplyT sem_typed_pair_elim; first typed_var.
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

  Lemma F_KE_lazy_alice_typed : ⊢ sem_typed [] F_KE_lazy_alice F_KE_lazy_alice ⊥ (τ__F leakI gk) [].
  Proof using All.
    rewrite /F_KE_lazy_alice /samplelbl.
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloctape; iApplyT sem_typed_int').
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    (* [sample_or_load] captures copies of the tape and the cache. *)
    iApplyT sem_typed_let.
    { iApplyT (sem_typed_sub_env _ ([("γ", _); ("lc", _)] ++ [("lc", _); ("γ", _)])).
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
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _; _; _]). iApply sem_typed_RLam. iIntros (θ₂).
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

  Lemma C_lazy_val_typed_u :
    ⊢ sem_val_typed C_lazy C_lazy ((𝟙 ⊸ (𝔾 × 𝔾 × 𝔾)) → τ__Fu chan gk)%T.
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
    (* the captured group elements and the copyable reference are duplicable *)
    iApplyT sem_oval_typed_ufun.
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

  Lemma C_lazy_val_typed :
    ⊢ sem_val_typed C_lazy C_lazy ((𝟙 ⊸ (𝔾 × 𝔾 × 𝔾)) → τ__F chan gk)%T.
  Proof using Type*.
    iApply sem_val_typed_sub; last iApply C_lazy_val_typed_u.
    iApply ty_le_mbang_comp; first iApply mode.mode_le_refl.
    iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|iApply τ__Fu_le_τ__F].
  Qed.

  (* [τ_DH] is [τ__Fu aleak gk] *)
  Lemma red_self :
    ⊢ sem_typed [] (λ: "DH", F_AUTH ∘f (C_lazy "DH"))
                    (λ: "DH", F_AUTH ∘f (C_lazy "DH")) ⊥
        ((𝟙 ⊸ (𝔾 × 𝔾 × 𝔾)) → τ_DH)%T [].
  Proof using Type*.
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []). iApplyT sem_oval_typed_ufun. simpl.
    iApplyT sem_typed_app_nil.
    - iApplyT sem_typed_app_nil; last iApply F_AUTH_typed_u.
      iApply sem_typed_val. iApply func_comp_val_typed_u.
    - iApplyT sem_typed_app_nil; last typed_var.
      iApplyT sem_typed_sub_ty; first iApply ty_le_mbang_elim.
      iApply sem_typed_val. iApply C_lazy_val_typed_u.
      Unshelve. all: solve_typed_side.
  Qed.

End dhke_typing.
