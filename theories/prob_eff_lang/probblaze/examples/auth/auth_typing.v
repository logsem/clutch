(* Semantic typing of [AUTH] and [S_AUTH] (session bodies and factories), in
   the style of [dhke_typing] / [sec_channel_typing]. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze.uc Require Import comp_operators.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory logic.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def dhke_common.
From clutch.prob_eff_lang.probblaze.examples.auth Require Import auth_def.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems.
From clutch.prob_eff_lang.probblaze.examples Require Export dhke_typing.

Import fingroup.
Import fingroup.fingroup.

Section auth_typing.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  Import valgroup_notation.
  Import typed_hint_modes.
  #[local] Existing Instance multi_ty_group.
  #[local] Notation n := (S n'').

  (* [tag e1 e2 e3]: the arguments are evaluated right to left. *)
  Lemma sem_typed_tag Γ1 Γ2 Γ3 Γ4 ρ e1 e1' e2 e2' e3 e3' :
    ⊢ sem_typed Γ1 e3 e3' ρ 𝔾 Γ2 -∗ sem_typed Γ2 e2 e2' ρ ℕ Γ3 -∗ sem_typed Γ3 e1 e1' ρ ℕ Γ4 -∗
      sem_typed Γ1 (tag e1 e2 e3) (tag e1' e2' e3') ρ 𝔾 Γ4.
  Proof using G vgg.
    iIntros "#He3 #He2 #He1 !# %γ HΓ1 /=".
    iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ1]"); first by iApply "He3".
    iIntros "!# % % ((%m & -> & ->) & HΓ2) /=".
    iApply (brel_bind [AppLCtx _; AppRCtx _] [AppLCtx _; AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ2]"); first by iApply "He2".
    iIntros "!# % % ((%k2 & -> & ->) & HΓ3) /=".
    iApply (brel_bind [AppLCtx _; AppLCtx _; AppRCtx _] [AppLCtx _; AppLCtx _; AppRCtx _]); [iApply traversable_to_iThy|iApply to_iThy_le_refl|].
    iApply (brel_wand with "[HΓ3]"); first by iApply "He1".
    iIntros "!# % % ((%k1 & -> & ->) & HΓ4) /=".
    rewrite /tag. brel_pures_l. brel_pures_r.
    iApply (brel_exp_l [AppRCtx _]). iApply (brel_exp_r [AppRCtx _]).
    iApply (brel_exp_l [AppLCtx _; AppRCtx _]). iApply (brel_exp_r [AppLCtx _; AppRCtx _]).
    iApply (brel_mult_l []). iApply (brel_mult_r []).
    iApply brel_value. iIntros "$ !>". iFrame. by iExists _.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Interface types.                                                    *)
  (* ------------------------------------------------------------------ *)

  (* The raw network: tagged messages go out, tagged messages (chosen by the
     environment) come in. *)
  Definition raw (θ : sem_row Σ) : sem_ty Σ :=
    ((((𝔾 × 𝔾) × (𝟙 + 𝟙)) -{ θ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ }-> Option (𝔾 × 𝔾)))%T.

  (* ------------------------------------------------------------------ *)
  (* AUTH                                                                *)
  (* ------------------------------------------------------------------ *)

  (* What the send handler captures. *)
  Definition auth_send_env (θ : sem_row Σ) : env Σ :=
    [("k1a", ℕ); ("k2a", ℕ); ("k1b", ℕ); ("k2b", ℕ);
     ("sent1", Refᶜ 𝔹); ("sent2", Refᶜ 𝔹);
     ("doSend", (((𝔾 × 𝔾) × (𝟙 + 𝟙)) -{ θ }-> 𝟙)%T)].

  (* What the receive handler captures. *)
  Definition auth_recv_env (θ : sem_row Σ) : env Σ :=
    [("k1a", ℕ); ("k2a", ℕ); ("k1b", ℕ); ("k2b", ℕ);
     ("dec1", Refᶜ 𝔹); ("dec2", Refᶜ 𝔹);
     ("res1", Refᶜ (Option 𝔾)); ("res2", Refᶜ (Option 𝔾));
     ("doRecv", ((𝟙 + 𝟙) -{ θ }-> Option (𝔾 × 𝔾))%T)].

  Definition auth_send_body : expr :=
    (let, ("m", "dst") := "payload" in
     match: "dst" with
       InjL <> =>
         (if: !"sent1" then #()%V
          else "sent1" <- #true;; "doSend" (("m", tag "k1a" "k2a" "m"), "dst"));;
         "k" #()%V
     | InjR <> =>
         (if: !"sent2" then #()%V
          else "sent2" <- #true;; "doSend" (("m", tag "k1b" "k2b" "m"), "dst"));;
         "k" #()%V
     end)%E.

  Definition auth_recv_body : expr :=
    (let: "k1" := match: "from" with InjL <> => "k1b" | InjR <> => "k1a" end in
     let: "k2" := match: "from" with InjL <> => "k2b" | InjR <> => "k2a" end in
     let: "dec" := match: "from" with InjL <> => "dec2" | InjR <> => "dec1" end in
     let: "res" := match: "from" with InjL <> => "res2" | InjR <> => "res1" end in
     if: !"dec" then "k" !"res"
     else
       match: "doRecv" "from" with
         NONE => "k" NONEV
       | SOME "p" =>
           let, ("m'", "t'") := "p" in
           let: "r" := if: veq "t'" (tag "k1" "k2" "m'") then SOME "m'" else NONEV in
           "dec" <- #true;; "res" <- "r";; "k" "r"
       end)%E.

  (* A one-branch send: test the flag, tag, send. *)
  Lemma auth_send_branch_typed (θ ρh : sem_row Σ) (sent k1 k2 : string) Γ :
    ⊢ (¡ θ)%R ≤ᵣ ρh -∗
      sem_typed Γ (!sent) (!sent) ρh 𝔹 Γ -∗
      sem_typed Γ sent sent ρh (Refᶜ 𝔹) Γ -∗
      sem_typed Γ k1 k1 ρh ℕ Γ -∗
      sem_typed Γ k2 k2 ρh ℕ Γ -∗
      sem_typed Γ "m" "m" ρh 𝔾 Γ -∗
      sem_typed Γ "dst" "dst" ρh (𝟙 + 𝟙)%T Γ -∗
      sem_typed Γ "doSend" "doSend" ⟨⟩ ((((𝔾 × 𝔾) × (𝟙 + 𝟙)) -{ ¡ θ }-∘ 𝟙)%T) Γ -∗
      sem_typed Γ
        (if: !sent then #()%V else sent <- #true;; "doSend" (("m", tag k1 k2 "m"), "dst"))
        (if: !sent then #()%V else sent <- #true;; "doSend" (("m", tag k1 k2 "m"), "dst"))
        ρh 𝟙 Γ.
  Proof using All.
    iIntros "#Hρ #Hload #Hsent #Hk1 #Hk2 #Hm #Hdst #HdoSend".
    iApply sem_typed_if; first iApply "Hload".
    - iApply sem_typed_unit'.
    - iApply sem_typed_seq.
      { iApply (sem_typed_store_cpy_gen with "Hsent"). iApply sem_typed_bool'. }
      iApply (sem_typed_app_fun_nil with "Hρ [] HdoSend").
      iApply (sem_typed_pair with "Hdst").
      iApply (sem_typed_pair with "[] Hm").
      iApply (sem_typed_tag with "Hm Hk2 Hk1").
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma auth_send_handler_typed (θ ρh : sem_row Σ) :
    ⊢ (¡ θ)%R ≤ᵣ ρh -∗
    sem_typed (("payload", (𝔾 × (𝟙 + 𝟙))%T) :: ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T) :: auth_send_env θ)
      auth_send_body auth_send_body ρh 𝟙 (auth_send_env θ).
  Proof using All.
    iIntros "#Hρ". rewrite /auth_send_env /auth_send_body.
    iApplyT sem_typed_pair_elim; first tvar.
    iApplyT (sem_typed_match_split [] []).
    - tvar_copy.
    - iApply env_le_refl.
    - iApplyT sem_typed_seq.
      { iApply (auth_send_branch_typed _ _ "sent1" "k1a" "k2a" with "Hρ"); try tvar_copy.
        - iApplyT sem_typed_load_cpy. tvar_copy.
        - tleak_fun. }
      iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|tcont].
    - env_solve16.
    - iApply env_le_refl.
    - iApplyT sem_typed_seq.
      { iApply (auth_send_branch_typed _ _ "sent2" "k1b" "k2b" with "Hρ"); try tvar_copy.
        - iApplyT sem_typed_load_cpy. tvar_copy.
        - tleak_fun. }
      iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|tcont].
    - env_solve16.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma auth_recv_handler_typed (θ ρh : sem_row Σ) :
    ⊢ (¡ θ)%R ≤ᵣ ρh -∗
    sem_typed (("from", (𝟙 + 𝟙)%T) :: ("k", (Option 𝔾 -{ ρh }-[OS]-> 𝟙)%T) :: auth_recv_env θ)
      auth_recv_body auth_recv_body ρh 𝟙 (auth_recv_env θ).
  Proof using All.
    iIntros "#Hρ". rewrite /auth_recv_env /auth_recv_body.
    (* the four selections by [from] *)
    iApplyT sem_typed_let.
    { iApplyT (sem_typed_match_split [] []); [tvar_copy|iApply env_le_refl|tvar_copy|iApply env_le_refl
                                              |iApply env_le_refl|tvar_copy|iApply env_le_refl]. }
    iApplyT sem_typed_let.
    { iApplyT (sem_typed_match_split [] []); [tvar_copy|iApply env_le_refl|tvar_copy|iApply env_le_refl
                                              |iApply env_le_refl|tvar_copy|iApply env_le_refl]. }
    iApplyT sem_typed_let.
    { iApplyT (sem_typed_match_split [] []); [tvar_copy|iApply env_le_refl|tvar_copy|iApply env_le_refl
                                              |iApply env_le_refl|tvar_copy|iApply env_le_refl]. }
    iApplyT sem_typed_let.
    { iApplyT (sem_typed_match_split [] []); [tvar_copy|iApply env_le_refl|tvar_copy|iApply env_le_refl
                                              |iApply env_le_refl|tvar_copy|iApply env_le_refl]. }
    iApplyT sem_typed_if.
    { iApplyT sem_typed_load_cpy. tvar_copy. }
    - (* already decided *)
      iApplyT sem_typed_sub_env_final.
      2: { iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
           - iApplyT sem_typed_load_cpy. tvar_copy.
           - tcont. }
      env_solve16.
    - iApplyT sem_typed_sub_env_final.
      2: { iApplyT (sem_typed_match_split [] []).
           - iApplyT sem_typed_app_fun_nil; [iApply "Hρ"|tvar_copy|tleak_fun].
           - iApply env_le_refl.
           - iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|tcont].
           - iApply env_le_refl.
           - iApply env_le_refl.
           - iApplyT sem_typed_pair_elim; first tvar.
             iApplyT sem_typed_let.
             { iApplyT sem_typed_if.
               - iApplyT sem_typed_veq_gen; [iApplyT sem_typed_tag; tvar_copy|tvar].
               - iApplyT sem_typed_injr. tvar.
               - iApplyT sem_typed_sub_env; first iApply env_le_weaken. iApplyT sem_typed_none. }
             iApplyT sem_typed_seq.
             { iApplyT sem_typed_store_cpy_gen. 2: iApplyT sem_typed_bool'. tvar_copy. }
             iApplyT sem_typed_seq.
             { iApplyT sem_typed_store_cpy_gen. 2: tvar_copy. tvar_copy. }
             iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|tvar|tcont].
           - env_solve16. }
      env_solve16.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma AUTH_typed m : ⊢ ⊨ᵥ AUTH ≤ AUTH : fac m (τ__F raw chan).
  Proof using All.
    iApply fac_closure. rewrite /sample.
    do 4 (iApplyT sem_typed_let;
          first (iApplyT sem_typed_let; first iApplyT sem_typed_unit'; iApply sem_typed_rand_untaped)).
    do 4 (iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_bool')).
    do 2 (iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none)).
    (* the closure captures the keys and the state *)
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _; _; _; _; _; _; _; _; _]).
    iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _; _; _; _; _; _; _; _; _; _]). iApply sem_typed_RLam. iIntros (θ₂).
    iApplyT sem_oval_typed_afun. simpl.
    iApplyT sem_typed_pair_elim; first tvar.
    iApply sem_typed_effect_gen. iIntros (ls1 ls2).
    iApply sem_typed_effect_gen. iIntros (lr1 lr2). simpl.
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
    iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
    iApplyT (sem_typed_sub_env _ (([("doARecv", _); ("doASend", _); ("f", _)] ++ auth_send_env θ₂)
                                    ++ auth_recv_env θ₂)).
    { rewrite /auth_send_env /auth_recv_env. simpl. env_solve16. }
    (* Outer handler: recv. *)
    iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option 𝔾)%T).
    - (* Inner handler: send. *)
      iApplyT sem_typed_sub_row; first iApply row_le_swap_second.
      iApplyT (sem_typed_sub_env _ ([_; _; _] ++ auth_send_env θ₂)); first iApply env_le_refl.
      iApplyT (sem_typed_deep_handler_OS (ls1, ls2) (λ _, 𝔾 × (𝟙 + 𝟙))%T (λ _, 𝟙)%T).
      + (* the client call [f (doASend, doARecv)] *)
        iApplyT sem_typed_app_fun_nil.
        2: { iApplyT sem_typed_pair; tvar. }
        2: { iApplyT sem_typed_sub_ty; last tvar. iApply ty_le_row_forall_inst. }
        iApply row_le_trans; first iApplyT row_le_union'.
        * iApply row_le_mfbang_elim.
        * iApply row_le_refl.
        * row_le_submseteq.
      + iIntros (?). iApply auth_send_handler_typed; row_le_submseteq.
      + iApplyT sem_typed_sub_env_final; last iApplyT sem_typed_unit'. rewrite /auth_send_env. env_solve16.
    - iIntros (?). iApply auth_recv_handler_typed; row_le_submseteq.
    - iApplyT sem_typed_sub_env_final; last iApplyT sem_typed_unit'. rewrite /auth_recv_env. env_solve16.
      Unshelve. all: solve_typed_side.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* S_AUTH                                                              *)
  (* ------------------------------------------------------------------ *)

  (* What the two port closures of the simulator capture. *)
  Definition sauth_env (θ : sem_row Σ) : env Σ :=
    [("doSend", (((𝔾 × 𝔾) × (𝟙 + 𝟙)) -{ θ }-> 𝟙)%T);
     ("doRecv", ((𝟙 + 𝟙) -{ θ }-> Option (𝔾 × 𝔾))%T);
     ("k1a", ℕ); ("k2a", ℕ); ("k1b", ℕ); ("k2b", ℕ);
     ("tagged1", Refᶜ 𝔹); ("tagged2", Refᶜ 𝔹);
     ("tag1", Refᶜ (𝔾 × 𝔾)); ("tag2", Refᶜ (𝔾 × 𝔾));
     ("dec1", Refᶜ 𝔹); ("dec2", Refᶜ 𝔹); ("acc1", Refᶜ 𝔹); ("acc2", Refᶜ 𝔹)].
  Definition sauth_send_body : expr :=
    (let, ("m", "dst") := "payload" in
     match: "dst" with
       InjL <> => let: "t" := tag "k1a" "k2a" "m" in
                  "tagged1" <- #true;; "tag1" <- ("m", "t");; "doSend" (("m", "t"), "dst")
     | InjR <> => let: "t" := tag "k1b" "k2b" "m" in
                  "tagged2" <- #true;; "tag2" <- ("m", "t");; "doSend" (("m", "t"), "dst")
     end)%E.

  Definition sauth_recv_body : expr :=
    (let: "tagged" := match: "from" with InjL <> => "tagged2" | InjR <> => "tagged1" end in
     let: "tg" := match: "from" with InjL <> => "tag2" | InjR <> => "tag1" end in
     let: "dec" := match: "from" with InjL <> => "dec2" | InjR <> => "dec1" end in
     let: "acc" := match: "from" with InjL <> => "acc2" | InjR <> => "acc1" end in
     if: !"dec" then (if: !"acc" then SOME #(0%nat) else NONEV)
     else
       match: "doRecv" "from" with
         NONE => NONEV
       | SOME "p" =>
           let, ("m'", "t'") := "p" in
           let, ("m", "t") := !"tg" in
           let: "ok" := !"tagged" && veq "m'" "m" && veq "t'" "t" in
           "dec" <- #true;; "acc" <- "ok";;
           (if: "ok" then SOME #(0%nat) else NONEV)
       end)%E.

  Lemma sauth_send_branch_typed (θ ρh : sem_row Σ) (tagged tg k1 k2 : string) Γ `{!θ ᵣ⪯ₑ Γ} :
    "t" ∉ env_dom Γ →
    ⊢ θ ≤ᵣ ρh -∗
      sem_typed Γ tagged tagged ρh (Refᶜ 𝔹) Γ -∗
      sem_typed Γ tg tg ρh (Refᶜ (𝔾 × 𝔾)) Γ -∗
      sem_typed Γ k1 k1 ρh ℕ Γ -∗
      sem_typed Γ k2 k2 ρh ℕ Γ -∗
      sem_typed Γ "m" "m" ρh 𝔾 Γ -∗
      sem_typed Γ "dst" "dst" ρh (𝟙 + 𝟙)%T Γ -∗
      sem_typed Γ "doSend" "doSend" ⟨⟩ ((((𝔾 × 𝔾) × (𝟙 + 𝟙)) -{ θ }-∘ 𝟙)%T) Γ -∗
      sem_typed Γ
        (let: "t" := tag k1 k2 "m" in
         tagged <- #true;; tg <- ("m", "t");; "doSend" (("m", "t"), "dst"))
        (let: "t" := tag k1 k2 "m" in
         tagged <- #true;; tg <- ("m", "t");; "doSend" (("m", "t"), "dst"))
        ρh 𝟙 [].
  Proof using All.
    iIntros (Ht) "#Hρ #Htagged #Htg #Hk1 #Hk2 #Hm #Hdst #HdoSend".
    iApplyT sem_typed_let; first iApply (sem_typed_tag with "Hm Hk2 Hk1").
    iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
    iApplyT sem_typed_seq.
    { iApplyT sem_typed_store_cpy_gen. 2: iApplyT sem_typed_bool'. iApply (sem_typed_frame_env_gen _ [_]). iApply "Htagged". }
    iApplyT sem_typed_seq.
    { iApplyT sem_typed_store_cpy_gen.
      2: { iApplyT sem_typed_pair; first tvar_copy. iApply (sem_typed_frame_env_gen _ [_]). iApply "Hm". }
      iApply (sem_typed_frame_env_gen _ [_]). iApply "Htg". }
    iApplyT sem_typed_app_fun_nil; first iApply "Hρ".
    - iApplyT sem_typed_pair; first (iApply (sem_typed_frame_env_gen _ [_]); iApply "Hdst").
      iApplyT sem_typed_pair; first tvar_copy.
      iApply (sem_typed_frame_env_gen _ [_]). iApply "Hm".
    - iApply (sem_typed_frame_env_gen _ [_]). iApply "HdoSend".
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma sauth_send_body_typed (θ : sem_row Σ) :
    ⊢ sem_typed (("payload", (𝔾 × (𝟙 + 𝟙))%T) :: sauth_env θ) sauth_send_body sauth_send_body θ 𝟙 [].
  Proof using All.
    rewrite /sauth_env /sauth_send_body.
    iApplyT sem_typed_pair_elim; first tvar.
    iApplyT (sem_typed_match_split [] []).
    - tvar_copy.
    - iApply env_le_refl.
    - iApplyT (sauth_send_branch_typed _ _ "tagged1" "tag1" "k1a" "k2a"); [iApply row_le_refl|tvar_copy|tvar_copy|tvar_copy|tvar_copy|tvar_copy|tvar_copy|tufun].
    - iApply env_le_nil.
    - iApply env_le_refl.
    - iApplyT (sauth_send_branch_typed _ _ "tagged2" "tag2" "k1b" "k2b"); [iApply row_le_refl|tvar_copy|tvar_copy|tvar_copy|tvar_copy|tvar_copy|tvar_copy|tufun].
    - iApply env_le_nil.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma sauth_recv_body_typed (θ : sem_row Σ) :
    ⊢ sem_typed (("from", (𝟙 + 𝟙)%T) :: sauth_env θ) sauth_recv_body sauth_recv_body θ (Option ℕ) [].
  Proof using All.
    rewrite /sauth_env /sauth_recv_body.
    do 4 (iApplyT sem_typed_let;
          first (iApplyT (sem_typed_match_split [] []);
                 [tvar_copy|iApply env_le_refl|tvar_copy|iApply env_le_refl
                 |iApply env_le_refl|tvar_copy|iApply env_le_refl])).
    iApplyT sem_typed_if.
    { iApplyT sem_typed_load_cpy. tvar_copy. }
    - iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT sem_typed_if.
      { iApplyT sem_typed_load_cpy. tvar_copy. }
      + iApplyT sem_typed_injr. iApply sem_typed_nat'.
      + iApplyT sem_typed_none.
    - iApplyT (sem_typed_match_split [] []).
      + iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|tvar_copy|tufun].
      + iApply env_le_refl.
      + iApplyT sem_typed_sub_env_final; first iApply env_le_nil. iApplyT sem_typed_none.
      + iApply env_le_nil.
      + iApply env_le_refl.
      + iApplyT sem_typed_pair_elim; first tvar.
        iApplyT sem_typed_pair_elim; first (iApplyT sem_typed_load_cpy; tvar_copy).
        iApplyT sem_typed_let.
        { iApplyT sem_typed_if.
          - iApplyT sem_typed_if.
            + iApplyT sem_typed_load_cpy. tvar_copy.
            + iApplyT sem_typed_veq_gen; tvar_copy.
            + iApplyT sem_typed_bool'.
          - iApplyT sem_typed_veq_gen; tvar_copy.
          - iApplyT sem_typed_bool'. }
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_store_cpy_gen. 2: iApplyT sem_typed_bool'. tvar_copy. }
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_store_cpy_gen. 2: tvar_copy. tvar_copy. }
        iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
        iApplyT sem_typed_if; first tvar_copy.
        * iApplyT sem_typed_injr. iApply sem_typed_nat'.
        * iApplyT sem_typed_none.
      + iApply env_le_nil.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma S_AUTH_typed m : ⊢ ⊨ᵥ S_AUTH ≤ S_AUTH : fac m (τ__F raw aleak).
  Proof using All.
    iApply fac_closure. rewrite /sample.
    do 4 (iApplyT sem_typed_let;
          first (iApplyT sem_typed_let; first iApplyT sem_typed_unit'; iApply sem_typed_rand_untaped)).
    do 2 (iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_bool')).
    do 2 (iApplyT sem_typed_let;
          first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_pair; iApply sem_typed_vgval)).
    do 4 (iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_bool')).
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _; _; _; _; _; _; _; _; _; _; _]).
    iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _; _; _; _; _; _; _; _; _; _; _; _]). iApply sem_typed_RLam. iIntros (θ₂).
    iApplyT sem_oval_typed_afun. simpl.
    iApplyT sem_typed_pair_elim; first tvar.
    (* [f (send closure, receive closure)], with [f] instantiated at [¡θ₂] *)
    iApplyT sem_typed_app_fun_nil.
    2: { iApplyT (sem_typed_sub_env _ (sauth_env θ₂ ++ sauth_env θ₂ ++ [("f", _)])).
         { rewrite /sauth_env. simpl. env_solve16. }
         iApplyT sem_typed_pair.
         - iApply sem_typed_sub_nil. iApply (sem_typed_oval _ (sauth_env θ₂)).
           iApplyT sem_oval_typed_ufun. simpl. iApply sauth_recv_body_typed.
         - iApply sem_typed_sub_nil. iApply (sem_typed_oval _ (sauth_env θ₂)).
           iApplyT sem_oval_typed_ufun. simpl. iApply sauth_send_body_typed. }
    2: { iApplyT sem_typed_sub_ty; last tvar. iApply ty_le_row_forall_inst. }
    first [iApply row_le_refl | row_le_submseteq
          | (iApply row_le_trans; first iApplyT row_le_union';
             [iApply row_le_mfbang_elim|iApply row_le_refl|row_le_submseteq])].
      Unshelve. all: solve_typed_side.
  Qed.

End auth_typing.
