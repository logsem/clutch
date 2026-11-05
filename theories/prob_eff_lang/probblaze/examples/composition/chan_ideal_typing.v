(* Semantic typing of the ideal secure channel [F_CHAN] and of its simulator
   [CHAN_SIM_lazy], in the style of [new_composition_typing].

   The leak port of [F_CHAN] is [fleak]: a "sent" notification and a
   "received" query.  Two details of the programs show up in the types:

   - the simulator's [lsend] handler resumes with [NONEV] in one branch and
     with [#()] in the others.  [F_CHAN] discards the result, so this is
     harmless, but it means the result type of the "sent" notification is
     not [𝟙]; it is the semantic type [τ_sl] inhabited by both values.

   - the simulator answers the "received" query with the cached exponent, so
     the result type of that query is [Option ℕ]; [F_CHAN] only tests it for
     [NONE]/[SOME]. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import comp_operators primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory logic.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.examples Require Import sec_channel_def dhke_common mask new_composition_typing.
From clutch.prob_eff_lang.probblaze.examples Require Export dhke_typing.

Import fingroup.
Import fingroup.fingroup.

Section chan_ideal_typing.
  Context `{probblazeRGS Σ}.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.
  Context {msk : Mask vgG vgval}.
  Context `{!Mask_struc}.

  Import valgroup_notation.
  Import typed_hint_modes.
  #[local] Existing Instance multi_ty_group.

  (* The result of the "sent" notification: [#()] or [NONEV]. *)
  Definition τ_sl : sem_ty Σ := (λ v1 v2, ⌜v1 = v2 ∧ (v1 = #()%V ∨ v1 = NONEV)⌝)%I.

  Global Instance multi_ty_sl : MultiT τ_sl.
  Proof. constructor. iIntros "!# %v1 %v2 %Hv". rewrite /sem_ty_mbang /=. by iModIntro. Qed.

  Lemma sem_typed_sl_unit Γ ρ : ⊢ sem_typed Γ #()%V #()%V ρ τ_sl Γ.
  Proof. iApply sem_typed_sub_nil. iApply sem_typed_val. iIntros "!>". iPureIntro. by split; [|left]. Qed.

  Lemma sem_typed_sl_none Γ ρ : ⊢ sem_typed Γ NONEV NONEV ρ τ_sl Γ.
  Proof. iApply sem_typed_sub_nil. iApply sem_typed_val. iIntros "!>". iPureIntro. by split; [|right]. Qed.

  (* The leak port of [F_CHAN]. *)
  Definition fleak (θ : sem_row Σ) : sem_ty Σ :=
    (((𝟙 + 𝟙) -{ θ }-> τ_sl) × ((𝟙 + 𝟙) -{ θ }-> Option ℕ))%T.

  Definition τ_FCHAN : sem_ty Σ :=
    (∀ᵣ θ, hdl cli θ ⊸ ∀ᵣ θJ, fleak θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T.
  Definition τ_CHAN_SIM : sem_ty Σ :=
    (∀ᵣ θ, (∀ᵣ θJ, fleak θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙) ⊸ τ__f θ oaleak leakI)%T.

  (* Untaped sampling. *)
  Lemma sem_typed_rand_untaped Γ ρ (N : nat) :
    ⊢ sem_typed Γ (rand #N) (rand #N) ρ ℕ Γ.
  Proof.
    iIntros "!# %γ HΓ /=".
    iApply (brel_couple_rand_rand _ N (λ x, x) _ [] []); first done.
    iIntros (m) "%Hle". iApply brel_value. iIntros "$ !>". iFrame. by iExists m.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* F_CHAN                                                              *)
  (* ------------------------------------------------------------------ *)

  Lemma fchan_send_handler_typed (θJ ρh : sem_row Σ) :
    ⊢ (¡ θJ)%R ≤ᵣ ρh -∗
    sem_typed [("m", ℕ); ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T);
               ("message", Refᶜ (Option 𝔾)); ("doLeakSend", ((𝟙 + 𝟙) -{ θJ }-> τ_sl)%T)]
      (match: vg_of_int "m" with
       | NONE => "k" #()%V
       | SOME "m" =>
           match: !"message" with
           | NONE => "message" <- SOME "m";; ("doLeakSend" alice);; "k" #()%V
           | SOME "x" => "k" #()%V
           end
       end)%E
      (match: vg_of_int "m" with
       | NONE => "k" #()%V
       | SOME "m" =>
           match: !"message" with
           | NONE => "message" <- SOME "m";; ("doLeakSend" alice);; "k" #()%V
           | SOME "x" => "k" #()%V
           end
       end)%E
      ρh 𝟙 [("message", Refᶜ (Option 𝔾)); ("doLeakSend", ((𝟙 + 𝟙) -{ θJ }-> τ_sl)%T)].
  Proof using All.
    iIntros "#Hρ".
    iApplyT (sem_typed_match_split [] []).
    - iApplyT sem_typed_vg_of_int. typed_var.
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
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_app_fun_nil; [iApply "Hρ"|iApply (sem_typed_party false)|].
          typed_leak_fun. }
        iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|].
        typed_cont.
      + simpl. iApply env_le_weaken.
      + env_pick. iApply env_le_refl.
      + iApplyT sem_typed_sub_env; first iApply env_le_weaken.
        iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_unit'|].
        typed_cont.
      + env_solve.
    - env_solve.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma fchan_recv_handler_typed (θJ ρh : sem_row Σ) :
    ⊢ (¡ θJ)%R ≤ᵣ ρh -∗
    sem_typed [("payload", (𝟙 + 𝟙)%T); ("k", (Option 𝔾 -{ ρh }-[OS]-> 𝟙)%T);
               ("message", Refᶜ (Option 𝔾)); ("doLeakRecv", ((𝟙 + 𝟙) -{ θJ }-> Option ℕ)%T)]
      (let: "r" := ("doLeakRecv" bob) in
       match: "r" with
       | NONE => "k" NONEV
       | SOME "x" => "k" (!"message")
       end)%E
      (let: "r" := ("doLeakRecv" bob) in
       match: "r" with
       | NONE => "k" NONEV
       | SOME "x" => "k" (!"message")
       end)%E
      ρh 𝟙 [("message", Refᶜ (Option 𝔾)); ("doLeakRecv", ((𝟙 + 𝟙) -{ θJ }-> Option ℕ)%T)].
  Proof using All.
    iIntros "#Hρ".
    iApplyT sem_typed_sub_env; first iApply env_le_weaken.
    iApplyT sem_typed_let.
    { iApplyT sem_typed_app_fun_nil; [iApply "Hρ"|iApply (sem_typed_party true)|].
      typed_leak_fun. }
    iApplyT (sem_typed_match_split [] []).
    - typed_var.
    - iApply env_le_refl.
    - iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|].
      typed_cont.
    - iApply env_le_refl.
    - iApply env_le_refl.
    - iApplyT sem_typed_sub_env; first iApply env_le_weaken.
      iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
      + iApplyT sem_typed_load_cpy. typed_var_copy.
      + typed_cont.
    - iApply env_le_refl.
      Unshelve. all: solve_typed_side.
  Qed.

  (* The body of [F_CHAN] (free in "f", "LeakOp"), copied verbatim from
     [sec_channel_def.F_CHAN]. *)
  Definition F_CHAN_body : expr :=
    (let, ("doLeakSend", "doLeakRecv") := "LeakOp" in
     let: "message" := ref NONEV in
     effect "ssend"
       effect "srecv"
       let: "doSecSend" := (λ: "m", do: "ssend" "m")  in
       let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
       handle: handle: "f" ("doSecSend" ,"doSecRecv") with
     | effect "ssend" "m", rec "k" =>
         match: vg_of_int "m" with
         | NONE => "k" #()%V
         | SOME "m" =>
             match: !"message" with
             | NONE => "message" <- SOME "m";;
                       ("doLeakSend" alice);;
                       "k" #()%V
             | SOME "x" => "k" #()%V
             end
         end
     | return "y" => "y" end with
     | effect "srecv" "payload", rec "k" =>
         let: "r" := ("doLeakRecv" bob) in
         match: "r" with
         | NONE => "k" NONEV
         | SOME "x" => "k" (!"message")
         end
     | return "y" => "y"
     end)%E.

  Lemma F_CHAN_body_typed (θ θJ : sem_row Σ) :
    ⊢ sem_typed [("f", hdl cli θ); ("LeakOp", fleak θJ)] F_CHAN_body F_CHAN_body
        (sem_row_union (¡ θJ) θ) 𝟙 [].
  Proof using All.
    iApply sem_typed_swap_second.
    iApplyT sem_typed_pair_elim; first typed_var.
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
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
      iApply (sem_typed_do_const OS ⟨⟩%R (lr1, lr2) (𝟙 + 𝟙)%T (Option 𝔾)%T).
      iApply (sem_typed_party true). }
    (* The send handler keeps [message] and [doLeakSend]; the receive handler
       keeps [message] and [doLeakRecv]. *)
    iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
    iApplyT (sem_typed_sub_env _ ([("doSecRecv", _); ("doSecSend", _); ("f", _);
                                   ("message", _); ("doLeakSend", _)]
                                    ++ [("message", _); ("doLeakRecv", _)])).
    { simpl. env_solve. }
    (* Outer handler: srecv. *)
    iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option 𝔾)%T).
    - (* Inner handler: ssend. *)
      iApplyT sem_typed_sub_row; first iApply row_le_swap_second.
      iApplyT (sem_typed_sub_env _ ([_; _; _] ++ [_; _])); first iApply env_le_refl.
      iApplyT (sem_typed_deep_handler_OS (ls1, ls2) (λ _, ℕ) (λ _, 𝟙)%T).
      + iApplyT sem_typed_app_fun_nil.
        2: { iApplyT sem_typed_pair; typed_var. }
        2: { iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst. }
        row_le_submseteq.
      + iIntros (?). iApply fchan_send_handler_typed; row_le_submseteq.
      + typed_var.
    - iIntros (?). iApply fchan_recv_handler_typed; row_le_submseteq.
    - iApplyT sem_typed_sub_env_final; last typed_var. env_solve.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma F_CHAN_typed : ⊢ sem_typed [] F_CHAN F_CHAN ⊥ τ_FCHAN [].
  Proof using All.
    iApply sem_typed_val. iApply sem_typed_Rclosure. iIntros (θ).
    iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
    iApply sem_typed_closure; first done.
    iApply (sem_typed_oval _ [_]).
    iApply sem_typed_RLam. iIntros (θJ).
    iApplyT sem_oval_typed_afun. simpl.
    iApply sem_typed_swap_second. iApply F_CHAN_body_typed.
    Unshelve. all: solve_typed_side.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* CHAN_SIM_lazy                                                       *)
  (* ------------------------------------------------------------------ *)

  (* Context captured by both handlers of the simulator. *)
  Definition sim_env (θ1 θ2 : sem_row Σ) : env Σ :=
    [("doKeyLeakSnd", ((𝟙 + 𝟙) -{ θ2 }-> 𝟙)%T); ("doKeyLeakRecv", ((𝟙 + 𝟙) -{ θ2 }-> Option 𝟙)%T);
     ("doLeakASend", ((𝔾 × (𝟙 + 𝟙)) -{ θ1 }-> 𝟙)%T); ("doLeakARecv", ((𝟙 + 𝟙) -{ θ1 }-> Option 𝟙)%T);
     ("message", Refᶜ (Option ℕ)); ("m'_opt", Refᶜ (Option ℕ));
     ("sample_or_load", (𝟙 -{ ⟨⟩ }-> ℕ)%T)].
  Global Instance sim_env_MultiE θ1 θ2 : MultiE (sim_env θ1 θ2).
  Proof. rewrite /sim_env. apply _. Qed.

  Lemma sim_lsend_handler_typed (θ1 θ2 ρh : sem_row Σ) :
    ⊢ (¡ θ1)%R ≤ᵣ ρh -∗ (¡ θ2)%R ≤ᵣ ρh -∗
    sem_typed (("payload", (𝟙 + 𝟙)%T) :: ("k", (τ_sl -{ ρh }-[OS]-> 𝟙)%T) :: sim_env θ1 θ2)
      (let: "m'" := "sample_or_load" #()%V in
       ("doKeyLeakSnd" (bob));;
       let: "r" := "doKeyLeakRecv" (bob) in
       match: "r" with
       | NONE => "k" NONEV
       | SOME "x" =>
           match: !"message" with
           | NONE =>
               let: "mA" := g^"m'" in
               "message" <- SOME "m'";;
               ("doLeakASend" ("mA", bob));;
               "k" #()%V
           | SOME "m" => "k" #()%V
           end
       end)%E
      (let: "m'" := "sample_or_load" #()%V in
       ("doKeyLeakSnd" (bob));;
       let: "r" := "doKeyLeakRecv" (bob) in
       match: "r" with
       | NONE => "k" NONEV
       | SOME "x" =>
           match: !"message" with
           | NONE =>
               let: "mA" := g^"m'" in
               "message" <- SOME "m'";;
               ("doLeakASend" ("mA", bob));;
               "k" #()%V
           | SOME "m" => "k" #()%V
           end
       end)%E
      ρh 𝟙 (sim_env θ1 θ2).
  Proof using All.
    iIntros "#Hρ1 #Hρ2". rewrite /sim_env.
    (* The payload is not used. *)
    iApplyT sem_typed_sub_env; first iApply env_le_weaken.
    iApplyT sem_typed_let.
    { iApplyT sem_typed_app_fun_nil; [iApply row_le_nil|iApplyT sem_typed_unit'|].
      iApplyT sem_typed_sub_ty; [iApply ty_le_u2aarr|typed_var_copy]. }
    iApplyT sem_typed_seq.
    { iApplyT sem_typed_app_fun_nil; [iApply "Hρ2"|iApply (sem_typed_party true)|typed_leak_fun]. }
    iApplyT sem_typed_let.
    { iApplyT sem_typed_app_fun_nil; [iApply "Hρ2"|iApply (sem_typed_party true)|typed_leak_fun]. }
    iApplyT (sem_typed_match_split [] []).
    - typed_var.
    - iApply env_le_refl.
    - iApplyT sem_typed_sub_env; first iApply env_le_weaken.
      iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply sem_typed_sl_none|typed_cont].
    - iApply env_le_refl.
    - iApply env_le_refl.
    - iApplyT sem_typed_sub_env; first iApply env_le_weaken.
      iApplyT (sem_typed_match_split [] []).
      + iApplyT sem_typed_load_cpy. typed_var_copy.
      + iApply env_le_refl.
      + iApplyT sem_typed_let; first (iApplyT sem_typed_vexp; typed_var_copy).
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_store_cpy_gen.
          2: { iApplyT sem_typed_injr. typed_var_copy. }
          typed_var_copy. }
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_app_fun_nil; first iApply "Hρ1".
          - iApplyT sem_typed_pair; [iApply (sem_typed_party true)|typed_var].
          - typed_leak_fun. }
        iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply sem_typed_sl_unit|typed_cont].
      + simpl. iApply env_le_weaken.
      + iApply env_le_refl.
      + iApplyT sem_typed_sub_env; first iApply env_le_weaken.
        iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply sem_typed_sl_unit|typed_cont].
      + env_solve.
    - iApply env_le_refl.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma sim_lrecv_handler_typed (θ1 θ2 ρh : sem_row Σ) :
    ⊢ (¡ θ1)%R ≤ᵣ ρh -∗ (¡ θ2)%R ≤ᵣ ρh -∗
    sem_typed (("payload", (𝟙 + 𝟙)%T) :: ("k", (Option ℕ -{ ρh }-[OS]-> 𝟙)%T) :: sim_env θ1 θ2)
      (let: "r" := "doKeyLeakRecv" (alice) in
       match: "r" with
       | NONE => "k" NONEV
       | SOME "x" =>
           ("doKeyLeakSnd" alice);;
           match: !"m'_opt" with
           | NONE => "k" NONEV
           | SOME "_" =>
               let: "rla" := ("doLeakARecv" bob) in
               match: "rla" with
               | NONE => "k" NONEV
               | SOME "x" => "k" !"message"
               end
           end
       end)%E
      (let: "r" := "doKeyLeakRecv" (alice) in
       match: "r" with
       | NONE => "k" NONEV
       | SOME "x" =>
           ("doKeyLeakSnd" alice);;
           match: !"m'_opt" with
           | NONE => "k" NONEV
           | SOME "_" =>
               let: "rla" := ("doLeakARecv" bob) in
               match: "rla" with
               | NONE => "k" NONEV
               | SOME "x" => "k" !"message"
               end
           end
       end)%E
      ρh 𝟙 (sim_env θ1 θ2).
  Proof using All.
    iIntros "#Hρ1 #Hρ2". rewrite /sim_env.
    iApplyT sem_typed_sub_env; first iApply env_le_weaken.
    iApplyT sem_typed_let.
    { iApplyT sem_typed_app_fun_nil; [iApply "Hρ2"|iApply (sem_typed_party false)|typed_leak_fun]. }
    iApplyT (sem_typed_match_split [] []).
    - typed_var.
    - iApply env_le_refl.
    - iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|typed_cont].
    - iApply env_le_refl.
    - iApply env_le_refl.
    - iApplyT sem_typed_sub_env; first iApply env_le_weaken.
      iApplyT sem_typed_seq.
      { iApplyT sem_typed_app_fun_nil; [iApply "Hρ2"|iApply (sem_typed_party false)|typed_leak_fun]. }
      iApplyT (sem_typed_match_split [] []).
      + iApplyT sem_typed_load_cpy. typed_var_copy.
      + iApply env_le_refl.
      + iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|typed_cont].
      + iApply env_le_refl.
      + iApply env_le_refl.
      + iApplyT sem_typed_sub_env; first iApply env_le_weaken.
        iApplyT sem_typed_let.
        { iApplyT sem_typed_app_fun_nil; [iApply "Hρ1"|iApply (sem_typed_party true)|typed_leak_fun]. }
        iApplyT (sem_typed_match_split [] []).
        * typed_var.
        * iApply env_le_refl.
        * iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApplyT sem_typed_none|typed_cont].
        * iApply env_le_refl.
        * iApply env_le_refl.
        * iApplyT sem_typed_sub_env; first iApply env_le_weaken.
          iApplyT sem_typed_app_fun_nil; first iApply row_le_refl.
          -- iApplyT sem_typed_load_cpy. typed_var_copy.
          -- typed_cont.
        * iApply env_le_refl.
      + iApply env_le_refl.
    - iApply env_le_refl.
      Unshelve. all: solve_typed_side.
  Qed.

  Lemma CHAN_SIM_lazy_typed : ⊢ sem_typed [] CHAN_SIM_lazy CHAN_SIM_lazy ⊥ τ_CHAN_SIM [].
  Proof using All.
    iApply sem_typed_val. iApply sem_typed_Rclosure. iIntros (θ).
    iApply sem_val_typed_sub; first iApply (ty_le_mbang_elim OS).
    iApply sem_typed_closure; first done.
    iApply (sem_typed_oval _ [_]).
    iApply sem_typed_RLam. iIntros (θ1). iApply sem_typed_RLam. iIntros (θ2).
    iApplyT sem_oval_typed_afun. simpl.
    iApply sem_typed_swap_second.
    iApplyT sem_typed_pair_elim; first typed_var.
    iApplyT sem_typed_pair_elim; first typed_var.
    iApplyT sem_typed_pair_elim; first typed_var.
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    (* [sample_or_load] captures a copy of the cache. *)
    iApplyT sem_typed_let.
    { iApplyT (sem_typed_sub_env _ ([("m'_opt", _)] ++ [("m'_opt", _); ("message", _);
                                     ("doKeyLeakSnd", _); ("doKeyLeakRecv", _);
                                     ("doLeakASend", _); ("doLeakARecv", _); ("f", _)])).
      { simpl. env_solve. }
      iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_]).
      iApplyT sem_oval_typed_ufun. simpl.
      iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
      iApplyT (sem_typed_match_split [] []).
      - iApplyT sem_typed_load_cpy. typed_var_copy.
      - iApply env_le_refl.
      - iApplyT sem_typed_let.
        { rewrite /sample. iApplyT sem_typed_let; first iApplyT sem_typed_unit'.
          iApply sem_typed_rand_untaped. }
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_store_cpy_gen.
          2: { iApplyT sem_typed_injr. typed_var_copy. }
          typed_var_copy. }
        typed_var.
      - iApply env_le_refl.
      - iApply env_le_refl.
      - typed_var.
      - iApply env_le_refl. }
    iApply sem_typed_effect_gen. iIntros (ls1 ls2).
    iApply sem_typed_effect_gen. iIntros (lr1 lr2). simpl.
    iApplyT sem_typed_let.
    { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
      iApplyT sem_oval_typed_ufun.
      iApply (sem_typed_do_const OS _ (ls1, ls2) (𝟙 + 𝟙)%T τ_sl).
      iApply sem_typed_sub_nil. iApply sem_typed_var. }
    iApplyT sem_typed_let.
    { iApply sem_typed_sub_nil. iApply (sem_typed_oval _ []).
      iApplyT sem_oval_typed_ufun.
      iApplyT sem_typed_sub_row; first iApply row_le_cons_extend.
      iApply (sem_typed_do_const OS ⟨⟩%R (lr1, lr2) (𝟙 + 𝟙)%T (Option ℕ)%T).
      iApply sem_typed_sub_nil. iApply sem_typed_var. }
    iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
    iApplyT (sem_typed_sub_env _ (([("doLeakSecRecv", _); ("doLeakSecSend", _); ("f", _)] ++ sim_env θ1 θ2)
                                    ++ sim_env θ1 θ2)).
    { rewrite /sim_env. simpl. env_solve. }
    (* Outer handler: lrecv. *)
    iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option ℕ)%T).
    - (* Inner handler: lsend. *)
      iApplyT sem_typed_sub_row; first iApply row_le_swap_second.
      iApplyT (sem_typed_sub_env _ ([_; _; _] ++ sim_env θ1 θ2)); first iApply env_le_refl.
      iApplyT (sem_typed_deep_handler_OS (ls1, ls2) (λ _, 𝟙 + 𝟙)%T (λ _, τ_sl)).
      + (* The client call [f (doLeakSecSend, doLeakSecRecv)], at [¡θJ ∪ θ ≤ θJ ∪ θ]. *)
        iApplyT sem_typed_app_fun_nil.
        2: { iApplyT sem_typed_pair; typed_var. }
        2: { iApplyT sem_typed_sub_ty; last typed_var. iApply ty_le_row_forall_inst. }
        iApply row_le_trans; first iApplyT row_le_union'.
        * iApply row_le_mfbang_elim.
        * iApply row_le_refl.
        * row_le_submseteq.
      + iIntros (?). iApply sim_lsend_handler_typed; row_le_submseteq.
      + typed_var.
    - iIntros (?). iApply sim_lrecv_handler_typed; row_le_submseteq.
    - iApplyT sem_typed_sub_env_final; last typed_var. rewrite /sim_env. simpl. env_solve.
      Unshelve. all: solve_typed_side.
  Qed.

End chan_ideal_typing.

