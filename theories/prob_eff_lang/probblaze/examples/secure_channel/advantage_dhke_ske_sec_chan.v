(* DHKE composed with the one-message secure channel over a symmetric
   encryption scheme: [uc_composition] applied to the two standalone results

     dhke_realises  REAL_DHKE ≤_{ε_DDH} SIM_DHKE ∘f IDEAL_DHKE  (DH_KE/dhke_factory)
     adv_SKE        REAL_SKE  ≤_{ε_ENC} SIM_SKE  ∘f IDEAL_SKE   (secure_channel/advantage_ske_sec_chan)

   The composed real system runs the channel protocol [CHAN] in the hybrid
   world where the key exchange is [REAL_DHKE] and the authenticated channel
   is [F_OAUTH]; the simulator is the DHKE simulator plugged into the channel
   simulator; the ideal functionality is the ideal secure channel.  The bound
   is a DDH term plus an encryption term, each through its reduction applied
   to the environment closed under the other component.

   The composition theorem needs the ideal side typed; the typings of
   [F_CHAN] and [CHAN_SIM] are proved here (they follow
   [composition/sec_channel_ideal_typing] for the mask channel). *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze.typing Require Import types.
From clutch.prob_eff_lang.probblaze.typing Require interp.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory mode adequacy.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage comp_operators.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems uc_advantage uc_theorem.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_typed.
From clutch.prob_eff_lang.probblaze.examples Require Import fin_val_type ske ske_sec_chan_def ske_sec_chan_common ske_sec_chan_typing advantage_ske_sec_chan.
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_common dhke_typing.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def advantage_dhke.
From Stdlib Require Import Reals Psatz.

Import fingroup.
Import fingroup.fingroup.

#[local] Open Scope R_scope.
#[local] Open Scope factory_scope.
#[local] Set Default Proof Using "All".

(* ------------------------------------------------------------------ *)
(* The systems.                                                        *)
(* ------------------------------------------------------------------ *)

Section dhke_ske_systems.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.

  (* The real system: the channel protocol in the (REAL_DHKE, F_OAUTH)-hybrid world. *)
  Definition REAL_DHKE_SKE : val := ((REAL_DHKE ||ᵣ F_OAUTH) ∘f CHAN)%fac.
  (* The ideal functionality: the ideal secure channel. *)
  Definition IDEAL_DHKE_SKE : val := IDEAL_SKE ms.
  (* The simulator: the DHKE simulator plugged into the channel simulator. *)
  Definition SIM_DHKE_SKE : val := (SIM_DHKE ∘F SIM_SKE)%fac.
  (* The DDH reduction for an environment [A]: the DHKE reduction for the
     environment that runs [A] against the channel protocol. *)
  Definition RED_DHKE_SKE (A : val) : val :=
    RED_DHKE (λ: "v", A (("v" ||ᵣₚ F_OAUTH) ∘fₚ CHAN)%fac)%V.
  (* The encryption reduction for [A]: the channel reduction for the
     environment that runs [A] behind the DHKE simulator. *)
  Definition RED_SKE_DHKE (A : val) : val :=
    RED_SKE ms (λ: "v", A (SIM_DHKE ∘Fₚ "v")%fac)%V.

End dhke_ske_systems.

#[global] Arguments IDEAL_DHKE_SKE {mt} ms.
#[global] Arguments RED_SKE_DHKE {vg cg vgg mt} ms A.

(* ------------------------------------------------------------------ *)
(* Typing of the ideal side.                                           *)
(* ------------------------------------------------------------------ *)

Section dhke_ske_typing.
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

  Import valgroup_notation.
  Import typed_hint_modes.
  #[local] Existing Instance multi_ty_group.
  #[local] Existing Instance multi_ty_fvt.

  (* The leak-send of the ideal channel returns either [()] (the simulator)
     or [NONE] (the functionality's own handler); its result is discarded. *)
  Definition τ_sl : sem_ty Σ := (λ v1 v2, ⌜v1 = v2 ∧ (v1 = #()%V ∨ v1 = NONEV)⌝)%I.

  #[local] Instance multi_ty_sl : MultiT τ_sl.
  Proof. constructor. iIntros "!# %v1 %v2 %Hv". rewrite /sem_ty_mbang /=. by iModIntro. Qed.

  Lemma sem_typed_sl_unit Γ ρ : ⊢ sem_typed Γ #()%V #()%V ρ τ_sl Γ.
  Proof. iApply sem_typed_sub_nil. iApply sem_typed_val. iIntros "!>". iPureIntro. by split; [|left]. Qed.

  Lemma sem_typed_sl_none Γ ρ : ⊢ sem_typed Γ NONEV NONEV ρ τ_sl Γ.
  Proof. iApply sem_typed_sub_nil. iApply sem_typed_val. iIntros "!>". iPureIntro. by split; [|right]. Qed.

  (* The leak port of [F_CHAN]: the simulator answers the leak-receive with
     the ciphertext it chose. *)
  Definition fleak_ske (θ : sem_row Σ) : sem_ty Σ :=
    (((𝟙 + 𝟙) -{ θ }-> τ_sl) × ((𝟙 + 𝟙) -{ θ }-> Option Cph))%T.

  Definition τ_FCHAN_ske : sem_ty Σ :=
    (∀ᵣ θ, hdl (cli msg) θ ⊸ ∀ᵣ θJ, fleak_ske θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T.
  Definition τ_CHAN_SIM_ske : sem_ty Σ :=
    (∀ᵣ θ, (∀ᵣ θJ, fleak_ske θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙) ⊸ τ__f θ (oaleak cipher) leakI)%T.
  (* The interface of the composed system: a channel client, over the
     authenticated-channel leakage and the DHKE leakage. *)
  Definition τ_DHKE_SKE : sem_ty Σ := (∀ᵣ θ, hdl (cli msg) θ ⊸ τ__f θ (oaleak cipher) aleak)%T.

  (* ---------------------------------------------------------------- *)
  (* F_CHAN                                                             *)
  (* ---------------------------------------------------------------- *)

  Definition fchan_send_body : expr :=
      (match: ms.(fvt_of_int) "m" with
       | NONE => "k" #()%V
       | SOME "m" =>
           match: !"message" with
           | NONE => "message" <- SOME "m";; ("doLeakSend" alice);; "k" #()%V
           | SOME "x" => "k" #()%V
           end
       end)%E.

  Lemma fchan_send_handler_typed (θJ ρh : sem_row Σ) :
    ⊢ (¡ θJ)%R ≤ᵣ ρh -∗
    sem_typed [("m", ℕ); ("k", (𝟙 -{ ρh }-[OS]-> 𝟙)%T);
               ("message", Refᶜ (Option Msg)); ("doLeakSend", ((𝟙 + 𝟙) -{ θJ }-> τ_sl)%T)]
      fchan_send_body fchan_send_body
      ρh 𝟙 [("message", Refᶜ (Option Msg)); ("doLeakSend", ((𝟙 + 𝟙) -{ θJ }-> τ_sl)%T)].
  Proof using All.
    iIntros "#Hρ".
    iApplyT (sem_typed_match_split [] []).
    - iApplyT (sem_typed_fvt_of_int (msg := msg)). typed_var.
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

  Definition fchan_recv_body : expr :=
      (let: "r" := ("doLeakRecv" bob) in
       match: "r" with
       | NONE => "k" NONEV
       | SOME "x" => "k" (!"message")
       end)%E.

  Lemma fchan_recv_handler_typed (θJ ρh : sem_row Σ) :
    ⊢ (¡ θJ)%R ≤ᵣ ρh -∗
    sem_typed [("payload", (𝟙 + 𝟙)%T); ("k", (Option Msg -{ ρh }-[OS]-> 𝟙)%T);
               ("message", Refᶜ (Option Msg)); ("doLeakRecv", ((𝟙 + 𝟙) -{ θJ }-> Option Cph)%T)]
      fchan_recv_body fchan_recv_body
      ρh 𝟙 [("message", Refᶜ (Option Msg)); ("doLeakRecv", ((𝟙 + 𝟙) -{ θJ }-> Option Cph)%T)].
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

  (* The body of [F_CHAN] (free in "f", "LeakOp" and the hoisted
     "message"), copied verbatim from [ske_sec_chan_def.F_CHAN]. *)
  Definition F_CHAN_body : expr :=
    (let, ("doLeakSend", "doLeakRecv") := "LeakOp" in
     effect "ssend"
       effect "srecv"
       let: "doSecSend" := (λ: "m", do: "ssend" "m")  in
       let: "doSecRecv" := (λ: <>, do: "srecv" bob) in
       handle: handle: "f" ("doSecSend" ,"doSecRecv") with
     | effect "ssend" "m", rec "k" =>
         match: ms.(fvt_of_int) "m" with
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
    ⊢ sem_typed [("f", hdl (cli msg) θ); ("LeakOp", fleak_ske θJ); ("message", Refᶜ (Option Msg))]
        F_CHAN_body F_CHAN_body (sem_row_union (¡ θJ) θ) 𝟙 [].
  Proof using All.
    iApply sem_typed_swap_second.
    iApplyT sem_typed_pair_elim; first typed_var.
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
    (* The send handler keeps [message] and [doLeakSend]; the receive handler
       keeps [message] and [doLeakRecv]. *)
    iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
    iApplyT (sem_typed_sub_env _ ([("doSecRecv", _); ("doSecSend", _); ("f", _);
                                   ("message", _); ("doLeakSend", _)]
                                    ++ [("message", _); ("doLeakRecv", _)])).
    { simpl. env_solve. }
    (* Outer handler: srecv. *)
    iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option Msg)%T).
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

  Lemma F_CHAN_typed m : ⊢ ⊨ᵥ (F_CHAN ms) ≤ (F_CHAN ms) : fac m τ_FCHAN_ske.
  Proof using All.
    iApply fac_closure.
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApply (sem_typed_none Msg)).
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _]).
    iApply sem_typed_RLam. iIntros (θJ).
    iApplyT sem_oval_typed_afun. simpl.
    iApply sem_typed_swap_second. iApply F_CHAN_body_typed.
    Unshelve. all: solve_typed_side.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* CHAN_SIM                                                           *)
  (* ---------------------------------------------------------------- *)

  (* Context captured by both handlers of the simulator. *)
  Definition sim_env (θ1 θ2 : sem_row Σ) : env Σ :=
    [("doKeyLeakSnd", ((𝟙 + 𝟙) -{ θ2 }-> 𝟙)%T); ("doKeyLeakRecv", ((𝟙 + 𝟙) -{ θ2 }-> Option 𝟙)%T);
     ("doLeakASend", ((Cph × (𝟙 + 𝟙)) -{ θ1 }-> 𝟙)%T); ("doLeakARecv", ((𝟙 + 𝟙) -{ θ1 }-> Option 𝟙)%T);
     ("message", Refᶜ (Option Cph)); ("started", Refᶜ (Option 𝟙))].

  Definition sim_lsend_body : expr :=
      ("started" <- SOME #()%V ;;
       ("doKeyLeakSnd" (bob));;
       let: "r" := "doKeyLeakRecv" (bob) in
       match: "r" with
       | NONE => "k" NONEV
       | SOME "x" =>
           match: !"message" with
           | NONE =>
               let: "mA" := ske.(rand_cipher) #()%V in
               "message" <- SOME "mA";;
               ("doLeakASend" ("mA", bob));;
               "k" #()%V
           | SOME "m" => "k" #()%V
           end
       end)%E.

  Lemma sim_lsend_handler_typed (θ1 θ2 ρh : sem_row Σ) :
    ⊢ (¡ θ1)%R ≤ᵣ ρh -∗ (¡ θ2)%R ≤ᵣ ρh -∗
    sem_typed (("payload", (𝟙 + 𝟙)%T) :: ("k", (τ_sl -{ ρh }-[OS]-> 𝟙)%T) :: sim_env θ1 θ2)
      sim_lsend_body sim_lsend_body
      ρh 𝟙 (sim_env θ1 θ2).
  Proof using All.
    iIntros "#Hρ1 #Hρ2". rewrite /sim_env.
    (* The payload is not used. *)
    iApplyT sem_typed_sub_env; first iApply env_le_weaken.
    iApplyT sem_typed_seq.
    { iApplyT sem_typed_store_cpy_gen.
      2: { iApplyT sem_typed_injr. iApplyT sem_typed_unit'. }
      typed_var_copy. }
    iApplyT sem_typed_seq.
    { iApplyT sem_typed_app_fun_nil; [iApply "Hρ2"|iApply (sem_typed_party true)|typed_leak_fun]. }
    iApplyT sem_typed_let.
    { iApplyT sem_typed_app_fun_nil; [iApply "Hρ2"|iApply (sem_typed_party true)|typed_leak_fun]. }
    iApplyT (sem_typed_match_split [] []).
    - typed_var.
    - iApply env_le_refl.
    - iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply sem_typed_sl_none|typed_cont].
    - iApply env_le_refl.
    - iApply env_le_refl.
    - iApplyT sem_typed_sub_env; first iApply env_le_weaken.
      iApplyT (sem_typed_match_split [] []).
      + iApplyT sem_typed_load_cpy. typed_var_copy.
      + iApply env_le_refl.
      + iApplyT sem_typed_let; first iApply (sem_typed_rand_cipher (G := G) (SKE := SKE)).
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_store_cpy_gen.
          2: { iApplyT sem_typed_injr. typed_var_copy. }
          typed_var_copy. }
        iApplyT sem_typed_seq.
        { iApplyT sem_typed_app_fun_nil; first iApply "Hρ1".
          - iApplyT sem_typed_pair; [iApply (sem_typed_party true)|typed_var].
          - typed_leak_fun. }
        iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply sem_typed_sl_unit|typed_cont].
      + iApply env_le_refl.
      + iApply env_le_refl.
      + iApplyT sem_typed_sub_env; first iApply env_le_weaken.
        iApplyT sem_typed_app_fun_nil; [iApply row_le_refl|iApply sem_typed_sl_unit|typed_cont].
      + env_solve.
    - iApply env_le_refl.
      Unshelve. all: solve_typed_side.
  Qed.

  Definition sim_lrecv_body : expr :=
      (let: "r" := "doKeyLeakRecv" (alice) in
       match: "r" with
       | NONE => "k" NONEV
       | SOME "x" =>
           ("doKeyLeakSnd" alice);;
           match: !"started" with
           | NONE => "k" NONEV
           | SOME "s" =>
               let: "rla" := ("doLeakARecv" bob) in
               match: "rla" with
               | NONE => "k" NONEV
               | SOME "x" => "k" !"message"
               end
           end
       end)%E.

  Lemma sim_lrecv_handler_typed (θ1 θ2 ρh : sem_row Σ) :
    ⊢ (¡ θ1)%R ≤ᵣ ρh -∗ (¡ θ2)%R ≤ᵣ ρh -∗
    sem_typed (("payload", (𝟙 + 𝟙)%T) :: ("k", (Option Cph -{ ρh }-[OS]-> 𝟙)%T) :: sim_env θ1 θ2)
      sim_lrecv_body sim_lrecv_body
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

  Lemma CHAN_SIM_typed m : ⊢ ⊨ᵥ CHAN_SIM ≤ CHAN_SIM : fac m τ_CHAN_SIM_ske.
  Proof using All.
    iApply fac_closure.
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApply (sem_typed_none Cph)).
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApply (sem_typed_none 𝟙)).
    (* The state is captured by the client-taking closures *)
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_afun.
    iApply (sem_typed_oval _ [_; _; _]).
    iApply sem_typed_RLam. iIntros (θ1). iApply sem_typed_RLam. iIntros (θ2).
    iApplyT sem_oval_typed_afun. simpl.
    iApply sem_typed_swap_second.
    iApplyT sem_typed_pair_elim; first typed_var.
    iApplyT sem_typed_pair_elim; first typed_var.
    iApplyT sem_typed_pair_elim; first typed_var.
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
      iApply (sem_typed_do_const OS ⟨⟩%R (lr1, lr2) (𝟙 + 𝟙)%T (Option Cph)%T).
      iApply sem_typed_sub_nil. iApply sem_typed_var. }
    iApplyT sem_typed_sub_env_final; first iApply env_le_nil.
    iApplyT (sem_typed_sub_env _ (([("doLeakSecRecv", _); ("doLeakSecSend", _); ("f", _)] ++ sim_env θ1 θ2)
                                    ++ sim_env θ1 θ2)).
    { rewrite /sim_env. simpl. env_solve. }
    (* Outer handler: lrecv. *)
    iApplyT (sem_typed_deep_handler_OS (lr1, lr2) (λ _, 𝟙 + 𝟙)%T (λ _, Option Cph)%T).
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

  (* ---------------------------------------------------------------- *)
  (* The factories.                                                     *)
  (* ---------------------------------------------------------------- *)


  Lemma REAL_DHKE_SKE_typed_f m : ⊢ ⊨ᵥ REAL_DHKE_SKE ≤ REAL_DHKE_SKE : fac m τ_DHKE_SKE.
  Proof using All.
    rewrite /τ_DHKE_SKE.
    iApply (func_comp_f_typed_gen m _ _ _ _ (λ θ, hdl (cli msg) θ) (λ θ, τ__f θ (cchan cipher) gk) (λ θ, τ__f θ (oaleak cipher) aleak)).
    { intros θ. apply eta_ty_τf. }
    { iApply parallel_comp_f_typed; [|iApply (F_OAUTH_typed (G := G) (SKE := SKE))].
      iApply func_comp_f_typed; [iApply (F_AUTH_typed (G := G))|iApply (DH_KE_typed (G := G))]. }
    iApply (CHAN_typed (G := G) (SKE := SKE)).
  Qed.

  Lemma SIM_DHKE_SKE_IDEAL_typed_f m :
    ⊢ ⊨ᵥ (SIM_DHKE_SKE ∘f (IDEAL_DHKE_SKE ms)) ≤ (SIM_DHKE_SKE ∘f (IDEAL_DHKE_SKE ms)) : fac m τ_DHKE_SKE.
  Proof using All.
    rewrite /τ_DHKE_SKE.
    iApply (func_comp_f_typed_gen m _ _ _ _ (λ θ, hdl (cli msg) θ)
              (λ θ, ∀ᵣ θJ, fleak_ske θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T (λ θ, τ__f θ (oaleak cipher) aleak)).
    { intros θ. apply eta_ty_row_forall => θJ. apply eta_ty_arr. }
    { iApply functionality_comp_f_typed; [iApply (SIM_DHKE_typed_f (G := G))|iApply CHAN_SIM_typed]. }
    iApply F_CHAN_typed.
  Qed.

End dhke_ske_typing.

#[global] Arguments fleak_ske {Σ H ct cs} cipher θ.
#[global] Arguments τ_FCHAN_ske {Σ H mt ct ms cs} msg cipher.
#[global] Arguments τ_CHAN_SIM_ske {Σ H ct cs} cipher.
#[global] Arguments τ_DHKE_SKE {Σ H vg mt ct ms cs} msg cipher.

(* ------------------------------------------------------------------ *)
(* The advantage bound, by UC composition.                             *)
(* ------------------------------------------------------------------ *)

Section dhke_ske_advantage.
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context {vgg : @val_group_generator vg}.
  Context `{probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {mt ct : fin_val_type}.
  Context {ms : @fin_val_type_struct mt} {cs : @fin_val_type_struct ct}.
  Context {ske : @SYM_struct vg_fvt vg_fvts mt ms ct cs}.
  Context {msg : ∀ `(!probblazeRGS Σ), @fin_val Σ _ mt ms} {cipher : ∀ `(!probblazeRGS Σ), @fin_val Σ _ ct cs}.
  Context {SKE : ∀ `{H : !probblazeRGS Σ}, @SYM Σ _ vg_fvt mt ct vg_fvts ms cs (vg_fv (Σ := Σ) (H := H)) (msg H) (cipher H) ske}.

  Import valgroup_notation.

  Theorem dhke_ske_realises (m : mode) (A : val) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m (τ_DHKE_SKE (msg _) (cipher _)) → 𝔹)%T) →
    advantage A REAL_DHKE_SKE (SIM_DHKE_SKE ∘f (IDEAL_DHKE_SKE ms)) #true <=
      advantage (RED_DHKE_SKE A) DH_real DH_rand #true
      + advantage ((RED_SKE_DHKE ms) A) (enc_real ske) (enc_ideal ske) #true.
  Proof using All.
    intros HA.
    rewrite /REAL_DHKE_SKE /SIM_DHKE_SKE /IDEAL_DHKE_SKE /RED_DHKE_SKE /RED_SKE_DHKE /SIM_SKE /IDEAL_SKE.
    apply (uc_composition m REAL_DHKE SIM_DHKE IDEAL_DHKE F_OAUTH CHAN CHAN_SIM (F_CHAN ms) true
             (λ A', advantage (RED_DHKE A') DH_real DH_rand #true)
             (λ A', advantage (RED_SKE ms A') (enc_real ske) (enc_ideal ske) #true)
             (λ H : probblazeRGS Σ, hdl (cli (msg H))) (λ H : probblazeRGS Σ, (cchan (cipher H)))
             (λ H : probblazeRGS Σ, gk) (λ H : probblazeRGS Σ, (oaleak (cipher H)))
             (λ H : probblazeRGS Σ, leakI) (λ H : probblazeRGS Σ, aleak)
             (λ H : probblazeRGS Σ, (fleak_ske (cipher H)))).
    + intros HRGS. iApply (SIM_DHKE_typed_f (G := G _ _)).
    + intros HRGS. iApply (F_KE_lazy_alice_typed (G := G _ _)).
    + intros HRGS. iApply (F_OAUTH_typed (G := G _ _) (SKE := SKE _)).
    + intros HRGS. iApply (CHAN_typed (G := G _ _) (SKE := SKE _)).
    + intros HRGS. iApply (CHAN_SIM_typed (G := G _ _) (SKE := SKE _)).
    + intros HRGS. iApply (F_CHAN_typed (G := G _ _) (SKE := SKE _)).
    + intros A' HA'. by apply (dhke_realises (G := G) m).
    + intros A' HA'. by apply (adv_SKE (G := G) (ske := ske) (SKE := SKE) m).
    + exact HA.
  Qed.

  (** Syntactically typed environments *)

  (* [τ_DHKE_SKE], syntactically. *)
  Definition T_DHKE_SKE : type :=
    (∀R:
      (∀R: ((ℕ -{ RVar 0%nat }-> ()) * (() -{ RVar 0%nat }-> (() + ms.(τFT))))
             -{ RVar 0%nat ∪ᵣ RVar 1%nat }-∘ ()) -∘
      (∀R: ∀R: ((((cs.(τFT) * (() + ())) -{ RVar 1%nat }-> ()) * ((() + ()) -{ RVar 1%nat }-> (() + ())))
                 * (((τG * (() + ())) -{ RVar 0%nat }-> ()) * ((() + ()) -{ RVar 0%nat }-> (() + ℕ))))
             -{ (RFlip OS (RVar 1%nat)) ∪ᵣ ((RFlip OS (RVar 0%nat)) ∪ᵣ RVar 2%nat) }-∘ ()))%ty.

  Lemma T_DHKE_SKE_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ τ_DHKE_SKE (msg _) (cipher _) ≤ₜ interp.interp._ty η μ δ T_DHKE_SKE ξ.
  Proof using G msg cipher.
    rewrite /T_DHKE_SKE /τ_DHKE_SKE /hdl /cli /τ__f /oaleak /aleak /sem_ty_option /=.
    iApply ty_le_row_forall; iIntros (θL).
    iApply ty_le_arr; first iApply row_le_refl.
    - (* the client: its receive returns a message *)
      iApply ty_le_row_forall; iIntros (θh).
      iApply ty_le_arr; [iApply row_le_refl | | iApply ty_le_refl].
      iApply ty_le_prod; first iApply ty_le_refl.
      iApply ty_le_mbang_comp; first iApply mode_le_refl.
      iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|].
      iApply ty_le_sum; first iApply ty_le_refl.
      iIntros (??) "!#". iApply (τFT_subtype (fin_val := msg _)).
    - (* the leaks: the channel's takes a ciphertext, the key exchange's a group element *)
      iApply ty_le_row_forall; iIntros (θ1). iApply ty_le_row_forall; iIntros (θ2).
      iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
      iApply ty_le_prod; (iApply ty_le_prod; last iApply ty_le_refl);
        (iApply ty_le_mbang_comp; first iApply mode_le_refl);
        (iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl]);
        (iApply ty_le_prod; last iApply ty_le_refl);
        iIntros (??) "!#"; [iApply (τFT_subtype (fin_val := cipher _))|iApply τG_subtype].
  Qed.

  Corollary dhke_ske_realises_typed A :
    ⊢ᵥ A : ((() -∘ T_DHKE_SKE) ⇾ TBool)%ty →
    advantage A REAL_DHKE_SKE (SIM_DHKE_SKE ∘f (IDEAL_DHKE_SKE ms)) #true <=
      advantage (RED_DHKE_SKE A) DH_real DH_rand #true
      + advantage ((RED_SKE_DHKE ms) A) (enc_real ske) (enc_ideal ske) #true.
  Proof using All.
    intros HA. apply (dhke_ske_realises OS), (typed_env_fac A T_DHKE_SKE (λ _, τ_DHKE_SKE (msg _) (cipher _))); last done.
    intros. apply T_DHKE_SKE_subtype.
  Qed.

End dhke_ske_advantage.
