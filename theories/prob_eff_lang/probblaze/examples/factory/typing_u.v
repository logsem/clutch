(* Unrestricted typings ([→] client arrow) of the components that so far had
   only one-shot typings: [DH_SIM] (one-shot in [dhke_typing]) and [F_CHAN],
   [CHAN_SIM_lazy] (one-shot in [chan_ideal_typing]).  Each proof is the
   one-shot one with the client binder typed by [sem_oval_typed_ufun]: all
   state captured by the client-taking closure (tapes and copyable
   references) is copyable.  Also [F_AUTH ∘f DH_SIM] at [τ__Fu]. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import comp_operators primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory logic.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.examples Require Import
  sec_channel_def dhke_common dhke_typing mask new_composition_typing chan_ideal_typing.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_tactics.

Section dh_sim_typing_u.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  Import valgroup_notation.
  Import typed_hint_modes.
  #[local] Existing Instance multi_ty_group.

  Lemma DH_SIM_typed_u : ⊢ sem_typed [] DH_SIM DH_SIM ⊥ (τ__Fu chan leakI) [].
  Proof using All.
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloctape; iApplyT sem_typed_int').
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloctape; iApplyT sem_typed_int').
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _; _; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_ufun.
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

  Lemma F_AUTH_DH_SIM_typed_u :
    ⊢ sem_typed [] (F_AUTH ∘f DH_SIM) (F_AUTH ∘f DH_SIM) ⊥ (τ__Fu aleak leakI) [].
  Proof using All.
    iApplyT sem_typed_app_nil; last iApply DH_SIM_typed_u.
    iApplyT sem_typed_app_nil; last iApply F_AUTH_typed_u.
    iApply sem_typed_val. iApply func_comp_val_typed_u.
  Qed.

End dh_sim_typing_u.

Section chan_ideal_typing_u.
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

  Definition τ_FCHAN_u : sem_ty Σ :=
    (∀ᵣ θ, hdl cli θ → ∀ᵣ θJ, fleak θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T.
  Definition τ_CHAN_SIM_u : sem_ty Σ :=
    (∀ᵣ θ, (∀ᵣ θJ, fleak θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙) → τ__f θ oaleak leakI)%T.

  Lemma F_CHAN_typed_u : ⊢ sem_typed [] F_CHAN F_CHAN ⊥ τ_FCHAN_u [].
  Proof using All.
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_ufun.
    iApply (sem_typed_oval _ [_; _]).
    iApply sem_typed_RLam. iIntros (θJ).
    iApplyT sem_oval_typed_afun. simpl.
    iApply sem_typed_swap_second. iApply F_CHAN_body_typed.
    Unshelve. all: solve_typed_side.
  Qed.

  Lemma CHAN_SIM_lazy_typed_u : ⊢ sem_typed [] CHAN_SIM_lazy CHAN_SIM_lazy ⊥ τ_CHAN_SIM_u [].
  Proof using All.
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    iApplyT sem_typed_let; first (iApplyT sem_typed_alloc_cpy; iApplyT sem_typed_none).
    (* [sample_or_load] captures a copy of the cache. *)
    iApplyT sem_typed_let.
    { iApplyT (sem_typed_sub_env _ ([("m'_opt", _)] ++ [("m'_opt", _); ("message", _)])).
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
    (* The state is captured by the client-taking closures *)
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_; _; _]). iApply sem_typed_RLam. iIntros (θ).
    iApplyT sem_oval_typed_ufun.
    iApply (sem_typed_oval _ [_; _; _; _]).
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

End chan_ideal_typing_u.
