From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import comp_operators primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory.
From clutch.prob_eff_lang.probblaze Require Import sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_common ske ske_sec_chan_common
  ske_composition_defs.
From clutch.prob_eff_lang.probblaze.examples Require Export ske_typing dhke_typing.

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
  #[local] Existing Instance dhke_typing.multi_ty_group.

  (* [chan], [aleak], [leakI] and [gk], and the typings of [F_AUTH],
     [DH_SIM] and [C_lazy], come from [dhke_typing]. *)

  (* [F_AUTH ∘f DH_SIM]. *)
  Lemma F_AUTH_DH_SIM_FO_typed :
    ⊢ sem_typed [] (F_AUTH ∘f DH_SIM) (F_AUTH ∘f DH_SIM) ⊥ (τ__F aleak leakI) [].
  Proof using All.
    iApply func_comp_OS_typed; [iApply F_AUTH_typed|iApply DH_SIM_typed].
  Qed.

  Section reduction.
    Import typed_hint_modes.
    #[local] Existing Instance multi_ty_group.
    #[local] Existing Instance multi_ty_fvt.

    Lemma functionality_comp_val_typed (τ1' τ1 τF τ2 : sem_row Σ → sem_ty Σ) :
      ⊢ ⊨ᵥ functionality_composition ≤ functionality_composition :
        (τ__F τ2 τF ⊸ (∀ᵣ θ, τ1' θ ⊸ τ__f θ τ1 τF) ⊸ ∀ᵣ θ, τ1' θ ⊸ τ__f θ τ1 τ2)%T.
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
                rewrite /τ__f. iApply ty_le_trans; first iApply (ty_le_row_forall_inst _ θ1).
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

    Lemma DHSIM_FKE_RED_typed :
      ⊢ sem_typed [] (DHSIM_FKE_RED (mt := mt) (ms := ms)) (DHSIM_FKE_RED (mt := mt) (ms := ms)) ⊥ ((𝟙 ⊸ (Msg -{ ⊥ }-> Cph)) → τ)%T [].
    Proof using All.
      iApply (sem_typed_oval _ [] []). iApplyT sem_oval_typed_ufun.
      iApply DHSIM_FKE_RED_unfolded_typed.
      Unshelve. all: solve_typed_side.
    Qed.

  End reduction.

  Section real_chan.
    Import typed_hint_modes.

    Lemma REAL_CHAN_DH_RED_unfolded_typed :
      ⊢ sem_typed ((BNamed "DH", (𝟙 ⊸ (sem_ty_group × sem_ty_group) × sem_ty_group)) ::? []) (((F_AUTH ∘f (C_lazy "DH")) ||ᵣ F_OAUTH) ∘f CHAN)%E (((F_AUTH ∘f (C_lazy "DH")) ||ᵣ F_OAUTH) ∘f CHAN)%E  ⊥ τ [].
    Proof using All.
      (* [G ∘f CHAN] with [G := (F_AUTH ∘f C) ||ᵣ F_OAUTH]; arguments first. *)
      iApplyT sem_typed_app_nil; last first.
      { iApply (sem_typed_frame_env_gen _ [_]). iApply (CHAN_typed (SKE := SKE)). }
      iApplyT sem_typed_app_nil; last first.
      - iApplyT sem_typed_app_nil; last first.
        { iApply (sem_typed_frame_env_gen _ [_]). iApply (F_OAUTH_typed (SKE := SKE)). }
        iApplyT sem_typed_app_nil; last first.
        + (* [F_AUTH ∘f C], with [C := λ: "f", C_lazy "DH" "f"]. *)
          iApplyT sem_typed_app_nil; last first.
          * iApplyT sem_typed_app_nil; last typed_var. simpl.
            iApplyT sem_typed_sub_ty.
            2: { iApply sem_typed_val. iApply C_lazy_val_typed. }
            iApply ty_le_mbang_elim.
          * iApplyT sem_typed_app_nil; last iApply F_AUTH_typed.
            iApply sem_typed_val. iApply func_comp_val_typed.
        + iApply sem_typed_val. iApply right_comp_val_typed.
      - iApply sem_typed_val. iApply func_comp_val_typed.
        Unshelve. all: solve_typed_side.
    Qed.

    Lemma REAL_CHAN_DH_RED_typed :
      ⊢ sem_typed [] REAL_CHAN_DH_RED REAL_CHAN_DH_RED ⊥ ((𝟙 ⊸ (sem_ty_group × sem_ty_group) × sem_ty_group) → τ)%T [].
    Proof using All.
      iApply (sem_typed_oval _ [] []). iApplyT sem_oval_typed_ufun.
      iApply REAL_CHAN_DH_RED_unfolded_typed.
      Unshelve. all: solve_typed_side.
    Qed.


  End real_chan.

End ske_comp_verification.
