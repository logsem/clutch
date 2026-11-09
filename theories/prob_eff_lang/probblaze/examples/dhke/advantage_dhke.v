(* Diffie-Hellman key exchange as factories (uc/DESIGN.md).

   The systems are the factories of [def_dhke]:
     F_AUTH          the authenticated channel
     DH_KE           the protocol, in the F_AUTH-hybrid world
     DH_SIM          the simulator
     F_KE_lazy_alice the ideal key-exchange functionality
     C_lazy d        the DDH reduction, for a DDH oracle [d]
   and the standalone result is, at both modes [m],

     advantage A (F_AUTH ∘f DH_KE) (F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice))
       ≤ advantage (λ d, A (F_AUTH ∘f C_lazy d)) DH_real DH_rand

   for environments [A : fac m (τ__F aleak gk) → 𝔹].  At [m = OS] the DDH
   term is single-instance DDH; at [m = MS] the reduction calls [d] once per
   instance, i.e. multi-instance DDH.

   The two perfect steps are proved directly on the factories from the
   per-component core lemmas of [dhke_channel_lazy_*]; the DDH step is the
   β-reduction [advantage_reduction_ctx].  [dhke_realises] puts the
   simulator in the shape [(F_AUTH ∘f DH_SIM) ∘f F_KE_lazy_alice] wanted by
   the composition theorem. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze.uc Require Import comp_operators.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory logic mode adequacy.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems uc_advantage uc_theorem.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import
  dhke_real
  dhke_sim
  dhke_authchan.
(* After the core lemmas: their files define a [chan] row that would shadow
   the interface type [dhke_typing.chan]. *)
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_common dhke_typing.
From Stdlib Require Import Reals Psatz.

Import fingroup.
Import fingroup.fingroup.

#[local] Open Scope R_scope.
#[local] Open Scope factory_scope.
#[local] Set Default Proof Using "All".

(* ------------------------------------------------------------------ *)
(* ------------------------------------------------------------------ *)
(* Typing.                                                             *)
(* ------------------------------------------------------------------ *)

Section dhke_typing_f.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  Import valgroup_notation.
  Import typed_hint_modes.
  #[local] Notation n := (S n'').

  (* The session body of [DH_KE]: its setup, then the core. *)
  Lemma sem_val_typed_mbang (m : mode) (v1 v2 : val) (τ : sem_ty Σ) :
    ⊢ ⊨ᵥ v1 ≤ v2 : τ -∗ ⊨ᵥ v1 ≤ v2 : (![m] τ)%T.
  Proof.
    rewrite /sem_val_typed /tc_opaque /sem_ty_mbang /=. iIntros "#H !#".
    destruct m; simpl; [iApply "H"|iModIntro; iApply "H"].
  Qed.

  (* The composite systems. *)
  Lemma SIM_DHKE_typed_f m : ⊢ ⊨ᵥ SIM_DHKE ≤ SIM_DHKE : fac m (τ__F aleak leakI).
  Proof using All. iApply func_comp_f_typed; [iApply F_AUTH_typed|iApply DH_SIM_typed]. Qed.

  (* The DDH oracles, as thunks of either mode. *)
  Lemma DH_real_typed_f m : ⊢ ⊨ᵥ DH_real ≤ DH_real : (𝟙 -{ ⟨⟩ }-[ m ]-> (𝔾 × 𝔾 × 𝔾))%T.
  Proof using All. iApply sem_val_typed_mbang. iApply DH_real_self. Qed.
  Lemma DH_rand_typed_f m : ⊢ ⊨ᵥ DH_rand ≤ DH_rand : (𝟙 -{ ⟨⟩ }-[ m ]-> (𝔾 × 𝔾 × 𝔾))%T.
  Proof using All. iApply sem_val_typed_mbang. iApply DH_rand_self. Qed.

  (* The reduction: a DDH oracle of mode [m] gives a factory of mode [m]. *)
  Lemma C_lazy_typed_f m :
    ⊢ ⊨ᵥ C_lazy ≤ C_lazy : ((𝟙 -{ ⟨⟩ }-[ m ]-> (𝔾 × 𝔾 × 𝔾)) → fac m (τ__F chan gk))%T.
  Proof using All.
    rewrite /C_lazy. iApply (sem_typed_closure _ _ _ BAnon "DH" _ _ MS); first done. simpl.
    iApply sem_typed_sub_nil. iApply (sem_typed_oval _ [_]).
    destruct m.
    - iApplyT (sem_oval_typed_afun 𝟙%T ⟨⟩%R _ BAnon). simpl.
      iApplyT sem_typed_app_nil; last first.
      { iApplyT sem_typed_sub_ty; [iApply ty_le_mbang_elim|typed_var]. }
      iApply sem_typed_val. iApply sem_val_typed_sub; [iApply (ty_le_mbang_elim MS)|iApply C_lazy_val_typed].
    - iApplyT (sem_oval_typed_ufun 𝟙%T ⟨⟩%R _ _ BAnon BAnon). simpl.
      iApplyT sem_typed_app_nil; last first.
      { iApplyT sem_typed_sub_ty; [iApply ty_le_mbang_elim|typed_var]. }
      iApply sem_typed_val. iApply sem_val_typed_sub; [iApply (ty_le_mbang_elim MS)|iApply C_lazy_val_typed].
    Unshelve. all: solve_typed_side.
  Qed.

  (* The reduction environment is an environment for the DDH oracles. *)
  Lemma RED_DHKE_typed m (A : val) :
    ⊢ sem_val_typed A A (fac m (τ__F aleak gk) → 𝔹)%T -∗
      sem_val_typed (RED_DHKE A) (RED_DHKE A) ((𝟙 -{ ⟨⟩ }-[ m ]-> (𝔾 × 𝔾 × 𝔾)) → 𝔹)%T.
  Proof using All.
    iIntros "#HA". rewrite /RED_DHKE.
    change (F_AUTH ∘fₚ (C_lazy "v"))%fac with (fill [AppRCtx (fac_app func_comp F_AUTH); AppRCtx C_lazy] "v").
    iApply ctx_adv_typed; first iApply "HA". simpl.
    iApplyT sem_typed_app_nil; last first.
    { iApplyT sem_typed_app_nil; last typed_var.
      iApply sem_typed_val. iApply sem_val_typed_sub; [iApply (ty_le_mbang_elim MS)|iApply C_lazy_typed_f]. }
    iApplyT sem_typed_app_nil; last (iApply sem_typed_val; iApply F_AUTH_typed).
    iApply sem_typed_val. iApply func_comp_app_typed.
    Unshelve. all: solve_typed_side.
  Qed.

End dhke_typing_f.

(* [C_lazy d] evaluates to the factory [λ: <>, C_lazy_sess d]. *)
Section pure.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.

  Lemma C_lazy_pure (d : val) : rtc pure_step (C_lazy d) (λ: <>, C_lazy_sess d)%V.
  Proof.
    rewrite /C_lazy.
    eapply rtc_l.
    { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
    simpl.
    eapply rtc_l.
    { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
    done.
  Qed.

  (* The reduction context applied to an oracle evaluates to a composite. *)
  Lemma RED_pure (d : val) :
    rtc pure_step (fill [AppRCtx (fac_app func_comp F_AUTH); AppRCtx C_lazy] d)
      (F_AUTH ∘f (λ: <>, C_lazy_sess d)%V)%fac.
  Proof.
    etrans.
    { apply (rtc_congruence (R := pure_step) (fill [AppRCtx (fac_app func_comp F_AUTH)]) pure_step
               (C_lazy d) (λ: <>, C_lazy_sess d)%V).
      - intros ???. by apply (@language.pure_step_ctx _ _
          (fill_ctx_no_handler [AppRCtx (fac_app func_comp F_AUTH)] eq_refl)).
      - apply C_lazy_pure. }
    apply fac_app_pure.
  Qed.

End pure.

(* ------------------------------------------------------------------ *)
(* The perfect steps, directly on the factories.                       *)
(* ------------------------------------------------------------------ *)

Section dhke_relations_f.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.

  Import valgroup_notation.
  Import valgroup_tactics.
  #[local] Notation n := (S n'').

  (* Calling the composite factory: the operator's thunk, then the leaves
     in evaluation order.  The per-component core lemmas then apply to the
     session bodies.  The client-taking function of the result is
     unrestricted ([τ_DH]); [τ__F aleak gk] follows by subtyping. *)

  Lemma F_AUTH_DH_KE_C_DH_real_f m :
    ⊢ sem_typed [] (F_AUTH ∘f DH_KE) (F_AUTH ∘f C_DH_real) ⊥ (fac m τ_DH) [].
  Proof using All.
    iApply sem_typed_sub_ty; first iApply fac_MS_le.
    iIntros (vs) "!# _". simpl.
    iApply brel_value. iIntros "$ !>". iSplit; last done.
    rewrite /fac /sem_ty_mbang /sem_ty_arr /=. iModIntro.
    iIntros (u1 u2) "[-> ->]".
    brel_pures_l 1%nat. brel_pures_r 1%nat.
    iMod token_alloc as (γtoka) "Htoka".
    iMod token_alloc as (γtokb) "Htokb".
    iMod message_alloc as (γautha) "Hautha".
    iMod message_alloc as (γauthb) "Hauthb".
    iMod all_receipts_alloc as (γfraca) "Hfraca".
    iMod all_receipts_alloc as (γfracb) "Hfracb".
    iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[] [Htoka Htokb Hautha Hauthb]");
      [iApply to_iThy_le_bot|iApply (DH_KE_C_DH_real _ _ γfraca γfracb with "Htoka Htokb Hautha Hauthb")|simpl].
    iIntros (D1 D2) "#HD".
    iApply (brel_bind [AppLCtx _; AppRCtx _] [AppLCtx _; AppRCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[] [Hfraca Hfracb]");
      [iApply to_iThy_le_bot
      |iApply (F_AUTH_F_AUTH_new γtoka γtokb γfraca γfracb (P_at eq_logic.Fwd γautha) (P'_at eq_logic.Fwd γauthb) with "Hfraca Hfracb")
      |simpl].
    iIntros (F1 F2) "#HF".
    rewrite /func_comp. brel_pures'.
    iIntros "!>" (L). rewrite /sem_ty_mbang /=. iIntros "!#" (f1 f2) "Hff".
    brel_pures_l 1%nat. brel_pures_r 1%nat.
    iApply "HF".
    brel_pures'.
    iModIntro.
    iIntros (????).
    brel_pures'.
    iApply (brel_bind [AppLCtx _] [AppLCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HD Hff]"); [iApply to_iThy_le_bot|by iApply "HD"|simpl].
    iIntros (??) "H". iApply "H".
  Qed.

  Lemma F_AUTH_C_DH_real_DH_KE_f m :
    ⊢ sem_typed [] (F_AUTH ∘f C_DH_real) (F_AUTH ∘f DH_KE) ⊥ (fac m τ_DH) [].
  Proof using All.
    iApply sem_typed_sub_ty; first iApply fac_MS_le.
    iIntros (vs) "!# _". simpl.
    iApply brel_value. iIntros "$ !>". iSplit; last done.
    rewrite /fac /sem_ty_mbang /sem_ty_arr /=. iModIntro.
    iIntros (u1 u2) "[-> ->]".
    brel_pures_l 1%nat. brel_pures_r 1%nat.
    iMod token_alloc as (γtoka) "Htoka".
    iMod token_alloc as (γtokb) "Htokb".
    iMod message_alloc as (γautha) "Hautha".
    iMod message_alloc as (γauthb) "Hauthb".
    iMod all_receipts_alloc as (γfraca) "Hfraca".
    iMod all_receipts_alloc as (γfracb) "Hfracb".
    iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[] [Htoka Htokb Hautha Hauthb]");
      [iApply to_iThy_le_bot|iApply (C_DH_real_DH_KE _ _ γfraca γfracb with "Htoka Htokb Hautha Hauthb")|simpl].
    iIntros (D1 D2) "#HD".
    iApply (brel_bind [AppLCtx _; AppRCtx _] [AppLCtx _; AppRCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[] [Hfraca Hfracb]");
      [iApply to_iThy_le_bot
      |iApply (F_AUTH_F_AUTH_new γtoka γtokb γfraca γfracb (P_at eq_logic.Bwd γautha) (P'_at eq_logic.Bwd γauthb) with "Hfraca Hfracb")
      |simpl].
    iIntros (F1 F2) "#HF".
    rewrite /func_comp. brel_pures'.
    iIntros "!>" (L). rewrite /sem_ty_mbang /=. iIntros "!#" (f1 f2) "Hff".
    brel_pures_l 1%nat. brel_pures_r 1%nat.
    iApply "HF".
    brel_pures'.
    iModIntro.
    iIntros (????).
    brel_pures'.
    iApply (brel_bind [AppLCtx _] [AppLCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HD Hff]"); [iApply to_iThy_le_bot|by iApply "HD"|simpl].
    iIntros (??) "H". iApply "H".
  Qed.

  (* On the ideal side the inner composite [DH_SIM ∘f F_KE_lazy_alice] is a
     thunk whose call runs [F_KE_lazy_alice] first; the simulator's own
     thunk call is still pending when the core lemma is applied, which is
     what its [D1] argument is for. *)
  Lemma F_AUTH_DH_SIM_F_KE_C_DH_rand_f m :
    ⊢ sem_typed [] (F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)) (F_AUTH ∘f C_DH_rand) ⊥ (fac m τ_DH) [].
  Proof using All.
    iApply sem_typed_sub_ty; first iApply fac_MS_le.
    iIntros (vs) "!# _". simpl.
    iApply brel_value. iIntros "$ !>". iSplit; last done.
    rewrite /fac /sem_ty_mbang /sem_ty_arr /=. iModIntro.
    iIntros (u1 u2) "[-> ->]".
    brel_pures_l 2%nat. brel_pures_r 1%nat.
    iMod token_alloc as (γtoka) "Htoka".
    iMod token_alloc as (γtokb) "Htokb".
    iMod message_alloc as (γautha) "Hautha".
    iMod message_alloc as (γauthb) "Hauthb".
    iMod all_receipts_alloc as (γfraca) "Hfraca".
    iMod all_receipts_alloc as (γfracb) "Hfracb".
    iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[] [Htoka Htokb Hautha Hauthb]");
      [iApply to_iThy_le_bot
      |iApply (DH_SIM_F_KE_C_DH_rand _ _ γfraca γfracb _ _ _ (rtc_refl _ _) with "Htoka Htokb Hautha Hauthb")
      |simpl].
    iIntros (D1 D2) "#HD".
    iApply (brel_bind [AppLCtx _; AppRCtx _] [AppLCtx _; AppRCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[] [Hfraca Hfracb]");
      [iApply to_iThy_le_bot
      |iApply (F_AUTH_F_AUTH_new γtoka γtokb γfraca γfracb (Psim_at eq_logic.Fwd γautha) (Psim_at eq_logic.Fwd γauthb) with "Hfraca Hfracb")
      |simpl].
    iIntros (F1 F2) "#HF".
    rewrite /func_comp. brel_pures'.
    iIntros "!>" (L). rewrite /sem_ty_mbang /=. iIntros "!#" (f1 f2) "Hff".
    brel_pures_l 1%nat. brel_pures_r 1%nat.
    iApply "HF".
    brel_pures'.
    iModIntro.
    iIntros (????).
    brel_pures'.
    iApply (brel_bind [AppLCtx _] [AppLCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HD Hff]"); [iApply to_iThy_le_bot|by iApply "HD"|simpl].
    iIntros (??) "H". iApply "H".
  Qed.

  Lemma F_AUTH_C_DH_rand_DH_SIM_F_KE_f m :
    ⊢ sem_typed [] (F_AUTH ∘f C_DH_rand) (F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)) ⊥ (fac m τ_DH) [].
  Proof using All.
    iApply sem_typed_sub_ty; first iApply fac_MS_le.
    iIntros (vs) "!# _". simpl.
    iApply brel_value. iIntros "$ !>". iSplit; last done.
    rewrite /fac /sem_ty_mbang /sem_ty_arr /=. iModIntro.
    iIntros (u1 u2) "[-> ->]".
    brel_pures_l 1%nat. brel_pures_r 2%nat.
    iMod token_alloc as (γtoka) "Htoka".
    iMod token_alloc as (γtokb) "Htokb".
    iMod message_alloc as (γautha) "Hautha".
    iMod message_alloc as (γauthb) "Hauthb".
    iMod all_receipts_alloc as (γfraca) "Hfraca".
    iMod all_receipts_alloc as (γfracb) "Hfracb".
    iApply (brel_bind [AppRCtx _] [AppRCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[] [Htoka Htokb Hautha Hauthb]");
      [iApply to_iThy_le_bot
      |iApply (C_DH_rand_DH_SIM_F_KE _ _ γfraca γfracb _ _ _ (rtc_refl _ _) with "Htoka Htokb Hautha Hauthb")
      |simpl].
    iIntros (D1 D2) "#HD".
    iApply (brel_bind [AppLCtx _; AppRCtx _] [AppLCtx _; AppRCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[] [Hfraca Hfracb]");
      [iApply to_iThy_le_bot
      |iApply (F_AUTH_F_AUTH_new γtoka γtokb γfraca γfracb (Psim_at eq_logic.Bwd γautha) (Psim_at eq_logic.Bwd γauthb) with "Hfraca Hfracb")
      |simpl].
    iIntros (F1 F2) "#HF".
    rewrite /func_comp. brel_pures'.
    iIntros "!>" (L). rewrite /sem_ty_mbang /=. iIntros "!#" (f1 f2) "Hff".
    brel_pures_l 1%nat. brel_pures_r 1%nat.
    iApply "HF".
    brel_pures'.
    iModIntro.
    iIntros (????).
    brel_pures'.
    iApply (brel_bind [AppLCtx _] [AppLCtx _]); [iApply traversable_to_iThy_nil|iApply to_iThy_le_bot|].
    assert (to_iThyIfMono OS [] = []) as <- by done.
    iApply (brel_mono OS with "[][HD Hff]"); [iApply to_iThy_le_bot|by iApply "HD"|simpl].
    iIntros (??) "H". iApply "H".
  Qed.

End dhke_relations_f.

(* ------------------------------------------------------------------ *)
(* The advantage bound.                                                *)
(* ------------------------------------------------------------------ *)

Section dhke_advantage.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.

  Import valgroup_notation.

  Theorem adv_DHKE (m : mode) (A : val) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m (τ__F aleak gk) → 𝔹)%T) →
    advantage A (F_AUTH ∘f DH_KE) (F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)) #true <=
      advantage (λ: "v", A (F_AUTH ∘fₚ (C_lazy "v")))%V DH_real DH_rand #true.
  Proof using All.
    intros HA.
    (*   F_AUTH ∘f DH_KE  ≃  F_AUTH ∘f C_DH_real                              *)
    eapply (advantage_triangle _ _ (F_AUTH ∘f C_DH_real) _ _ 0); first last.
    { rewrite Rplus_0_l. reflexivity. }
    2: { apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, fac m (τ__F aleak gk))); [exact HA| |]; intros HRGS.
         - iApply sem_typed_sub_ty; [iApply fac_le; iApply τ_DH_le_τ_DH_OS|iApply F_AUTH_DH_KE_C_DH_real_f].
         - iApply sem_typed_sub_ty; [iApply fac_le; iApply τ_DH_le_τ_DH_OS|iApply F_AUTH_C_DH_real_DH_KE_f]. }
    (*   F_AUTH ∘f C_DH_rand  ≃  F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)       *)
    eapply (advantage_triangle _ _ (F_AUTH ∘f C_DH_rand) _ _ _ 0); first last.
    { rewrite Rplus_0_r. reflexivity. }
    1: { apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, fac m (τ__F aleak gk))); [exact HA| |]; intros HRGS.
         - iApply sem_typed_sub_ty; [iApply fac_le; iApply τ_DH_le_τ_DH_OS|iApply F_AUTH_C_DH_rand_DH_SIM_F_KE_f].
         - iApply sem_typed_sub_ty; [iApply fac_le; iApply τ_DH_le_τ_DH_OS|iApply F_AUTH_DH_SIM_F_KE_C_DH_rand_f]. }
    (*   F_AUTH ∘f C_DH_real  vs  F_AUTH ∘f C_DH_rand: the DDH step, through
         the reduction [λ d, A (F_AUTH ∘f C_lazy d)]                          *)
    etrans; first apply (advantage_pure_r_rev _ [] _ (fill [AppRCtx (fac_app func_comp F_AUTH); AppRCtx C_lazy] DH_rand) _);
      [done|apply RED_pure|].
    etrans; first apply (advantage_pure_l_rev _ [] (fill [AppRCtx (fac_app func_comp F_AUTH); AppRCtx C_lazy] DH_real) _ _);
      [done|apply RED_pure|].
    apply (advantage_reduction_ctx A [AppRCtx (fac_app func_comp F_AUTH); AppRCtx C_lazy]).
    { done. }
    { intros vs w Hw. simpl. by rewrite Hw. }
  Qed.

  (* The simulator in the shape of the composition theorem. *)
  Theorem dhke_realises (m : mode) (A : val) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m (τ__F aleak gk) → 𝔹)%T) →
    advantage A REAL_DHKE (SIM_DHKE ∘f IDEAL_DHKE) #true <=
      advantage (RED_DHKE A) DH_real DH_rand #true.
  Proof using All.
    intros HA. rewrite /REAL_DHKE /SIM_DHKE /IDEAL_DHKE /RED_DHKE.
    eapply (advantage_triangle _ _ (F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)) _ _ _ 0); first last.
    { rewrite Rplus_0_r. reflexivity. }
    1: { apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, fac m (τ__F aleak gk))); [exact HA| |]; intros HRGS.
         - iApply sem_typed_val. iApply func_comp_f_assoc;
             [iApply F_AUTH_typed|iApply DH_SIM_typed|iApply F_KE_lazy_alice_typed].
         - iApply sem_typed_val. iApply func_comp_f_assoc_rev;
             [iApply F_AUTH_typed|iApply DH_SIM_typed|iApply F_KE_lazy_alice_typed]. }
    by apply (adv_DHKE m).
  Qed.

End dhke_advantage.
