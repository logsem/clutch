(* The typing of the one-way authenticated channel
   (uc_eff/DESIGN.md), as self-equivalences in the logic of [eq/]. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_compat.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules auth.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section auth_typing.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').
  #[local] Open Scope bi_scope.

  Definition NO : namespace := nroot .@ "oauth".

  (* The channel carries any first-order type. *)
  Lemma F_OAUTH_eq_gen (τ : sem_ty Σ) (φ : val → Prop) :
    eq_ground τ φ → ⊢ ⟪ Mod (ONetT τ) (OEpT τ) ⟫ F_OAUTH F_OAUTH.
  Proof.
    intros Hτ.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /ONetT. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (l1 l2 d1 d2) "(-> & -> & #Hleak & #Hdel)".
    rewrite /F_OAUTH.
    eq_pures_l. eq_alloc_l box as "Hbox". eq_pures_l.
    eq_pures_r. eq_alloc_r box' as "Hbox'". eq_pures_r.
    iApply (eq_na_alloc (box_rel_gen φ box box') NO).
    iSplitL "Hbox Hbox'"; first (iNext; iLeft; iFrame). iIntros "#Hinv".
    iApply eq_value. iModIntro. rewrite /OEpT. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. iSplit; first done. iSplit; first done.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iSplitL.
    - (* send *)
      iApply eq_lift_arr. iIntros (xl xr) "Hx".
      iEval (rewrite Hτ) in "Hx". iDestruct "Hx" as %[<- Hx].
      eq_pures_l. eq_pures_r.
      iApply (eq_na_open _ _ NO); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iAssert (∃ v v', box ↦ₗ v ∗ box' ↦ᵣ v')%I with "[H]" as (v v') "[Hb Hb']".
      { iDestruct "H" as "[[??]|(% & _ & ? & ?)]"; iExists _, _; iFrame. }
      eq_store_l. eq_store_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hb Hb'"; first (iNext; iRight; iExists _; by iFrame).
      eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R τ 𝟙%T emp%I l1 l2 _ _ [] [] with "Hρ Hleak [] []");
        try (intros; apply _).
      { iEval (rewrite Hτ). done. }
      { done. }
      iIntros "!>" (vl vr) "Hu _". simpl. by iApply eq_value.
    - (* recv *)
      iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures_l. eq_pures_r.
      iLöb as "IH".
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I d1 d2 _ _ [AppRCtx _] [AppRCtx _]
                with "Hρ Hdel [] []"); try (intros; apply _).
      { by iEval (rewrite eq_lift_unit). }
      { done. }
      iIntros "!>" (vl vr) "Hu _". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
      iApply (eq_na_open _ _ NO); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "[[Hb Hb']|(%x & %Hx & Hb & Hb')]"; eq_load_l; eq_load_r;
        iApply eq_na_close_rule; iFrame "Hclose".
      + iSplitL "Hb Hb'"; first (iNext; iLeft; iFrame).
        eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply "IH".
      + iSplitL "Hb Hb'"; first (iNext; iRight; iExists _; by iFrame).
        eq_pures'. iApply eq_value. iModIntro. by iEval (rewrite Hτ).
  Qed.

  Lemma F_OAUTH_typed_gen (τ : sem_ty Σ) (φ : val → Prop) :
    eq_ground τ φ → ⊢ ⊨ᵥ F_OAUTH ≤ F_OAUTH : Mod (ONetT τ) (OEpT τ).
  Proof. intros Hτ. apply eq_val_typed, (F_OAUTH_eq_gen τ φ Hτ). Qed.

  Lemma F_OAUTH_eq : ⊢ ⟪ Mod ONet OEp ⟫ F_OAUTH F_OAUTH.
  Proof. iApply (F_OAUTH_eq_gen 𝔾 _ eq_ground_group). Qed.

  Lemma F_OAUTH_typed : ⊢ ⊨ᵥ F_OAUTH ≤ F_OAUTH : Mod ONet OEp.
  Proof. apply eq_val_typed, F_OAUTH_eq. Qed.

  Lemma F_AUTH_typed : ⊢ ⊨ᵥ F_AUTH ≤ F_AUTH : Mod Net Eps.
  Proof. iApply tens_op_typed; iApply F_OAUTH_typed. Qed.

End auth_typing.
