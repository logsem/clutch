(* The typings of the components of the secure channel
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
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules dhke channel.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section channel_typing.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').
  #[local] Open Scope bi_scope.

  Definition NO : namespace := nroot .@ "oauth".
  Definition NF : namespace := nroot .@ "fchan".
  Definition NSC : namespace := nroot .@ "sim_chan".

  Lemma F_OAUTH_eq : ⊢ ⟪ Mod ONet OEp ⟫ F_OAUTH F_OAUTH.
  Proof.
    rewrite /Mod. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /ONet. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (l1 l2 d1 d2) "(-> & -> & #Hleak & #Hdel)".
    rewrite /F_OAUTH.
    eq_pures_l. eq_alloc_l box as "Hbox". eq_pures_l.
    eq_pures_r. eq_alloc_r box' as "Hbox'". eq_pures_r.
    iApply (eq_na_alloc (box_rel box box') NO).
    iSplitL "Hbox Hbox'"; first (iNext; iLeft; iFrame). iIntros "#Hinv".
    iApply eq_value. iModIntro. rewrite /OEp. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. iSplit; first done. iSplit; first done.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iSplitL.
    - (* send *)
      iApply eq_lift_arr. iIntros (xl xr) "Hx".
      iEval (rewrite eq_lift_group) in "Hx". iDestruct "Hx" as %(x & -> & ->).
      eq_pures_l. eq_pures_r.
      iApply (eq_na_open _ _ NO); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iAssert (∃ v v', box ↦ₗ v ∗ box' ↦ᵣ v')%I with "[H]" as (v v') "[Hb Hb']".
      { iDestruct "H" as "[[??]|(% & ? & ?)]"; iExists _, _; iFrame. }
      eq_store_l. eq_store_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hb Hb'"; first (iNext; iRight; iExists _; iFrame).
      eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R 𝔾 𝟙%T emp%I l1 l2 _ _ [] [] with "Hρ Hleak [] []");
        try (intros; apply _).
      { iApply eq_lift_group. by iExists _. }
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
      iDestruct "H" as "[[Hb Hb']|(%x & Hb & Hb')]"; eq_load_l; eq_load_r;
        iApply eq_na_close_rule; iFrame "Hclose".
      + iSplitL "Hb Hb'"; first (iNext; iLeft; iFrame).
        eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply "IH".
      + iSplitL "Hb Hb'"; first (iNext; iRight; iExists _; iFrame).
        eq_pures'. iApply eq_value. iModIntro. by iApply eq_group_val.
  Qed.

  Lemma F_CHAN_eq : ⊢ ⟪ Mod CAdv SChan ⟫ F_CHAN F_CHAN.
  Proof.
    rewrite /Mod. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /CAdv. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (n1 n2 a1 a2) "(-> & -> & #Hnot & #Hall)".
    rewrite /F_CHAN.
    eq_pures_l. eq_alloc_l box as "Hbox". eq_pures_l.
    eq_pures_r. eq_alloc_r box' as "Hbox'". eq_pures_r.
    iApply (eq_na_alloc (box_rel box box') NF).
    iSplitL "Hbox Hbox'"; first (iNext; iLeft; iFrame). iIntros "#Hinv".
    iApply eq_value. iModIntro. rewrite /SChan. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. iSplit; first done. iSplit; first done.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iSplitL.
    - (* the sender *)
      iApply eq_lift_arr. iIntros (xl xr) "Hx".
      iEval (rewrite eq_lift_group) in "Hx". iDestruct "Hx" as %(x & -> & ->).
      eq_pures_l. eq_pures_r.
      iApply (eq_na_open _ _ NF); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iAssert (∃ v v', box ↦ₗ v ∗ box' ↦ᵣ v')%I with "[H]" as (v v') "[Hb Hb']".
      { iDestruct "H" as "[[??]|(% & ? & ?)]"; iExists _, _; iFrame. }
      eq_store_l. eq_store_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hb Hb'"; first (iNext; iRight; iExists _; iFrame).
      eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I n1 n2 _ _ [] [] with "Hρ Hnot [] []");
        try (intros; apply _).
      { by iEval (rewrite eq_lift_unit). }
      { done. }
      iIntros "!>" (vl vr) "Hu _". simpl. by iApply eq_value.
    - (* the receiver *)
      iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures_l. eq_pures_r.
      iLöb as "IH".
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I a1 a2 _ _ [AppRCtx _] [AppRCtx _]
                with "Hρ Hall [] []"); try (intros; apply _).
      { by iEval (rewrite eq_lift_unit). }
      { done. }
      iIntros "!>" (vl vr) "Hu _". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
      iApply (eq_na_open _ _ NF); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "[[Hb Hb']|(%x & Hb & Hb')]"; eq_load_l; eq_load_r;
        iApply eq_na_close_rule; iFrame "Hclose".
      + iSplitL "Hb Hb'"; first (iNext; iLeft; iFrame).
        eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply "IH".
      + iSplitL "Hb Hb'"; first (iNext; iRight; iExists _; iFrame).
        eq_pures'. iApply eq_value. iModIntro. by iApply eq_group_val.
  Qed.

  (* The protocol has no state: it holds the affine ports it is given, and
     keeps the one it has not used yet across the call to the other. *)
  Lemma CHAN_eq : ⊢ ⟪ Mod (IProd Keys OEp) SChan ⟫ CHAN CHAN.
  Proof.
    rewrite /Mod. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /Keys /OEp. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (keysl keysr epl epr) "(-> & -> & Hkeys & Hep)".
    iEval (rewrite eq_lift_prod) in "Hkeys".
    iDestruct "Hkeys" as (kAl kAr kBl kBr) "(-> & -> & HkA & HkB)".
    iEval (rewrite eq_lift_prod) in "Hep".
    iDestruct "Hep" as (sl sr rl rr) "(-> & -> & Hs & Hr)".
    rewrite /CHAN. eq_pures_l. eq_pures_r.
    iApply eq_value. iModIntro. rewrite /SChan. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. iSplit; first done. iSplit; first done.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iSplitL "HkA Hs".
    - (* the sender *)
      iApply eq_lift_arr. iIntros (ml mr) "Hm".
      iEval (rewrite eq_lift_group) in "Hm". iDestruct "Hm" as %(m & -> & ->).
      eq_pures_l. eq_pures_r.
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T 𝔾 (⟪ 𝔾 -{ ¡ θ }-∘ 𝟙 ⟫ sl sr)%I
                kAl kAr _ _ [AppRCtx _] [AppRCtx _] with "Hρ HkA [] Hs"); try (intros; apply _).
      { by iEval (rewrite eq_lift_unit). }
      iIntros "!>" (vl vr) "Hk Hs".
      iEval (rewrite eq_lift_group) in "Hk". iDestruct "Hk" as %(k & -> & ->).
      simpl. eq_pures'.
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝔾 𝟙%T emp%I sl sr _ _ [] [] with "Hρ Hs [] []");
        try (intros; apply _).
      { iApply eq_lift_group. by iExists _. }
      { done. }
      iIntros "!>" (vl vr) "Hu _". simpl. by iApply eq_value.
    - (* the receiver *)
      iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures_l. eq_pures_r.
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T 𝔾 (⟪ 𝟙 -{ ¡ θ }-∘ 𝔾 ⟫ rl rr)%I
                kBl kBr _ _ [AppRCtx _] [AppRCtx _] with "Hρ HkB [] Hr"); try (intros; apply _).
      { by iEval (rewrite eq_lift_unit). }
      iIntros "!>" (vl vr) "Hk Hr".
      iEval (rewrite eq_lift_group) in "Hk". iDestruct "Hk" as %(k & -> & ->).
      simpl. eq_pures_l. eq_pures_r.
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T 𝔾 emp%I rl rr _ _
                [AppRCtx _] [AppRCtx _] with "Hρ Hr [] []"); try (intros; apply _).
      { by iEval (rewrite eq_lift_unit). }
      { done. }
      iIntros "!>" (vl vr) "Hc _".
      iEval (rewrite eq_lift_group) in "Hc". iDestruct "Hc" as %(c & -> & ->).
      simpl. eq_pures'. iApply eq_value. iModIntro. by iApply eq_group_val.
  Qed.

  Lemma S_CHAN_eq : ⊢ ⟪ Mod (IProd Ctl ONet) CAdv ⟫ S_CHAN S_CHAN.
  Proof.
    rewrite /Mod. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /Ctl /ONet. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (ctll ctlr netl netr) "(-> & -> & Hctl & Hnet)".
    iEval (rewrite eq_lift_prod) in "Hctl".
    iDestruct "Hctl" as (n1 n2 a1 a2) "(-> & -> & #Hnot & #Hall)".
    iEval (rewrite eq_lift_prod) in "Hnet".
    iDestruct "Hnet" as (l1 l2 d1 d2) "(-> & -> & #Hleak & #Hdel)".
    rewrite /S_CHAN /samplelbl.
    eq_pures_l. eq_alloc_l st as "Hst". eq_pures_l. eq_alloc_l sn as "Hsn". eq_pures_l.
    eq_alloctape_l ρ as "Hρt". eq_pures_l.
    eq_pures_r. eq_alloc_r st' as "Hst'". eq_pures_r. eq_alloc_r sn' as "Hsn'". eq_pures_r.
    eq_alloctape_r ρ' as "Hρt'". eq_pures_r.
    rewrite !Nat2Z.id.
    iApply (eq_na_alloc (flag_rel st st' ∗ flag_rel sn sn' ∗ tape_rel n ρ ρ') NSC).
    iSplitL; first (iNext; iFrame). iIntros "#Hinv".
    iApply eq_value. iModIntro. rewrite /CAdv. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. iSplit; first done. iSplit; first done. iSplitL.
    - (* notify *)
      iModIntro. iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures_l. eq_pures_r.
      iApply (eq_na_open _ _ NSC); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "((%bS & Hst & Hst') & Hsn & Hρt)".
      eq_store_l. eq_store_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hst Hst' Hsn Hρt"; first (iNext; iFrame).
      eq_pures_l. eq_pures_r.
      iApply (eq_call MS θ 𝔹%T 𝟙%T n1 n2 _ _ [AppRCtx _] [AppRCtx _] with "Hnot []");
        try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      iIntros "!>" (vl vr) "Hu". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
      iApply (eq_call MS θ 𝔹%T 𝟙%T a1 a2 _ _ [AppRCtx _] [AppRCtx _] with "Hall []");
        try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      iIntros "!>" (vl vr) "Hu". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
      iApply (eq_na_open _ _ NSC); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "(Hst & (%bN & Hsn & Hsn') & [Hρt Hρt'])".
      eq_store_l. eq_store_r. eq_pures_l. eq_pures_r.
      iApply eq_couple_tapes. iFrame "Hρt Hρt'". iIntros (c) "[Hρt Hρt']". simpl.
      eq_rand_l as "H1". eq_rand_r as "H2".
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hst Hsn Hsn' Hρt Hρt'"; first (iNext; iFrame).
      eq_pures'.
      iApply (eq_lift_app with "Hleak"). iApply eq_lift_group. by iExists _.
    - (* allow *)
      iModIntro. iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures_l. eq_pures_r.
      (* wait for the key *)
      iLöb as "IH".
      iApply (eq_call MS θ 𝔹%T 𝟙%T a1 a2 _ _ [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _]
                with "Hall []"); try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      iIntros "!>" (vl vr) "Hu". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
      iApply (eq_na_open _ _ NSC); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "((%bS & Hst & Hst') & Hsn & Hρt)".
      eq_load_l. eq_load_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hst Hst' Hsn Hρt"; first (iNext; iFrame).
      destruct bS; last first.
      { eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply "IH". }
      eq_pures_l. eq_pures_r.
      iApply (eq_call MS θ 𝔹%T 𝟙%T n1 n2 _ _ [AppRCtx _] [AppRCtx _] with "Hnot []");
        try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      iIntros "!>" (vl vr) "Hu". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
      (* wait for the ciphertext *)
      iClear "IH". iLöb as "IH".
      iApply (eq_call MS θ 𝟙%T 𝟙%T d1 d2 _ _ [AppRCtx _] [AppRCtx _] with "Hdel []");
        try (intros; apply _).
      { by iEval (rewrite eq_lift_unit). }
      iIntros "!>" (vl vr) "Hu". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
      iApply (eq_na_open _ _ NSC); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "(Hst & (%bN & Hsn & Hsn') & Hρt)".
      eq_load_l. eq_load_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hst Hsn Hsn' Hρt"; first (iNext; iFrame).
      destruct bN.
      + eq_pures'. iApply eq_value. iModIntro. by iEval (rewrite eq_lift_unit).
      + eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply "IH".
  Qed.

  Lemma F_OAUTH_typed : ⊢ ⊨ᵥ F_OAUTH ≤ F_OAUTH : Mod ONet OEp.
  Proof. apply eq_val_typed, F_OAUTH_eq. Qed.
  Lemma F_CHAN_typed : ⊢ ⊨ᵥ F_CHAN ≤ F_CHAN : Mod CAdv SChan.
  Proof. apply eq_val_typed, F_CHAN_eq. Qed.
  Lemma CHAN_typed : ⊢ ⊨ᵥ CHAN ≤ CHAN : Mod (IProd Keys OEp) SChan.
  Proof. apply eq_val_typed, CHAN_eq. Qed.
  Lemma S_CHAN_typed : ⊢ ⊨ᵥ S_CHAN ≤ S_CHAN : Mod (IProd Ctl ONet) CAdv.
  Proof. apply eq_val_typed, S_CHAN_eq. Qed.

End channel_typing.
