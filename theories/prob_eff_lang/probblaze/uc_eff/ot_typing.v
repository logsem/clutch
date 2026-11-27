(* The typings of the components of oblivious transfer (uc_eff/DESIGN.md,
   section 6), as self-equivalences in the logic of [eq/]: the
   functionalities and simulators of the three cases.  They are the
   premises of [uc_composition] for the clients of OT ([ot_rev_ot.v]). *)

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
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules ot ot_eq
  ot_corrupted_receiver ot_corrupted_sender.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section ot_typing.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Open Scope bi_scope.

  (* ---------------------------------------------------------------- *)
  (* Receiver corrupted.                                                *)
  (* ---------------------------------------------------------------- *)

  Lemma F_OT_R_eq : ⊢ ⟪ Mod OTAdv SPort ⟫ F_OT_R F_OT_R.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /OTAdv. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (cl cr ol or) "(-> & -> & #Hchoose & #Houtput)".
    rewrite /F_OT_R. eq_pures'.
    iApply eq_value. iModIntro. rewrite /SPort. iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    eq_pures'.
    iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝔹%T emp%I cl cr _ _ [AppRCtx _] [AppRCtx _]
              with "Hρ Hchoose [] []"); try (intros; apply _);
      [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (bl br) "Hb _". iEval (rewrite eq_lift_bool) in "Hb". iDestruct "Hb" as %(b & -> & ->).
    eq_pures'.
    iApply eq_value. iModIntro. iApply eq_lift_arr. iIntros (ml mr) "Hm".
    iEval (rewrite eq_lift_prod) in "Hm".
    iDestruct "Hm" as (m0l m0r m1l m1r) "(-> & -> & Hm0 & Hm1)".
    iEval (rewrite eq_lift_group) in "Hm0". iDestruct "Hm0" as (m0) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hm1". iDestruct "Hm1" as (m1) "[-> ->]".
    destruct b; eq_pures';
      (iApply (eq_call_frame θ (¡ θ)%R 𝔾%T 𝟙%T emp%I ol or _ _ [] [] with "Hρ Houtput [] []");
         try (intros; apply _); [by iApply eq_group_val|done|]);
      iIntros "!>" (??) "Hu _"; by iApply eq_value.
  Qed.

  Lemma F_OT_R_typed : ⊢ ⊨ᵥ F_OT_R ≤ F_OT_R : Mod OTAdv SPort.
  Proof. apply eq_val_typed, F_OT_R_eq. Qed.

  Definition NSR : namespace := nroot .@ "sotr".

  (* The simulator's state, the same on both sides. *)
  Definition st_rel (st st' : loc) : iPropD Σ :=
    ∃ w : val, st ↦ₗ w ∗ st' ↦ᵣ w ∗ ⌜w = NONEV ∨ ∃ u v : vgG, w = SOMEV (vgval u, vgval v)%V⌝.

  Lemma S_OT_R_eq : ⊢ ⟪ Mod (IProd Pub RNet) OTAdv ⟫ S_OT_R S_OT_R.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /Pub /RNet. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (pl pr nl nr) "(-> & -> & #Hpub & Hnet)".
    iEval (rewrite eq_lift_prod) in "Hnet".
    iDestruct "Hnet" as (rl rr sl sr) "(-> & -> & #Hrecv & #Hsend)".
    rewrite /S_OT_R /sample /enc is_unit.
    eq_pures'.
    eq_couple_rand_rand. iIntros (a1 Ha1). eq_pures'.
    eq_couple_rand_rand. iIntros (t0 Ht0). eq_pures'.
    eq_couple_rand_rand. iIntros (t1 Ht1). eq_pures'.
    eq_reshape_l (pl _). eq_reshape_r (pr _).
    iApply (eq_call MS ⟨⟩%R Crs 𝟙%T with "Hpub"); try (intros; apply _); first iApply eq_crs.
    iIntros "!>" (wl wr) "_". simpl. eq_pures'.
    eq_alloc_l st as "Hst". eq_pures_l. eq_alloc_r st' as "Hst'". eq_pures_r.
    iApply (eq_na_alloc (st_rel st st') NSR).
    iSplitL "Hst Hst'"; first (iNext; iExists _; iFrame; by iLeft). iIntros "#Hinv".
    iApply eq_value. iModIntro. rewrite /OTAdv. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL.
    - (* choose *)
      iModIntro. iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (rl _). eq_reshape_r (rr _).
      iApply (eq_call MS θ 𝟙%T (𝔾 × 𝔾)%T with "Hrecv"); try (intros; apply _);
        first by iEval (rewrite eq_lift_unit).
      iIntros "!>" (uvl uvr) "Huv". iEval (rewrite eq_lift_prod) in "Huv".
      iDestruct "Huv" as (ul ur vl vr) "(-> & -> & Hu & Hv)".
      iEval (rewrite eq_lift_group) in "Hu". iDestruct "Hu" as (u) "[-> ->]".
      iEval (rewrite eq_lift_group) in "Hv". iDestruct "Hv" as (v) "[-> ->]".
      eq_pures'.
      iApply (eq_na_open _ _ NSR); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as (w) "(Hst & Hst' & _)".
      eq_store_l. eq_store_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hst Hst'"; first (iNext; iExists _; iFrame; iRight; by iExists _, _).
      eq_pures'. iApply eq_value. iApply eq_bool.
    - (* output *)
      iModIntro. iApply eq_lift_arr. iIntros (ml mr) "Hm".
      iEval (rewrite eq_lift_group) in "Hm". iDestruct "Hm" as (m) "[-> ->]".
      eq_pures'.
      iApply (eq_na_open _ _ NSR); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as (w) "(Hst & Hst' & %Hw)".
      eq_load_l. eq_load_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hst Hst'"; first (iNext; iExists _; by iFrame).
      destruct Hw as [->|(u & v & ->)].
      { eq_pures'. iApply eq_value. by iEval (rewrite eq_lift_unit). }
      eq_pures'.
      case_bool_decide; eq_pures';
        [iApply eq_value; by iEval (rewrite eq_lift_unit)|].
      case_bool_decide; eq_pures';
        (do 4 (eq_couple_rand_rand; iIntros (? ?); eq_pures');
         iApply (eq_lift_app with "Hsend"); by iApply eq_ctxts).
  Qed.

  Lemma S_OT_R_typed : ⊢ ⊨ᵥ S_OT_R ≤ S_OT_R : Mod (IProd Pub RNet) OTAdv.
  Proof. apply eq_val_typed, S_OT_R_eq. Qed.

  (* ---------------------------------------------------------------- *)
  (* Sender corrupted.                                                  *)
  (* ---------------------------------------------------------------- *)

  Lemma F_OT_S_eq : ⊢ ⟪ Mod OTSAdv RPort ⟫ F_OT_S F_OT_S.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (il ir) "#Hinput".
    rewrite /F_OT_S. eq_pures'.
    iApply eq_value. iModIntro. rewrite /RPort. iApply eq_lift_arr. iIntros (bl br) "Hb".
    iEval (rewrite eq_lift_bool) in "Hb". iDestruct "Hb" as %(b & -> & ->).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    eq_pures'.
    iApply (eq_call_frame θ (¡ θ)%R 𝟙%T (𝔾 × 𝔾)%T emp%I il ir _ _ [AppRCtx _] [AppRCtx _]
              with "Hρ Hinput [] []"); try (intros; apply _);
      [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (ml mr) "Hm _". iEval (rewrite eq_lift_prod) in "Hm".
    iDestruct "Hm" as (m0l m0r m1l m1r) "(-> & -> & Hm0 & Hm1)".
    iEval (rewrite eq_lift_group) in "Hm0". iDestruct "Hm0" as (m0) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hm1". iDestruct "Hm1" as (m1) "[-> ->]".
    destruct b; eq_pures'; iApply eq_value; by iApply eq_group_val.
  Qed.

  Lemma F_OT_S_typed : ⊢ ⊨ᵥ F_OT_S ≤ F_OT_S : Mod OTSAdv RPort.
  Proof. apply eq_val_typed, F_OT_S_eq. Qed.

  Lemma S_OT_S_eq : ⊢ ⟪ Mod (IProd Pub SNet) OTSAdv ⟫ S_OT_S S_OT_S.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /Pub /SNet. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (pl pr nl nr) "(-> & -> & #Hpub & Hnet)".
    iEval (rewrite eq_lift_prod) in "Hnet".
    iDestruct "Hnet" as (sl sr rl rr) "(-> & -> & #Hsend & #Hrecv)".
    rewrite /S_OT_S /sample /dec.
    eq_pures'.
    eq_couple_rand_rand. iIntros (y Hy). eq_pures'.
    eq_couple_rand_rand. iIntros (x Hx). eq_pures'.
    eq_reshape_l (pl _). eq_reshape_r (pr _).
    iApply (eq_call MS ⟨⟩%R Crs 𝟙%T with "Hpub"); try (intros; apply _); first iApply eq_crs.
    iIntros "!>" (wl wr) "_". simpl. eq_pures'.
    iApply eq_value. iModIntro. rewrite /OTSAdv. iModIntro.
    iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    eq_pures'.
    eq_couple_rand_rand. iIntros (a1 Ha1). eq_pures'.
    rewrite -Nat2Z.inj_mul. eq_pures'.
    eq_reshape_l (sl _). eq_reshape_r (sr _).
    iApply (eq_call MS θ (𝔾 × 𝔾)%T 𝟙%T with "Hsend"); try (intros; apply _);
      first by iApply eq_pair.
    iIntros "!>" (??) "Hu". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    eq_pures'.
    eq_reshape_l (rl _). eq_reshape_r (rr _).
    iApply (eq_call MS θ 𝟙%T ((𝔾 × 𝔾) × (𝔾 × 𝔾))%T with "Hrecv"); try (intros; apply _);
      first by iEval (rewrite eq_lift_unit).
    iIntros "!>" (el er) "He". iDestruct (eq_lift_ctxts with "He") as (c0 d0 c1 d1) "[-> ->]".
    eq_pures'. iApply eq_value. iModIntro. by iApply eq_pair.
  Qed.

  Lemma S_OT_S_typed : ⊢ ⊨ᵥ S_OT_S ≤ S_OT_S : Mod (IProd Pub SNet) OTSAdv.
  Proof. apply eq_val_typed, S_OT_S_eq. Qed.

  (* ---------------------------------------------------------------- *)
  (* Both honest.                                                       *)
  (* ---------------------------------------------------------------- *)

  Definition NOH : namespace := nroot .@ "oth".

  Definition gpair (v : val) : Prop := ∃ a b : vgG, v = (vgval a, vgval b)%V.
  Definition gelt (v : val) : Prop := ∃ a : vgG, v = vgval a.

  Lemma F_OT_H_eq : ⊢ ⟪ Mod OTHAdv OTPorts ⟫ F_OT_H F_OT_H.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /OTHAdv. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (ysl ysr yrl yrr) "(-> & -> & #Hys & #Hyr)".
    rewrite /F_OT_H.
    eq_pures_l. eq_alloc_l ch as "Hch". eq_pures_l. eq_alloc_l mm as "Hmm". eq_pures_l.
    eq_pures_r. eq_alloc_r ch' as "Hch'". eq_pures_r. eq_alloc_r mm' as "Hmm'". eq_pures_r.
    iApply (eq_na_alloc (bool_ref ch ch') (NOH .@ "ch")).
    iSplitL "Hch Hch'"; first (iNext; iExists _; iFrame). iIntros "#Ich".
    iApply (eq_na_alloc (box_rel_gen gpair mm mm') (NOH .@ "mm")).
    iSplitL "Hmm Hmm'"; first (iNext; iLeft; iFrame). iIntros "#Imm".
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iApply eq_value. iModIntro. rewrite /OTPorts. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL.
    - (* the sender *)
      rewrite /SPort. iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      iLöb as "IH".
      eq_reshape_l (ysl _). eq_reshape_r (ysr _).
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hys [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_bool with "Ich"). iIntros ([]).
      2: { eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply "IH". }
      eq_pures'. iApply eq_value. iModIntro.
      iApply eq_lift_arr. iIntros (ml mr) "Hm".
      iEval (rewrite eq_lift_prod) in "Hm".
      iDestruct "Hm" as (m0l m0r m1l m1r) "(-> & -> & Hm0 & Hm1)".
      iEval (rewrite eq_lift_group) in "Hm0". iDestruct "Hm0" as (m0) "[-> ->]".
      iEval (rewrite eq_lift_group) in "Hm1". iDestruct "Hm1" as (m1) "[-> ->]".
      eq_pures'.
      assert (gpair (vgval m0, vgval m1)%V) as Hm by (by exists m0, m1).
      eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
      iApply (eq_na_store_box _ _ _ _ _ _ _ _ _ Hm with "Imm"). eq_pures'.
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I ysl ysr _ _ [] [] with "Hρ Hys [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". by iApply eq_value.
    - (* the receiver *)
      rewrite /RPort. iApply eq_lift_arr. iIntros (bl br) "Hb".
      iEval (rewrite eq_lift_bool) in "Hb". iDestruct "Hb" as %(b & -> & ->).
      eq_pures'.
      eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
      iApply (eq_na_store_bool with "Ich"). eq_pures'.
      iLöb as "IH".
      eq_reshape_l (yrl _). eq_reshape_r (yrr _).
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hyr [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_box with "Imm"). iIntros (w) "%Hw".
      destruct Hw as [->|(? & (m0 & m1 & ->) & ->)].
      { eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply "IH". }
      destruct b; eq_pures'; iApply eq_value; iModIntro; by iApply eq_group_val.
  Qed.

  Lemma F_OT_H_typed : ⊢ ⊨ᵥ F_OT_H ≤ F_OT_H : Mod OTHAdv OTPorts.
  Proof. apply eq_val_typed, F_OT_H_eq. Qed.

  Lemma S_OT_H_eq : ⊢ ⟪ Mod OTHNet OTHAdv ⟫ S_OT_H S_OT_H.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /OTHNet /LNet. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (pl pr nl nr) "(-> & -> & #Hpub & Hnets)".
    iEval (rewrite eq_lift_prod) in "Hnets".
    iDestruct "Hnets" as (rsl rsr srl srr) "(-> & -> & Hrs & Hsr)".
    iEval (rewrite eq_lift_prod) in "Hrs".
    iDestruct "Hrs" as (lrsl lrsr drsl drsr) "(-> & -> & #Hlrs & #Hdrs)".
    iEval (rewrite eq_lift_prod) in "Hsr".
    iDestruct "Hsr" as (lsrl lsrr dsrl dsrr) "(-> & -> & #Hlsr & #Hdsr)".
    rewrite /S_OT_H /sample.
    eq_pures'.
    eq_couple_rand_rand. iIntros (y Hy). eq_pures'.
    eq_couple_rand_rand. iIntros (x Hx). eq_pures'.
    eq_reshape_l (pl _). eq_reshape_r (pr _).
    iApply (eq_call MS ⟨⟩%R Crs 𝟙%T with "Hpub"); try (intros; apply _); first iApply eq_crs.
    iIntros "!>" (wl wr) "_". simpl. eq_pures'.
    eq_alloc_l uu as "Huu". eq_pures_l. eq_alloc_l sgo as "Hsgo". eq_pures_l.
    eq_alloc_r uu' as "Huu'". eq_pures_r. eq_alloc_r sgo' as "Hsgo'". eq_pures_r.
    iApply (eq_na_alloc (box_rel_gen gelt uu uu') (NOH .@ "uu")).
    iSplitL "Huu Huu'"; first (iNext; iLeft; iFrame). iIntros "#Iuu".
    iApply (eq_na_alloc (bool_ref sgo sgo') (NOH .@ "sgo")).
    iSplitL "Hsgo Hsgo'"; first (iNext; iExists _; iFrame). iIntros "#Isgo".
    iApply eq_value. iModIntro. rewrite /OTHAdv. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL.
    - (* the sender *)
      iModIntro. iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_bool with "Isgo"). iIntros ([]).
      + eq_pures'.
        eq_reshape_l (Load _). eq_reshape_r (Load _).
        iApply (eq_na_load_box with "Iuu"). iIntros (w) "%Hw".
        destruct Hw as [->|(? & (u & ->) & ->)].
        { eq_pures'. iApply eq_value. by iEval (rewrite eq_lift_unit). }
        eq_pures'.
        do 4 (eq_couple_rand_rand; iIntros (? ?); eq_pures').
        iApply (eq_lift_app with "Hlsr"). by iApply eq_ctxts.
      + eq_pures'.
        eq_reshape_l (drsl _). eq_reshape_r (drsr _).
        iApply (eq_call MS θ 𝟙%T 𝟙%T with "Hdrs"); try (intros; apply _);
          first by iEval (rewrite eq_lift_unit).
        iIntros "!>" (??) "Hu". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
        eq_pures'.
        eq_reshape_l (Load _). eq_reshape_r (Load _).
        iApply (eq_na_load_box with "Iuu"). iIntros (w) "%Hw".
        destruct Hw as [->|(? & (u & ->) & ->)].
        { eq_pures'. iApply eq_value. by iEval (rewrite eq_lift_unit). }
        eq_pures'.
        iApply (eq_na_store_bool _ _ _ _ [] [] with "Isgo").
        iApply eq_value. by iEval (rewrite eq_lift_unit).
    - (* the receiver *)
      iModIntro. iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_box with "Iuu"). iIntros (w) "%Hw".
      destruct Hw as [->|(? & (u & ->) & ->)].
      + eq_pures'.
        eq_couple_rand_rand. iIntros (a Ha). eq_pures'.
        eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
        iApply (eq_na_store_box with "Iuu"); first by eexists.
        eq_pures'.
        eq_reshape_l (lrsl _). eq_reshape_r (lrsr _).
        iApply (eq_call MS θ (𝔾 × 𝔾)%T 𝟙%T with "Hlrs"); try (intros; apply _);
          first by iApply eq_pair.
        iIntros "!>" (??) "Hu". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
        eq_pures'.
        iApply (eq_lift_app with "Hdsr"). by iEval (rewrite eq_lift_unit).
      + eq_pures'.
        iApply (eq_lift_app with "Hdsr"). by iEval (rewrite eq_lift_unit).
  Qed.

  Lemma S_OT_H_typed : ⊢ ⊨ᵥ S_OT_H ≤ S_OT_H : Mod OTHNet OTHAdv.
  Proof. apply eq_val_typed, S_OT_H_eq. Qed.

End ot_typing.
