(* The typings of the components of oblivious transfer, as
   self-equivalences in the logic of [eq/]: the parties, the reference
   string, and the functionalities and simulators of the three cases.
   They are the premises of [uc_composition] for the clients of OT
   ([ot_rev_ot.v]). *)

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
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules auth auth_typing ot ot_eq
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
    iModIntro. iApply eq_lift_arr. iIntros (cl cr) "Hchoose".
    rewrite /F_OT_R. eq_pures'.
    iApply eq_value. iModIntro. rewrite /SPort. iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    eq_pures'. rewrite /OTAdv.
    eq_reshape_l (cl _). eq_reshape_r (cr _).
    iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T (𝔹 × (𝔾 -{ ¡ θ }-∘ 𝟙))%T emp%I with "Hρ Hchoose [] []");
      try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (pl pr) "Hp _". iEval (rewrite eq_lift_prod) in "Hp".
    iDestruct "Hp" as (bl br ol or) "(-> & -> & Hb & Hout)".
    iEval (rewrite eq_lift_bool) in "Hb". iDestruct "Hb" as %(b & -> & ->).
    eq_pures'.
    iApply eq_value. iModIntro. iApply eq_lift_arr. iIntros (ml mr) "Hm".
    iEval (rewrite eq_lift_prod) in "Hm".
    iDestruct "Hm" as (m0l m0r m1l m1r) "(-> & -> & Hm0 & Hm1)".
    iEval (rewrite eq_lift_group) in "Hm0". iDestruct "Hm0" as (m0) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hm1". iDestruct "Hm1" as (m1) "[-> ->]".
    destruct b; eq_pures';
      (iApply (eq_call_frame_aff θ (¡ θ)%R 𝔾%T 𝟙%T emp%I ol or _ _ [] [] with "Hρ Hout [] []");
         try (intros; apply _); [by iApply eq_group_val|done|]);
      iIntros "!>" (??) "Hu _"; by iApply eq_value.
  Qed.

  Lemma F_OT_R_typed : ⊢ ⊨ᵥ F_OT_R ≤ F_OT_R : Mod OTAdv SPort.
  Proof. apply eq_val_typed, F_OT_R_eq. Qed.

  (* [S_OT_R] runs the real sender; its typing is after [OT_S_eq]. *)

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
  (* The ciphertexts. *)
  #[local] Notation CT := ((𝔾 × 𝔾) × (𝔾 × 𝔾))%T.

  Lemma F_OT_H_eq : ⊢ ⟪ Mod OTHAdv OTPorts ⟫ F_OT_H F_OT_H.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /OTHAdv. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (rsl rsr rrl rrr) "(-> & -> & Hrs & Hrr)".
    rewrite /F_OT_H.
    eq_pures_l. eq_alloc_l ch as "Hch". eq_pures_l. eq_alloc_l mm as "Hmm". eq_pures_l.
    eq_pures_r. eq_alloc_r ch' as "Hch'". eq_pures_r. eq_alloc_r mm' as "Hmm'". eq_pures_r.
    iApply (eq_na_alloc (bool_ref ch ch') (NOH .@ "ch")).
    iSplitL "Hch Hch'"; first (iNext; iExists _; iFrame). iIntros "#Ich".
    iApply (eq_na_alloc (box_rel_gen gpair mm mm') (NOH .@ "mm")).
    iSplitL "Hmm Hmm'"; first (iNext; iLeft; iFrame). iIntros "#Imm".
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iApply eq_value. iModIntro. rewrite /OTPorts. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL "Hrs".
    - (* the sender *)
      rewrite /SPort. iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (rsl _). eq_reshape_r (rsr _).
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T (𝟙 -{ ¡ θ }-∘ 𝟙)%T emp%I with "Hρ Hrs [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (kl kr) "Hk _". eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_bool with "Ich"). iIntros ([]); eq_pures'; last iApply eq_loop.
      iApply eq_value. iModIntro. iApply eq_lift_arr. iIntros (ml mr) "Hm".
      iEval (rewrite eq_lift_prod) in "Hm".
      iDestruct "Hm" as (m0l m0r m1l m1r) "(-> & -> & Hm0 & Hm1)".
      iEval (rewrite eq_lift_group) in "Hm0". iDestruct "Hm0" as (m0) "[-> ->]".
      iEval (rewrite eq_lift_group) in "Hm1". iDestruct "Hm1" as (m1) "[-> ->]".
      eq_pures'.
      assert (gpair (vgval m0, vgval m1)%V) as Hm by (by exists m0, m1).
      eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
      iApply (eq_na_store_box _ _ _ _ _ _ _ _ _ Hm with "Imm"). eq_pures'.
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T 𝟙%T emp%I kl kr _ _ [] [] with "Hρ Hk [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". by iApply eq_value.
    - (* the receiver *)
      rewrite /RPort. iApply eq_lift_arr. iIntros (bl br) "Hb".
      iEval (rewrite eq_lift_bool) in "Hb". iDestruct "Hb" as %(b & -> & ->).
      eq_pures'.
      eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
      iApply (eq_na_store_bool with "Ich"). eq_pures'.
      eq_reshape_l (rrl _). eq_reshape_r (rrr _).
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hrr [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_box with "Imm"). iIntros (w) "%Hw".
      destruct Hw as [->|(? & (m0 & m1 & ->) & ->)].
      { eq_pures'. iApply eq_loop. }
      destruct b; eq_pures'; iApply eq_value; iModIntro; by iApply eq_group_val.
  Qed.

  Lemma F_OT_H_typed : ⊢ ⊨ᵥ F_OT_H ≤ F_OT_H : Mod OTHAdv OTPorts.
  Proof. apply eq_val_typed, F_OT_H_eq. Qed.

  (* The dummy inputs. *)
  Lemma DUMMY_OT_eq : ⊢ ⟪ Mod OTPorts OTHAdv ⟫ DUMMY_OT DUMMY_OT.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (pl pr) "Hp".
    rewrite /OTPorts. iEval (rewrite eq_lift_prod) in "Hp".
    iDestruct "Hp" as (sl sr rl rr) "(-> & -> & Hs & Hr)".
    rewrite /DUMMY_OT is_unit. eq_pures'.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iApply eq_value. iModIntro. rewrite /OTHAdv. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL "Hs".
    - iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->]. eq_pures'.
      rewrite /SPort. eq_reshape_l (sl _). eq_reshape_r (sr _).
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T ((𝔾 × 𝔾) -{ ¡ θ }-∘ 𝟙)%T emp%I with "Hρ Hs [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (kl kr) "Hk _". eq_pures'.
      iApply eq_value. iModIntro. iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->]. eq_pures'.
      iApply (eq_call_frame_aff θ (¡ θ)%R (𝔾 × 𝔾)%T 𝟙%T emp%I kl kr _ _ [] [] with "Hρ Hk [] []");
        try (intros; apply _); [by iApply eq_pair|done|].
      iIntros "!>" (??) "Hu _". by iApply eq_value.
    - iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->]. eq_pures'.
      rewrite /RPort. eq_reshape_l (rl _). eq_reshape_r (rr _).
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝔹%T 𝔾%T emp%I with "Hρ Hr [] []");
        try (intros; apply _); [iApply eq_bool|done|].
      iIntros "!>" (??) "_ _". eq_pures'. iApply eq_value. by iEval (rewrite eq_lift_unit).
  Qed.

  Lemma DUMMY_OT_typed : ⊢ ⊨ᵥ DUMMY_OT ≤ DUMMY_OT : Mod OTPorts OTHAdv.
  Proof. apply eq_val_typed, DUMMY_OT_eq. Qed.

  (* The real parties and the reference string, for the simulator. *)
  Lemma eq_lift_crs vl vr :
    ⟪ Crs ⟫ vl vr ⊢ ∃ a b c d : vgG,
      ⌜vl = (vgval a, vgval b, vgval c, vgval d)%V ∧ vr = (vgval a, vgval b, vgval c, vgval d)%V⌝.
  Proof.
    rewrite /Crs. iIntros "H".
    iEval (rewrite eq_lift_prod) in "H". iDestruct "H" as (l3 r3 dl dr) "(-> & -> & H3 & Hd)".
    iEval (rewrite eq_lift_prod) in "H3". iDestruct "H3" as (l2 r2 cl cr) "(-> & -> & H2 & Hc)".
    iEval (rewrite eq_lift_prod) in "H2". iDestruct "H2" as (al ar bl br) "(-> & -> & Ha & Hb)".
    iEval (rewrite eq_lift_group) in "Ha". iDestruct "Ha" as (a) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hb". iDestruct "Hb" as (b) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hc". iDestruct "Hc" as (c) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hd". iDestruct "Hd" as (d) "[-> ->]".
    by iExists a, b, c, d.
  Qed.

  Lemma F_CRS_real_eq : ⊢ ⟪ Mod Pub CrsPort ⟫ (F_CRS_DH DDH_real) (F_CRS_DH DDH_real).
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (pl pr) "#Hpub".
    rewrite /F_CRS_DH /DDH_real /sample. eq_pures'.
    eq_couple_rand_rand. iIntros (y Hy). eq_pures'.
    eq_couple_rand_rand. iIntros (x Hx). eq_pures'.
    eq_reshape_l (pl _). eq_reshape_r (pr _).
    iApply (eq_call MS ⟨⟩%R Crs 𝟙%T with "Hpub"); try (intros; apply _); first iApply eq_crs.
    iIntros "!>" (wl wr) "_". simpl. eq_pures'.
    iApply eq_value. iModIntro. rewrite /CrsPort. iModIntro.
    iApply eq_lift_arr. iIntros (??) "Hu". iEval (rewrite eq_lift_unit) in "Hu".
    iDestruct "Hu" as %[-> ->]. eq_pures'. iApply eq_value. iModIntro. iApply eq_crs.
  Qed.

  (* Requesting the reference string from inside a port. *)
  Lemma eq_get_crs (θ : sem_row Σ) (gl gr : val) Kl Kr R :
    (∀ l1s, NeutralEctx l1s Kl) → (∀ l2s, NeutralEctx l2s Kr) →
    ⊢ ⟪ CrsPort θ ⟫ gl gr -∗
      (∀ a b c d : vgG,
         EQ fill Kl (Val (vgval a, vgval b, vgval c, vgval d)%V)
           ≈ fill Kr (Val (vgval a, vgval b, vgval c, vgval d)%V) <|iLblSig_to_iLblThy (¡ θ)|> {{ R }}) -∗
      EQ fill Kl (gl #()%V) ≈ fill Kr (gr #()%V) <|iLblSig_to_iLblThy (¡ θ)|> {{ R }}.
  Proof.
    iIntros (??) "#Hg H".
    iApply (eq_call_frame ⟨⟩%R (¡ θ)%R 𝟙%T Crs (∀ a b c d : vgG,
         EQ fill Kl (Val (vgval a, vgval b, vgval c, vgval d)%V)
           ≈ fill Kr (Val (vgval a, vgval b, vgval c, vgval d)%V) <|iLblSig_to_iLblThy (¡ θ)|> {{ R }})%I
              with "[] Hg [] H"); try assumption.
    { iApply row_le_nil_flip. }
    { by iEval (rewrite eq_lift_unit). }
    iIntros "!>" (vl vr) "Hv H". iDestruct (eq_lift_crs with "Hv") as (a b c d) "[-> ->]".
    iApply "H".
  Qed.

  Lemma OT_S_eq :
    ⊢ ⟪ Mod (IProd CrsPort (IProd (λ θ, 𝟙 -{ ¡ θ }-∘ (𝔾 × 𝔾)) (λ θ, CT -{ ¡ θ }-∘ 𝟙))) SPort ⟫
        OT_S OT_S.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (resl resr) "Hres".
    rewrite /IProd. iEval (rewrite eq_lift_prod) in "Hres".
    iDestruct "Hres" as (crsl crsr nl nr) "(-> & -> & #Hcrs & Hn)".
    iEval (rewrite eq_lift_prod) in "Hn".
    iDestruct "Hn" as (rcl rcr sdl sdr) "(-> & -> & Hrecv & Hsend)".
    rewrite /OT_S /sample /enc is_unit. eq_pures'.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iApply eq_value. iModIntro. rewrite /SPort. iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->]. eq_pures'.
    eq_reshape_l (crsl _). eq_reshape_r (crsr _).
    iApply (eq_get_crs with "Hcrs"); try (intros; apply _).
    iIntros (h1 h0 g1 g0). eq_pures'.
    eq_reshape_l (rcl _). eq_reshape_r (rcr _).
    iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T (𝔾 × 𝔾)%T (⟪ CT -{ ¡ θ }-∘ 𝟙 ⟫ sdl sdr)%I
              with "Hρ Hrecv [] Hsend");
      try (intros; apply _); first by iEval (rewrite eq_lift_unit).
    iIntros "!>" (uvl uvr) "Huv Hsend". iEval (rewrite eq_lift_prod) in "Huv".
    iDestruct "Huv" as (ul ur vl vr) "(-> & -> & Hu & Hv)".
    iEval (rewrite eq_lift_group) in "Hu". iDestruct "Hu" as (u) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hv". iDestruct "Hv" as (v) "[-> ->]".
    eq_pures'.
    iApply eq_value. iModIntro. iApply eq_lift_arr. iIntros (ml mr) "Hm".
    iEval (rewrite eq_lift_prod) in "Hm".
    iDestruct "Hm" as (m0l m0r m1l m1r) "(-> & -> & Hm0 & Hm1)".
    iEval (rewrite eq_lift_group) in "Hm0". iDestruct "Hm0" as (m0) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hm1". iDestruct "Hm1" as (m1) "[-> ->]".
    eq_pures'.
    case_bool_decide; eq_pures'.
    { iApply eq_value. by iEval (rewrite eq_lift_unit). }
    do 4 (eq_couple_rand_rand; iIntros (? ?); eq_pures').
    iApply (eq_call_frame_aff θ (¡ θ)%R CT 𝟙%T emp%I sdl sdr _ _ [] [] with "Hρ Hsend [] []");
      try (intros; apply _); [by iApply eq_ctxts|done|].
    iIntros "!>" (??) "Hu _". by iApply eq_value.
  Qed.

  Lemma OT_R_eq :
    ⊢ ⟪ Mod (IProd CrsPort (IProd (λ θ, (𝔾 × 𝔾) -{ ¡ θ }-∘ 𝟙) (λ θ, 𝟙 -{ ¡ θ }-∘ CT))) RPort ⟫
        OT_R OT_R.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (resl resr) "Hres".
    rewrite /IProd. iEval (rewrite eq_lift_prod) in "Hres".
    iDestruct "Hres" as (crsl crsr nl nr) "(-> & -> & #Hcrs & Hn)".
    iEval (rewrite eq_lift_prod) in "Hn".
    iDestruct "Hn" as (sdl sdr rcl rcr) "(-> & -> & Hsend & Hrecv)".
    rewrite /OT_R /sample /dec. eq_pures'.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iApply eq_value. iModIntro. rewrite /RPort. iApply eq_lift_arr. iIntros (bl br) "Hb".
    iEval (rewrite eq_lift_bool) in "Hb". iDestruct "Hb" as %(b & -> & ->). eq_pures'.
    eq_reshape_l (crsl _). eq_reshape_r (crsr _).
    iApply (eq_get_crs with "Hcrs"); try (intros; apply _).
    iIntros (h1 h0 g1 g0). eq_pures'.
    eq_couple_rand_rand. iIntros (x Hx).
    destruct b; (eq_pures';
      eq_reshape_l (sdl _); eq_reshape_r (sdr _);
      (iApply (eq_call_frame_aff θ (¡ θ)%R (𝔾 × 𝔾)%T 𝟙%T (⟪ 𝟙 -{ ¡ θ }-∘ CT ⟫ rcl rcr)%I
                 with "Hρ Hsend [] Hrecv");
         try (intros; apply _); first by iApply eq_pair);
      iIntros "!>" (??) "_ Hrecv"; eq_pures';
      eq_reshape_l (rcl _); eq_reshape_r (rcr _);
      (iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T CT emp%I with "Hρ Hrecv [] []");
         try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|]);
      iIntros "!>" (el er) "He _";
      iDestruct (eq_lift_ctxts with "He") as (c0 d0 c1 d1) "[-> ->]";
      eq_pures'; iApply eq_value; iModIntro; by iApply eq_group_val).
  Qed.

  Lemma PARTIES_OT_eq :
    ⊢ ⟪ Mod (IProd CrsPort (IProd (OEpT (𝔾 × 𝔾)) (OEpT CT))) OTPorts ⟫ PARTIES_OT PARTIES_OT.
  Proof.
    iPoseProof OT_S_eq as "HS". iPoseProof OT_R_eq as "HR".
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall) in "HS". iEval (rewrite eq_lift_forall) in "HR".
    iEval (rewrite eq_lift_forall). iIntros (θ).
    iSpecialize ("HS" $! θ). iSpecialize ("HR" $! θ).
    iModIntro. iApply eq_lift_arr. iIntros (resl resr) "Hres".
    rewrite /IProd /OEpT. iEval (rewrite eq_lift_prod) in "Hres".
    iDestruct "Hres" as (crsl crsr nl nr) "(-> & -> & #Hcrs & Hn)".
    iEval (rewrite eq_lift_prod) in "Hn". iDestruct "Hn" as (rsl rsr srl srr) "(-> & -> & Hrs & Hsr)".
    iEval (rewrite eq_lift_prod) in "Hrs". iDestruct "Hrs" as (a1 a2 b1 b2) "(-> & -> & Hsrs & Hrrs)".
    iEval (rewrite eq_lift_prod) in "Hsr". iDestruct "Hsr" as (c1 c2 d1 d2) "(-> & -> & Hssr & Hrsr)".
    rewrite /PARTIES_OT. eq_pures'.
    iAssert (⎡(¡ ⟨⟩)%R ≤ᵣ (⟨⟩%R : sem_row Σ)⎤)%I as "#H0"; first by iApply row_le_mfbang_elim_nil.
    eq_reshape_l (OT_R _). eq_reshape_r (OT_R _).
    iApply (eq_call_frame ⟨⟩%R ⟨⟩%R
              (CrsPort θ × (((𝔾 × 𝔾) -{ ¡ θ }-∘ 𝟙) × (𝟙 -{ ¡ θ }-∘ CT)))%T (RPort θ)
              (⟪ 𝟙 -{ ¡ θ }-∘ (𝔾 × 𝔾) ⟫ b1 b2 ∗ ⟪ CT -{ ¡ θ }-∘ 𝟙 ⟫ c1 c2)%I
              with "H0 HR [Hsrs Hrsr] [$Hrrs $Hssr]"); try (intros; apply _).
    { iEval (rewrite eq_lift_prod). iExists _, _, _, _. do 2 (iSplit; first done).
      iSplitR; first done.
      iEval (rewrite eq_lift_prod). iExists _, _, _, _. do 2 (iSplit; first done). iFrame. }
    iIntros "!>" (rpl rpr) "Hrp [Hrrs Hssr]". eq_pures'.
    eq_reshape_l (OT_S _). eq_reshape_r (OT_S _).
    iApply (eq_call_frame ⟨⟩%R ⟨⟩%R
              (CrsPort θ × ((𝟙 -{ ¡ θ }-∘ (𝔾 × 𝔾)) × (CT -{ ¡ θ }-∘ 𝟙)))%T (SPort θ)
              (⟪ RPort θ ⟫ rpl rpr)%I with "H0 HS [Hrrs Hssr] Hrp"); try (intros; apply _).
    { iEval (rewrite eq_lift_prod). iExists _, _, _, _. do 2 (iSplit; first done).
      iSplitR; first done.
      iEval (rewrite eq_lift_prod). iExists _, _, _, _. do 2 (iSplit; first done). iFrame. }
    iIntros "!>" (spl spr) "Hsp Hrp". eq_pures'.
    iApply eq_value. iModIntro. rewrite /OTPorts. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iFrame.
  Qed.

  (* The simulator: the real parties on dummy inputs, in decryption mode. *)
  Lemma HYB1_OT_H_real_typed : ⊢ ⊨ᵥ HYB1_OT_H DDH_real ≤ HYB1_OT_H DDH_real : Mod OTHNet OTPorts.
  Proof.
    iApply comp_op_typed; first by iApply eq_val_typed; iApply PARTIES_OT_eq.
    iApply tens_op_typed; first by iApply eq_val_typed; iApply F_CRS_real_eq.
    iApply tens_op_typed.
    - iApply (F_OAUTH_typed_gen (𝔾 × 𝔾) _ (eq_ground_prod _ _ _ _ eq_ground_group eq_ground_group)).
    - iApply (F_OAUTH_typed_gen CT _
                (eq_ground_prod _ _ _ _
                   (eq_ground_prod _ _ _ _ eq_ground_group eq_ground_group)
                   (eq_ground_prod _ _ _ _ eq_ground_group eq_ground_group))).
  Qed.

  Lemma S_OT_H_typed : ⊢ ⊨ᵥ S_OT_H ≤ S_OT_H : Mod OTHNet OTHAdv.
  Proof. iApply comp_op_typed; [iApply DUMMY_OT_typed|iApply HYB1_OT_H_real_typed]. Qed.

  (* ---------------------------------------------------------------- *)
  (* The simulator with the receiver corrupted, which runs [OT_S].      *)
  (* ---------------------------------------------------------------- *)

  Lemma S_OT_R_eq : ⊢ ⟪ Mod (IProd Pub RNet) OTAdv ⟫ S_OT_R S_OT_R.
  Proof.
    iPoseProof OT_S_eq as "HS".
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall) in "HS".
    iEval (rewrite eq_lift_forall). iIntros (θ). iSpecialize ("HS" $! θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /Pub /RNet. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (pl pr nl nr) "(-> & -> & #Hpub & Hnet)".
    iEval (rewrite eq_lift_prod) in "Hnet".
    iDestruct "Hnet" as (rl rr sl sr) "(-> & -> & #Hrecv & #Hsend)".
    rewrite /S_OT_R /sample.
    eq_pures'.
    eq_couple_rand_rand. iIntros (a1 Ha1). eq_pures'.
    eq_couple_rand_rand. iIntros (t0 Ht0). eq_pures'.
    eq_couple_rand_rand. iIntros (t1 Ht1). eq_pures'.
    eq_reshape_l (pl _). eq_reshape_r (pr _).
    iApply (eq_call MS ⟨⟩%R Crs 𝟙%T with "Hpub"); try (intros; apply _); first iApply eq_crs.
    iIntros "!>" (wl wr) "_". simpl. eq_pures'.
    iApply eq_value. iModIntro. rewrite /OTAdv. iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iAssert (⎡(¡ ⟨⟩)%R ≤ᵣ (¡ θ)%R⎤)%I as "#H0".
    { iApply (row_le_trans _ ⟨⟩%R); [iApply row_le_mfbang_elim_nil|iApply row_le_nil]. }
    eq_pures'.
    (* The receiver's message. *)
    eq_reshape_l (rl _). eq_reshape_r (rr _).
    iApply (eq_call_frame θ (¡ θ)%R 𝟙%T (𝔾 × 𝔾)%T emp%I with "Hρ Hrecv [] []");
      try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (uvl uvr) "Huv _". iEval (rewrite eq_lift_prod) in "Huv".
    iDestruct "Huv" as (ul ur vl vr) "(-> & -> & Hu & Hv)".
    iEval (rewrite eq_lift_group) in "Hu". iDestruct "Hu" as (u) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hv". iDestruct "Hv" as (v) "[-> ->]".
    eq_pures'.
    (* The real sender, on that message. *)
    eq_reshape_l (OT_S _). eq_reshape_r (OT_S _).
    iApply (eq_call_frame ⟨⟩%R (¡ θ)%R
              (CrsPort θ × ((𝟙 -{ ¡ θ }-∘ (𝔾 × 𝔾)) × (((𝔾 × 𝔾) × (𝔾 × 𝔾)) -{ ¡ θ }-∘ 𝟙)))%T (SPort θ)
              emp%I with "H0 HS [] []"); try (intros; apply _); [|done|].
    { iEval (rewrite eq_lift_prod). iExists _, _, _, _. do 2 (iSplit; first done).
      iSplitR.
      { rewrite /CrsPort. iModIntro. iApply eq_lift_arr. iIntros (??) "Hw".
        iEval (rewrite eq_lift_unit) in "Hw". iDestruct "Hw" as %[-> ->]. eq_pures'.
        iApply eq_value. iModIntro. iApply eq_crs. }
      iEval (rewrite eq_lift_prod). iExists _, _, _, _. do 2 (iSplit; first done). iSplitR.
      - iApply eq_lift_arr. iIntros (??) "Hw". iEval (rewrite eq_lift_unit) in "Hw".
        iDestruct "Hw" as %[-> ->]. eq_pures'. iApply eq_value. iModIntro. by iApply eq_pair.
      - by iApply eq_arr_aff. }
    iIntros "!>" (spl spr) "Hsp _". rewrite /SPort. eq_pures'.
    eq_reshape_l (spl _). eq_reshape_r (spr _).
    iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T ((𝔾 × 𝔾) -{ ¡ θ }-∘ 𝟙)%T emp%I with "Hρ Hsp [] []");
      try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (kl kr) "Hk _". eq_pures'.
    (* The extracted choice, and the second phase on the chosen message. *)
    iApply eq_value. iModIntro. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitR; first iApply eq_bool.
    iApply eq_lift_arr. iIntros (ml mr) "Hm".
    iEval (rewrite eq_lift_group) in "Hm". iDestruct "Hm" as (m) "[-> ->]".
    case_bool_decide; eq_pures';
      (iApply (eq_call_frame_aff θ (¡ θ)%R (𝔾 × 𝔾)%T 𝟙%T emp%I kl kr _ _ [] [] with "Hρ Hk [] []");
         try (intros; apply _); [by iApply eq_pair|done|]);
      iIntros "!>" (??) "Hu _"; by iApply eq_value.
  Qed.

  Lemma S_OT_R_typed : ⊢ ⊨ᵥ S_OT_R ≤ S_OT_R : Mod (IProd Pub RNet) OTAdv.
  Proof. apply eq_val_typed, S_OT_R_eq. Qed.

End ot_typing.
