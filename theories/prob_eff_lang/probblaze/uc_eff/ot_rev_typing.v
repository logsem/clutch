(* The typings of the components of oblivious transfer reversal
   (uc_eff/DESIGN.md, section 6), as self-equivalences in the logic of
   [eq/]: the parties, and the functionalities and simulators of the three
   cases.  They are the premises of [uc_composition] in [ot_rev_ot.v]. *)

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
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules auth ot ot_eq
  ot_corrupted_receiver ot_corrupted_sender ot_rev ot_rev_corrupted_sender
  ot_rev_corrupted_receiver.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section ot_rev_typing.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Open Scope bi_scope.

  (* Bob, the receiver of the transfer, for any interface [R] to Alice's
     message that can be used as a one-shot receive: the adversary's
     ([ARecv], Alice corrupted) or a channel's endpoint (both honest). *)
  Lemma TO_R_eq_gen (R : sem_row Σ → sem_ty Σ) :
    (∀ θ rl rr, ⟪ R θ ⟫ rl rr ⊢ ⟪ 𝟙 -{ ¡ θ }-∘ 𝔹 ⟫ rl rr) →
    ⊢ ⟪ Mod (IProd SPort R) TPort ⟫ TO_R TO_R.
  Proof.
    intros HR.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (spl spr rl rr) "(-> & -> & Hsport & Hrecv)".
    iDestruct (HR with "Hrecv") as "Hrecv".
    rewrite /TO_R /ot_rev.flip /bxor /gbit is_unit. eq_pures'.
    iApply eq_value. iModIntro. rewrite /TPort. iApply eq_lift_arr. iIntros (cl cr) "Hc".
    iEval (rewrite eq_lift_bool) in "Hc". iDestruct "Hc" as %(c & -> & ->).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    eq_pures'.
    rewrite /SPort.
    eq_reshape_l (spl _). eq_reshape_r (spr _).
    iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T ((𝔾 × 𝔾) -{ ¡ θ }-∘ 𝟙)%T
              (⟪ 𝟙 -{ ¡ θ }-∘ 𝔹 ⟫ rl rr)%I with "Hρ Hsport [] Hrecv");
      try (intros; apply _); first by iEval (rewrite eq_lift_unit).
    iIntros "!>" (sndl sndr) "Hsnd Hrecv". eq_pures'.
    eq_couple_rand_rand. iIntros (k Hk).
    assert (k = 0%nat ∨ k = 1%nat)%type as [-> | ->] by (simpl in Hk; lia); destruct c;
      (eq_pures';
       eq_reshape_l (sndl _); eq_reshape_r (sndr _);
       (iApply (eq_call_frame_aff θ (¡ θ)%R (𝔾 × 𝔾)%T 𝟙%T (⟪ 𝟙 -{ ¡ θ }-∘ 𝔹 ⟫ rl rr)%I
                  with "Hρ Hsnd [] Hrecv");
          try (intros; apply _); first by iApply eq_pair);
       iIntros "!>" (??) "Hu Hrecv"; iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->];
       eq_pures'; eq_reshape_l (rl _); eq_reshape_r (rr _);
       (iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T 𝔹%T emp%I with "Hρ Hrecv [] []");
          try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|]);
       iIntros "!>" (ml mr) "Hm _"; iEval (rewrite eq_lift_bool) in "Hm";
       iDestruct "Hm" as %(m & -> & ->);
       destruct m; eq_pures'; iApply eq_value; iApply eq_bool).
  Qed.

  Lemma TO_R_eq : ⊢ ⟪ Mod (IProd SPort ARecv) TPort ⟫ TO_R TO_R.
  Proof. iApply TO_R_eq_gen. intros θ rl rr. rewrite /ARecv. iApply eq_arr_aff. Qed.

  Lemma TO_R_typed : ⊢ ⊨ᵥ TO_R ≤ TO_R : Mod (IProd SPort ARecv) TPort.
  Proof. apply eq_val_typed, TO_R_eq. Qed.

  (* Alice, the sender of the transfer, likewise for any interface [S] to
     her message that can be used as a one-shot send. *)
  Lemma TO_S_eq_gen (S : sem_row Σ → sem_ty Σ) :
    (∀ θ sl sr, ⟪ S θ ⟫ sl sr ⊢ ⟪ 𝔹 -{ ¡ θ }-∘ 𝟙 ⟫ sl sr) →
    ⊢ ⟪ Mod (IProd RPort S) TSPort ⟫ TO_S TO_S.
  Proof.
    intros HS.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (rpl rpr sl sr) "(-> & -> & Hrport & Hsend)".
    iDestruct (HS with "Hsend") as "Hsend".
    rewrite /TO_S /bxor /ungbit. eq_pures'.
    iApply eq_value. iModIntro. rewrite /TSPort. iApply eq_lift_arr. iIntros (xl xr) "Hx".
    iEval (rewrite eq_lift_prod) in "Hx".
    iDestruct "Hx" as (x0l x0r x1l x1r) "(-> & -> & Hx0 & Hx1)".
    iEval (rewrite eq_lift_bool) in "Hx0". iDestruct "Hx0" as %(x0 & -> & ->).
    iEval (rewrite eq_lift_bool) in "Hx1". iDestruct "Hx1" as %(x1 & -> & ->).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    rewrite /RPort.
    destruct x0, x1; eq_pures';
      eq_reshape_l (rpl _); eq_reshape_r (rpr _);
      (iApply (eq_call_frame_aff θ (¡ θ)%R 𝔹%T 𝔾%T (⟪ 𝔹 -{ ¡ θ }-∘ 𝟙 ⟫ sl sr)%I
                 with "Hρ Hrport [] Hsend");
         try (intros; apply _); first iApply eq_bool);
      iIntros "!>" (zl zr) "Hz Hsend"; iEval (rewrite eq_lift_group) in "Hz";
      iDestruct "Hz" as (z) "[-> ->]";
      eq_pures'; case_bool_decide; eq_pures';
      (iApply (eq_call_frame_aff θ (¡ θ)%R 𝔹%T 𝟙%T emp%I sl sr _ _ [] [] with "Hρ Hsend [] []");
         try (intros; apply _); [iApply eq_bool|done|]);
      iIntros "!>" (??) "Hu _"; by iApply eq_value.
  Qed.

  Lemma TO_S_eq : ⊢ ⟪ Mod (IProd RPort ASend) TSPort ⟫ TO_S TO_S.
  Proof. iApply TO_S_eq_gen. intros θ sl sr. rewrite /ASend. iApply eq_arr_aff. Qed.

  Lemma TO_S_typed : ⊢ ⊨ᵥ TO_S ≤ TO_S : Mod (IProd RPort ASend) TSPort.
  Proof. apply eq_val_typed, TO_S_eq. Qed.

  (* ---------------------------------------------------------------- *)
  (* Alice corrupted.                                                   *)
  (* ---------------------------------------------------------------- *)

  Lemma F_TO_S_eq : ⊢ ⟪ Mod TOSAdv TPort ⟫ F_TO_S F_TO_S.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (il ir) "#Hinput".
    rewrite /F_TO_S. eq_pures'.
    iApply eq_value. iModIntro. rewrite /TPort. iApply eq_lift_arr. iIntros (cl cr) "Hc".
    iEval (rewrite eq_lift_bool) in "Hc". iDestruct "Hc" as %(c & -> & ->).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    eq_pures'.
    iApply (eq_call_frame θ (¡ θ)%R 𝟙%T (𝔹 × 𝔹)%T emp%I il ir _ _ [AppRCtx _] [AppRCtx _]
              with "Hρ Hinput [] []"); try (intros; apply _);
      [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (xl xr) "Hx _". iEval (rewrite eq_lift_prod) in "Hx".
    iDestruct "Hx" as (x0l x0r x1l x1r) "(-> & -> & Hx0 & Hx1)".
    iEval (rewrite eq_lift_bool) in "Hx0". iDestruct "Hx0" as %(x0 & -> & ->).
    iEval (rewrite eq_lift_bool) in "Hx1". iDestruct "Hx1" as %(x1 & -> & ->).
    destruct c; eq_pures'; iApply eq_value; iApply eq_bool.
  Qed.

  Lemma F_TO_S_typed : ⊢ ⊨ᵥ F_TO_S ≤ F_TO_S : Mod TOSAdv TPort.
  Proof. apply eq_val_typed, F_TO_S_eq. Qed.

  Lemma S_TO_S_eq : ⊢ ⟪ Mod (IProd OTAdv ARecv) TOSAdv ⟫ S_TO_S S_TO_S.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /OTAdv /ARecv. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (otl otr rl rr) "(-> & -> & Hot & #Hrecv)".
    iEval (rewrite eq_lift_prod) in "Hot".
    iDestruct "Hot" as (cl cr ol or) "(-> & -> & #Hchoose & #Houtput)".
    rewrite /S_TO_S /ot_rev.flip /bxor /gbit is_unit. eq_pures'.
    iApply eq_value. iModIntro. rewrite /TOSAdv. iModIntro.
    iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    eq_pures'.
    eq_reshape_l (cl _). eq_reshape_r (cr _).
    iApply (eq_call MS θ 𝟙%T 𝔹%T with "Hchoose"); try (intros; apply _);
      first by iEval (rewrite eq_lift_unit).
    iIntros "!>" (sl sr) "Hs". iEval (rewrite eq_lift_bool) in "Hs". iDestruct "Hs" as %(s & -> & ->).
    eq_pures'.
    eq_couple_rand_rand. iIntros (k Hk).
    assert (k = 0%nat ∨ k = 1%nat)%type as [-> | ->] by (simpl in Hk; lia);
      (eq_pures';
       eq_reshape_l (ol _); eq_reshape_r (or _);
       (iApply (eq_call MS θ 𝔾%T 𝟙%T with "Houtput"); try (intros; apply _);
          [by iApply eq_group_val|]);
       iIntros "!>" (??) "Hu"; iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->];
       eq_pures'; eq_reshape_l (rl _); eq_reshape_r (rr _);
       (iApply (eq_call MS θ 𝟙%T 𝔹%T with "Hrecv"); try (intros; apply _);
          [by iEval (rewrite eq_lift_unit)|]);
       iIntros "!>" (ml mr) "Hm"; iEval (rewrite eq_lift_bool) in "Hm";
       iDestruct "Hm" as %(m & -> & ->);
       destruct m, s; eq_pures'; iApply eq_value; iModIntro; iEval (rewrite eq_lift_prod);
       iExists _, _, _, _; do 2 (iSplit; first done); iSplitL; iApply eq_bool).
  Qed.

  Lemma S_TO_S_typed : ⊢ ⊨ᵥ S_TO_S ≤ S_TO_S : Mod (IProd OTAdv ARecv) TOSAdv.
  Proof. apply eq_val_typed, S_TO_S_eq. Qed.

  (* ---------------------------------------------------------------- *)
  (* Bob corrupted.                                                     *)
  (* ---------------------------------------------------------------- *)

  Lemma F_TO_R_eq : ⊢ ⟪ Mod TORAdv TSPort ⟫ F_TO_R F_TO_R.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /TORAdv. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (cl cr ol or) "(-> & -> & #Hchoose & #Houtput)".
    rewrite /F_TO_R. eq_pures'.
    iApply eq_value. iModIntro. rewrite /TSPort. iApply eq_lift_arr. iIntros (xl xr) "Hx".
    iEval (rewrite eq_lift_prod) in "Hx".
    iDestruct "Hx" as (x0l x0r x1l x1r) "(-> & -> & Hx0 & Hx1)".
    iEval (rewrite eq_lift_bool) in "Hx0". iDestruct "Hx0" as %(x0 & -> & ->).
    iEval (rewrite eq_lift_bool) in "Hx1". iDestruct "Hx1" as %(x1 & -> & ->).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    eq_pures'.
    eq_reshape_l (cl _). eq_reshape_r (cr _).
    iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝔹%T emp%I with "Hρ Hchoose [] []");
      try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (bl br) "Hb _". iEval (rewrite eq_lift_bool) in "Hb".
    iDestruct "Hb" as %(b & -> & ->).
    destruct b; eq_pures';
      (iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝟙%T emp%I ol or _ _ [] [] with "Hρ Houtput [] []");
         try (intros; apply _); [iApply eq_bool|done|]);
      iIntros "!>" (??) "Hu _"; by iApply eq_value.
  Qed.

  Lemma F_TO_R_typed : ⊢ ⊨ᵥ F_TO_R ≤ F_TO_R : Mod TORAdv TSPort.
  Proof. apply eq_val_typed, F_TO_R_eq. Qed.

  Definition NSTR : namespace := nroot .@ "stor".

  (* The simulator's state, Bob's mask, the same on both sides. *)
  Definition str_rel (st st' : loc) : iPropD Σ :=
    ∃ w : val, st ↦ₗ w ∗ st' ↦ᵣ w ∗ ⌜w = NONEV ∨ ∃ r : bool, w = SOMEV #r⌝.

  Lemma S_TO_R_eq : ⊢ ⟪ Mod (IProd OTSAdv ASend) TORAdv ⟫ S_TO_R S_TO_R.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /OTSAdv /ASend. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (il ir sl sr) "(-> & -> & #Hinput & #Hsend)".
    rewrite /S_TO_R /bxor /ungbit. eq_pures'.
    eq_alloc_l st as "Hst". eq_pures_l. eq_alloc_r st' as "Hst'". eq_pures_r.
    iApply (eq_na_alloc (str_rel st st') NSTR).
    iSplitL "Hst Hst'"; first (iNext; iExists _; iFrame; by iLeft). iIntros "#Hinv".
    iApply eq_value. iModIntro. rewrite /TORAdv. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL.
    - (* choose *)
      iModIntro. iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (il _). eq_reshape_r (ir _).
      iApply (eq_call MS θ 𝟙%T (𝔾 × 𝔾)%T with "Hinput"); try (intros; apply _);
        first by iEval (rewrite eq_lift_unit).
      iIntros "!>" (uvl uvr) "Huv". iEval (rewrite eq_lift_prod) in "Huv".
      iDestruct "Huv" as (u0l u0r u1l u1r) "(-> & -> & Hu0 & Hu1)".
      iEval (rewrite eq_lift_group) in "Hu0". iDestruct "Hu0" as (u0) "[-> ->]".
      iEval (rewrite eq_lift_group) in "Hu1". iDestruct "Hu1" as (u1) "[-> ->]".
      eq_pures'.
      iApply (eq_na_open _ _ NSTR); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as (w) "(Hst & Hst' & _)".
      case_bool_decide; case_bool_decide; eq_pures'; eq_store_l; eq_store_r;
        (iApply eq_na_close_rule; iFrame "Hclose";
         iSplitL "Hst Hst'"; first (iNext; iExists _; iFrame; iRight; by iExists _));
        eq_pures'; iApply eq_value; iApply eq_bool.
    - (* output *)
      iModIntro. iApply eq_lift_arr. iIntros (xl xr) "Hx".
      iEval (rewrite eq_lift_bool) in "Hx". iDestruct "Hx" as %(x & -> & ->).
      eq_pures'.
      iApply (eq_na_open _ _ NSTR); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as (w) "(Hst & Hst' & %Hw)".
      eq_load_l. eq_load_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hst Hst'"; first (iNext; iExists _; by iFrame).
      destruct Hw as [->|(r & ->)].
      { eq_pures'. iApply eq_value. by iEval (rewrite eq_lift_unit). }
      destruct x, r; eq_pures'; iApply (eq_lift_app with "Hsend"); iApply eq_bool.
  Qed.

  Lemma S_TO_R_typed : ⊢ ⊨ᵥ S_TO_R ≤ S_TO_R : Mod (IProd OTSAdv ASend) TORAdv.
  Proof. apply eq_val_typed, S_TO_R_eq. Qed.

  (* ---------------------------------------------------------------- *)
  (* Both honest.                                                       *)
  (* ---------------------------------------------------------------- *)

  (* The parties, on the OT's ports and the channel's endpoints. *)
  Lemma PARTIES_TO_eq : ⊢ ⟪ Mod (IProd OTPorts (OEpT 𝔹)) TPorts ⟫ PARTIES_TO PARTIES_TO.
  Proof.
    iPoseProof (TO_S_eq_gen (λ θ, 𝔹 -{ ¡ θ }-∘ 𝟙)%T ltac:(by intros)) as "HS".
    iPoseProof (TO_R_eq_gen (λ θ, 𝟙 -{ ¡ θ }-∘ 𝔹)%T ltac:(by intros)) as "HR".
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall) in "HS". iEval (rewrite eq_lift_forall) in "HR".
    iEval (rewrite eq_lift_forall). iIntros (θ).
    iSpecialize ("HS" $! θ). iSpecialize ("HR" $! θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /OTPorts /OEpT. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (otl otr abl abr) "(-> & -> & Hot & Hab)".
    iEval (rewrite eq_lift_prod) in "Hot". iDestruct "Hot" as (spl spr rpl rpr) "(-> & -> & Hsp & Hrp)".
    iEval (rewrite eq_lift_prod) in "Hab". iDestruct "Hab" as (sl sr rl rr) "(-> & -> & Hs & Hr)".
    rewrite /PARTIES_TO. eq_pures'.
    iAssert (⎡(¡ ⟨⟩)%R ≤ᵣ (⟨⟩%R : sem_row Σ)⎤)%I as "#H0"; first by iApply row_le_mfbang_elim_nil.
    eq_reshape_l (TO_R _). eq_reshape_r (TO_R _).
    iApply (eq_call_frame ⟨⟩%R ⟨⟩%R (SPort θ × (𝟙 -{ ¡ θ }-∘ 𝔹))%T (TPort θ)
              (⟪ RPort θ ⟫ rpl rpr ∗ ⟪ 𝔹 -{ ¡ θ }-∘ 𝟙 ⟫ sl sr)%I with "H0 HR [Hsp Hr] [$Hrp $Hs]");
      try (intros; apply _).
    { iEval (rewrite eq_lift_prod). iExists _, _, _, _. do 2 (iSplit; first done). iFrame. }
    iIntros "!>" (bl br) "Hb [Hrp Hs]". eq_pures'.
    eq_reshape_l (TO_S _). eq_reshape_r (TO_S _).
    iApply (eq_call_frame ⟨⟩%R ⟨⟩%R (RPort θ × (𝔹 -{ ¡ θ }-∘ 𝟙))%T (TSPort θ)
              (⟪ TPort θ ⟫ bl br)%I with "H0 HS [Hrp Hs] Hb");
      try (intros; apply _).
    { iEval (rewrite eq_lift_prod). iExists _, _, _, _. do 2 (iSplit; first done). iFrame. }
    iIntros "!>" (al ar) "Ha Hb". simpl. eq_pures'.
    iApply eq_value. iModIntro. rewrite /TPorts. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iFrame.
  Qed.

  Lemma PARTIES_TO_typed : ⊢ ⊨ᵥ PARTIES_TO ≤ PARTIES_TO : Mod (IProd OTPorts (OEpT 𝔹)) TPorts.
  Proof. apply eq_val_typed, PARTIES_TO_eq. Qed.

  Definition NTH : namespace := nroot .@ "toh".

  Definition bits (v : val) : Prop := ∃ b0 b1 : bool, v = (#b0, #b1)%V.

  Lemma F_TO_H_eq : ⊢ ⟪ Mod TOHAdv TPorts ⟫ F_TO_H F_TO_H.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /TOHAdv. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (yal yar ybl ybr) "(-> & -> & #Hya & #Hyb)".
    rewrite /F_TO_H.
    eq_pures_l. eq_alloc_l xs as "Hxs". eq_pures_l. eq_alloc_l cs as "Hcs". eq_pures_l.
    eq_alloc_l fin as "Hfin". eq_pures_l.
    eq_pures_r. eq_alloc_r xs' as "Hxs'". eq_pures_r. eq_alloc_r cs' as "Hcs'". eq_pures_r.
    eq_alloc_r fin' as "Hfin'". eq_pures_r.
    iApply (eq_na_alloc (box_rel_gen bits xs xs') (NTH .@ "xs")).
    iSplitL "Hxs Hxs'"; first (iNext; iLeft; iFrame). iIntros "#Ixs".
    iApply (eq_na_alloc (bool_ref cs cs') (NTH .@ "cs")).
    iSplitL "Hcs Hcs'"; first (iNext; iExists _; iFrame). iIntros "#Ics".
    iApply (eq_na_alloc (bool_ref fin fin') (NTH .@ "fin")).
    iSplitL "Hfin Hfin'"; first (iNext; iExists _; iFrame). iIntros "#Ifin".
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iApply eq_value. iModIntro. rewrite /TPorts. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL.
    - (* Alice *)
      rewrite /TSPort. iApply eq_lift_arr. iIntros (xl xr) "Hx".
      iEval (rewrite eq_lift_prod) in "Hx".
      iDestruct "Hx" as (x0l x0r x1l x1r) "(-> & -> & Hx0 & Hx1)".
      iEval (rewrite eq_lift_bool) in "Hx0". iDestruct "Hx0" as %(x0 & -> & ->).
      iEval (rewrite eq_lift_bool) in "Hx1". iDestruct "Hx1" as %(x1 & -> & ->).
      eq_pures'.
      assert (bits (#x0, #x1)%V) as Hb by (by exists x0, x1).
      eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
      iApply (eq_na_store_box _ _ _ _ _ _ _ _ _ Hb with "Ixs").
      eq_pures'.
      iLöb as "IH".
      eq_reshape_l (yal _). eq_reshape_r (yar _).
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hya [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_bool with "Ics"). iIntros ([]).
      + eq_pures'.
        eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
        iApply (eq_na_store_bool with "Ifin"). eq_pures'.
        iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I yal yar _ _ [] [] with "Hρ Hya [] []");
          try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
        iIntros "!>" (??) "Hu _". by iApply eq_value.
      + eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply "IH".
    - (* Bob *)
      rewrite /TPort. iApply eq_lift_arr. iIntros (cl cr) "Hc".
      iEval (rewrite eq_lift_bool) in "Hc". iDestruct "Hc" as %(c & -> & ->).
      eq_pures'.
      iLöb as "IH".
      eq_reshape_l (ybl _). eq_reshape_r (ybr _).
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hyb [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_box with "Ixs"). iIntros (w) "%Hw".
      destruct Hw as [->|(? & (x0 & x1 & ->) & ->)].
      { eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply "IH". }
      eq_pures'.
      eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
      iApply (eq_na_store_bool with "Ics"). eq_pures'.
      eq_reshape_l (ybl _). eq_reshape_r (ybr _).
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hyb [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      iClear "IH". iLöb as "IH".
      eq_reshape_l (ybl _). eq_reshape_r (ybr _).
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hyb [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_bool with "Ifin"). iIntros ([]).
      + destruct c; eq_pures'; iApply eq_value; iModIntro; iApply eq_bool.
      + eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply "IH".
  Qed.

  Lemma F_TO_H_typed : ⊢ ⊨ᵥ F_TO_H ≤ F_TO_H : Mod TOHAdv TPorts.
  Proof. apply eq_val_typed, F_TO_H_eq. Qed.

  Lemma S_TO_H_eq : ⊢ ⟪ Mod TOHNet TOHAdv ⟫ S_TO_H S_TO_H.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /TOHNet /OTHAdv /LNet. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (otl otr nl nr) "(-> & -> & Hot & Hnet)".
    iEval (rewrite eq_lift_prod) in "Hot".
    iDestruct "Hot" as (ysl ysr yrl yrr) "(-> & -> & #Hys & #Hyr)".
    iEval (rewrite eq_lift_prod) in "Hnet".
    iDestruct "Hnet" as (lkl lkr dl dr) "(-> & -> & #Hleak & #Hdel)".
    rewrite /S_TO_H /ot_rev.flip.
    eq_pures_l. eq_alloc_l rho as "H1". eq_pures_l. eq_alloc_l ain as "H2". eq_pures_l.
    eq_alloc_l alast as "H3". eq_pures_l. eq_alloc_l bgo as "H4". eq_pures_l.
    eq_alloc_l bsent as "H5". eq_pures_l.
    eq_pures_r. eq_alloc_r rho' as "H1'". eq_pures_r. eq_alloc_r ain' as "H2'". eq_pures_r.
    eq_alloc_r alast' as "H3'". eq_pures_r. eq_alloc_r bgo' as "H4'". eq_pures_r.
    eq_alloc_r bsent' as "H5'". eq_pures_r.
    iApply (eq_na_alloc (bool_ref rho rho') (NTH .@ "rho")).
    iSplitL "H1 H1'"; first (iNext; iExists _; iFrame). iIntros "#Irho".
    iApply (eq_na_alloc (bool_ref ain ain') (NTH .@ "ain")).
    iSplitL "H2 H2'"; first (iNext; iExists _; iFrame). iIntros "#Iain".
    iApply (eq_na_alloc (bool_ref alast alast') (NTH .@ "alast")).
    iSplitL "H3 H3'"; first (iNext; iExists _; iFrame). iIntros "#Ialast".
    iApply (eq_na_alloc (bool_ref bgo bgo') (NTH .@ "bgo")).
    iSplitL "H4 H4'"; first (iNext; iExists _; iFrame). iIntros "#Ibgo".
    iApply (eq_na_alloc (bool_ref bsent bsent') (NTH .@ "bsent")).
    iSplitL "H5 H5'"; first (iNext; iExists _; iFrame). iIntros "#Ibsent".
    iApply eq_value. iModIntro. rewrite /TOHAdv. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL.
    - (* Alice *)
      iModIntro. iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_bool with "Ialast"). iIntros ([]).
      + eq_pures'.
        eq_reshape_l (Load _). eq_reshape_r (Load _).
        iApply (eq_na_load_bool with "Irho"). iIntros (r). eq_pures'.
        iApply (eq_lift_app with "Hleak"). iApply eq_bool.
      + eq_pures'.
        eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
        iApply (eq_na_store_bool with "Iain"). eq_pures'.
        eq_reshape_l (yrl _). eq_reshape_r (yrr _).
        iApply (eq_call MS θ 𝟙%T 𝟙%T with "Hyr"); try (intros; apply _);
          first by iEval (rewrite eq_lift_unit).
        iIntros "!>" (??) "Hu". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
        eq_pures'.
        eq_reshape_l (Load _). eq_reshape_r (Load _).
        iApply (eq_na_load_bool with "Ibsent"). iIntros ([]); eq_pures'.
        * eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
          iApply (eq_na_store_bool with "Ialast"). eq_pures'.
          iApply eq_value. by iEval (rewrite eq_lift_unit).
        * iApply eq_value. by iEval (rewrite eq_lift_unit).
    - (* Bob *)
      iModIntro. iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_bool with "Ibsent"). iIntros ([]).
      { eq_pures'. iApply (eq_lift_app with "Hdel"). by iEval (rewrite eq_lift_unit). }
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_bool with "Ibgo"). iIntros ([]).
      + eq_pures'.
        eq_couple_rand_rand. iIntros (k Hk).
        assert (k = 0%nat ∨ k = 1%nat)%type as [-> | ->] by (simpl in Hk; lia);
          (eq_pures';
           eq_reshape_l (Store _ _); eq_reshape_r (Store _ _);
           iApply (eq_na_store_bool with "Irho"); eq_pures';
           eq_reshape_l (Store _ _); eq_reshape_r (Store _ _);
           iApply (eq_na_store_bool with "Ibsent"); eq_pures';
           iApply (eq_lift_app with "Hys"); by iEval (rewrite eq_lift_unit)).
      + eq_pures'.
        eq_reshape_l (ysl _). eq_reshape_r (ysr _).
        iApply (eq_call MS θ 𝟙%T 𝟙%T with "Hys"); try (intros; apply _);
          first by iEval (rewrite eq_lift_unit).
        iIntros "!>" (??) "Hu". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
        eq_pures'.
        eq_reshape_l (Load _). eq_reshape_r (Load _).
        iApply (eq_na_load_bool with "Iain"). iIntros ([]); eq_pures'.
        * eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
          iApply (eq_na_store_bool with "Ibgo"). eq_pures'.
          iApply eq_value. by iEval (rewrite eq_lift_unit).
        * iApply eq_value. by iEval (rewrite eq_lift_unit).
  Qed.

  Lemma S_TO_H_typed : ⊢ ⊨ᵥ S_TO_H ≤ S_TO_H : Mod TOHNet TOHAdv.
  Proof. apply eq_val_typed, S_TO_H_eq. Qed.

End ot_rev_typing.
