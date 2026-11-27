(* The typings of the components of oblivious transfer reversal, as
   self-equivalences in the logic of [eq/]: the parties, and the
   functionalities and simulators of the three cases.  They are the premises of [uc_composition] in [ot_rev_ot.v]. *)

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
  ot_typing
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
    iModIntro. iApply eq_lift_arr. iIntros (il ir) "Hinput".
    rewrite /F_TO_S. eq_pures'.
    iApply eq_value. iModIntro. rewrite /TPort. iApply eq_lift_arr. iIntros (cl cr) "Hc".
    iEval (rewrite eq_lift_bool) in "Hc". iDestruct "Hc" as %(c & -> & ->).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    eq_pures'. rewrite /TOSAdv.
    eq_reshape_l (il _). eq_reshape_r (ir _).
    iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T (𝔹 × 𝔹)%T emp%I with "Hρ Hinput [] []");
      try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (xl xr) "Hx _". iEval (rewrite eq_lift_prod) in "Hx".
    iDestruct "Hx" as (x0l x0r x1l x1r) "(-> & -> & Hx0 & Hx1)".
    iEval (rewrite eq_lift_bool) in "Hx0". iDestruct "Hx0" as %(x0 & -> & ->).
    iEval (rewrite eq_lift_bool) in "Hx1". iDestruct "Hx1" as %(x1 & -> & ->).
    destruct c; eq_pures'; iApply eq_value; iApply eq_bool.
  Qed.

  Lemma F_TO_S_typed : ⊢ ⊨ᵥ F_TO_S ≤ F_TO_S : Mod TOSAdv TPort.
  Proof. apply eq_val_typed, F_TO_S_eq. Qed.

  Lemma HYB_TO_S_typed : ⊢ ⊨ᵥ HYB_TO_S ≤ HYB_TO_S : Mod (IProd OTAdv ARecv) TPort.
  Proof.
    iApply comp_op_typed; first iApply TO_R_typed.
    iApply tens_op_typed; [iApply F_OT_R_typed|iApply id_mod_typed].
  Qed.

  Lemma S_TO_S_eq : ⊢ ⟪ Mod (IProd OTAdv ARecv) TOSAdv ⟫ S_TO_S S_TO_S.
  Proof.
    iPoseProof (val_typed_eq _ _ HYB_TO_S_typed) as "HH".
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall) in "HH".
    iEval (rewrite eq_lift_forall). iIntros (θ). iSpecialize ("HH" $! θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /ARecv. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (chl chr rl rr) "(-> & -> & Hch & #Hrecv)".
    rewrite /S_TO_S /bxor. eq_pures'.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iPoseProof (row_le_nil_flip θ) as "#H0".
    iApply eq_value. iModIntro. rewrite /TOSAdv. iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    eq_pures'. rewrite /OTAdv.
    (* Alice's OT choice. *)
    eq_reshape_l (chl _). eq_reshape_r (chr _).
    iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T (𝔹 × (𝔾 -{ ¡ θ }-∘ 𝟙))%T emp%I with "Hρ Hch [] []");
      try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (pl pr) "Hp _". iEval (rewrite eq_lift_prod) in "Hp".
    iDestruct "Hp" as (sl sr ol or) "(-> & -> & Hs & Hout)".
    iEval (rewrite eq_lift_bool) in "Hs". iDestruct "Hs" as %(s & -> & ->).
    eq_pures'.
    (* Bob on the dummy choice, with the choice replayed. *)
    eq_reshape_l (HYB_TO_S _). eq_reshape_r (HYB_TO_S _).
    iApply (eq_call_frame ⟨⟩%R (¡ θ)%R (OTAdv θ × ARecv θ)%T (TPort θ) emp%I
              with "H0 HH [Hout] []"); try (intros; apply _); [|done|].
    { iEval (rewrite eq_lift_prod). iExists _, _, _, _. do 2 (iSplit; first done).
      iSplitL; last done. rewrite /OTAdv. iApply eq_lift_arr. iIntros (??) "Hw".
      iEval (rewrite eq_lift_unit) in "Hw". iDestruct "Hw" as %[-> ->]. eq_pures'.
      iApply eq_value. iModIntro. iEval (rewrite eq_lift_prod).
      iExists _, _, _, _. do 2 (iSplit; first done). iFrame "Hout". iApply eq_bool. }
    iIntros "!>" (tl tr) "Ht _". rewrite /TPort. eq_pures'.
    eq_reshape_l (tl _). eq_reshape_r (tr _).
    iApply (eq_call_frame_aff θ (¡ θ)%R 𝔹%T 𝔹%T emp%I with "Hρ Ht [] []");
      try (intros; apply _); [iApply eq_bool|done|].
    iIntros "!>" (xl xr) "Hx _". iEval (rewrite eq_lift_bool) in "Hx".
    iDestruct "Hx" as %(x0 & -> & ->).
    destruct x0, s; eq_pures'; iApply eq_value; iModIntro; iEval (rewrite eq_lift_prod);
      iExists _, _, _, _; do 2 (iSplit; first done); iSplitL; iApply eq_bool.
  Qed.

  Lemma S_TO_S_typed : ⊢ ⊨ᵥ S_TO_S ≤ S_TO_S : Mod (IProd OTAdv ARecv) TOSAdv.
  Proof. apply eq_val_typed, S_TO_S_eq. Qed.

  (* ---------------------------------------------------------------- *)
  (* Bob corrupted.                                                     *)
  (* ---------------------------------------------------------------- *)

  Lemma F_TO_R_eq : ⊢ ⟪ Mod TORAdv TSPort ⟫ F_TO_R F_TO_R.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (chl chr) "Hch".
    rewrite /F_TO_R. eq_pures'.
    iApply eq_value. iModIntro. rewrite /TSPort. iApply eq_lift_arr. iIntros (xl xr) "Hx".
    iEval (rewrite eq_lift_prod) in "Hx".
    iDestruct "Hx" as (x0l x0r x1l x1r) "(-> & -> & Hx0 & Hx1)".
    iEval (rewrite eq_lift_bool) in "Hx0". iDestruct "Hx0" as %(x0 & -> & ->).
    iEval (rewrite eq_lift_bool) in "Hx1". iDestruct "Hx1" as %(x1 & -> & ->).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    eq_pures'. rewrite /TORAdv.
    eq_reshape_l (chl _). eq_reshape_r (chr _).
    iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T (𝔹 × (𝔹 -{ ¡ θ }-∘ 𝟙))%T emp%I with "Hρ Hch [] []");
      try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (pl pr) "Hp _". iEval (rewrite eq_lift_prod) in "Hp".
    iDestruct "Hp" as (cl cr ol or) "(-> & -> & Hc & Hout)".
    iEval (rewrite eq_lift_bool) in "Hc". iDestruct "Hc" as %(c & -> & ->).
    destruct c; eq_pures';
      (iApply (eq_call_frame_aff θ (¡ θ)%R 𝔹%T 𝟙%T emp%I ol or _ _ [] [] with "Hρ Hout [] []");
         try (intros; apply _); [iApply eq_bool|done|]);
      iIntros "!>" (??) "Hu _"; by iApply eq_value.
  Qed.

  Lemma F_TO_R_typed : ⊢ ⊨ᵥ F_TO_R ≤ F_TO_R : Mod TORAdv TSPort.
  Proof. apply eq_val_typed, F_TO_R_eq. Qed.

  Lemma HYB_TO_R_typed : ⊢ ⊨ᵥ HYB_TO_R ≤ HYB_TO_R : Mod (IProd OTSAdv ASend) TSPort.
  Proof.
    iApply comp_op_typed; first iApply TO_S_typed.
    iApply tens_op_typed; [iApply F_OT_S_typed|iApply id_mod_typed].
  Qed.

  Lemma S_TO_R_eq : ⊢ ⟪ Mod (IProd OTSAdv ASend) TORAdv ⟫ S_TO_R S_TO_R.
  Proof.
    iPoseProof (val_typed_eq _ _ HYB_TO_R_typed) as "HH".
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall) in "HH".
    iEval (rewrite eq_lift_forall). iIntros (θ). iSpecialize ("HH" $! θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /OTSAdv /ASend. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (il ir sl sr) "(-> & -> & #Hinput & #Hsend)".
    rewrite /S_TO_R /bxor /ungbit. eq_pures'.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iPoseProof (row_le_nil_flip θ) as "#H0".
    iApply eq_value. iModIntro. rewrite /TORAdv. iApply eq_lift_arr. iIntros (ul ur) "Hu".
    iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
    eq_pures'.
    (* Bob's OT messages. *)
    eq_reshape_l (il _). eq_reshape_r (ir _).
    iApply (eq_call_frame θ (¡ θ)%R 𝟙%T (𝔾 × 𝔾)%T emp%I with "Hρ Hinput [] []");
      try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (uvl uvr) "Huv _". iEval (rewrite eq_lift_prod) in "Huv".
    iDestruct "Huv" as (u0l u0r u1l u1r) "(-> & -> & Hu0 & Hu1)".
    iEval (rewrite eq_lift_group) in "Hu0". iDestruct "Hu0" as (u0) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hu1". iDestruct "Hu1" as (u1) "[-> ->]".
    eq_pures'.
    (* His choice, and Alice on [(x, x)] with his messages replayed. *)
    iAssert (⟪ 𝔹 -{ ¡ θ }-∘ 𝟙 ⟫
               (λ: "x", HYB_TO_R ((λ: <>, (vgval u0, vgval u1)), sl) ("x", "x"))%V
               (λ: "x", HYB_TO_R ((λ: <>, (vgval u0, vgval u1)), sr) ("x", "x"))%V)%I as "Hk".
    { iApply eq_lift_arr. iIntros (xl xr) "Hx".
      iEval (rewrite eq_lift_bool) in "Hx". iDestruct "Hx" as %(x & -> & ->).
      eq_pures'.
      eq_reshape_l (HYB_TO_R _). eq_reshape_r (HYB_TO_R _).
      iApply (eq_call_frame ⟨⟩%R (¡ θ)%R (OTSAdv θ × ASend θ)%T (TSPort θ) emp%I
                with "H0 HH [] []"); try (intros; apply _); [|done|].
      { iEval (rewrite eq_lift_prod). iExists _, _, _, _. do 2 (iSplit; first done).
        iSplitL; last done. rewrite /OTSAdv. iModIntro. iApply eq_lift_arr. iIntros (??) "Hw".
        iEval (rewrite eq_lift_unit) in "Hw". iDestruct "Hw" as %[-> ->]. eq_pures'.
        iApply eq_value. iModIntro. by iApply eq_pair. }
      iIntros "!>" (tl tr) "Ht _". rewrite /TSPort. eq_pures'.
      iApply (eq_call_frame_aff θ (¡ θ)%R (𝔹 × 𝔹)%T 𝟙%T emp%I tl tr _ _ [] [] with "Hρ Ht [] []");
        try (intros; apply _); [|done|].
      { iEval (rewrite eq_lift_prod). iExists _, _, _, _. do 2 (iSplit; first done).
        iSplitL; iApply eq_bool. }
      iIntros "!>" (??) "Hu _". by iApply eq_value. }
    case_bool_decide; case_bool_decide; eq_pures';
      iApply eq_value; iModIntro; iEval (rewrite eq_lift_prod);
      iExists _, _, _, _; (do 2 (iSplit; first done)); (iSplitR; [iApply eq_bool|iApply "Hk"]).
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
    iDestruct "Hadv" as (ral rar rbl rbr) "(-> & -> & Hra & Hrb)".
    rewrite /F_TO_H.
    eq_pures_l. eq_alloc_l xs as "Hxs". eq_pures_l.
    eq_pures_r. eq_alloc_r xs' as "Hxs'". eq_pures_r.
    iApply (eq_na_alloc (box_rel_gen bits xs xs') (NTH .@ "xs")).
    iSplitL "Hxs Hxs'"; first (iNext; iLeft; iFrame). iIntros "#Ixs".
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iApply eq_value. iModIntro. rewrite /TPorts. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL "Hra".
    - (* Alice *)
      rewrite /TSPort. iApply eq_lift_arr. iIntros (xl xr) "Hx".
      iEval (rewrite eq_lift_prod) in "Hx".
      iDestruct "Hx" as (x0l x0r x1l x1r) "(-> & -> & Hx0 & Hx1)".
      iEval (rewrite eq_lift_bool) in "Hx0". iDestruct "Hx0" as %(x0 & -> & ->).
      iEval (rewrite eq_lift_bool) in "Hx1". iDestruct "Hx1" as %(x1 & -> & ->).
      eq_pures'.
      assert (bits (#x0, #x1)%V) as Hb by (by exists x0, x1).
      eq_reshape_l (Store _ _). eq_reshape_r (Store _ _).
      iApply (eq_na_store_box _ _ _ _ _ _ _ _ _ Hb with "Ixs"). eq_pures'.
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T 𝟙%T emp%I ral rar _ _ [] [] with "Hρ Hra [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". by iApply eq_value.
    - (* Bob *)
      rewrite /TPort. iApply eq_lift_arr. iIntros (cl cr) "Hc".
      iEval (rewrite eq_lift_bool) in "Hc". iDestruct "Hc" as %(c & -> & ->).
      eq_pures'.
      eq_reshape_l (rbl _). eq_reshape_r (rbr _).
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T 𝟙%T emp%I with "Hρ Hrb [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'.
      eq_reshape_l (Load _). eq_reshape_r (Load _).
      iApply (eq_na_load_box with "Ixs"). iIntros (w) "%Hw".
      destruct Hw as [->|(? & (x0 & x1 & ->) & ->)].
      { eq_pures'. iApply eq_loop. }
      destruct c; eq_pures'; iApply eq_value; iModIntro; iApply eq_bool.
  Qed.

  Lemma F_TO_H_typed : ⊢ ⊨ᵥ F_TO_H ≤ F_TO_H : Mod TOHAdv TPorts.
  Proof. apply eq_val_typed, F_TO_H_eq. Qed.

  (* The dummy inputs. *)
  Lemma DUMMY_TO_eq : ⊢ ⟪ Mod TPorts TOHAdv ⟫ DUMMY_TO DUMMY_TO.
  Proof.
    rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (pl pr) "Hp".
    rewrite /TPorts. iEval (rewrite eq_lift_prod) in "Hp".
    iDestruct "Hp" as (al ar bl br) "(-> & -> & Ha & Hb)".
    rewrite /DUMMY_TO. eq_pures'.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iApply eq_value. iModIntro. rewrite /TOHAdv. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. do 2 (iSplit; first done). iSplitL "Ha".
    - iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->]. eq_pures'.
      rewrite /TSPort.
      iApply (eq_call_frame_aff θ (¡ θ)%R (𝔹 × 𝔹)%T 𝟙%T emp%I al ar _ _ [] [] with "Hρ Ha [] []");
        try (intros; apply _); [|done|].
      { iEval (rewrite eq_lift_prod). iExists _, _, _, _. do 2 (iSplit; first done).
        iSplitL; iApply eq_bool. }
      iIntros "!>" (??) "Hu _". by iApply eq_value.
    - iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->]. eq_pures'.
      rewrite /TPort. eq_reshape_l (bl _). eq_reshape_r (br _).
      iApply (eq_call_frame_aff θ (¡ θ)%R 𝔹%T 𝔹%T emp%I with "Hρ Hb [] []");
        try (intros; apply _); [iApply eq_bool|done|].
      iIntros "!>" (??) "_ _". eq_pures'. iApply eq_value. by iEval (rewrite eq_lift_unit).
  Qed.

  Lemma DUMMY_TO_typed : ⊢ ⊨ᵥ DUMMY_TO ≤ DUMMY_TO : Mod TPorts TOHAdv.
  Proof. apply eq_val_typed, DUMMY_TO_eq. Qed.

  (* The hybrid, and the simulator: the hybrid on dummy inputs. *)
  Lemma HYB_TO_H_typed : ⊢ ⊨ᵥ HYB_TO_H ≤ HYB_TO_H : Mod TOHNet TPorts.
  Proof.
    iApply comp_op_typed; first iApply PARTIES_TO_typed.
    iApply tens_op_typed; [iApply F_OT_H_typed|iApply (F_OAUTH_typed_gen 𝔹 _ eq_ground_bool)].
  Qed.

  Lemma S_TO_H_typed : ⊢ ⊨ᵥ S_TO_H ≤ S_TO_H : Mod TOHNet TOHAdv.
  Proof. iApply comp_op_typed; [iApply DUMMY_TO_typed|iApply HYB_TO_H_typed]. Qed.

End ot_rev_typing.
