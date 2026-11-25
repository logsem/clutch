(* The typings of the ideal key exchange and of its simulator
   (uc_eff/DESIGN.md), as self-equivalences in the logic of [eq/].  They
   are what the composition theorem asks of the components it moves
   around. *)

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
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules dhke.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section dhke_typing.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').
  #[local] Open Scope bi_scope.

  Definition NK : namespace := nroot .@ "ke".
  Definition NS : namespace := nroot .@ "sim_dhke".

  Lemma F_KE_eq : ⊢ ⟪ Mod Ctl Keys ⟫ F_KE F_KE.
  Proof.
    rewrite /Mod. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /Ctl. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (n1 n2 a1 a2) "(-> & -> & #Hnot & #Hall)".
    rewrite /F_KE /samplelbl.
    eq_pures_l. eq_alloctape_l γ as "Hγ". eq_pures_l. eq_alloc_l kr as "Hkr". eq_pures_l.
    eq_pures_r. eq_alloctape_r γ' as "Hγ'". eq_pures_r. eq_alloc_r kr' as "Hkr'". eq_pures_r.
    rewrite !Nat2Z.id.
    iApply (eq_na_alloc (box_rel kr kr') NK).
    iSplitL "Hkr Hkr'"; first (iNext; iLeft; iFrame). iIntros "#Hinv".
    iApply eq_value. iModIntro. rewrite /Keys. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. iSplit; first done. iSplit; first done.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iSplitL "Hγ Hγ'".
    - (* the initiator *)
      iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures_l. eq_pures_r.
      iApply eq_couple_tapes. iFrame "Hγ Hγ'". iIntros (c) "[Hγ Hγ']". simpl.
      eq_rand_l as "H1". eq_rand_r as "H2". eq_pures'.
      iApply (eq_na_open _ _ NK); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iAssert (∃ v v', kr ↦ₗ v ∗ kr' ↦ᵣ v')%I with "[H]" as (v v') "[Hkr Hkr']".
      { iDestruct "H" as "[[??]|(% & ? & ?)]"; iExists _, _; iFrame. }
      eq_store_l. eq_store_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hkr Hkr'"; first (iNext; iRight; iExists _; iFrame).
      eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝟙%T emp%I n1 n2 _ _ [AppRCtx _] [AppRCtx _]
                with "Hρ Hnot [] []"); try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      { done. }
      iIntros "!>" (vl vr) "Hu _". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝔹%T emp%I a1 a2 _ _ [IfCtx _ _] [IfCtx _ _]
                with "Hρ Hall [] []"); try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      { done. }
      iIntros "!>" (vl vr) "Hb _". iEval (rewrite eq_lift_bool) in "Hb".
      iDestruct "Hb" as %(b' & -> & ->). simpl. destruct b'; eq_pures_l; eq_pures_r.
      + iApply eq_value. iModIntro. by iApply eq_some.
      + iApply eq_value. iModIntro. iApply eq_none.
    - (* the responder *)
      iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝔹%T emp%I a1 a2 _ _ [IfCtx _ _] [IfCtx _ _]
                with "Hρ Hall [] []"); try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      { done. }
      iIntros "!>" (vl vr) "Hb _". iEval (rewrite eq_lift_bool) in "Hb".
      iDestruct "Hb" as %(b' & -> & ->). simpl. destruct b'; eq_pures_l; eq_pures_r.
      + iApply (eq_na_open _ _ NK); first done. iFrame "Hinv". iIntros "[>H Hclose]".
        iDestruct "H" as "[[Hkr Hkr']|(%k & Hkr & Hkr')]"; eq_load_l; eq_load_r;
          iApply eq_na_close_rule; iFrame "Hclose".
        * iSplitL "Hkr Hkr'"; first (iNext; iLeft; iFrame).
          eq_pures_l. eq_pures_r.
          iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝟙%T emp%I n1 n2 _ _ [AppRCtx _] [AppRCtx _]
                    with "Hρ Hnot [] []"); try (intros; apply _).
          { iApply eq_lift_same. by iExists _. }
          { done. }
          iIntros "!>" (vl vr) "Hu _". iEval (rewrite eq_lift_unit) in "Hu".
          iDestruct "Hu" as %[-> ->]. simpl. eq_pures'.
          iApply eq_value. iModIntro. iApply eq_none.
        * iSplitL "Hkr Hkr'"; first (iNext; iRight; iExists _; iFrame).
          eq_pures_l. eq_pures_r.
          iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝟙%T emp%I n1 n2 _ _ [AppRCtx _] [AppRCtx _]
                    with "Hρ Hnot [] []"); try (intros; apply _).
          { iApply eq_lift_same. by iExists _. }
          { done. }
          iIntros "!>" (vl vr) "Hu _". iEval (rewrite eq_lift_unit) in "Hu".
          iDestruct "Hu" as %[-> ->]. simpl. eq_pures'.
          iApply eq_value. iModIntro. by iApply eq_some.
      + iApply eq_value. iModIntro. iApply eq_none.
  Qed.

  Lemma S_DHKE_eq : ⊢ ⟪ Mod Net Ctl ⟫ S_DHKE S_DHKE.
  Proof.
    rewrite /Mod. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /Net. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (l1 l2 d1 d2) "(-> & -> & #Hleak & #Hdel)".
    rewrite /S_DHKE /samplelbl.
    eq_pures_l. eq_alloc_l sA as "HsA". eq_pures_l. eq_alloc_l sB as "HsB". eq_pures_l.
    eq_alloctape_l α as "Hα". eq_pures_l. eq_alloctape_l β as "Hβ". eq_pures_l.
    eq_pures_r. eq_alloc_r sA' as "HsA'". eq_pures_r. eq_alloc_r sB' as "HsB'". eq_pures_r.
    eq_alloctape_r α' as "Hα'". eq_pures_r. eq_alloctape_r β' as "Hβ'". eq_pures_r.
    rewrite !Nat2Z.id.
    iApply (eq_na_alloc (flag_rel sA sA' ∗ flag_rel sB sB' ∗ tape_rel n α α' ∗ tape_rel n β β') NS).
    iSplitL; first (iNext; iFrame). iIntros "#Hinv".
    iApply eq_value. iModIntro. rewrite /Ctl. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. iSplit; first done. iSplit; first done. iSplitL.
    - (* notify *)
      iModIntro. iApply eq_lift_arr. iIntros (pl pr) "Hp".
      iEval (rewrite eq_lift_bool) in "Hp". iDestruct "Hp" as %(p & -> & ->).
      destruct p; eq_pures_l; eq_pures_r.
      + iApply (eq_na_open _ _ NS); first done. iFrame "Hinv". iIntros "[>H Hclose]".
        iDestruct "H" as "((%bA & HsA & HsA') & HB & [Hα Hα'] & Hβ)".
        eq_store_l. eq_store_r. eq_pures_l. eq_pures_r.
        iApply eq_couple_tapes. iFrame "Hα Hα'". iIntros (c) "[Hα Hα']". simpl.
        eq_rand_l as "H1". eq_rand_r as "H2".
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitL "HsA HsA' HB Hα Hα' Hβ"; first (iNext; iFrame).
        eq_pures'.
        iApply (eq_lift_app with "Hleak").
        iApply eq_lift_same. iExists _, _, _, _. iSplit; first done. iSplit; first done.
        iSplit; [by iExists _|by iExists _].
      + iApply (eq_na_open _ _ NS); first done. iFrame "Hinv". iIntros "[>H Hclose]".
        iDestruct "H" as "(HA & (%bB & HsB & HsB') & Hα & [Hβ Hβ'])".
        eq_store_l. eq_store_r. eq_pures_l. eq_pures_r.
        iApply eq_couple_tapes. iFrame "Hβ Hβ'". iIntros (c) "[Hβ Hβ']". simpl.
        eq_rand_l as "H1". eq_rand_r as "H2".
        iApply eq_na_close_rule. iFrame "Hclose".
        iSplitL "HsB HsB' HA Hα Hβ Hβ'"; first (iNext; iFrame).
        eq_pures'.
        iApply (eq_lift_app with "Hleak").
        iApply eq_lift_same. iExists _, _, _, _. iSplit; first done. iSplit; first done.
        iSplit; [by iExists _|by iExists _].
    - (* allow *)
      iModIntro. iApply eq_lift_arr. iIntros (pl pr) "Hp".
      iEval (rewrite eq_lift_bool) in "Hp". iDestruct "Hp" as %(p & -> & ->).
      eq_pures_l. eq_pures_r.
      iApply (eq_call MS θ 𝔹%T 𝔹%T d1 d2 _ _ [AppRCtx _] [AppRCtx _] with "Hdel []");
        try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      iIntros "!>" (vl vr) "Hb". iEval (rewrite eq_lift_bool) in "Hb".
      iDestruct "Hb" as %(b' & -> & ->). simpl. destruct b'; eq_pures_l; eq_pures_r.
      + destruct p; eq_pures_l; eq_pures_r;
          (iApply (eq_na_open _ _ NS); first done); iFrame "Hinv"; iIntros "[>H Hclose]";
          iDestruct "H" as "((%bA & HsA & HsA') & (%bB & HsB & HsB') & Hα & Hβ)";
          eq_load_l; eq_load_r; iApply eq_na_close_rule; iFrame "Hclose";
          (iSplitL; first (iNext; iFrame));
          iApply eq_value; iModIntro; iApply eq_lift_bool; by iExists _.
      + iApply eq_value. iModIntro. iApply eq_lift_bool. by iExists _.
  Qed.

  Lemma F_KE_typed : ⊢ ⊨ᵥ F_KE ≤ F_KE : Mod Ctl Keys.
  Proof. apply eq_val_typed, F_KE_eq. Qed.

  Lemma S_DHKE_typed : ⊢ ⊨ᵥ S_DHKE ≤ S_DHKE : Mod Net Ctl.
  Proof. apply eq_val_typed, S_DHKE_eq. Qed.

End dhke_typing.
