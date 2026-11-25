(* Security of Diffie-Hellman key exchange as modules (uc_eff/DESIGN.md).

   The real module [DH_KE ⊳ F_AUTH] is equivalent to the reduction on a real
   DDH triple, and the reduction on a random triple is equivalent to the
   ideal module [F_KE ⊳ S_DHKE].  Both equivalences are proved in the
   equivalence logic of [eq/]: each is one proof, read in both directions. *)

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
From clutch.prob_eff_lang.probblaze.uc Require Import advantage uc_advantage.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules dhke.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section dhke_eq.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').
  #[local] Open Scope bi_scope.

  Definition NA : namespace := nroot .@ "dhke" .@ "A".
  Definition NB : namespace := nroot .@ "dhke" .@ "B".

  (* A message slot of the channel in both programs: empty, or holding [x]. *)
  Definition slot (m m' : loc) (x : vgG) : iPropD Σ :=
    (m ↦ₗ NONEV ∗ m' ↦ᵣ NONEV) ∨ (m ↦ₗ SOMEV (vgval x) ∗ m' ↦ᵣ SOMEV (vgval x)).

  Lemma real_C_real_EQ :
    ⊢ EQ REAL_DHKE ≈ (C_DH_v DH_real ⊳ F_AUTH)%md <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|>
        {{ ⟪ Mod Net Keys ⟫ }}.
  Proof.
    iApply eq_value. iModIntro. rewrite /Mod. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /Net. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (l1 l2 d1 d2) "(-> & -> & #Hleak & #Hdel)".
    rewrite /REAL_DHKE /comp_op /F_AUTH /DH_KE /C_DH_v /C_DH_of /DH_real /sample /samplelbl.
    eq_pures_l. eq_pures_r.
    eq_alloc_l mA as "HmA". eq_pures_l. eq_alloc_l mB as "HmB". eq_pures_l.
    eq_alloc_r mA' as "HmA'". eq_pures_r. eq_alloc_r mB' as "HmB'". eq_pures_r.
    eq_alloctape_l α as "Hα". eq_pures_l. eq_alloctape_l β as "Hβ". rewrite !Nat2Z.id.
    eq_couple_tape_rand "Hα". iIntros (a Ha) "Hα". eq_pures_r.
    eq_couple_tape_rand "Hβ". iIntros (b Hb) "Hβ". eq_pures_r.
    rewrite -Nat2Z.inj_mul.
    iApply (eq_na_alloc (slot mA mA' (g ^+ a)%g) NA).
    iSplitL "HmA HmA'"; first (iNext; iLeft; iFrame). iIntros "#HinvA".
    iApply (eq_na_alloc (slot mB mB' (g ^+ b)%g) NB).
    iSplitL "HmB HmB'"; first (iNext; iLeft; iFrame). iIntros "#HinvB".
    eq_pures_l. eq_pures'.
    iApply eq_value. iModIntro. rewrite /Keys. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. iSplit; first done. iSplit; first done.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iSplitL "Hα".
    - (* the initiator *)
      iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures_l. eq_rand_l as "Hα0". eq_pures'.
      iApply (eq_na_open _ _ NA); first done. iFrame "HinvA". iIntros "[>H Hclose]".
      iAssert (∃ v v', mA ↦ₗ v ∗ mA' ↦ᵣ v')%I with "[H]" as (v v') "[Hm Hm']".
      { iDestruct "H" as "[[??]|[??]]"; iExists _, _; iFrame. }
      eq_store_l. eq_store_r.
      iApply eq_na_close_rule. iFrame "Hclose". iSplitL "Hm Hm'"; first (iNext; iRight; iFrame).
      eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R (𝔹 × 𝔾)%T 𝟙%T emp%I l1 l2 _ _ [AppRCtx _] [AppRCtx _]
                with "Hρ Hleak [] []"); try (intros; apply _).
      { iApply eq_lift_same. iExists _, _, _, _. iSplit; first done. iSplit; first done.
        iSplit; [by iExists _|by iExists _]. }
      { done. }
      iIntros "!>" (vl vr) "Hu _". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝔹%T emp%I d1 d2 _ _
                [CaseCtx _ _; IfCtx _ _] [CaseCtx _ _; IfCtx _ _]
                with "Hρ Hdel [] []"); try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      { done. }
      iIntros "!>" (vl vr) "Hb _". iEval (rewrite eq_lift_bool) in "Hb".
      iDestruct "Hb" as %(b' & -> & ->). simpl. destruct b'; eq_pures_l; eq_pures_r.
      + iApply (eq_na_open _ _ NB); first done. iFrame "HinvB".
        iIntros "[>[[Hm Hm']|[Hm Hm']] Hclose]"; eq_load_l; eq_load_r;
          iApply eq_na_close_rule; iFrame "Hclose".
        * iSplitL; first (iNext; iLeft; iFrame). eq_pures'.
          iApply eq_value. iModIntro. iApply eq_none.
        * iSplitL; first (iNext; iRight; iFrame). eq_pures'.
          iApply eq_value. iModIntro. iApply eq_some. by rewrite -expgM ssrnat.mulnC.
      + iApply eq_value. iModIntro. iApply eq_none.
    - (* the responder *)
      iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝔹%T (β ↪ₗN (n; [b]))%I d1 d2 _ _
                [CaseCtx _ _; IfCtx _ _] [CaseCtx _ _; IfCtx _ _]
                with "Hρ Hdel [] Hβ"); try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      iIntros "!>" (vl vr) "Hb Hβ". iEval (rewrite eq_lift_bool) in "Hb".
      iDestruct "Hb" as %(b' & -> & ->). simpl. destruct b'; eq_pures_l; eq_pures_r.
      + iApply (eq_na_open _ _ NA); first done. iFrame "HinvA".
        iIntros "[>[[Hm Hm']|[Hm Hm']] Hclose]"; eq_load_l; eq_load_r;
          iApply eq_na_close_rule; iFrame "Hclose".
        * iSplitL "Hm Hm'"; first (iNext; iLeft; iFrame). eq_pures'.
          iApply eq_value. iModIntro. iApply eq_none.
        * iSplitL "Hm Hm'"; first (iNext; iRight; iFrame).
          eq_pures_l. eq_rand_l as "Hβ0". eq_pures'.
          iApply (eq_na_open _ _ NB); first done. iFrame "HinvB". iIntros "[>H Hclose]".
          iAssert (∃ v v', mB ↦ₗ v ∗ mB' ↦ᵣ v')%I with "[H]" as (v v') "[Hm Hm']".
          { iDestruct "H" as "[[??]|[??]]"; iExists _, _; iFrame. }
          eq_store_l. eq_store_r.
          iApply eq_na_close_rule. iFrame "Hclose".
          iSplitL "Hm Hm'"; first (iNext; iRight; iFrame).
          eq_pures_l. eq_pures_r.
          iApply (eq_call_frame θ (¡ θ)%R (𝔹 × 𝔾)%T 𝟙%T emp%I l1 l2 _ _ [AppRCtx _] [AppRCtx _]
                    with "Hρ Hleak [] []"); try (intros; apply _).
          { iApply eq_lift_same. iExists _, _, _, _. iSplit; first done. iSplit; first done.
            iSplit; [by iExists _|by iExists _]. }
          { done. }
          iIntros "!>" (vl vr) "Hu _". iEval (rewrite eq_lift_unit) in "Hu".
          iDestruct "Hu" as %[-> ->]. simpl. eq_pures'.
          iApply eq_value. iModIntro. iApply eq_some. by rewrite -expgM.
      + iApply eq_value. iModIntro. iApply eq_none.
  Qed.

  (* The initiator's channel slot against the simulator's flag and the
     ideal key: empty, unset and no key; or holding [x], set, and key [k]. *)
  Definition slotK (m s kr : loc) (x k : vgG) : iPropD Σ :=
    (m ↦ₗ NONEV ∗ s ↦ᵣ #false ∗ kr ↦ᵣ NONEV) ∨
    (m ↦ₗ SOMEV (vgval x) ∗ s ↦ᵣ #true ∗ kr ↦ᵣ SOMEV (vgval k)).
  (* The responder's slot against the simulator's flag. *)
  Definition slotS (m s : loc) (x : vgG) : iPropD Σ :=
    (m ↦ₗ NONEV ∗ s ↦ᵣ #false) ∨ (m ↦ₗ SOMEV (vgval x) ∗ s ↦ᵣ #true).

  Lemma C_rand_ideal_EQ :
    ⊢ EQ (C_DH_v DH_rand ⊳ F_AUTH)%md ≈ IDEAL_DHKE <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|>
        {{ ⟪ Mod Net Keys ⟫ }}.
  Proof.
    iApply eq_value. iModIntro. rewrite /Mod. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /Net. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (l1 l2 d1 d2) "(-> & -> & #Hleak & #Hdel)".
    rewrite /IDEAL_DHKE /comp_op /F_AUTH /F_KE /S_DHKE /C_DH_v /C_DH_of /DH_rand /sample /samplelbl.
    eq_pures_l. eq_pures_r.
    eq_alloc_l mA as "HmA". eq_pures_l. eq_alloc_l mB as "HmB". eq_pures_l.
    eq_alloc_r sA as "HsA". eq_pures_r. eq_alloc_r sB as "HsB". eq_pures_r.
    eq_alloctape_r α as "Hα". eq_pures_r. eq_alloctape_r β as "Hβ". eq_pures_r.
    eq_alloctape_r γ as "Hγ". eq_pures_r. eq_alloc_r kr as "Hkr".
    rewrite !Nat2Z.id.
    eq_couple_rand_tape "Hα". iIntros (a Ha) "Hα". eq_pures_l.
    eq_couple_rand_tape "Hβ". iIntros (b Hb) "Hβ". eq_pures_l.
    eq_couple_rand_tape "Hγ". iIntros (c Hc) "Hγ".
    iApply (eq_na_alloc (slotK mA sA kr (g ^+ a)%g (g ^+ c)%g) NA).
    iSplitL "HmA HsA Hkr"; first (iNext; iLeft; iFrame). iIntros "#HinvA".
    iApply (eq_na_alloc (slotS mB sB (g ^+ b)%g) NB).
    iSplitL "HmB HsB"; first (iNext; iLeft; iFrame). iIntros "#HinvB".
    eq_pures'.
    iApply eq_value. iModIntro. rewrite /Keys. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. iSplit; first done. iSplit; first done.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iSplitL "Hα Hγ".
    - (* the initiator *)
      iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures_l. eq_pures_r. eq_rand_r as "Hγ0". eq_pures'.
      iApply (eq_na_open _ _ NA); first done. iFrame "HinvA". iIntros "[>H Hclose]".
      iAssert (∃ v v' v'', mA ↦ₗ v ∗ sA ↦ᵣ v' ∗ kr ↦ᵣ v'')%I with "[H]" as (v v' v'') "(Hm & Hs & Hk)".
      { iDestruct "H" as "[(?&?&?)|(?&?&?)]"; iExists _, _, _; iFrame. }
      eq_store_l. eq_store_r. eq_pures_r. eq_store_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hm Hs Hk"; first (iNext; iRight; iFrame).
      eq_pures_l. eq_pures_r. eq_rand_r as "Hα0". eq_pures'.
      iApply (eq_call_frame θ (¡ θ)%R (𝔹 × 𝔾)%T 𝟙%T emp%I l1 l2 _ _ [AppRCtx _] [AppRCtx _]
                with "Hρ Hleak [] []"); try (intros; apply _).
      { iApply eq_lift_same. iExists _, _, _, _. iSplit; first done. iSplit; first done.
        iSplit; [by iExists _|by iExists _]. }
      { done. }
      iIntros "!>" (vl vr) "Hu _". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝔹%T emp%I d1 d2 _ _
                [CaseCtx _ _; IfCtx _ _] [IfCtx _ _; AppRCtx _]
                with "Hρ Hdel [] []"); try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      { done. }
      iIntros "!>" (vl vr) "Hb _". iEval (rewrite eq_lift_bool) in "Hb".
      iDestruct "Hb" as %(b' & -> & ->). simpl. destruct b'; eq_pures_l; eq_pures_r.
      + iApply (eq_na_open _ _ NB); first done. iFrame "HinvB".
        iIntros "[>[[Hm Hs]|[Hm Hs]] Hclose]"; eq_load_l; eq_load_r;
          iApply eq_na_close_rule; iFrame "Hclose".
        * iSplitL; first (iNext; iLeft; iFrame). eq_pures'.
          iApply eq_value. iModIntro. iApply eq_none.
        * iSplitL; first (iNext; iRight; iFrame). eq_pures'.
          iApply eq_value. iModIntro. by iApply eq_some.
      + iApply eq_value. iModIntro. iApply eq_none.
    - (* the responder *)
      iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝔹%T (β ↪ᵣN (n; [b]))%I d1 d2 _ _
                [CaseCtx _ _; IfCtx _ _] [IfCtx _ _; AppRCtx _]
                with "Hρ Hdel [] Hβ"); try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      iIntros "!>" (vl vr) "Hb Hβ". iEval (rewrite eq_lift_bool) in "Hb".
      iDestruct "Hb" as %(b' & -> & ->). simpl. destruct b'; eq_pures_l; eq_pures_r.
      + iApply (eq_na_open _ _ NA); first done. iFrame "HinvA".
        iIntros "[>[(Hm & Hs & Hk)|(Hm & Hs & Hk)] Hclose]"; eq_load_l; eq_load_r.
        * iApply eq_na_close_rule. iFrame "Hclose".
          iSplitL "Hm Hs Hk"; first (iNext; iLeft; iFrame). eq_pures'.
          iApply eq_value. iModIntro. iApply eq_none.
        * eq_pures_r. eq_load_r.
          iApply eq_na_close_rule. iFrame "Hclose".
          iSplitL "Hm Hs Hk"; first (iNext; iRight; iFrame).
          eq_pures_l. eq_pures_r.
          iApply (eq_na_open _ _ NB); first done. iFrame "HinvB". iIntros "[>H Hclose]".
          iAssert (∃ v v', mB ↦ₗ v ∗ sB ↦ᵣ v')%I with "[H]" as (v v') "[Hm Hs]".
          { iDestruct "H" as "[[??]|[??]]"; iExists _, _; iFrame. }
          eq_store_l. eq_store_r.
          iApply eq_na_close_rule. iFrame "Hclose".
          iSplitL "Hm Hs"; first (iNext; iRight; iFrame).
          eq_pures_l. eq_pures_r. eq_rand_r as "Hβ0". eq_pures'.
          iApply (eq_call_frame θ (¡ θ)%R (𝔹 × 𝔾)%T 𝟙%T emp%I l1 l2 _ _ [AppRCtx _] [AppRCtx _]
                    with "Hρ Hleak [] []"); try (intros; apply _).
          { iApply eq_lift_same. iExists _, _, _, _. iSplit; first done. iSplit; first done.
            iSplit; [by iExists _|by iExists _]. }
          { done. }
          iIntros "!>" (vl vr) "Hu _". iEval (rewrite eq_lift_unit) in "Hu".
          iDestruct "Hu" as %[-> ->]. simpl. eq_pures'.
          iApply eq_value. iModIntro. by iApply eq_some.
      + iApply eq_value. iModIntro. iApply eq_none.
  Qed.

End dhke_eq.

(* ------------------------------------------------------------------ *)
(* The security theorem.                                               *)
(* ------------------------------------------------------------------ *)

Section dhke_security.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.

  (* The context through which the reduction sees the DDH oracle. *)
  Definition red_ctx : ectx := [AppLCtx F_AUTH; AppRCtx comp_app; AppRCtx C_DH].

  Lemma red_ctx_pure (d : val) :
    rtc pure_step (fill red_ctx d) (C_DH_v d ⊳ F_AUTH)%md.
  Proof.
    etrans; last apply comp_app_pure.
    apply (rtc_congruence (R := pure_step) (fill [AppLCtx F_AUTH; AppRCtx comp_app]) pure_step
             (C_DH d) (C_DH_v d)).
    - intros ???. by apply (@language.pure_step_ctx _ _
        (fill_ctx_no_handler [AppLCtx F_AUTH; AppRCtx comp_app] eq_refl)).
    - rewrite /C_DH /C_DH_v. eapply rtc_l.
      { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
      simpl. eapply rtc_l.
      { apply nsteps_once_inv, (pure_exec (φ := True)); done. }
      done.
  Qed.

  Theorem dhke_security : dhke_secure.
  Proof.
    intros A HA.
    (*   REAL_DHKE  ≃  C_DH_v DH_real ⊳ F_AUTH   *)
    eapply (advantage_triangle _ _ (C_DH_v DH_real ⊳ F_AUTH)%md _ _ 0); first last.
    { rewrite Rplus_0_l. reflexivity. }
    2: { apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, Mod Net Keys)); [exact HA| |];
           intros HRGS;
           [apply (EQ_sem_typed _ _ ⊥ _ real_C_real_EQ Fwd)
           |apply (EQ_sem_typed _ _ ⊥ _ real_C_real_EQ Bwd)]. }
    (*   C_DH_v DH_rand ⊳ F_AUTH  ≃  IDEAL_DHKE   *)
    eapply (advantage_triangle _ _ (C_DH_v DH_rand ⊳ F_AUTH)%md _ _ _ 0); first last.
    { rewrite Rplus_0_r. reflexivity. }
    1: { apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, Mod Net Keys)); [exact HA| |];
           intros HRGS;
           [apply (EQ_sem_typed _ _ ⊥ _ C_rand_ideal_EQ Fwd)
           |apply (EQ_sem_typed _ _ ⊥ _ C_rand_ideal_EQ Bwd)]. }
    (*   the DDH step, through the reduction   *)
    etrans; first apply (advantage_pure_r_rev _ [] _ (fill red_ctx DH_rand) _);
      [done|apply red_ctx_pure|].
    etrans; first apply (advantage_pure_l_rev _ [] (fill red_ctx DH_real) _ _);
      [done|apply red_ctx_pure|].
    apply (advantage_reduction_ctx A red_ctx); first done.
    intros vs w Hw. simpl. by rewrite Hw.
  Qed.

End dhke_security.
