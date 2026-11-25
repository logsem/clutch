(* Security of the one-time secure channel as modules (uc_eff/DESIGN.md).

   The protocol on the ideal key exchange and the authenticated channel,
   [CHAN ⊳ (F_KE ⊗ F_OAUTH)], is equivalent to the ideal module
   [F_CHAN ⊳ S_CHAN]: one proof in the equivalence logic of [eq/], read in
   both directions.  The key is coupled with the simulator's fake
   ciphertext when the sender starts, along the bijection that masks with
   the sender's message. *)

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
From clutch.prob_eff_lang.probblaze.examples.secure_add Require Import secure_add_bijection.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules dhke channel.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section channel_eq.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S n'').
  #[local] Open Scope bi_scope.

  Definition NC : namespace := nroot .@ "chan".

  (* The state of the two programs.  Before the sender starts there is no
     key and no message.  Once it has started, the key [k] (left) and the
     message [m] (right) are fixed for good; the ciphertext is then either
     not yet out, or it is, and the simulator has recorded it. *)
  Definition chan_inv (kr mo st sn cm : loc) : iPropD Σ :=
    (kr ↦ₗ NONEV ∗ st ↦ᵣ #false ∗ cm ↦ᵣ NONEV) ∨
    (∃ k m : vgG, kr ↦ₗ□ SOMEV (vgval k) ∗ cm ↦ᵣ□ SOMEV (vgval m) ∗ st ↦ᵣ #true ∗
       ((mo ↦ₗ NONEV ∗ sn ↦ᵣ #false) ∨ (mo ↦ₗ SOMEV (vgval (m * k)%g) ∗ sn ↦ᵣ #true))).

  Lemma hyb_ideal_EQ :
    ⊢ EQ HYB_CHAN ≈ IDEAL_CHAN <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|>
        {{ ⟪ Mod (IProd Ctl ONet) SChan ⟫ }}.
  Proof.
    iApply eq_value. iModIntro. rewrite /Mod. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /Ctl /ONet. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (ctll ctlr netl netr) "(-> & -> & Hctl & Hnet)".
    iEval (rewrite eq_lift_prod) in "Hctl".
    iDestruct "Hctl" as (n1 n2 a1 a2) "(-> & -> & #Hnot & #Hall)".
    iEval (rewrite eq_lift_prod) in "Hnet".
    iDestruct "Hnet" as (l1 l2 d1 d2) "(-> & -> & #Hleak & #Hdel)".
    rewrite /HYB_CHAN /IDEAL_CHAN /comp_op /tens_op /CHAN /F_KE /F_OAUTH /F_CHAN /S_CHAN
      /sample /samplelbl.
    eq_pures_l. eq_alloctape_l γ as "Hγ". eq_pures_l. eq_alloc_l kr as "Hkr". eq_pures_l.
    eq_alloc_l mo as "Hmo". eq_pures_l.
    eq_pures_r. eq_alloc_r st as "Hst". eq_pures_r. eq_alloc_r sn as "Hsn". eq_pures_r.
    eq_alloctape_r ρ as "Hρt". eq_pures_r. eq_alloc_r cm as "Hcm". eq_pures_r.
    rewrite !Nat2Z.id.
    iApply (eq_na_alloc (chan_inv kr mo st sn cm) NC).
    iSplitL "Hkr Hst Hcm"; first (iNext; iLeft; iFrame). iIntros "#Hinv".
    iApply eq_value. iModIntro. rewrite /SChan. iEval (rewrite eq_lift_prod).
    iExists _, _, _, _. iSplit; first done. iSplit; first done.
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    iSplitL "Hγ Hρt Hmo Hsn".
    - (* the sender *)
      iApply eq_lift_arr. iIntros (ml mr) "Hm".
      iEval (rewrite eq_lift_group) in "Hm". iDestruct "Hm" as %(m & -> & ->).
      eq_pures_l. eq_pures_r.
      (* the key against the fake ciphertext *)
      iApply (eq_couple_tapes_bij _ _ (add_coupling_nat m)); first apply add_coupling_nat_bound.
      iFrame "Hγ Hρt". iIntros (c Hc) "[Hγ Hρt]". simpl.
      eq_rand_l as "Hγ0". eq_pures'.
      iApply (eq_na_open _ _ NC); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "[(Hkr & Hst & Hcm)|(%k' & %m' & _ & _ & _ & [[Hmo' _]|[Hmo' _]])]";
        [|by iDestruct (eq_pt_l_excl with "Hmo Hmo'") as %[]..].
      eq_store_l. eq_store_r. eq_pures_r. eq_store_r.
      iMod (eq_pt_l_persist with "Hkr") as "#Hkr". iMod (eq_pt_r_persist with "Hcm") as "#Hcm".
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hst Hmo Hsn".
      { iNext. iRight. iExists _, m. iFrame "Hkr Hcm Hst". iLeft. iFrame. }
      eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝟙%T (ρ ↪ᵣN (n; [add_coupling_nat m c]))%I n1 n2 _ _
                [AppRCtx _; AppRCtx _] [AppRCtx _] with "Hρ Hnot [] Hρt"); try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      iIntros "!>" (vl vr) "Hu Hρt". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
      iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝟙%T (ρ ↪ᵣN (n; [add_coupling_nat m c]))%I a1 a2 _ _
                [AppRCtx _; AppRCtx _] [AppRCtx _] with "Hρ Hall [] Hρt"); try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      iIntros "!>" (vl vr) "Hu Hρt". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures'.
      iApply (eq_na_open _ _ NC); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "[(Hkr' & _)|(%k' & %m' & _ & _ & Hst & Hin)]".
      { by iDestruct (eq_pt_l_agree with "Hkr' Hkr") as %?. }
      iAssert (∃ v v', mo ↦ₗ v ∗ sn ↦ᵣ v')%I with "[Hin]" as (v v') "[Hmo Hsn]".
      { iDestruct "Hin" as "[[??]|[??]]"; iExists _, _; iFrame. }
      eq_store_l. eq_store_r.
      iApply eq_na_close_rule. iFrame "Hclose".
      iSplitL "Hst Hmo Hsn".
      { iNext. iRight. iExists _, m. iFrame "Hkr Hcm Hst". iRight. iFrame. }
      eq_pures_l. eq_pures_r. eq_rand_r as "Hρ0". eq_pures'.
      rewrite add_coupling_nat_mult; last lia.
      iApply (eq_call_frame θ (¡ θ)%R 𝔾 𝟙%T emp%I l1 l2 _ _ [] [] with "Hρ Hleak [] []");
        try (intros; apply _).
      { iApply eq_lift_group. by iExists _. }
      { done. }
      iIntros "!>" (vl vr) "Hu _". simpl. by iApply eq_value.
    - (* the receiver *)
      iApply eq_lift_arr. iIntros (ul ur) "Hu".
      iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures_l. eq_pures_r.
      (* wait for the key: the responder of the key exchange against the
         simulator's first loop *)
      iLöb as "IH".
      iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝟙%T emp%I a1 a2 _ _
                [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _; AppRCtx _] with "Hρ Hall [] []");
        try (intros; apply _).
      { iApply eq_lift_same. by iExists _. }
      { done. }
      iIntros "!>" (vl vr) "Hu _". iEval (rewrite eq_lift_unit) in "Hu".
      iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
      iApply (eq_na_open _ _ NC); first done. iFrame "Hinv". iIntros "[>H Hclose]".
      iDestruct "H" as "[(Hkr & Hst & Hcm)|(%k & %m & #Hkr & #Hcm & Hst & Hin)]";
        eq_load_l; eq_load_r; iApply eq_na_close_rule; iFrame "Hclose".
      + iSplitL "Hkr Hst Hcm"; first (iNext; iLeft; iFrame).
        eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply "IH".
      + iSplitL "Hst Hin".
        { iNext. iRight. iExists k, m. iFrame "Hkr Hcm Hst Hin". }
        eq_pures_l. eq_pures_r.
        iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝟙%T emp%I n1 n2 _ _
                  [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _] with "Hρ Hnot [] []");
          try (intros; apply _).
        { iApply eq_lift_same. by iExists _. }
        { done. }
        iIntros "!>" (vl vr) "Hu _". iEval (rewrite eq_lift_unit) in "Hu".
        iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
        (* wait for the ciphertext: the channel's [recv] against the
           simulator's second loop *)
        iClear "IH". iLöb as "IH".
        iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝟙%T emp%I d1 d2 _ _
                  [AppRCtx _; AppRCtx _] [AppRCtx _; AppRCtx _] with "Hρ Hdel [] []");
          try (intros; apply _).
        { by iEval (rewrite eq_lift_unit). }
        { done. }
        iIntros "!>" (vl vr) "Hu _". iEval (rewrite eq_lift_unit) in "Hu".
        iDestruct "Hu" as %[-> ->]. simpl. eq_pures_l. eq_pures_r.
        iApply (eq_na_open _ _ NC); first done. iFrame "Hinv". iIntros "[>H Hclose]".
        iDestruct "H" as "[(Hkr' & _)|(%k' & %m' & #Hkr' & #Hcm' & Hst & Hin)]".
        { by iDestruct (eq_pt_l_agree with "Hkr' Hkr") as %?. }
        iDestruct (eq_pt_l_agree with "Hkr' Hkr") as %Hk.
        iDestruct (eq_pt_r_agree with "Hcm' Hcm") as %Hm.
        assert (k' = k) as -> by (apply vgval_inj; congruence).
        assert (m' = m) as -> by (apply vgval_inj; congruence).
        iDestruct "Hin" as "[[Hmo Hsn]|[Hmo Hsn]]"; eq_load_l; eq_load_r;
          iApply eq_na_close_rule; iFrame "Hclose".
        * iSplitL "Hst Hmo Hsn".
          { iNext. iRight. iExists k, m. iFrame "Hkr Hcm Hst". iLeft. iFrame. }
          eq_pures_lr. try (try eq_pures_l). try (try eq_pures_r). iApply "IH".
        * iSplitL "Hst Hmo Hsn".
          { iNext. iRight. iExists k, m. iFrame "Hkr Hcm Hst". iRight. iFrame. }
          eq_pures'. eq_load_r. eq_pures'.
          iApply eq_value. iModIntro. iApply eq_group_val. by rewrite mulgK.
  Qed.

End channel_eq.

(* ------------------------------------------------------------------ *)
(* The security theorem.                                               *)
(* ------------------------------------------------------------------ *)

Section channel_security.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.

  Theorem chan_security : chan_secure.
  Proof.
    intros A HA.
    apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, Mod (IProd Ctl ONet) SChan));
      [exact HA| |]; intros HRGS;
      [apply (EQ_sem_typed _ _ ⊥ _ hyb_ideal_EQ Fwd)|apply (EQ_sem_typed _ _ ⊥ _ hyb_ideal_EQ Bwd)].
  Qed.

End channel_security.
