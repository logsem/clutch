(* Oblivious transfer reversal with the receiver (Bob) corrupted is
   perfect (uc_eff/DESIGN.md, section 6).

   The simulator reads Bob's mask and choice off his OT messages; the
   proof is a case analysis on the bits. *)

From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch Require Import stdpp_ext.
From iris.base_logic.lib Require Import na_invariants.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_compat.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage uc_advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules ot ot_corrupted_sender ot_rev ot_rev_corrupted_receiver.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section ot_rev_corrupted_receiver_eq.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Open Scope bi_scope.

  (* Bob corrupted: the simulator reads Bob's mask and choice off his OT
     messages; no sample, no coupling. *)
  Lemma hyb_ideal_TO_R_EQ :
    ⊢ EQ HYB_TO_R ≈ IDEAL_TO_R <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|>
        {{ ⟪ Mod (IProd OTSAdv ASend) TSPort ⟫ }}.
  Proof.
    iApply eq_value. iModIntro. rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /OTSAdv /ASend. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (il ir sl sr) "(-> & -> & #Hinput & #Hsend)".
    rewrite /HYB_TO_R /IDEAL_TO_R /comp_op /tens_op /id_mod /TO_S /F_OT_S /F_TO_R /S_TO_R
      /bxor /ungbit.
    eq_pures_l. eq_pures_r. eq_alloc_r st as "Hst". eq_pures_r.

    (* Alice's port. *)
    iApply eq_value. iModIntro. rewrite /TSPort. iApply eq_lift_arr. iIntros (xl xr) "Hx".
    iEval (rewrite eq_lift_prod) in "Hx".
    iDestruct "Hx" as (x0l x0r x1l x1r) "(-> & -> & Hx0 & Hx1)".
    iEval (rewrite eq_lift_bool) in "Hx0". iDestruct "Hx0" as %(x0 & -> & ->).
    iEval (rewrite eq_lift_bool) in "Hx1". iDestruct "Hx1" as %(x1 & -> & ->).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    (* Bob's OT messages; Alice's message. *)
    destruct x0, x1; eq_pures';
      eq_reshape_l (il _); eq_reshape_r (ir _);
      (iApply (eq_call_frame θ (¡ θ)%R 𝟙%T (𝔾 × 𝔾)%T (st ↦ᵣ NONEV)%I with "Hρ Hinput [] Hst");
         try (intros; apply _); [by iEval (rewrite eq_lift_unit)|]);
      iIntros "!>" (uvl uvr) "Huv Hst"; iEval (rewrite eq_lift_prod) in "Huv";
      iDestruct "Huv" as (u0l u0r u1l u1r) "(-> & -> & Hu0 & Hu1)";
      iEval (rewrite eq_lift_group) in "Hu0"; iDestruct "Hu0" as (u0) "[-> ->]";
      iEval (rewrite eq_lift_group) in "Hu1"; iDestruct "Hu1" as (u1) "[-> ->]";
      eq_pures'; case_bool_decide; case_bool_decide;
      eq_pures'; eq_store_r; eq_pures'; eq_load_r; eq_pures';
      (iApply (eq_call_frame θ (¡ θ)%R 𝔹%T 𝟙%T emp%I sl sr _ _ [] [] with "Hρ Hsend [] []");
         try (intros; apply _); [iApply eq_bool|done|]);
      iIntros "!>" (??) "Hu _"; by iApply eq_value.
  Qed.

End ot_rev_corrupted_receiver_eq.

Section ot_rev_corrupted_receiver_security.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.

  Theorem to_r_security : to_r_secure.
  Proof.
    intros A HA.
    apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, Mod (IProd OTSAdv ASend) TSPort));
      [exact HA| |]; intros HRGS;
      [apply (EQ_sem_typed _ _ ⊥ _ hyb_ideal_TO_R_EQ Fwd)
      |apply (EQ_sem_typed _ _ ⊥ _ hyb_ideal_TO_R_EQ Bwd)].
  Qed.

End ot_rev_corrupted_receiver_security.
