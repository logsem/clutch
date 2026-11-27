(* Oblivious transfer reversal with the sender (Alice) corrupted is
   perfect.

   Bob on the ideal OT, [TO_R ⊳ (F_OT_R ⊗ id)], and the ideal transfer
   with the simulator, [F_TO_S ⊳ S_TO_S], which runs the same Bob on the
   choice [false], line up call for call: [choose], a sample, [output],
   [recv].  Bob's mask [r] is coupled with the dummy Bob's [ρ] along
   [ρ = r ⊕ (s ∧ c)], which is known when Bob samples because the OT's
   sender port has two phases (ot.v). *)

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
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules ot ot_corrupted_receiver ot_rev ot_rev_corrupted_sender.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section ot_rev_corrupted_sender_eq.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  #[local] Open Scope bi_scope.

  Lemma hyb_ideal_TO_S_EQ :
    ⊢ EQ HYB_TO_S ≈ IDEAL_TO_S <|iLblSig_to_iLblThy (⊥ : sem_row Σ)|>
        {{ ⟪ Mod (IProd OTAdv ARecv) TPort ⟫ }}.
  Proof.
    iApply eq_value. iModIntro. rewrite /Mod /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    iModIntro. iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /OTAdv /ARecv. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (cl cr rl rr) "(-> & -> & Hchoose & #Hrecv)".
    rewrite /IDEAL_TO_S /F_TO_S /S_TO_S /HYB_TO_S /comp_op /tens_op /id_mod /TO_R /F_OT_R
      /ot_rev.flip /bxor /gbit is_unit.
    eq_pures_l. eq_pures_r.

    (* Bob's port. *)
    iApply eq_value. iModIntro. rewrite /TPort. iApply eq_lift_arr. iIntros (cvl cvr) "Hc".
    iEval (rewrite eq_lift_bool) in "Hc". iDestruct "Hc" as %(c & -> & ->).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    eq_pures'.

    (* Alice's OT choice [s]; on the right the simulator replays it to the
       dummy Bob's OT. *)
    eq_reshape_l (cl _). eq_reshape_r (cr _).
    iApply (eq_call_frame_aff θ (¡ θ)%R 𝟙%T (𝔹 × (𝔾 -{ ¡ θ }-∘ 𝟙))%T emp%I with "Hρ Hchoose [] []");
      try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (pl pr) "Hp _". iEval (rewrite eq_lift_prod) in "Hp".
    iDestruct "Hp" as (svl svr ol or) "(-> & -> & Hs & Houtput)".
    iEval (rewrite eq_lift_bool) in "Hs". iDestruct "Hs" as %(s & -> & ->).
    eq_pures'.

    (* Bob's mask [r] and the simulator's [ρ = r ⊕ (s ∧ c)]. *)
    eq_focus_l (rand #_)%E; eq_focus_r (rand #_)%E.
    iApply (eq_couple_rand_rand_bij _ _ (bmask (s && c))); first by apply bmask_lt.
    iIntros (k Hk).
    (* Alice's OT output, her message [m], and Bob's output. *)
    destruct s, c, k as [|[|k]]; try lia; eq_pures';
      eq_reshape_l (ol _); eq_reshape_r (or _);
      (iApply (eq_call_frame_aff θ (¡ θ)%R 𝔾%T 𝟙%T emp%I with "Hρ Houtput [] []");
         try (intros; apply _); [by iApply eq_group_val|done|]);
      iIntros "!>" (??) "Hu _"; iEval (rewrite eq_lift_unit) in "Hu"; iDestruct "Hu" as %[-> ->];
      eq_pures'; eq_reshape_l (rl _); eq_reshape_r (rr _);
      (iApply (eq_call_frame θ (¡ θ)%R 𝟙%T 𝔹%T emp%I with "Hρ Hrecv [] []");
         try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|]);
      iIntros "!>" (mvl mvr) "Hm _"; iEval (rewrite eq_lift_bool) in "Hm";
      iDestruct "Hm" as %(m & -> & ->);
      destruct m; eq_pures'; iApply eq_value; iApply eq_bool.
  Qed.

End ot_rev_corrupted_sender_eq.

Section ot_rev_corrupted_sender_security.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.

  Theorem to_s_security : to_s_secure.
  Proof.
    intros A HA.
    apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, Mod (IProd OTAdv ARecv) TPort));
      [exact HA| |]; intros HRGS;
      [apply (EQ_sem_typed _ _ ⊥ _ hyb_ideal_TO_S_EQ Fwd)
      |apply (EQ_sem_typed _ _ ⊥ _ hyb_ideal_TO_S_EQ Bwd)].
  Qed.

End ot_rev_corrupted_sender_security.
