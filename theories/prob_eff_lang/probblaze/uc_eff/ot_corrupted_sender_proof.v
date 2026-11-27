(* Security of oblivious transfer with a corrupted sender as modules
   (uc_eff/DESIGN.md, section 6).

   Two steps, from the real module [OT_R ⊳ (F_CRS ⊗ id)] to the ideal
   module [F_OT_S ⊳ S_OT_S]:

   1. The real reference string is a random DDH tuple ([F_CRS] is
      [F_CRS_DH DDH_rand]); against a real one: the DDH advantage of the
      reduction [DDH_RED A] ([hyb_ddh]).
   2. [dh_ideal_EQ]: with the reference string a DDH tuple, the real
      receiver's message for the choice [b] is the simulator's message,
      which opens both slots, when [y ≠ 0]: one error credit of [1/n].
      The simulator decrypts both ciphertexts and the functionality hands
      the receiver the one it chose. *)

From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.eq Require Import eq_logic eq_valgroup eq_compat.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage uc_advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules ot ot_eq ot_arith ot_corrupted_sender.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section ot_corrupted_sender_eq.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S (S n'')).
  Context `{n_prime : is_true (prime.prime n)}.
  #[local] Open Scope bi_scope.

  (* Step 2: with a DDH tuple as reference string, the real receiver is the
     ideal one with the simulator. *)
  Lemma dh_ideal_EQ :
    ⎡↯ (1 / n)⎤ ⊢ ⟪ ModA (IProd Pub SNet) RPort ⟫ (HYB_OT_S DDH_real) IDEAL_OT_S.
  Proof.
    iIntros "He". rewrite /ModA /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    rewrite eq_lift_mbang /=.
    iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /SNet /Pub. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (pl pr nl nr) "(-> & -> & #Hpub & Hnet)".
    iEval (rewrite eq_lift_prod) in "Hnet".
    iDestruct "Hnet" as (sl sr rl rr) "(-> & -> & #Hsend & #Hrecv)".
    rewrite /IDEAL_OT_S /HYB_OT_S /comp_op /tens_op /id_mod /F_CRS_DH /DDH_real
      /OT_R /F_OT_S /S_OT_S /sample.
    eq_pures_l. eq_pures_r.

    (* The reference string, the same on both sides; the trapdoor [y] is
       not [0]. *)
    couple_along (λ x : nat, x) avoiding 0%nat; [intros; lia|lia|].
    iFrame "He". iIntros (y Hy Hnz). simpl. eq_pures'.
    eq_couple_rand_rand. iIntros (x Hx). simpl. eq_pures'.

    (* Publish it. *)
    eq_reshape_l (pl _). eq_reshape_r (pr _).
    iApply (eq_call MS ⟨⟩%R Crs 𝟙%T with "Hpub"); try (intros; apply _);
      first iApply eq_crs.
    iIntros "!>" (wl wr) "_". simpl. eq_pures'.

    (* The receiver's port.  The receiver's [x'] is the simulator's [a0]
       if [b] is [false] and its [a1] otherwise. *)
    iApply eq_value. iModIntro. rewrite /RPort. iApply eq_lift_arr. iIntros (bl br) "Hb".
    iEval (rewrite eq_lift_bool) in "Hb". iDestruct "Hb" as %(b & -> & ->).
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    eq_pures'.
    destruct b.
    - (* [b] is [true]: [a1 = x'], and [g ^ (x' y) = g1 ^ x']. *)
      eq_couple_rand_rand. iIntros (x' Hx'). eq_pures'.
      rewrite -Nat2Z.inj_mul /dec. eq_pures'. rewrite !(expg_mul n_prime) (expgAC g x y).
      eq_reshape_l (sl _). eq_reshape_r (sr _).
      iApply (eq_call_frame θ (¡ θ)%R (𝔾 × 𝔾)%T 𝟙%T emp%I with "Hρ Hsend [] []");
        try (intros; apply _); [by iApply eq_pair|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'. eq_reshape_l (rl _). eq_reshape_r (rr _).
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T ((𝔾 × 𝔾) × (𝔾 × 𝔾))%T emp%I with "Hρ Hrecv [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (el er) "He _". iDestruct (eq_lift_ctxts with "He") as (c0 d0 c1 d1) "[-> ->]".
      eq_pures'.
      iApply eq_value. by iApply eq_group_val.
    - (* [b] is [false]: [a0 = a1 y = x'] for [a1 = trap y x']. *)
      assert (Bij (trap y)) as Hb by by apply trap_bij.
      couple_along (trap y); first by apply trap_lt.
      iIntros (x' Hx'). eq_pures'.
      rewrite -Nat2Z.inj_mul /dec. eq_pures'. rewrite !(trap_mul n_prime) //.
      eq_reshape_l (sl _). eq_reshape_r (sr _).
      iApply (eq_call_frame θ (¡ θ)%R (𝔾 × 𝔾)%T 𝟙%T emp%I with "Hρ Hsend [] []");
        try (intros; apply _); [by iApply eq_pair|done|].
      iIntros "!>" (??) "Hu _". iEval (rewrite eq_lift_unit) in "Hu". iDestruct "Hu" as %[-> ->].
      eq_pures'. eq_reshape_l (rl _). eq_reshape_r (rr _).
      iApply (eq_call_frame θ (¡ θ)%R 𝟙%T ((𝔾 × 𝔾) × (𝔾 × 𝔾))%T emp%I with "Hρ Hrecv [] []");
        try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
      iIntros "!>" (el er) "He _". iDestruct (eq_lift_ctxts with "He") as (c0 d0 c1 d1) "[-> ->]".
      eq_pures'.
      rewrite (trap_mul n_prime) //. iApply eq_value. by iApply eq_group_val.
  Qed.

End ot_corrupted_sender_eq.

(* ------------------------------------------------------------------ *)
(* The security theorem.                                               *)
(* ------------------------------------------------------------------ *)

Section ot_corrupted_sender_security.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.

  #[local] Notation n := (S (S n'')).
  Context `{n_prime : is_true (prime.prime n)}.

  Lemma one_n_nonneg : (0 <= 1 / n)%R.
  Proof. apply Rcomplements.Rdiv_le_0_compat; first lra. apply lt_0_INR. lia. Qed.

  (* Step 1: the real module is the hybrid with a random DDH tuple, and the
     two hybrids are the reduction run against the two DDH samplers. *)
  Lemma hyb_ddh (A : val) (b : bool) :
    (advantage A (HYB_OT_S DDH_rand) (HYB_OT_S DDH_real) #b
       <= advantage (DDH_RED A) DDH_rand DDH_real #b)%R.
  Proof.
    rewrite /HYB_OT_S.
    etrans; first apply (advantage_pure_l_rev _ []
      (comp_app OT_R (tens_op (F_CRS_DH DDH_rand) id_mod)) _ _); [done|apply comp_app_pure|].
    etrans; first apply (advantage_pure_r_rev _ [] _
      (comp_app OT_R (tens_op (F_CRS_DH DDH_real) id_mod)) _); [done|apply comp_app_pure|].
    etrans; first apply (advantage_pure_l_rev _ [AppRCtx (comp_app OT_R)]
      (tens_app (F_CRS_DH DDH_rand) id_mod) _ _); [done|apply tens_app_pure|].
    etrans; first apply (advantage_pure_r_rev _ [AppRCtx (comp_app OT_R)] _
      (tens_app (F_CRS_DH DDH_real) id_mod) _); [done|apply tens_app_pure|].
    etrans; first apply (advantage_pure_l_rev _ [AppRCtx (comp_app OT_R); AppLCtx id_mod; AppRCtx tens_app]
      (F_CRS_DH_app DDH_rand) _ _); [done|apply F_CRS_DH_app_pure|].
    etrans; first apply (advantage_pure_r_rev _ [AppRCtx (comp_app OT_R); AppLCtx id_mod; AppRCtx tens_app] _
      (F_CRS_DH_app DDH_real) _); [done|apply F_CRS_DH_app_pure|].
    etrans; first apply (advantage_reduction_ctx A
      [AppRCtx (comp_app OT_R); AppLCtx id_mod; AppRCtx tens_app; AppRCtx F_CRS_DH_app]).
    { done. }
    { intros vs w Hw. simpl. by rewrite Hw. }
    apply Rle_refl.
  Qed.

  Theorem ot_s_security : ot_s_secure.
  Proof.
    intros A HA.
    set (τ := λ H : probblazeRGS Σ, ModA (IProd Pub SNet) RPort).
    (* The real reference string is a random DDH tuple. *)
    change REAL_OT_S with (HYB_OT_S DDH_rand).
    apply (advantage_triangle _ _ (HYB_OT_S DDH_real) _ _
             (advantage (DDH_RED A) DDH_rand DDH_real #true) (1 / n)); [| |lra].
    { apply hyb_ddh. }
    apply (sem_typed_advantage_aff A _ _ τ (1 / n) one_n_nonneg); first exact HA.
    split; intros HRGS; iIntros "Herr".
    - pose proof (dh_ideal_EQ (n_prime := n_prime)) as [H]. specialize (H Fwd).
      rewrite !monPred_at_embed eq_lift_at /pick /= in H. by iApply H.
    - pose proof (dh_ideal_EQ (n_prime := n_prime)) as [H]. specialize (H Bwd).
      rewrite !monPred_at_embed eq_lift_at /pick /= in H. by iApply H.
  Qed.

End ot_corrupted_sender_security.
