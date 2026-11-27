(* Security of oblivious transfer with a corrupted receiver.

   The real module [OT_S ⊳ (F_CRS ⊗ id_mod)] and the ideal module
   [F_OT_R ⊳ S_OT_R] are related by one proof in the equivalence logic of
   [eq/], read in both directions, that spends two error credits of
   [1/n]: one for the reference string's generator [g1] not being the
   unit, and one for the two trapdoors being different.  The bijections it
   couples along, and what they do to the reference string and to a
   ciphertext, are in [ot_arith.v]. *)

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
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules ot ot_eq ot_arith ot_corrupted_receiver.

Import fingroup.
Import fingroup.fingroup.
Import valgroup_notation.

#[local] Set Default Proof Using "All".

Section ot_corrupted_receiver_eq.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.

  #[local] Notation n := (S (S n'')).
  Context `{n_prime : is_true (prime.prime n)}.
  #[local] Open Scope bi_scope.

  #[local] Instance mask_r_bij' a t km ku kv : Bij (mask_r a t km ku kv).
  Proof. by apply mask_r_bij. Qed.
  #[local] Instance mask_s_bij' a t km ku kv : Bij (mask_s a t km ku kv).
  Proof. by apply mask_s_bij. Qed.

  Lemma real_ideal_EQ :
    ⎡↯ (1 / n)⎤ ∗ ⎡↯ (1 / n)⎤
    ⊢ ⟪ ModA (IProd Pub RNet) SPort ⟫ REAL_OT_R IDEAL_OT_R.
  Proof.
    iIntros "(He1 & He2)". rewrite /ModA /ModM. iEval (rewrite eq_lift_forall). iIntros (θ).
    rewrite eq_lift_mbang /=.
    iApply eq_lift_arr. iIntros (advl advr) "Hadv".
    rewrite /IProd /RNet /Pub. iEval (rewrite eq_lift_prod) in "Hadv".
    iDestruct "Hadv" as (pl pr nl nr) "(-> & -> & #Hpub & Hnet)".
    iEval (rewrite eq_lift_prod) in "Hnet".
    iDestruct "Hnet" as (rl rr sl sr) "(-> & -> & #Hrecv & #Hsend)".
    rewrite /REAL_OT_R /IDEAL_OT_R /comp_op /tens_op /id_mod /F_CRS /F_CRS_DH /DDH_rand /F_OT_R /S_OT_R /OT_S /sample is_unit.
    eq_pures_l. eq_pures_r.

    (* The reference string [(h1, h0, g1, g)].  The generator [g1 = g ^+ a1]
       is not the unit; the simulator's [h0 = g ^ t0] is the real one, and
       its [h1 = g1 ^ t1'] is the real [h1 = g ^+ t1] for
       [t1' = trap a1 t1], with the trapdoors [t0] and [t1'] different. *)
    couple_along (λ x : nat, x) avoiding 0%nat; [intros; lia|lia|].
    iFrame "He1". iIntros (a1 Ha1 Hnz1). simpl. eq_pures'.
    eq_couple_rand_rand. iIntros (t0 Ht0). simpl. eq_pures'.
    assert (Bij (trap a1)) as Hb1 by by apply trap_bij.
    couple_along (trap a1) avoiding (untrap a1 t0);
      [by apply trap_lt|apply (untrap_lt n_prime); lia|].
    iFrame "He2". iIntros (t1 Ht1 Hneq). simpl. eq_pures'.
    rewrite !(trap_exp n_prime) //.

    (* Publish it. *)
    eq_reshape_l (pl _). eq_reshape_r (pr _).
    iApply (eq_call MS ⟨⟩%R Crs 𝟙%T with "Hpub"); try (intros; apply _); first iApply eq_crs.
    iIntros "!>" (wl wr) "_". simpl. eq_pures'.

    (* The sender's port, first phase: the receiver's message [(u, v)],
       from which the simulator extracts the choice. *)
    iApply eq_value. iModIntro. rewrite /SPort. iApply eq_lift_arr. iIntros (wl' wr') "Hw".
    iEval (rewrite eq_lift_unit) in "Hw". iDestruct "Hw" as %[-> ->].
    iAssert (⎡(¡ θ)%R ≤ᵣ (¡ θ)%R⎤)%I as "#Hρ"; first by iApply row_le_refl.
    eq_pures'.
    eq_reshape_l (rl _). eq_reshape_r (rr _).
    iApply (eq_call_frame θ (¡ θ)%R 𝟙%T (𝔾 × 𝔾)%T emp%I with "Hρ Hrecv [] []");
      try (intros; apply _); [by iEval (rewrite eq_lift_unit)|done|].
    iIntros "!>" (uvl uvr) "Huv _". iEval (rewrite eq_lift_prod) in "Huv".
    iDestruct "Huv" as (ul ur vl vr) "(-> & -> & Hu & Hv)".
    iEval (rewrite eq_lift_group) in "Hu". iDestruct "Hu" as (u) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hv". iDestruct "Hv" as (v) "[-> ->]".
    simpl. eq_pures'.

    (* Second phase: the sender's messages. *)
    iApply eq_value. iModIntro. iApply eq_lift_arr. iIntros (ml mr) "Hm".
    iEval (rewrite eq_lift_prod) in "Hm".
    iDestruct "Hm" as (m0l m0r m1l m1r) "(-> & -> & Hm0 & Hm1)".
    iEval (rewrite eq_lift_group) in "Hm0". iDestruct "Hm0" as (m0) "[-> ->]".
    iEval (rewrite eq_lift_group) in "Hm1". iDestruct "Hm1" as (m1) "[-> ->]".
    eq_pures'.
    destruct (log_g_nat n_prime m0) as (km0 & Hkm0 & ->). destruct (log_g_nat n_prime m1) as (km1 & Hkm1 & ->).
    destruct (log_g_nat n_prime u) as (ku & Hku & ->). destruct (log_g_nat n_prime v) as (kv & Hkv & ->).

    destruct (decide (g ^+ ku = 1)%g) as [Hu|Hu].
    { (* [u] is the unit: the sender stops. *)
      rewrite (bool_decide_eq_true_2 _ Hu). eq_pures'.
      case_bool_decide; eq_pures'; rewrite (bool_decide_eq_true_2 _ Hu);
        eq_pures'; iApply eq_value; by iEval (rewrite eq_lift_unit). }
    rewrite (bool_decide_eq_false_2 _ Hu).

    destruct (decide (g ^+ kv = (g ^+ ku ^+ t0))%g) as [Hv|Hv].
    - (* The message opens slot [0]: the choice is [m0], and the ciphertext
         of [m1] is that of the dummy. *)
      rewrite (bool_decide_eq_true_2 _ Hv).
      eq_pures'. rewrite (bool_decide_eq_false_2 _ Hu). eq_pures'.
      couple_along (mask_s a1 t1 km1 ku kv); first by apply mask_s_lt.
      iIntros (s1 Hs1). eq_pures'.
      couple_along (mask_r a1 t1 km1 ku kv); first by apply mask_r_lt.
      iIntros (r1 Hr1). eq_pures'.
      eq_couple_rand_rand. iIntros (s0 Hs0). eq_pures'.
      eq_couple_rand_rand. iIntros (r0 Hr0). rewrite /enc. eq_pures'.
      iApply (eq_call_frame θ (¡ θ)%R ((𝔾 × 𝔾) × (𝔾 × 𝔾))%T 𝟙%T emp%I sl sr _ _ [] []
                with "Hρ Hsend [] []"); try (intros; apply _); [|done|].
      { iApply eq_ctxts; [done|done|by apply mask_fst|apply mask_snd; try done].
        by apply (nondeg_other1 n_prime (t0 := t0)). }
      iIntros "!>" (??) "Hunit _". simpl. by iApply eq_value.
    - (* It does not: the choice is [m1], and the ciphertext of [m0] is that
         of the dummy. *)
      rewrite (bool_decide_eq_false_2 _ Hv).
      eq_pures'. rewrite (bool_decide_eq_false_2 _ Hu). eq_pures'.
      eq_couple_rand_rand. iIntros (s1 Hs1). eq_pures'.
      eq_couple_rand_rand. iIntros (r1 Hr1). eq_pures'.
      couple_along (mask_s 1 t0 km0 ku kv); first by apply mask_s_lt.
      iIntros (s0 Hs0). eq_pures'.
      couple_along (mask_r 1 t0 km0 ku kv); first by apply mask_r_lt.
      iIntros (r0 Hr0). rewrite /enc. eq_pures'.
      iApply (eq_call_frame θ (¡ θ)%R ((𝔾 × 𝔾) × (𝔾 × 𝔾))%T 𝟙%T emp%I sl sr _ _ [] []
                with "Hρ Hsend [] []"); try (intros; apply _); [|done|].
      { iApply eq_ctxts; [by apply mask_fst1|apply mask_snd; try done; try lia|done|done].
        by apply nondeg_self1. }
      iIntros "!>" (??) "Hunit _". simpl. by iApply eq_value.
  Qed.


End ot_corrupted_receiver_eq.

(* ------------------------------------------------------------------ *)
(* The security theorem.                                               *)
(* ------------------------------------------------------------------ *)

Section ot_corrupted_receiver_security.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.

  #[local] Notation n := (S (S n'')).
  Context `{n_prime : is_true (prime.prime n)}.

  Lemma ot_credits `{!probblazeRGS Σ} :
    ↯ (2 / n) ⊢ ↯ (1 / n) ∗ ↯ (1 / n).
  Proof.
    assert (0 <= 1 / n)%R as Hn.
    { apply Rcomplements.Rdiv_le_0_compat; first lra. apply lt_0_INR. lia. }
    assert (2 / n = 1 / n + 1 / n)%R as -> by lra.
    iIntros "H". by iDestruct (ec_split with "H") as "[$ $]".
  Qed.

  Theorem ot_r_security : ot_r_secure.
  Proof.
    intros A HA.
    apply (sem_typed_advantage_aff A REAL_OT_R IDEAL_OT_R
             (λ H : probblazeRGS Σ, ModA (IProd Pub RNet) SPort) (2 / n)).
    { apply Rcomplements.Rdiv_le_0_compat; first lra. apply lt_0_INR. lia. }
    { exact HA. }
    split; intros HRGS; iIntros "Herr"; iDestruct (ot_credits with "Herr") as "Herr".
    - pose proof (real_ideal_EQ (n_prime := n_prime)) as [H]. specialize (H Fwd).
      rewrite !monPred_at_sep !monPred_at_embed eq_lift_at /pick /= in H. by iApply H.
    - pose proof (real_ideal_EQ (n_prime := n_prime)) as [H]. specialize (H Bwd).
      rewrite !monPred_at_sep !monPred_at_embed eq_lift_at /pick /= in H. by iApply H.
  Qed.

End ot_corrupted_receiver_security.
