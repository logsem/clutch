(* Oblivious transfer reversal composed with oblivious transfer: the
   reversal on the real OT protocol realises the transfer, by
   [uc_composition] at one-instance modules.

   For each case there are two results.  The first ([*_beside]) is the
   OT's realisation of its functionality beside what the reversal adds to
   it (Alice's message, through the adversary or a channel), from the OT's
   security theorem by [env_beside_typed] and interchange.  The second
   ([*_ot_security]) composes it with the reversal's perfect realisation
   of the transfer on the ideal OT. *)

From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Import monpred.
From iris.proofmode Require Import monpred.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage uc_advantage.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules eq_modules auth auth_typing
  ot ot_proof ot_rev_proof ot_corrupted_receiver
  ot_corrupted_receiver_proof ot_corrupted_sender ot_corrupted_sender_proof ot_typing ot_rev
  ot_rev_corrupted_sender ot_rev_corrupted_sender_proof ot_rev_corrupted_receiver
  ot_rev_corrupted_receiver_proof ot_rev_typing.
From Stdlib Require Import Reals Lra.

#[local] Set Default Proof Using "All".

Section ot_rev_ot.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.

  #[local] Notation n := (S (S n'')).
  Context `{n_prime : is_true (prime.prime n)}.
  #[local] Open Scope R_scope.
  #[local] Open Scope mod_scope.

  (* ---------------------------------------------------------------- *)
  (* Alice corrupted: the OT with a corrupted receiver.                 *)
  (* ---------------------------------------------------------------- *)

  (* The OT realises its functionality beside Alice's
     message. *)
  Lemma ot_r_beside (A : val) :
    (∀ `{probblazeRGS Σ},
       ⊢ sem_val_typed A A (ModA (IProd (IProd Pub RNet) ARecv) (IProd SPort ARecv) → 𝔹)%T) →
    advantage A (REAL_OT_R ⊗ id_mod) ((F_OT_R ⊗ id_mod) ⊳ (S_OT_R ⊗ id_mod)) #true <= 2 / n.
  Proof.
    intros HA.
    apply (advantage_triangle _ _ (IDEAL_OT_R ⊗ id_mod) _ _ (2 / n) 0); [| |lra].
    - etrans; first apply (advantage_pure_l_rev _ [] (tens_app REAL_OT_R id_mod) _ _);
        [done|apply tens_app_pure|].
      etrans; first apply (advantage_pure_r_rev _ [] _ (tens_app IDEAL_OT_R id_mod) _);
        [done|apply tens_app_pure|].
      etrans; first apply (advantage_reduction_ctx A [AppLCtx id_mod; AppRCtx tens_app]).
      { done. }
      { intros vs w Hw. simpl. by rewrite Hw. }
      apply (ot_r_security (n_prime := n_prime)). intros HRGS.
      iApply env_beside_typed; [iApply HA|iApply id_mod_typed].
    - rewrite /IDEAL_OT_R.
      apply (advantage_zero _ _ _ _
               (λ H : probblazeRGS Σ, ModA (IProd (IProd Pub RNet) ARecv) (IProd SPort ARecv)));
        [exact HA| |]; intros HRGS; iApply sem_typed_val.
      + iApply tens_interchange;
          [iApply Mod_ModA_typed; iApply F_OT_R_typed
          |iApply Mod_ModA_typed; iApply S_OT_R_typed
          |iApply id_mod_typed].
      + iApply tens_interchange_rev;
          [iApply Mod_ModA_typed; iApply F_OT_R_typed
          |iApply Mod_ModA_typed; iApply S_OT_R_typed
          |iApply id_mod_typed].
  Qed.

  (* Bob on the real OT realises the transfer with Alice
     corrupted, with the simulator [S_TO_S ⊳ (S_OT_R ⊗ id)]. *)
  Theorem to_s_ot_security (A : val) :
    (∀ `{probblazeRGS Σ},
       ⊢ sem_val_typed A A (ModA (IProd (IProd Pub RNet) ARecv) TPort → 𝔹)%T) →
    advantage A (TO_R ⊳ (REAL_OT_R ⊗ id_mod)) (F_TO_S ⊳ (S_TO_S ⊳ (S_OT_R ⊗ id_mod))) #true
      <= 2 / n.
  Proof.
    intros HA.
    etrans; first apply (uc_composition OS
      (REAL_OT_R ⊗ id_mod) (S_OT_R ⊗ id_mod) (F_OT_R ⊗ id_mod) TO_R S_TO_S F_TO_S true
      (λ _, 2 / n) (λ _, 0)
      (λ _, IProd (IProd Pub RNet) ARecv) (λ _, IProd OTAdv ARecv) (λ _, TOSAdv)
      (λ _, IProd SPort ARecv) (λ _, TPort)).
    - intros HRGS. iApply tens_op_typed;
        [iApply Mod_ModA_typed; iApply S_OT_R_typed|iApply id_mod_typed].
    - intros HRGS. iApply tens_op_typed;
        [iApply Mod_ModA_typed; iApply F_OT_R_typed|iApply id_mod_typed].
    - intros HRGS. iApply Mod_ModA_typed. iApply TO_R_typed.
    - intros HRGS. iApply Mod_ModA_typed. iApply S_TO_S_typed.
    - intros HRGS. iApply Mod_ModA_typed. iApply F_TO_S_typed.
    - apply ot_r_beside.
    - apply (advantage_Mod_ModA _ _ _ _ (λ _, IProd OTAdv ARecv) (λ _, TPort)).
      intros A' HA'. apply to_s_security. exact HA'.
    - exact HA.
    - simpl. lra.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Bob corrupted: the OT with a corrupted sender.                     *)
  (* ---------------------------------------------------------------- *)

  (* The OT realises its functionality beside Alice's
     message; the DDH reduction gets the environment with the identity
     beside. *)
  Lemma ot_s_beside (A : val) :
    (∀ `{probblazeRGS Σ},
       ⊢ sem_val_typed A A (ModA (IProd (IProd Pub SNet) ASend) (IProd RPort ASend) → 𝔹)%T) →
    advantage A (REAL_OT_S ⊗ id_mod) ((F_OT_S ⊗ id_mod) ⊳ (S_OT_S ⊗ id_mod)) #true
      <= advantage (DDH_RED (λ: "v", A (tens_app "v" id_mod))%V) DDH_rand DDH_real #true + 1 / n.
  Proof.
    intros HA.
    apply (advantage_triangle _ _ (IDEAL_OT_S ⊗ id_mod) _ _
             (advantage (DDH_RED (λ: "v", A (tens_app "v" id_mod))%V) DDH_rand DDH_real #true + 1 / n)
             0); [| |lra].
    - etrans; first apply (advantage_pure_l_rev _ [] (tens_app REAL_OT_S id_mod) _ _);
        [done|apply tens_app_pure|].
      etrans; first apply (advantage_pure_r_rev _ [] _ (tens_app IDEAL_OT_S id_mod) _);
        [done|apply tens_app_pure|].
      etrans; first apply (advantage_reduction_ctx A [AppLCtx id_mod; AppRCtx tens_app]).
      { done. }
      { intros vs w Hw. simpl. by rewrite Hw. }
      apply (ot_s_security (n_prime := n_prime)). intros HRGS.
      iApply env_beside_typed; [iApply HA|iApply id_mod_typed].
    - rewrite /IDEAL_OT_S.
      apply (advantage_zero _ _ _ _
               (λ H : probblazeRGS Σ, ModA (IProd (IProd Pub SNet) ASend) (IProd RPort ASend)));
        [exact HA| |]; intros HRGS; iApply sem_typed_val.
      + iApply tens_interchange;
          [iApply Mod_ModA_typed; iApply F_OT_S_typed
          |iApply Mod_ModA_typed; iApply S_OT_S_typed
          |iApply id_mod_typed].
      + iApply tens_interchange_rev;
          [iApply Mod_ModA_typed; iApply F_OT_S_typed
          |iApply Mod_ModA_typed; iApply S_OT_S_typed
          |iApply id_mod_typed].
  Qed.

  (* Alice on the real OT realises the transfer with Bob
     corrupted, with the simulator [S_TO_R ⊳ (S_OT_S ⊗ id)]. *)
  Theorem to_r_ot_security (A : val) :
    (∀ `{probblazeRGS Σ},
       ⊢ sem_val_typed A A (ModA (IProd (IProd Pub SNet) ASend) TSPort → 𝔹)%T) →
    advantage A (TO_S ⊳ (REAL_OT_S ⊗ id_mod)) (F_TO_R ⊳ (S_TO_R ⊳ (S_OT_S ⊗ id_mod))) #true
      <= advantage
           (DDH_RED (λ: "v", (λ: "v", A (comp_app TO_S "v"))%V (tens_app "v" id_mod))%V)
           DDH_rand DDH_real #true + 1 / n.
  Proof.
    intros HA.
    etrans; first apply (uc_composition OS
      (REAL_OT_S ⊗ id_mod) (S_OT_S ⊗ id_mod) (F_OT_S ⊗ id_mod) TO_S S_TO_R F_TO_R true
      (λ A, advantage (DDH_RED (λ: "v", A (tens_app "v" id_mod))%V) DDH_rand DDH_real #true + 1 / n)
      (λ _, 0)
      (λ _, IProd (IProd Pub SNet) ASend) (λ _, IProd OTSAdv ASend) (λ _, TORAdv)
      (λ _, IProd RPort ASend) (λ _, TSPort)).
    - intros HRGS. iApply tens_op_typed;
        [iApply Mod_ModA_typed; iApply S_OT_S_typed|iApply id_mod_typed].
    - intros HRGS. iApply tens_op_typed;
        [iApply Mod_ModA_typed; iApply F_OT_S_typed|iApply id_mod_typed].
    - intros HRGS. iApply Mod_ModA_typed. iApply TO_S_typed.
    - intros HRGS. iApply Mod_ModA_typed. iApply S_TO_R_typed.
    - intros HRGS. iApply Mod_ModA_typed. iApply F_TO_R_typed.
    - apply ot_s_beside.
    - apply (advantage_Mod_ModA _ _ _ _ (λ _, IProd OTSAdv ASend) (λ _, TSPort)).
      intros A' HA'. apply to_r_security. exact HA'.
    - exact HA.
    - simpl. lra.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Both honest.                                                       *)
  (* ---------------------------------------------------------------- *)

  (* The OT realises its functionality beside the channel
     carrying Alice's message; the DDH reductions get the environment
     with the channel beside. *)
  Lemma ot_h_beside (A : val) :
    (∀ `{probblazeRGS Σ},
       ⊢ sem_val_typed A A
           (ModA (IProd OTHNet (ONetT 𝔹)) (IProd OTPorts (OEpT 𝔹)) → 𝔹)%T) →
    advantage A (REAL_OT_H ⊗ F_OAUTH) ((F_OT_H ⊗ F_OAUTH) ⊳ (S_OT_H ⊗ id_mod)) #true
      <= advantage (RED1_OT_H (λ: "v", A (tens_app "v" F_OAUTH))%V) DDH_rand DDH_real #true
         + advantage (RED2_OT_H (λ: "v", A (tens_app "v" F_OAUTH))%V) DDH_real DDH_rand #true
         + advantage (RED2_OT_H (DENV_OT_H (λ: "v", A (tens_app "v" F_OAUTH))%V)) DDH_real DDH_rand #true
         + 3 / n.
  Proof.
    intros HA.
    apply (advantage_triangle _ _ (IDEAL_OT_H ⊗ F_OAUTH) _ _
             (advantage (RED1_OT_H (λ: "v", A (tens_app "v" F_OAUTH))%V) DDH_rand DDH_real #true
              + advantage (RED2_OT_H (λ: "v", A (tens_app "v" F_OAUTH))%V) DDH_real DDH_rand #true
              + advantage (RED2_OT_H (DENV_OT_H (λ: "v", A (tens_app "v" F_OAUTH))%V))
                  DDH_real DDH_rand #true
              + 3 / n) 0); [| |lra].
    - etrans; first apply (advantage_pure_l_rev _ [] (tens_app REAL_OT_H F_OAUTH) _ _);
        [done|apply tens_app_pure|].
      etrans; first apply (advantage_pure_r_rev _ [] _ (tens_app IDEAL_OT_H F_OAUTH) _);
        [done|apply tens_app_pure|].
      etrans; first apply (advantage_reduction_ctx A [AppLCtx F_OAUTH; AppRCtx tens_app]).
      { done. }
      { intros vs w Hw. simpl. by rewrite Hw. }
      apply (ot_h_security (n_prime := n_prime)). intros HRGS.
      iApply env_beside_typed; [iApply HA|iApply Mod_ModA_typed; iApply (F_OAUTH_typed_gen 𝔹 _ eq_ground_bool)].
    - rewrite /IDEAL_OT_H.
      apply (advantage_zero _ _ _ _
               (λ H : probblazeRGS Σ,
                  ModA (IProd OTHNet (ONetT 𝔹)) (IProd OTPorts (OEpT 𝔹))));
        [exact HA| |]; intros HRGS; iApply sem_typed_val.
      + iApply tens_interchange;
          [iApply Mod_ModA_typed; iApply F_OT_H_typed
          |iApply Mod_ModA_typed; iApply S_OT_H_typed
          |iApply Mod_ModA_typed; iApply (F_OAUTH_typed_gen 𝔹 _ eq_ground_bool)].
      + iApply tens_interchange_rev;
          [iApply Mod_ModA_typed; iApply F_OT_H_typed
          |iApply Mod_ModA_typed; iApply S_OT_H_typed
          |iApply Mod_ModA_typed; iApply (F_OAUTH_typed_gen 𝔹 _ eq_ground_bool)].
  Qed.

  (* the parties on the real OT and the channel realise the
     transfer, with the simulator [S_TO_H ⊳ (S_OT_H ⊗ id)]. *)
  Theorem to_h_ot_security (A : val) :
    (∀ `{probblazeRGS Σ},
       ⊢ sem_val_typed A A (ModA (IProd OTHNet (ONetT 𝔹)) TPorts → 𝔹)%T) →
    advantage A (PARTIES_TO ⊳ (REAL_OT_H ⊗ F_OAUTH)) (F_TO_H ⊳ (S_TO_H ⊳ (S_OT_H ⊗ id_mod))) #true
      <= advantage
           (RED1_OT_H (λ: "v", (λ: "v", A (comp_app PARTIES_TO "v"))%V (tens_app "v" F_OAUTH))%V)
           DDH_rand DDH_real #true
         + advantage
           (RED2_OT_H (λ: "v", (λ: "v", A (comp_app PARTIES_TO "v"))%V (tens_app "v" F_OAUTH))%V)
           DDH_real DDH_rand #true
         + advantage
           (RED2_OT_H (DENV_OT_H
              (λ: "v", (λ: "v", A (comp_app PARTIES_TO "v"))%V (tens_app "v" F_OAUTH))%V))
           DDH_real DDH_rand #true
         + 3 / n.
  Proof.
    intros HA.
    etrans; first apply (uc_composition OS
      (REAL_OT_H ⊗ F_OAUTH) (S_OT_H ⊗ id_mod) (F_OT_H ⊗ F_OAUTH) PARTIES_TO S_TO_H F_TO_H true
      (λ A, advantage (RED1_OT_H (λ: "v", A (tens_app "v" F_OAUTH))%V) DDH_rand DDH_real #true
            + advantage (RED2_OT_H (λ: "v", A (tens_app "v" F_OAUTH))%V) DDH_real DDH_rand #true
            + advantage (RED2_OT_H (DENV_OT_H (λ: "v", A (tens_app "v" F_OAUTH))%V))
                DDH_real DDH_rand #true
            + 3 / n)
      (λ _, 0)
      (λ _, IProd OTHNet (ONetT 𝔹)) (λ _, TOHNet) (λ _, TOHAdv)
      (λ _, IProd OTPorts (OEpT 𝔹)) (λ _, TPorts)).
    - intros HRGS. iApply tens_op_typed;
        [iApply Mod_ModA_typed; iApply S_OT_H_typed|iApply id_mod_typed].
    - intros HRGS. iApply tens_op_typed;
        [iApply Mod_ModA_typed; iApply F_OT_H_typed
        |iApply Mod_ModA_typed; iApply (F_OAUTH_typed_gen 𝔹 _ eq_ground_bool)].
    - intros HRGS. iApply Mod_ModA_typed. iApply PARTIES_TO_typed.
    - intros HRGS. iApply Mod_ModA_typed. iApply S_TO_H_typed.
    - intros HRGS. iApply Mod_ModA_typed. iApply F_TO_H_typed.
    - apply ot_h_beside.
    - apply (advantage_Mod_ModA _ _ _ _ (λ _, TOHNet) (λ _, TPorts)).
      intros A' HA'. apply to_h_security. exact HA'.
    - exact HA.
    - simpl. lra.
  Qed.

End ot_rev_ot.
