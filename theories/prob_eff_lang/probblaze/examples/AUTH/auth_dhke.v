(* DHKE over the authenticated-channel protocol [AUTH], as an instance of the
   UC composition theorem [uc_composition_f]:

     π  = AUTH      in the raw-network world, simulator S_AUTH, realising F_AUTH
                    (hypothesis [auth_realises], up to 2/q);
     ρ  = DH_KE     in the F_AUTH-hybrid world, simulator F_AUTH ∘f DH_SIM,
                    realising F_KE_lazy_alice (computationally, via DDH).

   The composition theorem wants ρ to be a value, so the composition is stated
   for [DH_KE_v] and transported to [DH_KE] through [auth_relation]. *)

From clutch.prob_eff_lang.probblaze Require Import advantage.
From clutch.prob_eff_lang.probblaze.typing Require Import types fundamental interp.
From clutch.prob_eff_lang.probblaze Require Import comp_operators sem_types sem_row sem_judgement compatibility syntax semantics proofmode valgroup adequacy mode.
From clutch.prob_eff_lang.probblaze.examples Require Import
  dhke_common dhke_typing dhke_channel_lazy_results advantage_dhke_lazy dhke_closed uc_composition.
From clutch.prob_eff_lang.probblaze.examples.AUTH Require Import auth_def auth_typing auth_relation.
From Stdlib Require Import Reals Psatz.

Import fingroup.
Import fingroup.fingroup.

#[local] Open Scope R_scope.

Section auth_dhke.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.

  Import valgroup_notation.
  #[local] Notation n := (S n'').

  (* The standalone DDH reduction of the DHKE proof. *)
  Definition DH_RED : expr := (λ: "DH", F_AUTH ∘f (C_lazy "DH"))%E.

  Lemma F_AUTH_closed : is_closed_expr ∅ F_AUTH.
  Proof. is_closed. Qed.
  Lemma DH_SIM_closed : is_closed_expr ∅ DH_SIM.
  Proof. is_closed. Qed.
  Lemma F_AUTH_DH_SIM_closed : is_closed_expr ∅ (F_AUTH ∘f DH_SIM).
  Proof. apply closed_func_comp; [apply F_AUTH_closed|apply DH_SIM_closed]. Qed.

  Lemma F_AUTH_DH_SIM_typed `{!probblazeRGS Σ} :
    ⊢ sem_typed [] (F_AUTH ∘f DH_SIM) (F_AUTH ∘f DH_SIM) ⊥ (τ__F aleak leakI) [].
  Proof using All. iApply func_comp_cong_F; [iApply F_AUTH_typed|iApply DH_SIM_typed]. Qed.

  (* ρ = DH_KE_v realises F_KE in the F_AUTH-hybrid world: the standalone
     DHKE result, transported to [DH_KE_v] and with the simulator associated
     to the left. *)
  Lemma dhke_v_realises A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (τ__F aleak gk → 𝔹)%T) →
    advantage A (F_AUTH ∘f DH_KE_v) ((F_AUTH ∘f DH_SIM) ∘f F_KE_lazy_alice) #true <=
      advantage (λ: "v", A (DH_RED "v")) DH_real DH_rand #true.
  Proof using All.
    intros HA.
    eapply (advantage_triangle _ _ (F_AUTH ∘f DH_KE) _ _ 0); first last.
    { rewrite Rplus_0_l. reflexivity. }
    2: { apply (advantage_zero _ _ _ _ (λ _, τ__F aleak gk)); [exact HA| |]; intros HRGS.
         - iApply func_comp_cong_F; [iApply F_AUTH_typed|iApply DH_KE_v_le_DH_KE].
         - iApply func_comp_cong_F; [iApply F_AUTH_typed|iApply DH_KE_le_DH_KE_v]. }
    eapply (advantage_triangle _ _ (F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)) _ _ _ 0).
    - apply adv_DHKE_real. intros HRGS.
      iApply sem_val_typed_sub; last iApply HA.
      iApply ty_le_mbang_comp; first iApply mode_le_refl.
      iApply ty_le_arr; [iApply row_le_refl|iApply τ_DH_le_τ_DH_OS|iApply ty_le_refl].
    - apply (advantage_zero _ _ _ _ (λ _, τ__F aleak gk)); [exact HA| |]; intros HRGS.
      + iApply func_comp_assoc;
          [apply F_AUTH_closed|apply DH_SIM_closed|apply F_KE_lazy_alice_closed
          |iApply F_AUTH_typed|iApply DH_SIM_typed|iApply F_KE_lazy_alice_typed].
      + iApply func_comp_assoc_rev;
          [apply F_AUTH_closed|apply DH_SIM_closed|apply F_KE_lazy_alice_closed
          |iApply F_AUTH_typed|iApply DH_SIM_typed|iApply F_KE_lazy_alice_typed].
    - rewrite Rplus_0_r. reflexivity.
  Qed.

  (* π = AUTH realises F_AUTH over the raw network with simulator S_AUTH, up
     to the probability 2/q of forging one of the two one-time MACs.  (To be
     proved separately.) *)
  Hypothesis auth_realises : ∀ A : val,
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (τ__F raw chan → 𝔹)%T) →
    advantage A AUTH (S_AUTH ∘f F_AUTH) #true <= 2 / n.

  (* The composition theorem instantiated. *)
  Theorem auth_dhke A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (τ__F raw gk → 𝔹)%T) →
    advantage A (AUTH ∘f DH_KE) ((S_AUTH ∘f (F_AUTH ∘f DH_SIM)) ∘f F_KE_lazy_alice) #true
      <= 2 / n + advantage (λ: "v", (λ: "v", A (S_AUTH ∘f "v"))%V (DH_RED "v")) DH_real DH_rand #true.
  Proof using All.
    intros HA.
    eapply (advantage_triangle _ _ (AUTH ∘f DH_KE_v) _ _ 0); first last.
    { rewrite Rplus_0_l. reflexivity. }
    2: { apply (advantage_zero _ _ _ _ (λ _, τ__F raw gk)); [exact HA| |]; intros HRGS.
         - iApply func_comp_cong_F; [iApply AUTH_typed|iApply DH_KE_le_DH_KE_v].
         - iApply func_comp_cong_F; [iApply AUTH_typed|iApply DH_KE_v_le_DH_KE]. }
    apply (uc_composition_f AUTH S_AUTH F_AUTH (F_AUTH ∘f DH_SIM) F_KE_lazy_alice DH_KE_v true
             (λ _, 2 / n) (λ A', advantage (λ: "v", A' (DH_RED "v")) DH_real DH_rand #true)
             (λ _, gk) (λ _, chan) (λ _, aleak) (λ _, raw) (λ _, leakI)).
    + apply S_AUTH_closed.
    + apply F_AUTH_closed.
    + apply DH_KE_v_closed.
    + apply F_AUTH_DH_SIM_closed.
    + apply F_KE_lazy_alice_closed.
    + intros HRGS. iApply S_AUTH_typed.
    + intros HRGS. iApply F_AUTH_typed.
    + intros HRGS. iApply DH_KE_v_typed.
    + intros HRGS. iApply F_AUTH_DH_SIM_typed.
    + intros HRGS. iApply F_KE_lazy_alice_typed.
    + intros A' HA'. by apply auth_realises.
    + intros A' HA'. by apply dhke_v_realises.
    + exact HA.
  Qed.

End auth_dhke.
