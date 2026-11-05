(* The DHKE + secure-channel composition as an instance of the UC composition
   theorem [uc_composition].

     π  = DH_KE          in the F_AUTH-hybrid world, simulator F_AUTH ∘f DH_SIM,
                         realising F_KE_lazy_alice (computationally, via DDH);
     ρ  = CHAN           in the (F_KE, F_OAUTH)-hybrid world, simulator
                         CHAN_SIM_lazy, perfectly realising F_CHAN.

   The conclusion is the statement of [adv_composition_real] in
   [advantage_comp], with the composed simulator written uniformly as
   [(F_AUTH ∘f DH_SIM) ∘F CHAN_SIM_lazy] applied to [F_CHAN], and with the DDH
   reduction obtained by composing the standalone DHKE reduction with the
   hybrid-world context.  The typing of [F_CHAN] and [CHAN_SIM_lazy] is in
   [chan_ideal_typing]. *)

From clutch.prob_eff_lang.probblaze Require Import advantage.
From clutch.prob_eff_lang.probblaze.typing Require Import types fundamental interp.
From clutch.prob_eff_lang.probblaze Require Import comp_operators sem_types sem_row sem_judgement compatibility syntax semantics proofmode valgroup adequacy mode.
From clutch.prob_eff_lang.probblaze.examples Require Import
  mask sec_channel_def dhke_common dhke_typing dhke_channel_lazy_results
  advantage_dhke_lazy advantage_schan
  new_composition_defs new_composition_closed new_composition_typing
  chan_ideal_typing uc_composition.
From Stdlib Require Import Reals Psatz.

Import fingroup.
Import fingroup.fingroup.

#[local] Open Scope R_scope.

Section uc_dhke.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{Hpre :probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {msk : @Mask (@vgG vg) vgval}.
  Context {M : ∀ `{probblazeRGS Σ}, Mask_struc}.

  Import valgroup_notation.

  (* The standalone DDH reduction of the DHKE proof. *)
  Definition DH_RED : expr := (λ: "DH", F_AUTH ∘f (C_lazy "DH"))%E.

  (* The composed simulator, and the ideal system in uniform shape. *)
  Definition SIM_DHKE_CHAN : expr := (F_AUTH ∘f DH_SIM) ∘F CHAN_SIM_lazy.
  Definition IDEAL_CHAN : expr := SIM_DHKE_CHAN ∘f F_CHAN.

  Lemma CHAN_SIM_lazy_closed : is_closed_expr ∅ CHAN_SIM_lazy.
  Proof using All.
    by destruct (closed_app_inv _ _ (proj1 (closed_app_inv _ _ CHAN_SIM_lazy_F_CHAN_closed))).
  Qed.
  Lemma F_CHAN_closed : is_closed_expr ∅ F_CHAN.
  Proof using All. by destruct (closed_app_inv _ _ CHAN_SIM_lazy_F_CHAN_closed). Qed.

  (* π realises F_KE: the standalone DHKE result, for environments of the
     one-shot interface type [τ__F aleak gk], and with the simulator
     associated to the left. *)
  Lemma dhke_realises A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (τ__F aleak gk → 𝔹)%T) →
    advantage A (F_AUTH ∘f DH_KE) ((F_AUTH ∘f DH_SIM) ∘f F_KE_lazy_alice) #true <=
      advantage (λ: "v", A (DH_RED "v")) DH_real DH_rand #true.
  Proof using All.
    intros HA.
    eapply (advantage_triangle _ _ (F_AUTH ∘f (DH_SIM ∘f F_KE_lazy_alice)) _ _ _ 0).
    - apply adv_DHKE_real. intros HRGS.
      iApply sem_val_typed_sub; last iApply HA.
      iApply ty_le_mbang_comp; first iApply mode_le_refl.
      iApply ty_le_arr; [iApply row_le_refl|iApply τ_DH_le_τ_DH_OS|iApply ty_le_refl].
    - apply (advantage_zero _ _ _ _ (λ _, τ__F aleak gk)); [exact HA| |]; intros HRGS.
      + iApply func_comp_assoc;
          [apply F_AUTH_closed|apply DH_SIM_closed|apply FKE_closed
          |iApply F_AUTH_typed|iApply DH_SIM_typed|iApply F_KE_lazy_alice_typed].
      + iApply func_comp_assoc_rev;
          [apply F_AUTH_closed|apply DH_SIM_closed|apply FKE_closed
          |iApply F_AUTH_typed|iApply DH_SIM_typed|iApply F_KE_lazy_alice_typed].
    - rewrite Rplus_0_r. reflexivity.
  Qed.

  (* ρ realises F_CHAN perfectly: the standalone secure-channel result. *)
  Lemma chan_realises A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A ((∀ᵣ θ, hdl cli θ ⊸ τ__f θ oaleak leakI) → 𝔹)%T) →
    advantage A ((F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f CHAN) (CHAN_SIM_lazy ∘f F_CHAN) #true <= 0.
  Proof using All.
    intros HA. right. apply adv_SCHAN. intros HRGS. iApply HA.
  Qed.

  (* The composition theorem instantiated. *)
  Theorem adv_composition_uc A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (τ → 𝔹)%T) →
    advantage A REAL_CHAN_DHKE IDEAL_CHAN #true <=
      advantage (λ: "v", (λ: "v", A (("v" ||ᵣ F_OAUTH) ∘f CHAN))%V (DH_RED "v")) DH_real DH_rand #true.
  Proof using All.
    intros HA.
    unfold REAL_CHAN_DHKE, IDEAL_CHAN, SIM_DHKE_CHAN.
    etrans.
    - apply (uc_composition (F_AUTH ∘f DH_KE) (F_AUTH ∘f DH_SIM) F_KE_lazy_alice
               CHAN_SIM_lazy F_CHAN F_OAUTH CHAN true
               (λ A', advantage (λ: "v", A' (DH_RED "v")) DH_real DH_rand #true) (λ _, 0)
               (λ _, hdl cli) (λ _, chan) (λ _, gk) (λ _, oaleak) (λ _, leakI) (λ _, aleak) (λ _, fleak)).
      + apply F_AUTH_DH_SIM_closed.
      + apply FKE_closed.
      + apply F_OAUTH_closed.
      + apply CHAN_closed.
      + apply CHAN_SIM_lazy_closed.
      + apply F_CHAN_closed.
      + intros HRGS. iApply F_AUTH_DH_SIM_FO_typed.
      + intros HRGS. iApply F_KE_lazy_alice_typed.
      + intros HRGS. iApply F_OAUTH_typed.
      + intros HRGS. iApply CHAN_typed.
      + intros HRGS. iApply CHAN_SIM_lazy_typed.
      + intros HRGS. iApply F_CHAN_typed.
      + intros A' HA'. by apply dhke_realises.
      + intros A' HA'. by apply chan_realises.
      + exact HA.
    - rewrite Rplus_0_r. reflexivity.
  Qed.

End uc_dhke.


