(* The DHKE + secure-channel composition as an instance of the factory
   composition theorem [uc_composition_factory], with unrestricted
   functionalities.

     π  = DH_KE   (as the factory [DHKE_f]), realising F_KE_lazy_alice via DDH;
     ρ  = CHAN    in the (F_KE, F_OAUTH)-hybrid world, perfectly realising
                  F_CHAN.

   The environment gets the composed system as a factory, may start any
   number of sessions, and may call each session's client-taking function any
   number of times ([τ_u]).  Both realisations are used in their factory
   form ([adv_DHKE_f], [adv_SCHAN_f]), whose interfaces [τ_DH] and [τ_CHAN]
   are already unrestricted. *)

From clutch.prob_eff_lang.probblaze Require Import advantage.
From clutch.prob_eff_lang.probblaze.typing Require Import types fundamental interp.
From clutch.prob_eff_lang.probblaze Require Import comp_operators sem_types sem_row sem_judgement compatibility syntax semantics proofmode valgroup adequacy mode.
From clutch.prob_eff_lang.probblaze.examples Require Import
  mask sec_channel_def dhke_common dhke_typing dhke_channel_lazy_results
  new_composition_closed new_composition_typing
  chan_ideal_typing uc_composition
  factory_advantage comp_operators_u typing_u
  advantage_dhke_factory advantage_schan_factory uc_composition_factory.
From Stdlib Require Import Reals Psatz.

Import fingroup.
Import fingroup.fingroup.

#[local] Open Scope R_scope.

Section uc_dhke_factory.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{Hpre :probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {msk : @Mask (@vgG vg) vgval}.
  Context {M : ∀ `{probblazeRGS Σ}, Mask_struc}.

  Import valgroup_notation.

  (* The interface of the composed system: [τ] of [new_composition_defs] with
     an unrestricted client arrow. *)
  Definition τ_u `{!probblazeRGS Σ} : sem_ty Σ :=
    (∀ᵣ θ__L ,(∀ᵣ θₕ, ((ℕ -{ θₕ }-> 𝟙) × (𝟙 -{ θₕ }-> (Option 𝔾))) -{ sem_row_union  θₕ θ__L }-∘ 𝟙)
       → (∀ᵣ θ₁,∀ᵣ θ2, (((((𝔾 × (𝟙 + 𝟙))) -{ θ₁ }-> 𝟙) × ((𝟙 + 𝟙) -{ θ₁ }-> Option 𝟙))
           × (((𝔾 × (𝟙 + 𝟙)) -{ θ2 }-> 𝟙) × ((𝟙 + 𝟙) -{ θ2 }-> Option ℕ))) -{ sem_row_union (¡θ₁)%R (sem_row_union (¡θ2)%R θ__L) }-∘ 𝟙))%T.

  Lemma CHAN_SIM_lazy_closed_f : is_closed_expr ∅ CHAN_SIM_lazy.
  Proof using All.
    by destruct (closed_app_inv _ _ (proj1 (closed_app_inv _ _ CHAN_SIM_lazy_F_CHAN_closed))).
  Qed.
  Lemma F_CHAN_closed_f : is_closed_expr ∅ F_CHAN.
  Proof using All. by destruct (closed_app_inv _ _ CHAN_SIM_lazy_F_CHAN_closed). Qed.

  (* π realises F_KE: [adv_DHKE_f], with the simulator associated to the left. *)
  Lemma dhke_realises_f A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A ((𝟙 → τ__Fu aleak gk) → 𝔹)%T) →
    advantage A DHKE_f (λ: <>, (F_AUTH ∘f DH_SIM) ∘f F_KE_lazy_alice)%V #true <=
      advantage (λ: "d", A (λ: <>, F_AUTH ∘f (C_lazy "d")))%V DH_real DH_rand #true.
  Proof using All.
    intros HA.
    eapply (advantage_triangle _ _ DHKE_SIM_f _ _ _ 0).
    - by apply adv_DHKE_f.
    - apply (advantage_zero_f _ _ _ _ (λ _, τ__Fu aleak gk)); [exact HA| |]; intros HRGS.
      + iApply func_comp_assoc_u;
          [apply F_AUTH_closed|apply DH_SIM_closed|apply FKE_closed
          |iApply F_AUTH_typed_u|iApply DH_SIM_typed_u|iApply F_KE_lazy_alice_typed_u].
      + iApply func_comp_assoc_rev_u;
          [apply F_AUTH_closed|apply DH_SIM_closed|apply FKE_closed
          |iApply F_AUTH_typed_u|iApply DH_SIM_typed_u|iApply F_KE_lazy_alice_typed_u].
    - rewrite Rplus_0_r. reflexivity.
  Qed.

  (* ρ realises F_CHAN perfectly: [adv_SCHAN_f]. *)
  Lemma chan_realises_f A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A ((𝟙 → ∀ᵣ θ, hdl cli θ → τ__f θ oaleak leakI) → 𝔹)%T) →
    advantage A (λ: <>, (F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f CHAN)%V (λ: <>, CHAN_SIM_lazy ∘f F_CHAN)%V #true <= 0.
  Proof using All. intros HA. by apply adv_SCHAN_f. Qed.

  (* The composition theorem instantiated. *)
  Theorem adv_composition_uc_f A :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A ((𝟙 → τ_u) → 𝔹)%T) →
    advantage A (λ: <>, ((DHKE_f #()%V) ||ᵣ F_OAUTH) ∘f CHAN)%V
                (λ: <>, ((F_AUTH ∘f DH_SIM) ∘F CHAN_SIM_lazy) ∘f F_CHAN)%V #true <=
      advantage (λ: "d", (λ: "t", A (λ: <>, (("t" #()%V) ||ᵣ F_OAUTH) ∘f CHAN))%V
                           (λ: <>, F_AUTH ∘f (C_lazy "d")))%V DH_real DH_rand #true.
  Proof using All.
    intros HA.
    etrans.
    - apply (uc_composition_factory DHKE_f (F_AUTH ∘f DH_SIM) F_KE_lazy_alice
               CHAN_SIM_lazy F_CHAN F_OAUTH CHAN true
               (λ A', advantage (λ: "d", A' (λ: <>, F_AUTH ∘f (C_lazy "d")))%V DH_real DH_rand #true)
               (λ _, 0)
               (λ _, hdl cli) (λ _, chan) (λ _, gk) (λ _, oaleak) (λ _, leakI) (λ _, aleak) (λ _, fleak)).
      + apply F_AUTH_DH_SIM_closed.
      + apply FKE_closed.
      + apply F_OAUTH_closed.
      + apply CHAN_closed.
      + apply CHAN_SIM_lazy_closed_f.
      + apply F_CHAN_closed_f.
      + intros HRGS. iApply F_AUTH_DH_SIM_typed_u.
      + intros HRGS. iApply F_KE_lazy_alice_typed_u.
      + intros HRGS. iApply F_OAUTH_typed_u.
      + intros HRGS. iApply CHAN_typed_u.
      + intros HRGS. iApply CHAN_SIM_lazy_typed_u.
      + intros HRGS. iApply F_CHAN_typed_u.
      + intros A' HA'. by apply dhke_realises_f.
      + intros A' HA'. by apply chan_realises_f.
      + exact HA.
    - rewrite Rplus_0_r. reflexivity.
  Qed.

End uc_dhke_factory.
