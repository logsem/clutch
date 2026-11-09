(* DHKE composed with the one-message secure channel over the group mask:
   the UC composition theorem [uc_composition] applied to the two standalone
   results

     dhke_realises   REAL_DHKE  ≤_{ε_DDH} SIM_DHKE  ∘f IDEAL_DHKE   (DH_KE/dhke_factory)
     adv_SCHAN       REAL_SCHAN ≤_{0}     SIM_SCHAN ∘f IDEAL_SCHAN  (secure_channel/advantage_sec_channel)

   The composed real system runs the channel protocol [CHAN] in the hybrid
   world where the key exchange is the DHKE protocol [REAL_DHKE] and the
   authenticated channel is [F_OAUTH]; the composed simulator is the DHKE
   simulator plugged into the channel simulator; the ideal functionality is
   the ideal secure channel; the reduction is the DHKE reduction, applied to
   the environment closed under the channel. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze.typing Require Import types.
From clutch.prob_eff_lang.probblaze.typing Require interp.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory mode adequacy.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems uc_advantage uc_theorem.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_typed.
From clutch.prob_eff_lang.probblaze.examples Require Import mask sec_channel_def mask_bijection sec_channel_prf advantage_sec_channel.
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_common dhke_typing sec_channel_typing sec_channel_ideal_typing.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def advantage_dhke.
From Stdlib Require Import Reals Psatz.

Import fingroup.
Import fingroup.fingroup.

#[local] Open Scope R_scope.
#[local] Open Scope factory_scope.
#[local] Set Default Proof Using "All".

(* ------------------------------------------------------------------ *)
(* The systems.                                                        *)
(* ------------------------------------------------------------------ *)

Section dhke_chan_systems.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {msk : @Mask (@vgG vg) vgval}.

  (* The real system: the channel protocol in the (REAL_DHKE, F_OAUTH)-hybrid world. *)
  Definition REAL_DHKE_CHAN : val := ((REAL_DHKE ||ᵣ F_OAUTH) ∘f CHAN)%fac.
  (* The ideal functionality: the ideal secure channel. *)
  Definition IDEAL_DHKE_CHAN : val := IDEAL_SCHAN.
  (* The simulator: the DHKE simulator plugged into the channel simulator. *)
  Definition SIM_DHKE_CHAN : val := (SIM_DHKE ∘F SIM_SCHAN)%fac.
  (* The DDH reduction for an environment [A]: the DHKE reduction for the
     environment that runs [A] against the channel protocol. *)
  Definition RED_DHKE_CHAN (A : val) : val :=
    RED_DHKE (λ: "v", A (("v" ||ᵣₚ F_OAUTH) ∘fₚ CHAN))%V.

End dhke_chan_systems.

(* ------------------------------------------------------------------ *)
(* Typing.                                                             *)
(* ------------------------------------------------------------------ *)

Section dhke_chan_typing.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {msk : @Mask (@vgG vg) vgval}.
  Context `{!Mask_struc}.

  (* The interface of the composed system: a channel client, over the
     authenticated-channel leakage and the DHKE leakage. *)
  Definition τ_DHKE_CHAN : sem_ty Σ := (∀ᵣ θ, hdl cli θ ⊸ τ__f θ oaleak aleak)%T.

  Lemma REAL_DHKE_CHAN_typed_f m : ⊢ ⊨ᵥ REAL_DHKE_CHAN ≤ REAL_DHKE_CHAN : fac m τ_DHKE_CHAN.
  Proof using All.
    iApply func_comp_f_typed_gen; [intros θ; apply eta_ty_τf| |iApply CHAN_typed].
    iApply parallel_comp_f_typed; [|iApply F_OAUTH_typed].
    iApply func_comp_f_typed; [iApply F_AUTH_typed|iApply DH_KE_typed].
  Qed.

  Lemma SIM_DHKE_CHAN_IDEAL_typed_f m :
    ⊢ ⊨ᵥ (SIM_DHKE_CHAN ∘f IDEAL_DHKE_CHAN) ≤ (SIM_DHKE_CHAN ∘f IDEAL_DHKE_CHAN) : fac m τ_DHKE_CHAN.
  Proof using All.
    rewrite /τ_DHKE_CHAN.
    iApply (func_comp_f_typed_gen m _ _ _ _ (λ θ, hdl cli θ)
              (λ θ, ∀ᵣ θJ, fleak θJ -{ sem_row_union (¡θJ) θ }-∘ 𝟙)%T (λ θ, τ__f θ oaleak aleak)).
    { intros θ. apply eta_ty_row_forall => θJ. apply eta_ty_arr. }
    { iApply functionality_comp_f_typed; [iApply SIM_DHKE_typed_f|iApply CHAN_SIM_lazy_typed]. }
    iApply F_CHAN_typed.
  Qed.

End dhke_chan_typing.

(* ------------------------------------------------------------------ *)
(* The advantage bound, by UC composition.                             *)
(* ------------------------------------------------------------------ *)

Section dhke_chan_advantage.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {msk : @Mask (@vgG vg) vgval}.
  Context {M : ∀ `{probblazeRGS Σ}, Mask_struc}.

  Theorem dhke_chan_realises (m : mode) (A : val) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m τ_DHKE_CHAN → 𝔹)%T) →
    advantage A REAL_DHKE_CHAN (SIM_DHKE_CHAN ∘f IDEAL_DHKE_CHAN) #true <=
      advantage (RED_DHKE_CHAN A) DH_real DH_rand #true.
  Proof using All.
    intros HA.
    rewrite /REAL_DHKE_CHAN /SIM_DHKE_CHAN /IDEAL_DHKE_CHAN /RED_DHKE_CHAN /SIM_SCHAN /IDEAL_SCHAN.
    etrans.
    - apply (uc_composition m REAL_DHKE SIM_DHKE IDEAL_DHKE F_OAUTH CHAN CHAN_SIM_lazy F_CHAN true
               (λ A', advantage (RED_DHKE A') DH_real DH_rand #true) (λ _, 0)
               (λ H : probblazeRGS Σ, hdl cli) (λ H : probblazeRGS Σ, chan)
               (λ H : probblazeRGS Σ, gk) (λ H : probblazeRGS Σ, oaleak)
               (λ H : probblazeRGS Σ, leakI) (λ H : probblazeRGS Σ, aleak)
               (λ H : probblazeRGS Σ, fleak)).
      + intros HRGS. iApply SIM_DHKE_typed_f.
      + intros HRGS. iApply F_KE_lazy_alice_typed.
      + intros HRGS. iApply F_OAUTH_typed.
      + intros HRGS. iApply CHAN_typed.
      + intros HRGS. iApply CHAN_SIM_lazy_typed.
      + intros HRGS. iApply F_CHAN_typed.
      + intros A' HA'. by apply (dhke_realises m).
      + intros A' HA'. by apply (adv_SCHAN m).
      + exact HA.
    - rewrite Rplus_0_r. reflexivity.
  Qed.

  (** Syntactically typed environments *)

  (* [τ_DHKE_CHAN], syntactically. *)
  Definition T_DHKE_CHAN : type :=
    (∀R:
      (∀R: ((ℕ -{ RVar 0%nat }-> ()) * (() -{ RVar 0%nat }-> (() + τG)))
             -{ RVar 0%nat ∪ᵣ RVar 1%nat }-∘ ()) -∘
      (∀R: ∀R: ((((τG * (() + ())) -{ RVar 1%nat }-> ()) * ((() + ()) -{ RVar 1%nat }-> (() + ())))
                 * (((τG * (() + ())) -{ RVar 0%nat }-> ()) * ((() + ()) -{ RVar 0%nat }-> (() + ℕ))))
             -{ (RFlip OS (RVar 1%nat)) ∪ᵣ ((RFlip OS (RVar 0%nat)) ∪ᵣ RVar 2%nat) }-∘ ()))%ty.

  Lemma T_DHKE_CHAN_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ τ_DHKE_CHAN ≤ₜ interp.interp._ty η μ δ T_DHKE_CHAN ξ.
  Proof using All.
    rewrite /T_DHKE_CHAN /τ_DHKE_CHAN /hdl /cli /τ__f /oaleak /aleak /sem_ty_option /=.
    iApply ty_le_row_forall; iIntros (θL).
    iApply ty_le_arr; first iApply row_le_refl.
    - (* the client: its receive returns a group element *)
      iApply ty_le_row_forall; iIntros (θh).
      iApply ty_le_arr; [iApply row_le_refl | | iApply ty_le_refl].
      iApply ty_le_prod; first iApply ty_le_refl.
      iApply ty_le_mbang_comp; first iApply mode_le_refl.
      iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|].
      iApply ty_le_sum; first iApply ty_le_refl.
      iIntros (??) "!#". iApply τG_subtype.
    - (* the leaks of the channel and of the key exchange take group elements *)
      iApply ty_le_row_forall; iIntros (θ1). iApply ty_le_row_forall; iIntros (θ2).
      iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
      iApply ty_le_prod; (iApply ty_le_prod; last iApply ty_le_refl);
        (iApply ty_le_mbang_comp; first iApply mode_le_refl);
        (iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl]);
        (iApply ty_le_prod; last iApply ty_le_refl);
        iIntros (??) "!#"; iApply τG_subtype.
  Qed.

  Corollary dhke_chan_realises_typed A :
    ⊢ᵥ A : ((() -∘ T_DHKE_CHAN) ⇾ TBool)%ty →
    advantage A REAL_DHKE_CHAN (SIM_DHKE_CHAN ∘f IDEAL_DHKE_CHAN) #true <=
      advantage (RED_DHKE_CHAN A) DH_real DH_rand #true.
  Proof using All.
    intros HA. apply (dhke_chan_realises OS), (typed_env_fac A T_DHKE_CHAN (λ _, τ_DHKE_CHAN)); last done.
    intros. apply T_DHKE_CHAN_subtype.
  Qed.

End dhke_chan_advantage.
