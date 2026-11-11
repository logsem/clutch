(* The one-message secure channel over the group mask, as factories.

   The systems are the factories of [sec_channel_def]:
     F_OAUTH        the one-shot authenticated channel (leaks the message)
     CHAN           the protocol: mask the message with the DHKE key, send it
                    over F_OAUTH, in the (F_KE_lazy_alice ||ᵣ F_OAUTH)-hybrid world
     F_CHAN         the ideal secure channel (leaks the length only)
     CHAN_SIM_lazy  the simulator
   and the standalone result, at both modes [m], is perfect:

     advantage A ((F_KE_lazy_alice ||ᵣ F_OAUTH) ∘f CHAN) (CHAN_SIM_lazy ∘f F_CHAN) ≤ 0

   for environments [A : fac m τ_CHAN → 𝔹].  The two relations are
   proved in [sec_channel_prf]. *)

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
From clutch.prob_eff_lang.probblaze.examples Require Import mask sec_channel_def mask_bijection sec_channel_prf.
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_common dhke_typing sec_channel_typing sec_channel_ideal_typing.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import advantage_dhke.
From Stdlib Require Import Reals Psatz.

Import fingroup.
Import fingroup.fingroup.

#[local] Open Scope R_scope.
#[local] Open Scope factory_scope.
#[local] Set Default Proof Using "All".

(* Typing.                                                             *)
(* ------------------------------------------------------------------ *)

Section schan_typing_f.
  Context `{!probblazeRGS Σ}.
  Context {vg : val_group}.
  Context {cg : clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg : @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {msk : @Mask (@vgG vg) vgval}.
  Context `{!Mask_struc}.

End schan_typing_f.

(* ------------------------------------------------------------------ *)
(* The advantage bound: perfect.                                       *)
(* ------------------------------------------------------------------ *)

Section schan_advantage.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.
  Context {msk : @Mask (@vgG vg) vgval}.
  Context {M : ∀ `{probblazeRGS Σ}, Mask_struc}.

  Theorem adv_SCHAN (m : mode) (A : val) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m τ_CHAN → 𝔹)%T) →
    advantage A REAL_SCHAN (SIM_SCHAN ∘f IDEAL_SCHAN) #true <= 0.
  Proof using All.
    intros HA.
    apply (advantage_zero _ _ _ _ (λ H : probblazeRGS Σ, fac m τ_CHAN)); [exact HA| |]; intros HRGS;
      [iApply R_CHAN_SIM_f|iApply SIM_R_CHAN_f].
  Qed.

  (** Syntactically typed environments *)

  (* [τ_CHAN], syntactically. *)
  Definition T_SCHAN : type :=
    (∀R:
      (∀R: ((ℕ -{ RVar 0%nat }-> ()) * (() -{ RVar 0%nat }-> (() + τG)))
             -{ RVar 0%nat ∪ᵣ RVar 1%nat }-∘ ()) ⇾
      (∀R: ∀R: ((((τG * (() + ())) -{ RVar 1%nat }-> ()) * ((() + ()) -{ RVar 1%nat }-> (() + ())))
                 * (((() + ()) -{ RVar 0%nat }-> ()) * ((() + ()) -{ RVar 0%nat }-> (() + ()))))
             -{ (RFlip OS (RVar 1%nat)) ∪ᵣ ((RFlip OS (RVar 0%nat)) ∪ᵣ RVar 2%nat) }-∘ ()))%ty.

  Lemma T_SCHAN_subtype `{!probblazeRGS Σ} η μ δ ξ :
    ⊢ τ_CHAN ≤ₜ interp.interp._ty η μ δ T_SCHAN ξ.
  Proof using All.
    rewrite /T_SCHAN /τ_CHAN /sem_ty_option /=.
    iApply ty_le_row_forall; iIntros (θL).
    iApply ty_le_mbang_comp; first iApply mode_le_refl.
    iApply ty_le_arr; first iApply row_le_refl.
    - (* the client: its receive returns a group element *)
      iApply ty_le_row_forall; iIntros (θh).
      iApply ty_le_arr; [iApply row_le_refl | | iApply ty_le_refl].
      iApply ty_le_prod; first iApply ty_le_refl.
      iApply ty_le_mbang_comp; first iApply mode_le_refl.
      iApply ty_le_arr; [iApply row_le_refl|iApply ty_le_refl|].
      iApply ty_le_sum; first iApply ty_le_refl.
      iIntros (??) "!#". iApply τG_subtype.
    - (* the leaks: the network's leak takes a group element *)
      iApply ty_le_row_forall; iIntros (θ1). iApply ty_le_row_forall; iIntros (θ2).
      iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
      iApply ty_le_prod; last iApply ty_le_refl.
      iApply ty_le_prod; last iApply ty_le_refl.
      iApply ty_le_mbang_comp; first iApply mode_le_refl.
      iApply ty_le_arr; [iApply row_le_refl| |iApply ty_le_refl].
      iApply ty_le_prod; last iApply ty_le_refl.
      iIntros (??) "!#". iApply τG_subtype.
  Qed.

  Corollary adv_SCHAN_typed A :
    ⊢ᵥ A : ((() -∘ T_SCHAN) ⇾ TBool)%ty →
    advantage A REAL_SCHAN (SIM_SCHAN ∘f IDEAL_SCHAN) #true <= 0.
  Proof using All.
    intros HA. apply (adv_SCHAN OS), (typed_env_fac A T_SCHAN (λ _, τ_CHAN)); last done.
    intros. apply T_SCHAN_subtype.
  Qed.

End schan_advantage.
