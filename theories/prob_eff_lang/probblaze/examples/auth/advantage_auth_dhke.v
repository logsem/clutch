(* DHKE over the authenticated-channel protocol [AUTH], as an instance of the
   UC composition theorem [uc_composition_f]:

     π = AUTH    over the raw network, with simulator S_AUTH, realising
                 F_AUTH (hypothesis [auth_realises], up to 2/q);
     ρ = DH_KE   in the F_AUTH-hybrid world, with simulator SIM_DHKE, realising
                 IDEAL_DHKE (computationally, via DDH: [dhke_realises]).

   The composed protocol is AUTH ∘f DH_KE: the key exchange over the
   authenticated channel, itself realised over the raw network with the
   preshared MAC keys. *)

From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory mode adequacy.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage comp_operators.
From clutch.prob_eff_lang.probblaze.uc Require Import uc_systems uc_advantage uc_theorem.
From clutch.prob_eff_lang.probblaze.examples Require Import dhke_common dhke_typing.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def advantage_dhke.
From clutch.prob_eff_lang.probblaze.examples.auth Require Import auth_def auth_typing.
From Stdlib Require Import Reals Psatz.

Import fingroup.
Import fingroup.fingroup.

#[local] Open Scope R_scope.
#[local] Open Scope factory_scope.
#[local] Set Default Proof Using "All".

(* ------------------------------------------------------------------ *)
(* The systems.                                                        *)
(* ------------------------------------------------------------------ *)

Section auth_dhke_systems.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.

  (* The real system: the key exchange over the AUTH protocol, over the raw network. *)
  Definition REAL_AUTH_DHKE : val := (AUTH ∘f DH_KE)%fac.
  (* The ideal functionality: that of the key exchange. *)
  Definition IDEAL_AUTH_DHKE : val := IDEAL_DHKE.
  (* The simulator: the AUTH simulator on top of the DHKE simulator. *)
  Definition SIM_AUTH_DHKE : val := (S_AUTH ∘f SIM_DHKE)%fac.
  (* The DDH reduction for an environment [A]: the DHKE reduction for the
     environment that runs [A] behind the AUTH simulator. *)
  Definition RED_AUTH_DHKE (A : val) : val := RED_DHKE (λ: "v", A (S_AUTH ∘fₚ "v"))%V.

End auth_dhke_systems.

(* ------------------------------------------------------------------ *)
(* The advantage bound, by UC composition.                             *)
(* ------------------------------------------------------------------ *)

Section auth_dhke.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO, !inG Σ (dfrac_agreeR valO)}.

  Import valgroup_notation.
  #[local] Notation n := (S n'').

  (* π = AUTH realises F_AUTH over the raw network with simulator S_AUTH, up
     to the probability 2/q of forging one of the two one-time MACs.  (To be
     proved separately.) *)
  Hypothesis auth_realises : ∀ (m : mode) (A : val),
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m (τ__F raw chan) → 𝔹)%T) →
    advantage A AUTH (S_AUTH ∘f F_AUTH) #true <= 2 / n.

  Theorem auth_dhke (m : mode) (A : val) :
    (∀ `{!probblazeRGS Σ}, ⊢ sem_val_typed A A (fac m (τ__F raw gk) → 𝔹)%T) →
    advantage A REAL_AUTH_DHKE (SIM_AUTH_DHKE ∘f IDEAL_AUTH_DHKE) #true
      <= 2 / n + advantage (RED_AUTH_DHKE A) DH_real DH_rand #true.
  Proof using All.
    intros HA. rewrite /REAL_AUTH_DHKE /SIM_AUTH_DHKE /IDEAL_AUTH_DHKE /RED_AUTH_DHKE.
    apply (uc_composition_f m AUTH S_AUTH F_AUTH SIM_DHKE IDEAL_DHKE DH_KE true
             (λ _, 2 / n) (λ A', advantage (RED_DHKE A') DH_real DH_rand #true)
             (λ H : probblazeRGS Σ, gk) (λ H : probblazeRGS Σ, chan) (λ H : probblazeRGS Σ, aleak)
             (λ H : probblazeRGS Σ, raw) (λ H : probblazeRGS Σ, leakI)).
    + intros HRGS. iApply S_AUTH_typed.
    + intros HRGS. iApply F_AUTH_typed.
    + intros HRGS. iApply DH_KE_typed.
    + intros HRGS. iApply SIM_DHKE_typed_f.
    + intros HRGS. iApply F_KE_lazy_alice_typed.
    + intros A' HA'. by apply (auth_realises m).
    + intros A' HA'. by apply (dhke_realises m).
    + exact HA.
  Qed.

End auth_dhke.
