(* The secure channel over Diffie-Hellman key exchange: an instance of the
   composition theorem (uc_eff/DESIGN.md).

     - DH_KE on F_AUTH realises F_KE with the simulator S_DHKE
       ([dhke_security]);
     - CHAN on F_KE and F_OAUTH realises F_CHAN with the simulator S_CHAN
       ([chan_security]).

   Hence CHAN on the real key exchange (and F_OAUTH) realises F_CHAN, with
   the composed simulator and the advantage of the DDH reduction.  The
   authenticated channel F_OAUTH is beside the key exchange throughout:
   the first statement is put beside it with the tensor, whose simulator is
   [S_DHKE ⊗ id_mod]. *)

From iris.proofmode Require Import base proofmode classes.
From clutch.prob_eff_lang.probblaze Require Import primitive_laws proofmode.
From clutch.prob_eff_lang.probblaze Require Import spec_rules spec_ra class_instances tactics.
From clutch.prob_eff_lang.probblaze Require Import notation metatheory semantics logic adequacy mode.
From clutch.prob_eff_lang.probblaze Require Import sem_def sem_types sem_row sem_sig sem_env sem_judgement compatibility.
From clutch.prob_eff_lang.probblaze.uc Require Import advantage uc_advantage.
From clutch.prob_eff_lang.probblaze.examples.dhke Require Import dhke_def.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import modules auth auth_typing dhke dhke_typing dhke_proof.
From clutch.prob_eff_lang.probblaze.uc_eff Require Import channel channel_typing channel_proof.
From Stdlib Require Import Reals Psatz.

Import fingroup.
Import valgroup_notation.

#[local] Open Scope R_scope.
#[local] Set Default Proof Using "All".

Section channel_dhke.
  Context {vg : val_group} {cg : clutch_group_struct} {vgg : @val_group_generator vg}.
  Context `{Hpre : probblazeRGpreS Σ}.
  Context {G : ∀ `{!probblazeRGS Σ}, clutch_group}.
  #[local] Open Scope mod_scope.

  (* Key exchange beside the authenticated channel: the real modules
     realise the ideal ones with the simulator [S_DHKE ⊗ id_mod].  The
     environment of the key exchange is the given one extended by the
     channel; moving the simulator out of the tensor is the interchange
     law. *)
  Lemma dhke_beside_oauth (A : val) :
    (∀ `{probblazeRGS Σ},
       ⊢ sem_val_typed A A (Mod (IProd Net ONet) (IProd Keys OEp) → 𝔹)%T) →
    advantage A (REAL_DHKE ⊗ F_OAUTH) ((F_KE ⊗ F_OAUTH) ⊳ (S_DHKE ⊗ id_mod)) #true
      <= advantage (RED_DHKE (λ: "v", A (tens_app "v" F_OAUTH))%V) DH_real DH_rand #true.
  Proof.
    intros HA.
    apply (advantage_triangle _ _ (IDEAL_DHKE ⊗ F_OAUTH) _ _
             (advantage (RED_DHKE (λ: "v", A (tens_app "v" F_OAUTH))%V) DH_real DH_rand #true) 0); [| |lra].
    - etrans; first apply (advantage_pure_l_rev _ [] (tens_app REAL_DHKE F_OAUTH) _ _);
        [done|apply tens_app_pure|].
      etrans; first apply (advantage_pure_r_rev _ [] _ (tens_app IDEAL_DHKE F_OAUTH) _);
        [done|apply tens_app_pure|].
      etrans; first apply (advantage_reduction_ctx A [AppLCtx F_OAUTH; AppRCtx tens_app]).
      { done. }
      { intros vs w Hw. simpl. by rewrite Hw. }
      apply dhke_security. intros HRGS.
      iApply env_beside_typed; [iApply HA|iApply F_OAUTH_typed].
    - rewrite /IDEAL_DHKE.
      apply (advantage_zero _ _ _ _
               (λ H : probblazeRGS Σ, Mod (IProd Net ONet) (IProd Keys OEp)));
        [exact HA| |]; intros HRGS; iApply sem_typed_val.
      + iApply tens_interchange; [iApply F_KE_typed|iApply S_DHKE_typed|iApply F_OAUTH_typed].
      + iApply tens_interchange_rev; [iApply F_KE_typed|iApply S_DHKE_typed|iApply F_OAUTH_typed].
  Qed.

  (* The secure channel over Diffie-Hellman key exchange. *)
  Theorem chan_dhke_security (A : val) :
    (∀ `{probblazeRGS Σ}, ⊢ sem_val_typed A A (Mod (IProd Net ONet) SChan → 𝔹)%T) →
    advantage A (CHAN ⊳ (REAL_DHKE ⊗ F_OAUTH)) (F_CHAN ⊳ (S_CHAN ⊳ (S_DHKE ⊗ id_mod))) #true
      <= advantage
           (RED_DHKE (λ: "v", (λ: "v", A (comp_app CHAN "v"))%V (tens_app "v" F_OAUTH))%V)
           DH_real DH_rand #true.
  Proof.
    intros HA.
    etrans; first apply (uc_composition MS
      (REAL_DHKE ⊗ F_OAUTH) (S_DHKE ⊗ id_mod) (F_KE ⊗ F_OAUTH) CHAN S_CHAN F_CHAN true
      (λ A, advantage (RED_DHKE (λ: "v", A (tens_app "v" F_OAUTH))%V) DH_real DH_rand #true) (λ _, 0)
      (λ _, IProd Net ONet) (λ _, IProd Ctl ONet) (λ _, CAdv) (λ _, IProd Keys OEp) (λ _, SChan)).
    - intros HRGS. iApply tens_op_typed; [iApply S_DHKE_typed|iApply id_mod_typed].
    - intros HRGS. iApply tens_op_typed; [iApply F_KE_typed|iApply F_OAUTH_typed].
    - intros HRGS. iApply CHAN_typed.
    - intros HRGS. iApply S_CHAN_typed.
    - intros HRGS. iApply F_CHAN_typed.
    - apply dhke_beside_oauth.
    - apply chan_security.
    - exact HA.
    - simpl. lra.
  Qed.

End channel_dhke.
