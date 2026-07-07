From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import
  logic primitive_laws proofmode
  spec_rules spec_ra class_instances tactics notation valgroup metatheory
  sem_types sem_row sem_sig sem_judgement sem_def
  def_dhke sec_channel_def xor sec_channel_prf dhke_channel_lazy_results dhke_channel_lazy_authchan.
From clutch.prob_eff_lang.probblaze.typing Require Import fundamental.

Import fingroup.
Import fingroup.fingroup.

Import valgroup_tactics.

(* Syntactic closedness of the composite programs.  These [is_closed]
   proofs are slow, so they live in their own file. *)

Section new_comp_verification.
  Context `{probblazeRGS Σ}.
  Context (channel leaksec channel1 channel2 getKey1 getKey2 leakauth1 leakauth2 keyleak1 keyleak2 schannel1 schannel2 l1 l2 l2': label).
  Context {vg: val_group}.
  Context {cg: clutch_group_struct}.
  Context {G : clutch_group (vg:=vg) (cg:=cg)}.
  Context {vgg: @val_group_generator vg}.
  Context `{!inG Σ (exclR unitO), !inG Σ dfracO,!inG Σ (dfrac_agreeR valO)}.
  Let Key := S (S n'').
  Let Support := S (S n'').
  Variable xor_struct : XOR (Key := Key) (Support := Support).
  Context `{!XOR_spec (Key := Key) (Support := Support) (H := xor_struct)}.

  (* [is_closed] discharges its leaves with [auto]; make the XOR operation's
     closedness (a field of the [XOR] class) available to it. *)
  #[local] Hint Resolve xor_closed : core.

  Lemma F_AUTH_DHKE_closed : is_closed_expr ∅ ((λ: "f", F_AUTH (DH_KE "f"))%V ||ᵣ F_OAUTH).
  Proof. is_closed. Qed.
  Lemma F_AUTH_C_DDH_real_closed : is_closed_expr ∅ ( (λ: "f", F_AUTH (C_lazy DH_real "f"))%V ||ᵣ F_OAUTH).
  Proof. is_closed. Qed.
  Lemma F_AUTH_C_DDH_rand_closed : is_closed_expr ∅ ((λ: "f", F_AUTH (C_lazy DH_rand "f"))%V ||ᵣ F_OAUTH).
  Proof. is_closed. Qed.

  Lemma DHSIM_FKE_CHAN1_closed : is_closed_expr ∅ ((λ: "f", F_AUTH (DH_SIM (F_KE_lazy_alice "f")))%V ||ᵣ F_OAUTH).
  Proof. is_closed. Qed.

  Lemma DHSIM_FKE_CHAN2_closed : is_closed_expr ∅ ((λ: "f", (λ: "f", F_AUTH (DH_SIM "f"))%V (F_KE_lazy_alice "f"))%V ||ᵣ F_OAUTH).
  Proof. is_closed. Qed.

  Lemma DHSIM_FKE_CHAN3_closed : is_closed_expr ∅ ((F_AUTH ∘f DH_SIM) ∘F (F_KE_lazy_alice ||ᵣ F_OAUTH)%V)%V.
  Proof. is_closed. Qed.

  Lemma F_AUTH_DH_SIM_closed : is_closed_expr ∅ (F_AUTH ∘f DH_SIM).
  Proof. is_closed. Qed.

  Lemma F_KE_lazy_alice_F_OAUTH_closed : is_closed_expr ∅ (F_KE_lazy_alice ||ᵣ F_OAUTH).
  Proof. is_closed. Qed.

  Lemma R_CHAN_closed : is_closed_expr ∅ (R_CHAN xor_struct).
  Proof. is_closed. Qed.

  Lemma CHAN_SIM_lazy_F_CHAN_closed : is_closed_expr ∅ (CHAN_SIM_lazy ∘f F_CHAN).
  Proof. is_closed. Qed.

End new_comp_verification.
