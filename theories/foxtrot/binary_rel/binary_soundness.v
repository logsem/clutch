(** Logical relation is sound w.r.t. the contextual refinement. *)
From Stdlib Require Export Reals.
From iris.proofmode Require Import proofmode.
From Coquelicot Require Import Rbar Lub.
From clutch.con_prob_lang Require Import notation metatheory lang lub_termination.
From clutch.foxtrot Require Export primitive_laws.
From clutch.foxtrot.binary_rel Require Import binary_model binary_adequacy_rel binary_interp binary_fundamental.
From clutch.con_prob_lang.typing Require Export contextual_refinement.

Lemma refines_sound_open Σ `{!foxtrotRGpreS Σ} Γ e e' τ :
  (∀ `{foxtrotRGS Σ} Δ, ⊢ 〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ) →
  Γ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros Hlog K σ₀ b Htyped.
  rewrite <-rbar_le_rle.
  rewrite <- Rbar_plus_0_r.
  rewrite !lub_termination_prob_eq.
  eapply (foxtrot_rel_adequacy' Σ (λ _, interp b []) (λ _ _, True)); try done; eauto.
  iIntros (?).
  iPoseProof (bin_log_related_under_typed_ctx with "[]") as "H"; [done| |].
  { iIntros "!>" (?). iApply Hlog. }
  iSpecialize ("H" $! [] ∅ with "[]").
  { rewrite fmap_empty. iApply env_ltyped2_empty. }
  rewrite 2!fmap_empty 2!subst_map_empty /=.
  by iIntros. 
Qed.

Lemma refines_sound Σ `{Hpre : !foxtrotRGpreS Σ} (e e': expr) τ :
  (∀ `{foxtrotRGS Σ} Δ, ⊢ REL e << e' : (interp τ Δ)) →
  ∅ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros Hlog. eapply (refines_sound_open Σ).
  iIntros (? Δ vs).
  rewrite fmap_empty env_ltyped2_empty_inv.
  iIntros (->).
  rewrite !fmap_empty !subst_map_empty.
  iApply Hlog.
Qed.

