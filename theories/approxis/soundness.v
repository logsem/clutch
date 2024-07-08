(** Logical relation is sound w.r.t. the contextual refinement. *)
From Coq Require Export Reals.
From iris.proofmode Require Import proofmode.
From clutch.prob_lang Require Import notation metatheory lang.
From clutch.approxis Require Export primitive_laws model adequacy_rel interp fundamental.
From clutch.prob_lang.typing Require Export contextual_refinement.


Lemma refines_sound_open Σ `{!approxisRGpreS Σ} Γ e e' τ :
  (∀ `{approxisRGS Σ} Δ, ⊢ 〈⊤;Δ;Γ〉 ⊨ e ≤log≤ e' : τ) →
  Γ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros Hlog K σ₀ b Htyped.
  rewrite <- Rplus_0_r.
  eapply ARcoupl_eq_elim.
  eapply (refines_coupling Σ (λ _, lrel_bool)); eauto; last first.
  - iIntros (?).
    iPoseProof (bin_log_related_under_typed_ctx with "[]") as "H"; [done| |].
    { iIntros "!>" (?). iApply Hlog. }
    iSpecialize ("H" $! [] ∅ with "[]").
    { rewrite fmap_empty. iApply env_ltyped2_empty. }
    rewrite /interp 2!fmap_empty 2!subst_map_empty /=.
    done.
  - by iIntros (???) "[%b' [-> ->]]".
Qed.

Lemma refines_sound Σ `{Hpre : !approxisRGpreS Σ} (e e': expr) τ :
  (∀ `{approxisRGS Σ} Δ, ⊢ REL e << e' : (interp τ Δ)) →
  ∅ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros Hlog. eapply (refines_sound_open Σ).
  iIntros (? Δ vs).
  rewrite fmap_empty env_ltyped2_empty_inv.
  iIntros (->).
  rewrite !fmap_empty !subst_map_empty.
  iApply Hlog.
Qed.
