(** Logical relation is sound w.r.t. the contextual refinement. *)
From Coq Require Export Reals.
From clutch.program_logic Require Import exec.
From iris.proofmode Require Import proofmode.
From clutch.prob_lang Require Import notation metatheory lang.
From clutch.rel_logic Require Export primitive_laws model adequacy_rel.
From clutch.typing Require Export interp contextual_refinement.

Lemma refines_sound_open Σ `{!clutchRGpreS Σ} Γ e e' τ :
  (∀ `{clutchRGS Σ} Δ, ⊢ 〈⊤;Δ;Γ〉 ⊨ e ≤log≤ e' : τ) →
  Γ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros Hlog K σ₀ b Htyped.
  cut (∀ n, ((exec_val n (fill_ctx K e, σ₀)) (LitV (LitBool b)) <=
             (lim_exec_val (fill_ctx K e', σ₀)) (LitV (LitBool b)))%R).
  { intros Hn.
    by eapply lim_exec_val_continous.
  }
  intros n.
  eapply refRcoupl_eq_elim.
  eapply (refines_coupling Σ (λ _, lrel_bool)); auto; last first.
  - iIntros (?).
    iPoseProof (bin_log_related_under_typed_ctx with "[]") as "H"; [done| |].
    { iIntros "!>" (?). iApply Hlog. }
    iSpecialize ("H" $! [] ∅ with "[]").
    { rewrite fmap_empty. iApply env_ltyped2_empty. }
    rewrite /interp 2!fmap_empty 2!subst_map_empty /=.
    done.
  - by iIntros (???) "[%b' [-> ->]]".
Qed.

Lemma refines_sound Σ `{Hpre : !clutchRGpreS Σ} (e e': expr) τ :
  (∀ `{clutchRGS Σ} Δ, ⊢ REL e << e' : (interp τ Δ)) →
  ∅ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros Hlog. eapply (refines_sound_open Σ).
  iIntros (? Δ vs).
  rewrite fmap_empty env_ltyped2_empty_inv.
  iIntros (->).
  rewrite !fmap_empty !subst_map_empty.
  iApply Hlog.
Qed.
