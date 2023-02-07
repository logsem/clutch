(** Logical relation is sound w.r.t. the contextual refinement. *)
From Coq Require Export Reals.
From self.program_logic Require Import exec.
From iris.proofmode Require Import proofmode.
From self.prob_lang Require Import notation metatheory primitive_laws lang.
From self.logrel Require Import model adequacy.
From self.typing Require Import interp contextual_refinement.

Lemma refines_sound_open Σ `{!prelogrelGpreS Σ} Γ e e' τ :
  (∀ `{prelogrelGS Σ} Δ, ⊢ {⊤;Δ;Γ} ⊨ e ≤log≤ e' : τ) →
  Γ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros Hlog K σ₀ b Htyped.
  cut (∀ n, ((exec_val n (fill_ctx K e, σ₀)) #b <=
             (lim_exec_val (fill_ctx K e', σ₀)) #b)%R).
  { intros Hn. by eapply lim_exec_val_continous. }
  intros n.
  eapply refRcoupl_eq_elim.
  eapply (refines_coupling Σ (λ _, lrel_bool)); last first.
  - iIntros (?).
    iPoseProof (bin_log_related_under_typed_ctx with "[]") as "H"; [done| |].
    { iIntros "!>" (?). iApply Hlog. }
    iSpecialize ("H" $! [] ∅ with "[]").
    { rewrite fmap_empty. iApply env_ltyped2_empty. }
    rewrite /interp 2!fmap_empty 2!subst_map_empty /=.
    done.
  - by iIntros (???) "[%b' [-> ->]]".
Qed.

Lemma refines_sound Σ `{Hpre : !prelogrelGpreS Σ} (e e': expr) τ :
  (∀ `{prelogrelGS Σ} Δ, ⊢ REL e << e' : (interp τ Δ)) →
  ∅ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros Hlog. eapply (refines_sound_open Σ).
  iIntros (? Δ vs).
  rewrite fmap_empty env_ltyped2_empty_inv.
  iIntros (->).
  rewrite !fmap_empty !subst_map_empty.
  iApply Hlog.
Qed.
