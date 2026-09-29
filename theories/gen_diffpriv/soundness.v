(** Logical relation is sound w.r.t. the contextual refinement
    (generic DP, [gen_prob_lang]).

    Ported from [diffpriv/soundness].  The generic [ctx_refines] is parametric
    in the distribution signature, so [Sg] is threaded explicitly; the
    [≤ctx≤] notation is section-local to [contextual_refinement], hence the
    conclusions are stated with [ctx_refines Sg] directly. *)
From Stdlib Require Export Reals.
From iris.proofmode Require Import proofmode.
From clutch.gen_diffpriv Require Export primitive_laws model adequacy_rel interp fundamental.
From clutch.gen_prob_lang.typing Require Export contextual_refinement.
From clutch.gen_prob_lang Require Import notation metatheory lang.

Lemma refines_sound_open (Sg : Sig) Σ `{!diffprivRGpreS Σ} Γ e e' τ :
  (∀ `{diffprivRGS Sg Σ} Δ, ⊢ 〈⊤;Δ;Γ〉 ⊨ e ≤log≤ e' : τ) →
  ctx_refines Sg Γ e e' τ.
Proof.
  intros Hlog K σ₀ b Htyped.
  rewrite <- Rplus_0_r.
  replace (lim_exec (δ := lang_markov (gen_lang Sg)) (fill_ctx K e', σ₀) #b + 0)%R
    with ((exp 0 * lim_exec (δ := lang_markov (gen_lang Sg)) (fill_ctx K e', σ₀) #b) + 0)%R ; last first.
  { rewrite exp_0. lra. }
  eapply DPcoupl_eq_elim.
  eapply (refines_coupling Sg Σ (λ _, lrel_bool)); eauto; last first.
  - iIntros (?).
    iPoseProof (bin_log_related_under_typed_ctx with "[]") as "H"; [done| |].
    { iIntros "!>" (?). iApply Hlog. }
    iSpecialize ("H" $! [] ∅ with "[]").
    { rewrite fmap_empty. iApply env_ltyped2_empty. }
    rewrite /interp 2!fmap_empty 2!subst_map_empty /=.
    done.
  - by iIntros (???) "[%b' [-> ->]]".
Qed.

Lemma refines_sound (Sg : Sig) Σ `{Hpre : !diffprivRGpreS Σ} (e e': expr) τ :
  (∀ `{diffprivRGS Sg Σ} Δ, ⊢ REL e << e' : (interp τ Δ)) →
  ctx_refines Sg ∅ e e' τ.
Proof.
  intros Hlog. eapply (refines_sound_open Sg Σ).
  iIntros (? Δ vs).
  rewrite fmap_empty env_ltyped2_empty_inv.
  iIntros (->).
  rewrite !fmap_empty !subst_map_empty.
  iApply Hlog.
Qed.
