From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language ectx_language.
From clutch.eris Require Export weakestpre total_weakestpre complete_pre.
From clutch.prob Require Import distribution.
From clutch.base_logic Require Import error_credits.
From clutch.eris.complete Require Export exec_probs lang_completeness.


Local Open Scope R.

Class eris_ectx_lang_completeness_gen (Λ : ectxLanguage) (Σ : gFunctors) `{!erisWpGS Λ Σ} `{ecGS Σ} := ErisEctxCompleteness {
  heap_inv : Λ.(state) → iProp Σ;
  (* heap_inv_timeless :> ∀ σ, Timeless (heap_inv σ); *)

  na : Λ.(expr) → Prop;
  na_step : ∀ e σ e' σ', na e → prim_step e σ (e', σ') > 0 → na e';
  na_fill_inv : ∀ e K, na (fill K e) → na e; 

  err : (Λ.(val) → iProp Σ) → cfg Λ → R;
  err_ge0 : ∀ φ ρ, 0 <= err φ ρ;
  err_le1 : ∀ φ ρ, err φ ρ <= 1;
  err_exp : ∀ φ ρ, err φ ρ = Expval (step ρ) (err φ);
  err_stuck : ∀ φ ρ, stuck ρ → err φ ρ = 1;
  err_fin : ∀ φ (v : Λ.(val)) σ,
    err φ (of_val v, σ) < 1 →
      heap_inv σ -∗ φ v;
  err_fill : ∀ K e σ φ , 
    err (λ v : val Λ, WP fill K (of_val v) {{ v0, φ v0 }})%I (e, σ) = err φ (fill K e, σ) ;

  eris_ectx_lang_completeness :
    ∀ e1 σ E,
      na e1 →
      head_reducible e1 σ →
      heap_inv σ ={E}=∗
      ((* (∃ K e1', ⌜LanguageCtx K⌝ ∗ ⌜e1 = K e1'⌝ ∗ ⌜to_val e1' = None⌝ ∗ ⌜Atomic StronglyAtomic e1'⌝ ∗
        ∀ Ψ, ((▷ ∀ v2 σ',
          ⌜prim_step e1' σ (of_val v2, σ') > 0⌝ -∗
          heap_inv σ' ==∗
          (heap_inv σ' ∗ (heap_inv σ' -∗ Ψ v2))) -∗
          ↯ (err Ψ (e1', σ)) -∗
          WP e1' @ E {{ v, Ψ v }})) ∨ *)
      (heap_inv σ ∗ ∀ Ψ, ((▷ |={⊤,E}=> ∃ σ1, heap_inv σ1 ∗
        ∀ e2 σ1',
          ⌜prim_step e1 σ1 (e2, σ1') > 0⌝ -∗
          heap_inv σ1' ={E,⊤}=∗
          ↯ (err Ψ (e2, σ1')) -∗ WP e2 @ ⊤ {{ v, Ψ v }}) -∗
          ↯ (err Ψ (e1, σ)) -∗ WP e1 @ ⊤ {{ v, Ψ v }})) )
}.

Section completeness.
  Context `{eris_ectx_lang_completeness_gen Λ Σ}.

  Lemma pgl_wp_ectx_to_prim_completeness e1 σ E : 
    na e1 →
    reducible (e1, σ) →
    heap_inv σ ={E}=∗
    ((* (∃ K e1', ⌜LanguageCtx K⌝ ∗ ⌜e1 = K e1'⌝ ∗ ⌜to_val e1' = None⌝ ∗ ⌜Atomic StronglyAtomic e1'⌝ ∗
    ∀ Ψ, ((▷ ∀ v2 σ',
        ⌜prim_step e1' σ (of_val v2, σ') > 0⌝ -∗
        heap_inv σ' ==∗
        (heap_inv σ' ∗ (heap_inv σ' -∗ Ψ v2))) -∗
        ↯ (err Ψ (e1', σ)) -∗
        WP e1' @ E {{ v, Ψ v }})) ∨ *)
    (heap_inv σ ∗ ∀ Ψ, ((▷ |={⊤,E}=> ∃ σ1, heap_inv σ1 ∗
    ∀ e2 σ1',
        ⌜prim_step e1 σ1 (e2, σ1') > 0⌝ -∗
        heap_inv σ1' ={E,⊤}=∗
        ↯ (err Ψ (e2, σ1')) -∗ WP e2 @ ⊤ {{ v, Ψ v }}) -∗
        ↯ (err Ψ (e1, σ)) -∗ WP e1 @ ⊤ {{ v, Ψ v }})) ).
  Proof.
    iIntros (Hna ((e'&σ')&Hstep)) "Hheap".
    rewrite //= prim_step_iff in Hstep. 
    destruct Hstep as (K & e1' & e2' & <- & <- & Hstep).
    iMod (eris_ectx_lang_completeness e1' σ with "Hheap") as "(Hheap & HH)";
    [by eapply na_fill_inv | by econstructor |].
    iModIntro. iFrame.
    iIntros (Ψ) "Hc Herr".
    iApply pgl_wp_bind. 
    iSpecialize ("HH" $! (λ v , WP fill K (of_val v) {{v0, Ψ v0}})%I). 
    iApply ("HH" with "[Hc] [Herr]"); last by rewrite err_fill.
    iNext.
    iMod "Hc" as (σ1) "[Hf Hc]". iModIntro.
    iFrame "Hf". iIntros (e2 σ2) "%Hprims Hheap".
    iMod ("Hc" with "[] Hheap") as "Hc"; first by iPureIntro; eapply fill_step; eauto; apply ectx_lang_ctx.
    iModIntro. iIntros "Herr". 
    rewrite pgl_wp_bind_inv.
    iApply "Hc".
    by rewrite err_fill.
  Qed.

End completeness.

Global Program Instance eris_ectx_to_completeness `{eris_ectx_lang_completeness_gen Λ Σ} : 
  eris_lang_completeness_gen (ectx_lang Λ) Σ := {
    heap_inv σ := heap_inv σ;
    err := err;
    err_ge0 := err_ge0;
    err_le1 := err_le1;
    err_exp := err_exp;
    err_stuck := err_stuck;
    err_fin := err_fin;
    na := na;
    na_step := na_step;
  }.
Next Obligation.
  intros. simpl.
  by eapply pgl_wp_ectx_to_prim_completeness.
Defined.