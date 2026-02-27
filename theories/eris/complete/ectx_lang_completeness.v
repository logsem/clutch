From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language ectx_language.
From clutch.eris Require Export weakestpre total_weakestpre.
From clutch.prob Require Import distribution.
From clutch.base_logic Require Import error_credits.
From clutch.eris.complete Require Export lang_completeness.

Local Open Scope R.

Class eris_ectx_lang_completeness_gen (Λ : ectxLanguage) (Σ : gFunctors) `{!erisWpGS Λ Σ} `{ecGS Σ} := ErisEctxCompleteness {
  heap_inv : Λ.(state) → iProp Σ;

  na : Λ.(expr) → Λ.(state) → Prop;
  na_step : ∀ e σ e' σ', na e σ → prim_step e σ (e', σ') > 0 → na e' σ';
  na_fill_inv : ∀ e σ K, na (fill K e) σ → na e σ; 

  eris_ectx_lang_completeness :
    ∀ e1 σ E,
      na e1 σ →
      head_reducible e1 σ →
      heap_inv σ ={E}=∗
      ((∀ Ψ (ε1 : cfg Λ → R), 
        ⌜∀ e σ, head_reducible e σ → ε1 (e, σ) = Expval (step (e, σ)) ε1⌝ →
        ⌜∀ ρ, 0 <= ε1 ρ⌝ →
        ⌜∀ ρ, stuck ρ → ε1 ρ = 1⌝ →
          ((▷ |={⊤,E}=>  
            ∀ e2 σ1',
              ⌜prim_step e1 σ (e2, σ1') > 0⌝ -∗
                heap_inv σ1' -∗ 
                  ↯ (ε1 (e2, σ1')) ={E,⊤}=∗ 
                    WP e2 @ ⊤ {{ v, Ψ v }}) -∗
            ↯ (ε1 (e1, σ)) -∗ WP e1 @ ⊤ {{ v, Ψ v }})))
}.

Lemma stuck_fill {Λ : ectxLanguage} {e : expr Λ} {σ : state Λ} K : stuck (e, σ) → stuck (fill K e, σ).
Proof.
  intros [Hnv Hr].
  constructor.
  - intro H.
    apply fill_val in H.
    contradiction.
  - rewrite -not_reducible.
    intro H.
    apply reducible_fill_inv in H; first by rewrite -not_reducible in Hr.
    rewrite /is_final //= in Hnv. 
    rewrite /to_val //=.
    destruct (ectx_language.to_val e); simpl in *; auto.
    exfalso.
    by apply Hnv.
Qed.

Section completeness.
  Context `{eris_ectx_lang_completeness_gen Λ Σ}. 

  Lemma pgl_wp_ectx_to_prim_completeness e1 σ E :
    na e1 σ →
    reducible (e1, σ) →
    heap_inv σ ={E}=∗
    ((∀ Ψ (ε1 : cfg Λ → R), 
    ⌜∃ r, ∀ ρ, ε1 ρ <= r⌝  →
    ⌜∀ ρ, reducible ρ → ε1 ρ = Expval (step ρ) ε1⌝ →
    ⌜∀ ρ, 0 <= ε1 ρ⌝ →
    ⌜∀ ρ, stuck ρ → ε1 ρ = 1⌝ →
    ((▷ |={⊤,E}=> 
        ∀ e2 σ1',
        ⌜prim_step e1 σ (e2, σ1') > 0⌝ -∗
            heap_inv σ1' -∗ 
            ↯ (ε1 (e2, σ1')) ={E,⊤}=∗ 
                WP e2 @ ⊤ {{ v, Ψ v }}) -∗
        ↯ (ε1 (e1, σ)) -∗ WP e1 @ ⊤ {{ v, Ψ v }}))).
  Proof.
    iIntros (Hna ((e'&σ')&Hstep)) "Hheap".
    rewrite //= prim_step_iff in Hstep. 
    destruct Hstep as (K & e1' & e2' & <- & <- & Hstep).
    iMod (eris_ectx_lang_completeness e1' σ with "Hheap") as "HH";
    [by eapply na_fill_inv | by econstructor |].
    iModIntro. iFrame.
    iIntros (Ψ ε1 [r Hε1r] Hε1step Hε1nn Hε1stuck) "Hc Herr".
    iApply pgl_wp_bind. 
    iSpecialize ("HH" $! (λ v , WP fill K (of_val v) {{v0, Ψ v0}})%I (λ '(e, s), ε1 (fill K e, s))). 
    iApply ("HH" with "[] [] [] [Hc] Herr"). 
    { 
      iPureIntro. 
      intros e0 σ0 Hrd.
      replace (λ '(e, s), ε1 (fill K e, s)) with (ε1 ∘ (fill_lift (fill K))); last by apply functional_extensionality => [[??]] //=.
      rewrite -Expval_dmap //=; last by eapply ex_expval_bounded => [[??]]; split; real_solver.
      rewrite -fill_dmap //=; last by apply head_prim_reducible, reducible_not_final, to_final_None_1 in Hrd.
      by apply Hε1step, head_prim_fill_reducible.
    }
    { iPureIntro. intros [??]. apply Hε1nn. }
    { 
      iPureIntro. 
      intros [e0 σ0] [Hnv Hir].
      rewrite Hε1stuck //=.
      by apply stuck_fill.
    }  
    iNext.
    iMod "Hc". iModIntro.
    iIntros (e2 σ2) "%Hprims Hheap Herr".
    iMod ("Hc" with "[] Hheap [Herr]") as "Hc"; first by iPureIntro; eapply fill_step; eauto; apply ectx_lang_ctx.
    - iFrame.
    - by rewrite pgl_wp_bind_inv.
  Qed.

End completeness.

Global Program Instance eris_ectx_to_completeness `{eris_ectx_lang_completeness_gen Λ Σ} : 
  eris_lang_completeness_gen (ectx_lang Λ) Σ := {
    heap_inv := heap_inv;
    na := na;
    na_step := na_step;
  }.
Next Obligation.
  intros. simpl.
  exact (pgl_wp_ectx_to_prim_completeness e1 σ E H1 H2).
Defined.