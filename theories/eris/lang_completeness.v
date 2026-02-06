(** Adaptation of lang_completeness for the eris probabilistic framework.

    Key differences from the Iris version:
    - prim_step is probabilistic: expr → state → distr (expr * state)
    - cfg = expr * state (no thread pools, no forking)
    - No observations (κ)
    - No efs (forked threads)
    - Uses erisWpGS instead of irisGS_gen
*)

From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language.
From clutch.eris Require Export weakestpre total_weakestpre complete_pre.
From clutch.prob Require Import distribution.

(** Completeness class for eris - simplified for single-expression execution *)
Class eris_lang_completeness (Λ : language) (Σ : gFunctors) `{!erisWpGS Λ Σ} := ErisCompleteness {
  eris_heap_inv : Λ.(state) → iProp Σ;
  eris_heap_inv_timeless :> ∀ σ, Timeless (eris_heap_inv σ);
  eris_completeness_core :
    ∀ e1 σ E,
      reducible (e1, σ) →
      eris_heap_inv σ ∗ ⌜cfg_safe (e1, σ)⌝ ={E}=∗
      ((∃ K e1', ⌜LanguageCtx K⌝ ∗ ⌜e1 = K e1'⌝ ∗ ⌜to_val e1' = None⌝ ∗ ⌜Atomic StronglyAtomic e1'⌝ ∗
        ∀ Ψ, ((▷ ∀ v2 σ',
          ⌜prim_step e1' σ (of_val v2, σ') > 0⌝ -∗
          eris_heap_inv σ' ==∗
          (eris_heap_inv σ' ∗ (eris_heap_inv σ' -∗ Ψ v2))) -∗
          WP e1' @ E {{ v, Ψ v }})) ∨
      (eris_heap_inv σ ∗ ∀ Ψ, ((▷ |={⊤,E}=> ∃ σ1, eris_heap_inv σ1 ∗
        ∀ e2 σ1',
          ⌜prim_steps e1 σ1 e2 σ1'⌝ -∗
          eris_heap_inv σ1' ={E,⊤}=∗
          WP e2 @ ⊤ {{ v, Ψ v }}) -∗
          WP e1 @ ⊤ {{ v, Ψ v }})))
}.
Global Existing Instance eris_heap_inv_timeless.

Section completeness.
  Context `{!erisWpGS Λ Σ}.
  Context `{!eris_lang_completeness Λ Σ}.
  Context `{!cinvG Σ}.

  Let N := nroot .@ "eris_completeness".

  (** Configuration invariant for single-expression execution *)
  Definition eris_cfg_inv (e_init : expr Λ) (σ_init : state Λ) : iProp Σ :=
    ∃ e σ,
      eris_heap_inv σ ∗
      ⌜cfg_safe (e, σ)⌝ ∗
      ⌜prim_steps e_init σ_init e σ⌝.

  Definition is_eris_cfg γ e_init σ_init : iProp Σ :=
    cinv N γ (eris_cfg_inv e_init σ_init).

  (** Main completeness lemma using Löb induction.
      This states that if we have a configuration invariant and the current expression
      is reachable from the initial configuration, then we can derive a WP. *)
  Lemma eris_wp_completeness γ e_init σ_init q (e : expr Λ) σ :
    is_eris_cfg γ e_init σ_init -∗
    cinv_own γ q -∗
    ⌜prim_steps e_init σ_init e σ⌝ -∗
    ⌜cfg_safe (e, σ)⌝ -∗
    WP e {{ v, ∃ q', cinv_own γ q' }}.
  Proof.
    (* The proof uses Löb induction and the magic rule wp_inv_open_maybe.
       For values, we're done immediately.
       For non-values, we use eris_completeness_core to decompose into
       atomic and non-atomic cases, updating the invariant appropriately. *)
  Admitted.

  (** Semantic completeness: if e is safe, then we can derive WP *)
  Lemma eris_sem_completeness e σ φ :
    (∀ e' σ', prim_steps e σ e' σ' → not_stuck (e', σ')) →
    (∀ v σ', prim_steps e σ (of_val v) σ' → φ v) →
    (⊢ eris_heap_inv σ -∗ WP e @ ⊤ {{ v, ⌜φ v⌝ }}).
  Proof.
    intros Hsafe Hres.
    iIntros "Hheap".
    iMod (cinv_alloc _ _ (eris_cfg_inv e σ) with "[Hheap]") as (γ) "(#Hinv & Hq)".
    { iNext. iExists e, σ. iFrame "Hheap".
      iPureIntro. split.
      - intros e' σ' Hsteps. apply Hsafe. exact Hsteps.
      - constructor. }
    iApply pgl_wp_fupd.
    iApply (pgl_wp_wand with "[-]").
    - iApply (eris_wp_completeness γ e σ with "Hinv Hq"); iPureIntro.
      + constructor.
      + intros e' σ' Hsteps. apply Hsafe. exact Hsteps.
    - iIntros (v) "[%q' Hq']".
      (* To complete this proof, we need to track that the final value
         was reached from the initial configuration in the invariant. *)
  Admitted.

End completeness.
