From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language.
From clutch.eris Require Export weakestpre total_weakestpre complete_pre.
From clutch.prob Require Import distribution.
From clutch.base_logic Require Import error_credits.

Local Open Scope R.
 
(** Completeness class for eris - simplified for single-expression execution.

    Compared to the heap_lang [lang_completeness_gen]:
    - No thread pools, forking, or observations
    - Error credits [↯] are threaded through both branches
    - [na] classifies expressions where the Löb IH can be applied
    - [err φ ρ] gives the "failure probability" for postcondition [φ] at cfg [ρ]
    - [step] is [prim_step ρ.1 ρ.2] via [lang_markov]
*)
Class eris_lang_completeness_gen (Λ : language) (Σ : gFunctors) `{!erisWpGS Λ Σ} `{ecGS Σ} := ErisCompleteness {
  heap_inv : Λ.(state) → iProp Σ;
  (* heap_inv_timeless :> ∀ σ, Timeless (heap_inv σ); *)

  (** [na e] should state that the execution of na does not allocate any new locations in the state *)
  na : Λ.(expr) → Prop;
  na_step : ∀ e σ e' σ', na e → prim_step e σ (e', σ') > 0 → na e';

  (** [err φ ρ] is the "failure probability": the probability that execution
      from [ρ] does NOT produce a value satisfying [φ].
      Satisfies the Bellman equation via [err_exp]. *)
  err : (Λ.(val) → iProp Σ) → cfg Λ → R;
  err_ge0 : ∀ φ ρ, 0 <= err φ ρ;
  err_le1 : ∀ φ ρ, err φ ρ <= 1;
  err_exp : ∀ φ ρ, err φ ρ = Expval (step ρ) (err φ);
  err_stuck : ∀ φ ρ, stuck ρ → err φ ρ = 1;
  err_fin : ∀ φ (v : Λ.(val)) σ,
    err φ (of_val v, σ) < 1 →
      heap_inv σ -∗ φ v;

  eris_lang_completeness :
    ∀ e1 σ E,
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
          ↯ (err Ψ (e1, σ)) -∗ WP e1 @ ⊤ {{ v, Ψ v }})) )
}.

Section completeness.
  Context `{!erisWpGS Λ Σ}.
  Context `{!ecGS Σ}.
  Context `{!eris_lang_completeness_gen Λ Σ}.

  Lemma pgl_wp_completeness e σ (φ : Λ.(val) → iProp Σ) :
    na e →
    ↯ (err φ (e, σ)) -∗
    heap_inv σ -∗
    WP e {{v, φ v}}.
  Proof.
    iLöb as "IH" forall (e σ φ).
    iIntros (Hna) "Herr Hst".
    (* iApply wp_inv_open_maybe. *)
    destruct (to_val e) as [v|] eqn:Hev. {
      eapply of_to_val in Hev. subst e. 
      (* iRight.
      iModIntro. *)
      iApply pgl_wp_value'.
      destruct (decide ((err φ (of_val v, σ)) < 1)); first by iApply err_fin.
      iPoseProof (ec_contradict with "Herr") as "[]". 
      lra.
    } 
    destruct (decide (reducible (e, σ))). 2 : {
      iPoseProof (ec_contradict with "Herr") as "[]". 
      rewrite err_stuck; first lra.
      constructor; auto.
      by rewrite -not_reducible. 
    }
    iMod (eris_lang_completeness with "Hst") as "H"; eauto.
    iDestruct "H" as "(Hheap & H)". 
    (* iModIntro. iRight. *)
    iApply ("H" with "[Hheap] Herr"). iNext.
    iModIntro.
    iExists σ; iFrame.
    iIntros (e' σ') "%Hstep Hheap".
    iModIntro. iIntros "Herr".
    iApply ("IH" with "[] Herr Hheap"); iFrame.
    iPureIntro.
    eapply na_step; eauto.
    (* iMod (eris_lang_completeness with "Hst") as "[H|H]"; eauto.
    - iDestruct "H" as (K e1 Heq Hnotval Hctx Hatomic) "H". 
      iModIntro. iLeft. iExists K, e1. do 3 (iSplit; first done).
      iApply "H".
      2 : {
        admit.
      }
      iNext.
      iIntros (v σ') "%Hstep".
      (* iApply pgl_wp_bind. *)

      admit.
      Check pgl_wp_bind.
      (* iModIntro. *)
    - iDestruct "H" as "(Hheap & H)". iModIntro. iRight.
      iApply ("H" with "[Hheap] Herr"). iNext.
      iModIntro.
      iExists σ; iFrame.
      iIntros (e' σ') "%Hstep Hheap".
      iModIntro. iIntros "Herr".
      iApply ("IH" with "[] Herr Hheap"); iFrame.
      iPureIntro.
      eapply na_step; eauto. *)
  Admitted.
      (* rewrite pgl_wp_unfold /pgl_wp_pre Hev.
      iIntros (σ0 ε0) "[Hsta Herra]".
      iApply fupd_mask_intro; first set_solver.
      iIntros "Hemp". *)

      (* 
      iApply pgl_wp_atomic.
      1: eapply val_atomic_eris. *)
End completeness.