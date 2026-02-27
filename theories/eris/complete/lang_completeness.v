From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language exec_probs.
From clutch.eris Require Export weakestpre total_weakestpre lifting ectx_lifting.
From clutch.prob Require Import distribution.
From clutch.base_logic Require Import error_credits.

Local Open Scope R.

Class eris_lang_completeness_gen (Λ : language) (Σ : gFunctors) `{!erisWpGS Λ Σ} `{ecGS Σ} := ErisCompleteness {
  heap_inv : Λ.(state) → iProp Σ;

  (** [na e σ] should state that the execution of (e, σ) does not 
      allocate any new locations in the state *)
  na : Λ.(expr) → Λ.(state) → Prop;
  na_step : ∀ e σ e' σ', na e σ → prim_step e σ (e', σ') > 0 → na e' σ';

  eris_lang_completeness :
    ∀ e1 σ E,
      na e1 σ →
      reducible (e1, σ) →
      heap_inv σ ={E}=∗
      ((∀ Ψ (ε1 : cfg Λ → R), 
      (* ε1 is an abstract "error" random variable *)
      ⌜∃ r, ∀ ρ, ε1 ρ <= r⌝ →
      ⌜∀ ρ, reducible ρ → ε1 ρ = Expval (step ρ) ε1⌝ → 
      ⌜∀ ρ, 0 <= ε1 ρ⌝ →
      ⌜∀ ρ, stuck ρ → ε1 ρ = 1⌝ →
        ((▷ |={⊤,E}=> 
          ∀ e2 σ1',
            ⌜prim_step e1 σ (e2, σ1') > 0⌝ -∗
              heap_inv σ1' -∗ 
                ↯ (ε1 (e2, σ1')) ={E,⊤}=∗ 
                  WP e2 @ ⊤ {{ v, Ψ v }}) -∗
          ↯ (ε1 (e1, σ)) -∗ WP e1 @ ⊤ {{ v, Ψ v }})) )
}.

Section completeness.
  Context `{!erisWpGS Λ Σ} `{!ecGS Σ} `{!eris_lang_completeness_gen Λ Σ}.
  
  Lemma pgl_sem_completeness e σ (φ : Λ.(val) → Prop) :
    na e σ →
    ↯ (err_lb φ (e, σ)) -∗
    heap_inv σ -∗
    WP e {{v, ⌜φ v⌝}}.
  Proof.
    iLöb as "IH" forall (e σ φ).
    iIntros (Hna) "Herr Hst".
    destruct (to_val e) as [v|] eqn:Hev. {
      eapply of_to_val in Hev. subst e. 
      iApply pgl_wp_value'.
      destruct (decide (φ v)); first by iPureIntro.
      erewrite err_lb_fail_1; simpl; eauto; last by rewrite to_of_val.
      iPoseProof (ec_contradict with "Herr") as "[]".
      lra.
    } 
    destruct (decide (reducible (e, σ))) as [Hred|Hnred]. 2 : {
      iPoseProof (ec_contradict with "Herr") as "[]". 
      rewrite err_lb_stuck_1; first lra.
      constructor; auto.
      by rewrite -not_reducible.
    }
    iMod (eris_lang_completeness with "Hst") as "H"; eauto.
    iApply ("H" with "[] [] [] [] [] Herr").
    { iPureIntro. intros. by apply err_lb_bound. }
    { iPureIntro. intros. by apply err_lb_step. }
    { iPureIntro. intros. by apply err_lb_nn. }
    { iPureIntro. intros. by apply err_lb_stuck_1. }
    iNext. 
    iModIntro.
    iIntros (??) "%Hstep Hheap Herr".
    iApply ("IH" with "[] Herr Hheap").
    iPureIntro. 
    eapply na_step; eauto.
  Qed.

End completeness.