From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language.
From clutch.eris Require Export weakestpre total_weakestpre lifting ectx_lifting.
From clutch.prob Require Import distribution.
From clutch.base_logic Require Import error_credits.

Local Open Scope R.

Class eris_lang_completeness_gen (Λ : language) (Σ : gFunctors) `{!erisWpGS Λ Σ} `{ecGS Σ} := ErisCompleteness {
  heap_inv : Λ.(state) → iProp Σ;

  (** [na e] should state that the execution of na does not allocate any new locations in the state *)
  na : Λ.(expr) → Prop;
  na_step : ∀ e σ e' σ', na e → prim_step e σ (e', σ') > 0 → na e';

  eris_lang_completeness :
    ∀ e1 σ E,
      na e1 →
      reducible (e1, σ) →
      heap_inv σ ={E}=∗
      ((∀ Ψ (ε1 : cfg Λ → R), 
      (* ε1 is an abstract "error" random variable *)
      ⌜∀ ρ, reducible ρ → ε1 ρ = Expval (step ρ) ε1⌝ → 
      ⌜∀ ρ, 0 <= ε1 ρ⌝ →
      ⌜∀ ρ, stuck ρ → ε1 ρ = 1⌝ →
      ⌜∀ K ρ, reducible ρ → ε1 (fill_lift K ρ) = Expval (step ρ) (ε1 ∘ fill_lift K)⌝ →
        ((▷ |={⊤,E}=> 
          ∀ e2 σ1',
            ⌜prim_step e1 σ (e2, σ1') > 0⌝ -∗
              heap_inv σ1' -∗ 
                ↯ (ε1 (e2, σ1')) ={E,⊤}=∗ 
                  WP e2 @ ⊤ {{ v, Ψ v }}) -∗
          ↯ (ε1 (e1, σ)) -∗ WP e1 @ ⊤ {{ v, Ψ v }})) )
}.

Section prob.
  Definition stuck_prob {δ : markov} (ρ : mstate δ) : R 
    (* := 1 - Inf_seq (fun n => SeriesC (pexec n ρ)) *).
  Admitted.

  Definition err_prob {δ : markov} (ρ : mstate δ) (φ : mstate_ret δ → Prop) : R := 
    prob (lim_exec ρ) (λ a, negb (bool_decide (φ a))).

  (* need to check if this is correct *)
  Definition err_lb {δ : markov} (φ : mstate_ret δ → Prop) (ρ : mstate δ) : R := (stuck_prob ρ) + (err_prob ρ φ).

  Lemma err_lb_fail_1 {δ : markov} (ρ : mstate δ) v (φ : mstate_ret δ → Prop) :
    to_final ρ = Some v →
    ¬ φ v →
    err_lb φ ρ = 1.
  Admitted.

  Lemma err_lb_stuck_1 {δ : markov} (ρ : mstate δ) (φ : mstate_ret δ → Prop) :
    stuck ρ →
    err_lb φ ρ = 1.
  Admitted.

  Lemma err_lb_step {δ : markov} (ρ : mstate δ) (φ : mstate_ret δ → Prop) :
    err_lb φ ρ = Expval (step ρ) (err_lb φ).
  Admitted.

  Lemma err_lb_nn {δ : markov} (ρ : mstate δ) (φ : mstate_ret δ → Prop) :
    0 <= err_lb φ ρ.
  Admitted. 

  Lemma err_lb_fill {Λ : language} (e : Λ.(expr)) (σ : Λ.(state)) (φ : Λ.(val) → Prop) K :
    reducible (e, σ) →
    err_lb φ (fill_lift K (e, σ)) = Expval (step (e, σ)) (err_lb φ ∘ fill_lift K).
  Admitted.
End prob.

Section completeness.
  Context `{!erisWpGS Λ Σ}.
  Context `{!ecGS Σ}.
  Context `{!eris_lang_completeness_gen Λ Σ}.
  
  Lemma pgl_sem_completeness e σ (φ : Λ.(val) → Prop) :
    na e →
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
    { iPureIntro. intros. by apply err_lb_step. }
    { iPureIntro. intros. by apply err_lb_nn. }
    { iPureIntro. intros. by apply err_lb_stuck_1. }
    { iPureIntro. intros ? [??]. by apply err_lb_fill. }
    iNext. 
    iModIntro.
    iIntros (??) "%Hstep Hheap Herr".
    iApply ("IH" with "[] Herr Hheap").
    iPureIntro. 
    eapply na_step; eauto.
  Qed.

End completeness.