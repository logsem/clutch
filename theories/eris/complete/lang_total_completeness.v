From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode classes.
From iris.base_logic Require Export invariants lib.ghost_map lib.cancelable_invariants.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

From clutch.common Require Export language.
From clutch.eris Require Export weakestpre total_weakestpre lifting ectx_lifting.
From clutch.prob Require Import distribution.
From clutch.base_logic Require Import error_credits.
From clutch.eris.complete Require Import exec_probs.

Local Open Scope R.

Class eris_lang_total_completeness_gen (Λ : language) (Σ : gFunctors) `{!erisWpGS Λ Σ} `{ecGS Σ} := ErisCompleteness {
  heap_inv : Λ.(state) → iProp Σ;

  (** [na e σ] should state that the execution of (e, σ) does not 
      allocate any new locations in the state *)
  na : Λ.(expr) → Λ.(state) → Prop;
  na_step : ∀ e σ e' σ', na e σ → prim_step e σ (e', σ') > 0 → na e' σ';

  eris_lang_total_completeness :
    ∀ e1 σ E,
      na e1 σ →
      reducible (e1, σ) →
      heap_inv σ ={E}=∗
      ((∀ Ψ (ε1 : nat → cfg Λ → R) n, 
      (* ε1 is an abstract "error" random variable *)
      ⌜∃ r, ∀ n ρ, ε1 n ρ <= r⌝ →
      ⌜∀ n ρ, reducible ρ → ε1 (S n) ρ = Expval (step ρ) (ε1 n)⌝ → 
      ⌜∀ n ρ, 0 <= ε1 n ρ⌝ →
      ⌜∀ n ρ, stuck ρ → ε1 n ρ = 1⌝ →
        ((|={⊤,E}=> 
          ∀ e2 σ1',
            ⌜prim_step e1 σ (e2, σ1') > 0⌝ -∗
              heap_inv σ1' -∗ 
                ↯ (ε1 n (e2, σ1')) ={E,⊤}=∗ 
                  WP e2 @ ⊤ [{ v, Ψ v }]) -∗
          ↯ (ε1 (S n) (e1, σ)) -∗ WP e1 @ ⊤ [{ v, Ψ v }])) )
}.

Section prob.
  Context {δ : markov}.
  Implicit Types (n : nat)(ρ : mstate δ) (φ : mstate_ret δ → Prop).

  Definition err_tlb φ n ρ : R.
  Admitted.

  Lemma err_tlb_fail_1 n ρ v φ :
    to_final ρ = Some v →
    ¬ φ v →
    err_tlb φ n ρ = 1.
  Proof.
  Admitted.
  (*   intros.
    rewrite /err_lb /err_prob (stuck_prob_final_0 v) //= 
      (lim_exec_final _ v) //= prob_dret_true; real_solver.
  Qed. *)

  Lemma err_tlb_stuck_1 n ρ φ:
    stuck ρ →
    err_tlb φ n ρ = 1.
  Proof.
  Admitted.
  (*   intros.
    pose proof H as [??].
    rewrite /err_lb /err_prob stuck_prob_stuck_1 //= 
      lim_exec_not_final //= irreducible_dzero //= dbind_dzero /prob. 
    erewrite SeriesC_ext; first by erewrite dzero_mass; real_solver.
    real_solver.
  Qed. *)

  Lemma err_tlb_bound φ :
    ∃ r, ∀ n ρ, err_tlb φ n ρ <= r.
  Proof.
  Admitted.
  (*   exists (1+1).
    intros. rewrite /err_lb.
    apply Rle_plus_plus.
    - apply stuck_prob_le_1.
    - apply prob_le_1.
  Qed. *)

  Lemma err_tlb_nn n ρ φ :
    0 <= err_tlb φ n ρ.
  Proof.
  Admitted.
  (*   replace 0 with (0 + 0); last real_solver.
    rewrite /err_lb. 
    apply Rle_plus_plus.
    - apply stuck_prob_nn.
    - apply prob_ge_0.
  Qed.  *)

End prob.

Section lang.

  Context {Λ : language}.

  Lemma err_tlb_step n (ρ : cfg Λ) (φ : val Λ → Prop) :
    reducible ρ →
    err_tlb φ (S n) ρ = Expval (step ρ) (err_tlb φ n).
  Proof.
  Admitted.
  (*   intros.
    rewrite /err_lb.
    rewrite Expval_plus.
    - rewrite stuck_prob_step //= (err_prob_step ρ φ) //=.
    - eapply ex_expval_bounded => x. split; [apply stuck_prob_nn | apply stuck_prob_le_1]. 
    - eapply ex_expval_bounded => x. split; [apply prob_ge_0 | apply prob_le_1]. 
  Qed. *)

End lang.

Section completeness.
  Context `{!erisWpGS Λ Σ} `{!ecGS Σ} `{!eris_lang_total_completeness_gen Λ Σ}.
  
  Lemma tgl_sem_completeness e σ (φ : Λ.(val) → Prop) n :
    na e σ →
    ↯ (err_tlb φ n (e, σ)) -∗
    heap_inv σ -∗
    WP e [{v, ⌜φ v⌝}].
  Proof.
    iInduction n as [|n] "IH" forall (e σ φ).
    - iIntros (Hna) "Herr Hst".
      destruct (to_val e) as [v|] eqn:Hev. {
        eapply of_to_val in Hev. subst e. 
        iApply tgl_wp_value'.
        destruct (decide (φ v)); first by iPureIntro.
        erewrite err_tlb_fail_1; simpl; eauto; last by rewrite to_of_val.
        iPoseProof (ec_contradict with "Herr") as "[]".
        lra.
      } 
      admit.
    - iIntros (Hna) "Herr Hst".
      destruct (to_val e) as [v|] eqn:Hev. {
        eapply of_to_val in Hev. subst e. 
        iApply tgl_wp_value'.
        destruct (decide (φ v)); first by iPureIntro.
        erewrite err_tlb_fail_1; simpl; eauto; last by rewrite to_of_val.
        iPoseProof (ec_contradict with "Herr") as "[]".
        lra.
      } 
      destruct (decide (reducible (e, σ))) as [Hred|Hnred]. 2 : {
        iPoseProof (ec_contradict with "Herr") as "[]". 
        rewrite err_tlb_stuck_1; first lra.
        constructor; auto.
        by rewrite -not_reducible.
      } 
      iMod (eris_lang_total_completeness with "Hst") as "H"; eauto.
      iApply ("H" with "[] [] [] [] [] Herr").
      { iPureIntro. intros. by apply err_tlb_bound. }
      { iPureIntro. intros. by apply err_tlb_step. }
      { iPureIntro. intros. by apply err_tlb_nn. }
      { iPureIntro. intros. by apply err_tlb_stuck_1. }
      (* iNext. *)
      iModIntro.
      iIntros (??) "%Hstep Hheap Herr".
      iApply ("IH" with "[] Herr Hheap").
      iPureIntro. 
      eapply na_step; eauto.
  Admitted.

End completeness.