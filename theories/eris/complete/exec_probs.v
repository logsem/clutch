From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable finite.
From clutch.prelude Require Export base stdpp_ext Reals_ext Coquelicot_ext Series_ext classical uniform_list.
From clutch.prob Require Import countable_sum distribution markov graded_predicate_lifting.

Local Open Scope R.

Lemma is_inf_seq_major (u : nat → Rbar) (l : Rbar) (n : nat): 
  is_sup_seq u l → Rbar_le (u n) l.
Admitted.

Lemma lower_bound_le_inf (h : nat → Rbar) r :
  (∀ n, Rbar_le r (h n)) →
  Rbar_le r (Inf_seq h).
Proof.
  intro H2.
  pose proof (is_inf_seq_glb h (Inf_seq h) (Inf_seq_correct h)) as H3.
  rewrite /Lub.Rbar_is_glb in H3.
  apply H3.
  rewrite /Lub.Rbar_is_lower_bound. 
  intros q (n & Hn).
  rewrite Hn; auto.
Qed.

Lemma inf_is_lower_bound (h : nat → Rbar) n :
  Rbar_le (Inf_seq h) (h n).
Proof.
(*
  apply is_sup_seq_major.
  apply Sup_seq_correct.
Qed. *)
Admitted.

Section prob.
  Context {δ : markov}.
  Implicit Types (ρ : mstate δ) (φ : mstate_ret δ → Prop).

  Lemma pexec_mass_mono n ρ : 
    SeriesC (pexec (S n) ρ) <= SeriesC (pexec n ρ).
  Proof.
    rewrite pexec_Sn_r //=. 
    rewrite dbind_mass.
    apply SeriesC_le; real_solver.
  Qed.
  
  Definition stuck_prob ρ : R 
    := 1 - Inf_seq (fun n => SeriesC (pexec n ρ)).

  Lemma stuck_prob_le_1 ρ :
    stuck_prob ρ <= 1.
  Proof.
    rewrite /stuck_prob.
    assert (0 <= Inf_seq (fun n => SeriesC (pexec n ρ))); last by real_solver.

  Admitted. 

  Lemma stuck_prob_nn ρ :
    0 <= stuck_prob ρ.
  Proof.
    Local Opaque SeriesC.
    rewrite /stuck_prob.
    assert (Inf_seq (fun n => SeriesC (pexec n ρ)) <= 1); last by real_solver.
    transitivity (SeriesC (pexec 0 ρ)); last done.
    apply finite_rbar_le.
    - apply (Rbar_le_sandwich 0 1).
      + by apply lower_bound_le_inf =>/=.
      + (* by apply (Sup_seq_minor_le _ _ 0%nat)=>/=. *)admit.
    - apply (inf_is_lower_bound (λ n : nat, SeriesC (pexec n ρ)) 0).
  Admitted.

  Lemma stuck_prob_step ρ : 
    reducible ρ →
    stuck_prob ρ = Expval (step ρ) stuck_prob.
  Proof.
  Admitted.

  Lemma stuck_prob_final_0 {ρ} v :
    to_final ρ = Some v →
    stuck_prob ρ = 0.
  Proof.
  Admitted.

  Lemma stuck_prob_stuck_1 ρ :
    stuck ρ →
    stuck_prob ρ = 1.
  Proof.
    
  Admitted.

  Definition err_prob φ ρ : R := 
    prob (lim_exec ρ) (λ a, negb (bool_decide (φ a))).

  Lemma err_prob_step ρ φ : 
    reducible ρ →
    err_prob φ ρ = Expval (step ρ) (err_prob φ).
  Proof.
    Search reducible.
    - rewrite /err_prob lim_exec_step.
    intros Hred.
    pose proof (reducible_not_final _ Hred).
    rewrite step_or_final_no_final //=.
    by rewrite prob_dbind.
  Qed.

  Lemma err_prob_stuck_0 ρ φ : 
    stuck ρ →
    err_prob φ ρ = 0.
  Proof.
    intros.
    rewrite /err_prob.
  Admitted.

  (* need to check if this is correct *)
  Definition err_lb φ ρ : R := (stuck_prob ρ) + (err_prob φ ρ).

  Lemma err_lb_fail_1 ρ v φ :
    to_final ρ = Some v →
    ¬ φ v →
    err_lb φ ρ = 1.
  Proof.
    intros.
    rewrite /err_lb /err_prob (stuck_prob_final_0 v) //= 
      (lim_exec_final _ v) //= prob_dret_true; real_solver.
  Qed.

  Lemma err_lb_stuck_1 ρ φ:
    stuck ρ →
    err_lb φ ρ = 1.
  Proof.
    intros.
    pose proof H as [??].
    rewrite /err_lb /err_prob stuck_prob_stuck_1 //= 
      lim_exec_not_final //= irreducible_dzero //= dbind_dzero /prob. 
    erewrite SeriesC_ext; first by erewrite dzero_mass; real_solver.
    real_solver.
  Qed.

  Lemma err_lb_bound φ :
    ∃ r, ∀ ρ, err_lb φ ρ <= r.
  Proof.
    exists (1+1).
    intros. rewrite /err_lb.
    apply Rle_plus_plus.
    - apply stuck_prob_le_1.
    - apply prob_le_1.
  Qed.

  Lemma err_lb_step ρ φ :
    reducible ρ →
    err_lb φ ρ = Expval (step ρ) (err_lb φ).
  Proof.
    intros.

  Admitted.

  Lemma err_lb_nn ρ φ :
    0 <= err_lb φ ρ.
  Proof.
    replace 0 with (0 + 0); last real_solver.
    rewrite /err_lb. 
    apply Rle_plus_plus.
    - apply stuck_prob_nn.
    - apply prob_ge_0.
  Qed. 
  
End prob.