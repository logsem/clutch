From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable finite.
From clutch.prelude Require Export base stdpp_ext Reals_ext Coquelicot_ext Series_ext classical uniform_list.
From clutch.prob Require Import countable_sum distribution markov graded_predicate_lifting.
From clutch.common Require Import language.

Local Open Scope R.

Lemma is_inf_seq_minor (u : nat → Rbar) (l : Rbar) (n : nat): 
  is_inf_seq u l → Rbar_le l (u n).
Proof.
  unfold is_inf_seq. destruct l; intros; rewrite /Rbar_le //=. 
  - destruct (u n) eqn : Hun; auto.
    + destruct (decide (r <= r0)); auto.
      assert (0 < r - r0); first lra.
      pose proof (H (mkposreal (r - r0) H0)) as [??].
      specialize (H1 n). rewrite Hun //= in H1. 
      lra.
    + pose proof (H (mkposreal 1 Rlt_0_1)) as [??].
      specialize (H0 n). rewrite Hun //= in H0. 
  - pose proof (H (u n) n%nat).
    unfold Rbar_lt in H0.
    destruct (u n); auto. by apply Rlt_irrefl in H0. 
Qed.

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
  apply is_inf_seq_minor.
  apply Inf_seq_correct.
Qed.

Lemma Inf_seq_major_ge (u : nat → Rbar) (M : R) (n : nat) :
  Rbar_le (u n) M → Rbar_le (Inf_seq u) M.
Proof.
  intros. trans (u n); auto. 
  apply inf_is_lower_bound.
Qed.

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

  Lemma pexec_inf_exists ρ :
    is_finite (Inf_seq (λ n : nat, SeriesC (pexec n ρ))).
  Proof.
    apply (Rbar_le_sandwich 0 1).
    + by apply lower_bound_le_inf =>/=.
    + Check Sup_seq_minor_le.
      by apply (Inf_seq_major_ge _ _ 0%nat)=>/=. 
  Qed.
  
  Definition stuck_prob ρ : R := 1 - Inf_seq (fun n => SeriesC (pexec n ρ)).

  Local Opaque SeriesC.
  Lemma stuck_prob_le_1 ρ :
    stuck_prob ρ <= 1.
  Proof.
    rewrite /stuck_prob.
    assert (0 <= Inf_seq (fun n => SeriesC (pexec n ρ))); last by real_solver.
    
  Admitted. 

  Lemma stuck_prob_nn ρ :
    0 <= stuck_prob ρ.
  Proof.
    rewrite /stuck_prob.
    assert (Inf_seq (fun n => SeriesC (pexec n ρ)) <= 1); last by real_solver.
    transitivity (SeriesC (pexec 0 ρ)); last done.
    apply finite_rbar_le; first by apply pexec_inf_exists.
    apply (inf_is_lower_bound (λ n : nat, SeriesC (pexec n ρ)) 0).
  Qed.

  Lemma stuck_prob_final_0 {ρ} v :
    to_final ρ = Some v →
    stuck_prob ρ = 0.
  Proof.
    intros.
    apply Rle_antisym; last by apply stuck_prob_nn.
    rewrite /stuck_prob. 
    assert (1 <= Inf_seq (λ n : nat, SeriesC (pexec n ρ))); last by real_solver.
    apply rbar_le_finite; first by apply pexec_inf_exists.
    apply lower_bound_le_inf => ?. 
    apply rbar_le_rle.
    rewrite pexec_is_final; first by rewrite dret_mass; lra.
    by eapply to_final_Some_2.
  Qed.

  Lemma stuck_prob_stuck_1 ρ :
    stuck ρ →
    stuck_prob ρ = 1.
  Proof.
    intros [??].
    apply Rle_antisym; first by apply stuck_prob_le_1.
    rewrite /stuck_prob.
    assert (Inf_seq (λ n : nat, SeriesC (pexec n ρ)) <= 0); last by real_solver.
    assert (SeriesC (pexec 1 ρ) = 0) as <-; first by rewrite pexec_1 step_or_final_no_final //= 
      irreducible_dzero //= dzero_mass //=.
    apply finite_rbar_le; first by apply pexec_inf_exists.
    apply (inf_is_lower_bound (λ n : nat, SeriesC (pexec n ρ)) 1).
  Qed.

  Definition err_prob φ ρ : R := 
    prob (lim_exec ρ) (λ a, negb (bool_decide (φ a))).

  Lemma err_prob_step ρ φ : 
    reducible ρ →
    err_prob φ ρ = Expval (step ρ) (err_prob φ).
  Proof.
    rewrite /err_prob lim_exec_step.
    intros Hred.
    pose proof (reducible_not_final _ Hred).
    rewrite step_or_final_no_final //=.
    by rewrite prob_dbind.
  Qed.

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

Section lang.

  Context {Λ : language}.

  Lemma stuck_prob_step (ρ : cfg Λ) : 
    reducible ρ →
    stuck_prob ρ = Expval (step ρ) stuck_prob.
  Proof.
    intros.
    rewrite /stuck_prob. 
  Admitted.

  Lemma err_lb_step (ρ : cfg Λ) (φ : val Λ → Prop) :
    reducible ρ →
    err_lb φ ρ = Expval (step ρ) (err_lb φ).
  Proof.
    intros.
    rewrite /err_lb.
    rewrite Expval_plus.
    - rewrite stuck_prob_step //= (err_prob_step ρ φ) //=.
    - eapply ex_expval_bounded => x. split; [apply stuck_prob_nn | apply stuck_prob_le_1]. 
    - eapply ex_expval_bounded => x. split; [apply prob_ge_0 | apply prob_le_1]. 
  Qed.

End lang.