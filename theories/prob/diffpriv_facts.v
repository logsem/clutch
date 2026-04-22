From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Import couplings_exp couplings_dp couplings_dp_complete differential_privacy.

Local Open Scope R.

Definition c_sensitive {A B : Type} (dA : A -> A -> R) (dB : B -> B -> R) (f : A -> B) (c : R)
  := ∀ a a', (dB (f a) (f a') <= c * dA a a')%R.

Lemma dp_postprocessing {A B C : Type} `{Countable B, Countable C} (dA : A -> A -> R)
  (f : A -> distr B) (g : B -> C) (ε δ : R)
  : diffpriv_approx dA f ε δ -> diffpriv_approx dA (λ a, dbind (λ y, dret (g y)) (f a)) ε δ.
Proof.
  intros dp_f.
  intros a a' adj PC.
  unfold diffpriv_approx in dp_f.
  set (PB := λ b, PC (g b)).
  rewrite prob_dmap.
  specialize (dp_f a a' adj PB).
  unfold PB in dp_f.
  etrans.
  1: apply dp_f.
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_l.
  1: left ; apply exp_pos.
  rewrite prob_dmap.
  done.
Qed.

Definition dp_coupl {A} `{Countable B} (dA : A → A → R) (f : A -> distr B) (ε δ : R) :=
  ∀ a1 a2, (dA a1 a2 <= 1)%R → DPcoupl (f a1) (f a2) eq ε δ.

Lemma dp_coupl_seq_comp
  {DB B C : Type} `{Countable B, Countable C} (dDB : DB -> DB -> R)
  (f : DB -> distr B) (g : DB * B -> distr C) (ε1 δ1 ε2 δ2 : nonnegreal)
  (dp_f : dp_coupl dDB f ε1 δ1)
  (dp_g : ∀ b, dp_coupl dDB (λ x, g (x, b)) ε2 δ2)
   :
   dp_coupl dDB
     (λ x, dbind (λ b, g (x, b)) (f x))
     (ε1 + ε2)
     (δ1 + δ2).
Proof.
  intros a1 a2 adj.
  eapply DPcoupl_dbind.
  1,2: apply cond_nonneg.
  2: eapply dp_f => //.
  intros ? b ->. by apply dp_g.
Qed.

Lemma dp_seq_comp
  {DB B C : Type} `{Countable B, Countable C} (dDB : DB -> DB -> R)
  (f : DB -> distr B) (g : DB * B -> distr C) (ε1 δ1 ε2 δ2 : nonnegreal)
  (dp_f : diffpriv_approx dDB f ε1 δ1)
  (dp_g : ∀ b, diffpriv_approx dDB (λ x, g (x, b)) ε2 δ2)
   :
   diffpriv_approx dDB
     (λ x, dbind (λ b, g (x, b)) (f x))
     (ε1 + ε2)
     (δ1 + δ2).
Proof.
  intros a1 a2 adj PC.
  eapply DPcoupl_eq_elim_dp.
  eapply dp_coupl_seq_comp. 3: eassumption.
  - intros a1' a2' adj'. apply DPCoupl_complete. intros.
    eapply dp_f. done.
  - intros b ???.
    apply DPCoupl_complete. intros.
    eapply (dp_g b). done.
Qed.

Lemma metric_comp_laplace' {DB : Type} (dDB : DB -> DB -> R) (k : nat) f :
  c_sensitive dDB (λ x y, IZR (Z.abs (x - y))) f (INR k) ->
  ∀ ε, diffpriv_pure dDB (λ x, laplace ε (f x)) (ε * (INR k)).
Proof.
  intros fsens ε.
  apply Mcoupl_diffpriv. intros.

  opose proof (Mcoupl_laplace ε (f a1) (f a2) 0 (Z.of_nat k) _).
  {
    unfold c_sensitive in fsens.
    specialize (fsens a1 a2).
    apply le_IZR.
    etrans. 1: apply fsens.
    replace (IZR (Z.of_nat k)) with ((IZR (Z.of_nat k)) * 1) by lra.
    rewrite -INR_IZR_Zofnat.
    apply Rmult_le_compat_l ; try done.
    qify_r ; zify_q ; lia.
  }
  eapply Mcoupl_mono.
  5: apply H0.
  all: try intuition real_solver.
  rewrite -INR_IZR_Zofnat.
  lra.
Qed.

Definition pos_div (x : posreal) (y : nat) : y > 0 -> posreal.
  intros. pose (cond_pos x). exists (x / (INR y)). apply Rdiv_lt_0_compat ; real_solver.
Defined.

Lemma metric_comp_laplace {DB : Type} (dDB : DB -> DB -> R) (k : nat) (Hk : k > 0) f :
  c_sensitive dDB (λ x y, IZR (Z.abs (x - y))) f (INR k) ->
  ∀ ε, diffpriv_pure dDB (λ x, laplace (pos_div ε k Hk) (f x)) ε.
Proof.
  intros fsens ε.
  replace (pos ε) with ((pos_div ε k Hk) * (INR k)).
  2: rewrite /pos_div ; simpl ; field ; lra.
  eapply metric_comp_laplace'.
  done.
Qed.


(* Print Assumptions dp_postprocessing.
   Print Assumptions dp_seq_comp.
   Print Assumptions metric_comp_laplace. *)
