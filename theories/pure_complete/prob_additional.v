From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable finite.
From clutch.prelude Require Export base stdpp_ext Reals_ext Coquelicot_ext Series_ext classical uniform_list fiber_bounds.
From clutch.prob Require Import distribution couplings couplings_app markov.
From clutch.pure_complete Require Import pure.

Local Open Scope R.

Lemma dzero_neq_dret `{Countable A} (a : A) :
  dzero ≠ dret a.
Proof.
  move => Ha.
  assert (0 = 1); try lra.
  rewrite -(dzero_0 a) Ha.
  by apply dret_1. 
Qed.

Lemma dret_ext_inv `{Countable A} (a a' : A) :
  dret a = dret a' ->
  a = a'.
Proof.
  intros.
  eapply dret_1.
  rewrite H0.
  by apply dret_1.
Qed.

Lemma pos_series_le_one `{Countable A} (f : A -> R) (x : A):
  (∀ y, 0 <= f y) ->
  ex_seriesC f ->
  f x <= SeriesC f.
Proof.
  intros.
  rewrite -(SeriesC_singleton_dependent).
  by apply SeriesC_filter_leq.
Qed.

Lemma dmap_one `{Countable A, Countable B} (μ : distr A) (f : A -> B) a b :
  μ a = 1 ->
  b = f a ->
  dmap f μ b = 1.
Proof.
  intros.
  apply pmf_1_eq_dret in H1.
  subst. 
  rewrite dmap_dret.
  by apply dret_1_1.
Qed.

Lemma SeriesC_0_nonneg `{Countable A} (f : A -> R):
  ex_seriesC f ->
  (∀ x, 0 <= f x) ->
  SeriesC f = 0 ->
  ∀ x, f x = 0.
Proof.
  intros ???.
  destruct (ExcludedMiddle (∀ x, f x = 0)); auto.
  pose proof (Classical_Pred_Type.not_all_ex_not _ _ H3) as (a & ?).
  assert (f a > 0). {
    specialize (H1 a). lra.
  }
  assert (f a <= 0). {
    rewrite -H2.
    apply pos_series_le_one; auto.
  }
  lra.
Qed.

Lemma dbind_det_inv1 `{Countable A, Countable B} (μ : distr A) (f : A -> distr B):
  SeriesC (dbind f μ) = 1 ->
  SeriesC μ = 1.
Proof.
  intros.
  rewrite dbind_mass in H1.
  apply Rle_antisym; auto.
  rewrite -H1.
  apply SeriesC_le; auto.
  intros.
  split.
  - apply Rmult_le_pos; auto.
  - rewrite -(Rmult_1_r (μ n)) Rmult_assoc. 
    apply Rmult_le_compat_l; auto; real_solver.
Qed.

Lemma dbind_det_inv2 `{Countable A, Countable B} (μ : distr A) (f : A -> distr B):
  SeriesC (dbind f μ) = 1 ->
  ∀ a, μ a > 0 ->  
  SeriesC (f a) = 1.
Proof.
  intros.
  apply dbind_det_inv1 in H1 as H3.
  rewrite dbind_mass in H1.
  rewrite -H1 in H3.
  assert (SeriesC (fun x => μ x * (1 - SeriesC (f x))) = 0). {
    erewrite SeriesC_ext. 
    2 : intros; by rewrite Rmult_minus_distr_l Rmult_1_r.
    rewrite SeriesC_minus; auto.
    { rewrite H3. real_solver. }
    apply (ex_seriesC_le _ μ); auto.
    split; try real_solver.
  }
  epose proof (SeriesC_0_nonneg _ _ _ H4 a).
  simpl in H5. 
  apply Rmult_integral in H5 as [H5 | H5]; lra.
  Unshelve.
  - apply (ex_seriesC_le _ μ); auto.
    split; try real_solver. 
    apply Rmult_le_pos; try real_solver. by apply Rle_0_le_minus. 
  - intros.
    simpl.
    apply Rmult_le_pos; try real_solver. by apply Rle_0_le_minus. 
Qed.

Definition is_det `{Countable A} (μ : distr A) :=
  ∃ a, μ = dret a.

Lemma is_det_bind `{Countable A, Countable B} (μ : distr A) (f : A -> distr B) :
  is_det μ ->
  (∀ a, μ a > 0 -> is_det (f a)) ->
  is_det (dbind f μ).
Proof.
  intros [a Ha] Hd.
  epose proof (Hd a _) as [b Hdb].
  exists b.
  apply pmf_1_eq_dret.
  rewrite dbind_unfold_pmf.
  rewrite Ha.
  pose proof (Expval_dret (fun x => f x b) a).
  unfold Expval in*.
  rewrite H1 Hdb.
  by apply dret_1.
  Unshelve.
  rewrite Ha.
  rewrite dret_1_1; auto; lra. 
Qed.

Lemma ssd_zero `{Countable A} (μ : distr A) P a:
  μ a = 0 ->
  ssd P μ a = 0.
Proof.
  intros.
  unfold pmf. simpl. 
  unfold ssd_pmf. 
  destruct (P a); auto.
Qed.

Definition ssdp `{Countable A} (P : A -> Prop) μ := 
  ssd (fun a => bool_decide (P a)) μ.

Lemma ARcoupl_ssdp_inv `{Countable A, Countable B} (μ1 : distr A) (μ2 : distr B) ɛ R P1 P2:
  ARcoupl (ssdp P1 μ1) (ssdp P2 μ2) R ɛ ->
  ARcoupl μ1 μ2 (λ a b, R a b ∧ P1 a ∧ P2 b) (ɛ + probp μ1 (λ a, ¬ P1 a)).
Proof.
  rewrite /ARcoupl.
  intros.
  epose proof (H1 (fun a => if bool_decide (P1 a) then f a else 0) (fun b => if bool_decide (P2 b) then g b else 1) _ _ _).
  erewrite (SeriesC_ext _ (λ a : A, ssdp P1 μ1 a * f a)) in H5.
  2 : {
    intros. case_bool_decide; auto.
    unfold ssdp, pmf. simpl. unfold ssd_pmf.
    simpl. case_bool_decide; real_solver.
  }
  erewrite (SeriesC_ext _ (λ b : B, ssdp P2 μ2 b * g b)) in H5.
  2 : {
    intros. case_bool_decide; auto.
    unfold ssdp, pmf. simpl. unfold ssd_pmf.
    simpl. case_bool_decide; real_solver.
  }

  erewrite (SeriesC_ext _ (λ a : A, (ssdp P1 μ1 a) * f a + (ssdp (λ a : A, ¬ P1 a) μ1 a) * f a)).
  2 : {
    intros.
    rewrite -Rmult_plus_distr_r /ssdp.
    replace (λ a : A, bool_decide (¬ P1 a)) with (λ a : A, negb (bool_decide (P1 a))). 2 : {
      apply functional_extensionality. intros.
      case_bool_decide; case_bool_decide; done. 
    }
    by rewrite -(ssd_sum _ μ1).
  }
  rewrite SeriesC_plus;
  try by eapply ex_expval_unit.
  etrans.
  {
    eapply Rplus_le_compat_r.
    apply H5.
  }
  rewrite -Rplus_assoc. 
  apply Rplus_le_compat.
  {
    apply Rplus_le_compat_r.
    apply SeriesC_le.
    2 : by eapply ex_expval_unit.
    intros. split.
    - apply Rmult_le_pos; real_solver.
    - apply Rmult_le_compat_r; try real_solver.
      unfold pmf at 1.
      simpl. unfold ssd_pmf.
      case_bool_decide; real_solver.
  }
  unfold probp.
  apply SeriesC_le.
  2 : by eapply ex_seriesC_filter_bool_pos.
  intros.
  split; try real_solver.
  unfold pmf at 1.
  simpl. rewrite /ssd_pmf.
  case_bool_decide; case_bool_decide; try real_solver.
  Unshelve.
  - intros. simpl. case_bool_decide; real_solver.
  - intros. simpl. case_bool_decide; real_solver.
  - intros. simpl. case_bool_decide; case_bool_decide; try real_solver. 
Qed.
