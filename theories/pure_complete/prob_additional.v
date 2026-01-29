From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable finite.
From clutch.prelude Require Export base stdpp_ext Reals_ext Coquelicot_ext Series_ext classical uniform_list.
From clutch.prob Require Import distribution couplings couplings_app markov.
From clutch.pure_complete Require Import pure fiber_bounds.

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

Lemma ex_expval_unit `{Countable A} (μ : distr A) (f : A -> R):
  (∀ a, 0 <= f a <= 1) ->
  ex_expval μ f.
Proof.
  intros.
  eapply ex_expval_le.
  - exact H0.
  - unfold ex_expval. 
    eapply ex_seriesC_ext.
    { intros. by rewrite Rmult_1_r. }
    done.
Qed.

Lemma ARcoupl_map_inv `{Countable A, Countable B, Countable A', Countable B'} 
  (μ1 : distr A) (μ2 : distr B) (f1 : A → A') (f2 : B → B') ψ ε :
  0 <= ε ->
  ARcoupl (dmap f1 μ1) (dmap f2 μ2) ψ ε -> 
  ARcoupl μ1 μ2 (fun x y =>  ψ (f1 x) (f2 y)) ε.
Proof.
  rewrite /ARcoupl.
  intro He.
  intros. 
  assert (∀ a, f a <= 1). {
    intros. by destruct (H4 a).
  } 
  assert (∀ b, 0 <= g b). {
    intros. by destruct (H5 b).
  } 
  set F := sup_fiber f1 f H7.
  set G := inf_fiber f2 g H8.
  epose proof (H3 F G _ _ _).
  Unshelve.
  2 : {
    unfold F. 
    apply sup_fiber_range.
  }
  2 : {
    unfold G. 
    apply inf_fiber_range.
  }
  2 : {
    intros a' b'.
    destruct (ExcludedMiddle (∃ a, f1 a = a')). 2 : {
      pose proof (not_exists_forall_not _ _ H9) as H9'.
      simpl in H9'.
      intros.
      rewrite /F sup_fiber_empty; auto.
      epose proof (inf_fiber_range _ _ _ _ ) as [??]. 
      apply H11.
    }
    destruct  (ExcludedMiddle (∃ b, b' = f2 b)). 2 : {
      pose proof (not_exists_forall_not _ _ H10) as H10'.
      simpl in H10'.
      intros.
      rewrite /G inf_fiber_empty; auto.
      epose proof (sup_fiber_range _ _ _ _ ) as [??]. 
      apply H13. 
    }
    destruct H9 as [a H9], H10 as [b H10].
    intros.
    eapply sup_fiber_is_lub.
    move => x [Hx | Hx]; subst; eauto.
    {
      epose proof (inf_fiber_range _ _ _ _ ) as [??]. 
      apply H9.
    }
    destruct Hx as [a0 [Ha0 Ha1]]; subst.
    eapply inf_fiber_is_glb.
    move => x [Hx | Hx]; subst; eauto.
    destruct Hx as [b0 [Hb0 Hb1]]; subst.
    apply H6.
    by rewrite Ha0 Hb0. 
  }
  epose proof (Expval_dmap μ1 f1 F _ _).
  epose proof (Expval_dmap μ2 f2 G _ _).
  unfold Expval in *.
  rewrite H11 H10 in H9.
  trans (SeriesC (λ a : A, μ1 a * (F ∘ f1) a)).
  { 
    apply SeriesC_le.
    2: { apply ex_expval_unit. intros. simpl. by apply sup_fiber_range. }
    intros.
    split.
    - apply Rmult_le_pos; real_solver. 
    - apply Rmult_le_compat_l; auto. simpl. 
      apply sup_fiber_is_lub. right. econstructor; eauto.
  }
  etrans.
  { apply H9. }
  apply Rplus_le_compat_r. 
  apply SeriesC_le.
  2: by apply ex_expval_unit.
  intros.
  split. 
  - apply Rmult_le_pos; try real_solver. 
    epose proof (inf_fiber_range _ _ _ _ ) as [??]. 
    apply H12.
  - apply Rmult_le_compat_l; auto. simpl. 
    apply inf_fiber_is_glb. right. econstructor; eauto. 
  Unshelve.
  + intros. epose proof (sup_fiber_range _ _ _ _ ) as [??]. 
    apply H10.
  + apply ex_expval_unit. intros. simpl. by apply sup_fiber_range. 
  + intros. epose proof (inf_fiber_range _ _ _ _ ) as [??]. 
    apply H11.
  + apply ex_expval_unit. intros. simpl. by apply inf_fiber_range. 
Qed.

Lemma DPcoupl_map_inv `{Countable A, Countable B, Countable A', Countable B'} 
  (μ1 : distr A) (μ2 : distr B) (f1 : A → A') (f2 : B → B') ψ ε δ :
  0 <= ε ->
  DPcoupl (dmap f1 μ1) (dmap f2 μ2) ψ ε δ -> 
  DPcoupl μ1 μ2 (fun x y =>  ψ (f1 x) (f2 y)) ε δ.
Proof.
  rewrite /DPcoupl.
  intro He.
  intros H3 f g H4 H5 H6. 
  assert (∀ a, f a <= 1). {
    intros. by destruct (H4 a).
  } 
  assert (∀ b, 0 <= g b). {
    intros. by destruct (H5 b).
  } 
  set F := sup_fiber f1 f H7.
  set G := inf_fiber f2 g H8.
  epose proof (H3 F G _ _ _).
  Unshelve.
  2 : {
    unfold F. 
    apply sup_fiber_range.
  }
  2 : {
    unfold G. 
    apply inf_fiber_range.
  }
  2 : {
    intros a' b'.
    destruct (ExcludedMiddle (∃ a, f1 a = a')). 2 : {
      pose proof (not_exists_forall_not _ _ H9) as H9'.
      simpl in H9'.
      intros.
      rewrite /F sup_fiber_empty; auto.
      epose proof (inf_fiber_range _ _ _ _ ) as [??]. 
      apply H11.
    }
    destruct (ExcludedMiddle (∃ b, b' = f2 b)). 2 : {
      pose proof (not_exists_forall_not _ _ H10) as H10'.
      simpl in H10'.
      intros.
      rewrite /G inf_fiber_empty; auto.
      epose proof (sup_fiber_range _ _ _ _ ) as [??]. 
      apply H13. 
    }
    destruct H9 as [a H9], H10 as [b H10].
    intros.
    eapply sup_fiber_is_lub.
    move => x [Hx | Hx]; subst; eauto.
    {
      epose proof (inf_fiber_range _ _ _ _ ) as [??]. 
      apply H9.
    }
    destruct Hx as [a0 [Ha0 Ha1]]; subst.
    eapply inf_fiber_is_glb.
    move => x [Hx | Hx]; subst; eauto.
    destruct Hx as [b0 [Hb0 Hb1]]; subst.
    apply H6.
    by rewrite Ha0 Hb0. 
  }
  epose proof (Expval_dmap μ1 f1 F _ _).
  epose proof (Expval_dmap μ2 f2 G _ _).
  unfold Expval in *.
  rewrite H11 H10 in H9.
  trans (SeriesC (λ a : A, μ1 a * (F ∘ f1) a)).
  { 
    apply SeriesC_le.
    2: { apply ex_expval_unit. intros. simpl. by apply sup_fiber_range. }
    intros.
    split.
    - apply Rmult_le_pos; real_solver. 
    - apply Rmult_le_compat_l; auto. simpl. 
      apply sup_fiber_is_lub. right. econstructor; eauto.
  }
  etrans.
  { apply H9. } 
  apply Rplus_le_compat_r. 
  apply Rmult_le_compat_l. 
  { specialize (exp_pos ε). lra. }
  apply SeriesC_le.
  2: by apply ex_expval_unit.
  intros.
  split. 
  - apply Rmult_le_pos; try real_solver. 
    epose proof (inf_fiber_range _ _ _ _ ) as [??]. 
    apply H12.
  - apply Rmult_le_compat_l; auto. simpl. 
    apply inf_fiber_is_glb. right. econstructor; eauto. 
  Unshelve.
  + intros. epose proof (sup_fiber_range _ _ _ _ ) as [??]. 
    apply H10.
  + apply ex_expval_unit. intros. simpl. by apply sup_fiber_range. 
  + intros. epose proof (inf_fiber_range _ _ _ _ ) as [??]. 
    apply H11.
  + apply ex_expval_unit. intros. simpl. by apply inf_fiber_range. 
Qed.

Lemma ARcoupl_ret_inv `{Countable A, Countable B} (a : A) (b : B) ψ ɛ :
  ɛ < 1 ->
  ARcoupl (dret a) (dret b) ψ ɛ ->
  ψ a b.
Proof.
  rewrite /ARcoupl.
  intros.
  destruct (ExcludedMiddle (ψ a b)); auto.
  epose proof (H2 (fun x => if bool_decide (x = a) then 1 else 0) (fun x => if bool_decide (x = b) then 0 else 1) _ _ _).
  epose proof (Expval_dret (fun x => if bool_decide (x = a) then 1 else 0) a).
  epose proof (Expval_dret (fun x => if bool_decide (x = b) then 0 else 1) b).
  unfold Expval in *. 
  rewrite H5 H6 in H4.
  case_bool_decide; case_bool_decide; try lra; done.
  Unshelve.
  - intros. simpl. case_bool_decide; split; lra.
  - intros. simpl. case_bool_decide; split; lra.
  - intros. simpl. 
    case_bool_decide; case_bool_decide; try lra.
    subst. done.
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
