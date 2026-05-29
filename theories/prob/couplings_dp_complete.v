From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Import distribution couplings_exp couplings_dp differential_privacy.

(** * Completeness of DP couplings

      Every (ε,δ)-DP inequality can be witnessed by a DP coupling.
      The "only if" direction (soundness) is in [couplings_dp.v].
      This file proves the converse via a staircase approximation argument.
*)

Open Scope R.

(** Bounded variant of [sum_growing]: pointwise <= need only hold up to index [N]. *)
Local Lemma sum_f_R0_le (An Bn : nat → R) (N : nat) :
  (∀ k, (k <= N)%nat -> An k <= Bn k) ->
  sum_f_R0 An N <= sum_f_R0 Bn N.
Proof.
  intros H. induction N as [|N IHN].
  - simpl. apply H. lia.
  - rewrite !tech5. apply Rplus_le_compat.
    + apply IHN. intros k Hk. apply H. lia.
    + apply H. lia.
Qed.

(** ** Main staircase bound for the relational case *)

(** For [f,g] with [∀ a b, S a b → f a <= g b], the staircase approximation inherits the DP bound. *)
Lemma step_approx_bound_rel
  `{Countable A, Countable B}
  (μ1 : distr A) (μ2 : distr B) (S : A -> B -> Prop) (ε δ : R) :
  (∀ P Q : _ -> Prop,
      (∀ a b, S a b -> P a -> Q b) ->
      SeriesC (λ a, if @bool_decide (P a) (make_decision _) then μ1 a else 0) <=
        exp ε * SeriesC (λ b, if @bool_decide (Q b) (make_decision _) then μ2 b else 0) + δ) ->
  ∀ n f g,
    (0 < n)%nat ->
    (∀ a b, S a b -> f a <= g b) ->
    SeriesC (λ a, μ1 a * step_approx n f a) <=
      exp ε * SeriesC (λ b, μ2 b * step_approx n g b) + δ.
Proof.
  intros h n f g Hn Hfg.
  rewrite (SeriesC_step_approx μ1 n f Hn).
  rewrite (SeriesC_step_approx μ2 n g Hn).
  set (Tf := λ k,
         SeriesC (λ a, if @bool_decide (INR (Datatypes.S k) / INR n <= f a) (make_decision _) then μ1 a else 0)).
  set (Tg := λ k,
         SeriesC (λ b, if @bool_decide (INR (Datatypes.S k) / INR n <= g b) (make_decision _) then μ2 b else 0)).
  assert (Hk : ∀ k, (k <= pred n)%nat -> Tf k <= exp ε * Tg k + δ).
  { intros k _. eapply h. intros a b HS Hfa. exact (Rle_trans _ _ _ Hfa (Hfg a b HS)). }
  assert (Hs : sum_f_R0 Tf (pred n) <= sum_f_R0 (λ k, exp ε * Tg k + δ) (pred n)).
  { apply sum_f_R0_le. intros k Hkbound. exact (Hk k Hkbound). }
  assert (0 <= / INR n) as hn by (apply Rinv_0_le; apply pos_INR).
  assert (INR n <> 0) as Hne by (apply not_0_INR; lia).
  etrans. { apply Rmult_le_compat_l. { exact hn. } exact Hs. }
  (* Simplify: / n * sum_f (exp ε * Tg k + δ) = exp ε * (/ n * sum_f Tg k) + δ *)
  replace (/ INR n * sum_f_R0 (λ _ : nat, δ) (pred n)) with δ.
  2:{ erewrite sum_cte, Nat.lt_succ_pred => //. by field. }
  replace (/ INR n * sum_f_R0 (λ k, exp ε * Tg k) (pred n))
    with (exp ε * (/ INR n * sum_f_R0 Tg (pred n))).
  2:{
    rewrite -Rmult_assoc (Rmult_comm (exp ε)) Rmult_assoc scal_sum.
    transitivity (/ n * sum_f_R0 (λ k : nat, Tg k * exp ε) (pred n)).
    1: field ; apply not_0_INR ; lia.
    apply Rmult_eq_compat_l. apply sum_eq ; real_solver.
  }
  rewrite !scal_sum.
  trans (sum_f_R0 (λ i, exp ε * Tg i * / INR n + δ * / INR n) (pred n)).
  { right. apply sum_eq. intros. lra. }
  rewrite sum_plus sum_cte.
  apply Rplus_le_compat.
  - right. apply sum_eq. intros. lra.
  - erewrite Nat.lt_succ_pred => //. by field_simplify.
Qed.

(** ** Completeness theorems *)

Lemma DPcoupl_complete
  `{Countable A, Countable B}
  (μ1 : distr A) (μ2 : distr B) (S : A -> B -> Prop)
  (ε δ : R) :
  (∀ (P : A -> Prop) (Q : B -> Prop),
      (∀ a b, S a b -> P a -> Q b) ->
      prob μ1 (λ a, bool_decide (P a)) <=
        exp ε * prob μ2 (λ b, bool_decide (Q b)) + δ) ->
  DPcoupl μ1 μ2 S ε δ.
Proof.
  intros h f g Hf Hg Hfg.
  assert (∀ n, (0 < n)%nat ->
               SeriesC (λ a, μ1 a * step_approx n f a) <= exp ε * SeriesC (λ b, μ2 b * step_approx n g b) + δ) as Hstep.
  { intros n Hn. exact (step_approx_bound_rel μ1 μ2 S ε δ h n f g Hn Hfg). }
  assert (∀ n, (0 < n)%nat ->
               SeriesC (λ a, μ1 a * f a) - / INR n <= SeriesC (λ a, μ1 a * step_approx n f a)) as Hleft.
  { intros n Hn. exact (SeriesC_step_approx_lower μ1 n f Hn Hf). }
  assert (∀ n, (0 < n)%nat ->
               SeriesC (λ b, μ2 b * step_approx n g b) <= SeriesC (λ b, μ2 b * g b)) as Hright.
  { intros n Hn. exact (SeriesC_step_approx_upper μ2 n g Hn Hg). }
  (* combine: for all n, SeriesC (μ1 * f) - 1/n <= exp ε * SeriesC (μ2 * g) + δ *)
  assert (∀ n, (0 < n)%nat ->
               SeriesC (λ a, μ1 a * f a) - / INR n <= exp ε * SeriesC (λ b, μ2 b * g b) + δ) as Hnfinal.
  { intros n Hn.
    etrans. { exact (Hleft n Hn). }
    etrans. { exact (Hstep n Hn). }
    apply Rplus_le_compat_r. apply Rmult_le_compat_l. { left. apply exp_pos. }
    exact (Hright n Hn). }
  (* conclude by contradiction via archimedean property *)
  apply Rnot_gt_le. intro Hcontra.
  set (x := SeriesC (λ a, μ1 a * f a)).
  set (y := exp ε * SeriesC (λ b, μ2 b * g b) + δ).
  assert (0 < x - y) as Hgap by (fold x y in Hcontra; lra).
  destruct (archimed_cor1 (x - y) Hgap) as [m [Hm Hmpos]].
  fold x y in Hnfinal.
  pose proof (Hnfinal m Hmpos) as hnf. lra.
Qed.

Definition image_rel {A B} (S : A -> B -> Prop) (P : A -> Prop) : B -> Prop :=
  λ b, exists a, P a /\ S a b.

Corollary DPCoupl_complete_rel_image
  `{Countable A, Countable B}
  (μ1 : distr A) (μ2 : distr B) (S : A -> B -> Prop)
  (ε δ : nonnegreal) :
  (forall P,
      prob μ1 (λ a, bool_decide (P a))
      <=
        exp ε * prob μ2 (λ b, bool_decide (image_rel S P b)) + δ) ->
  DPcoupl μ1 μ2 S ε δ.
Proof.
  intros h.
  eapply DPcoupl_complete.
  intros P Q HPQ.
  etrans ; first apply h.
  apply Rplus_le_compat_r, Rmult_le_compat_l.
  1: left; apply exp_pos.
  rewrite /prob.
  apply SeriesC_indicator_le.
  intros b [a [Ha HS]].
  eapply HPQ. all: eauto.
Qed.

Corollary DPcoupl_complete_eq `{Countable A} (μ1 μ2 : distr A) (ε δ : R) :
  (∀ P, prob μ1 (λ a, bool_decide (P a)) <=
          exp ε * prob μ2 (λ a, bool_decide (P a)) + δ) ->
  DPcoupl μ1 μ2 eq ε δ.
Proof.
  intros h. apply DPcoupl_complete. intros P Q HPQ.
  etrans. { exact (h P). }
  apply Rplus_le_compat_r. apply Rmult_le_compat_l. { left. apply exp_pos. }
  apply SeriesC_indicator_le. intros a Ha. exact (HPQ a a eq_refl Ha).
Qed.

Corollary ARcoupl_complete
  `{Countable A, Countable B}
  (μ1 : distr A) (μ2 : distr B) (S : A -> B -> Prop)
  (δ : R) :
  (∀ (P : A -> Prop) (Q : B -> Prop),
      (∀ a b, S a b -> P a -> Q b) ->
      prob μ1 (λ a, bool_decide (P a)) <=
        prob μ2 (λ b, bool_decide (Q b)) + δ) ->
  ARcoupl μ1 μ2 S δ.
Proof.
  intros. apply couplings_dp.DPcoupl_to_ARcoupl.
  rewrite (eq_refl : 0 = (nonneg (mknonnegreal 0 _))).
  apply DPcoupl_complete.
  simpl.
  setoid_rewrite exp_0. setoid_rewrite Rmult_1_l. assumption.
Qed.
