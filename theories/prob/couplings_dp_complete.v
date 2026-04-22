From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Import couplings_exp couplings_dp differential_privacy.

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

(** [/ r >= 0] when [r >= 0]. *)
Local Lemma Rinv_0_le (r : R) : 0 <= r -> 0 <= / r.
Proof.
  intros Hr.
  destruct (decide (r = 0)) as [->|Hne].
  - rewrite Rinv_0. lra.
  - left. apply Rinv_pos. lra.
Qed.

(** ** Indicator series monotonicity *)

Lemma SeriesC_indicator_le `{Countable A} (μ : distr A) (P Q : A -> Prop) :
  (∀ a, P a -> Q a) ->
  SeriesC (λ a, if @bool_decide (P a) (make_decision _) then μ a else 0) <=
    SeriesC (λ a, if @bool_decide (Q a) (make_decision _) then μ a else 0).
Proof.
  intros HPQ. apply SeriesC_le.
  - intro a. split.
    + destruct (bool_decide (P a)); [apply pmf_pos | lra].
    + case_bool_decide as HP; case_bool_decide as HQ; try lra.
      * exfalso. exact (HQ (HPQ a HP)).
      * apply pmf_pos.
  - eapply ex_seriesC_le. 2: apply pmf_ex_seriesC.
    intro a. case_bool_decide; real_solver.
Qed.

(** ** Staircase approximation *)

(** [step_approx n u a] is the [1/n]-grid staircase approximation of [u a] from below:
      step_approx n u a = (1/n) * #{k ∈ {0,...,n−1} | (k+1)/n <= u a}. *)
Definition step_approx `{Countable A} (n : nat) (u : A -> R) : A -> R :=
  λ a,
    / INR n *
      sum_f_R0 (λ k, if @bool_decide (INR (S k) / INR n <= u a) (make_decision _) then 1 else 0) (pred n).

Lemma ex_seriesC_sum_f_R0 `{Countable A} (F : nat -> A -> R) n :
  (∀ k, (k <= n)%nat -> ex_seriesC (F k)) ->
  ex_seriesC (λ a, sum_f_R0 (λ k, F k a) n).
Proof.
  intros HF. induction n as [|n IHn].
  - simpl. replace (λ a : A, F 0%nat a) with (F 0%nat) by done.
    exact (HF 0%nat (Nat.le_refl _)).
  - setoid_rewrite tech5.
    eapply ex_seriesC_ext.
    2: apply ex_seriesC_plus.
    + intros a. done.
    + apply IHn. intros k Hk. apply HF. lia.
    + replace (λ a : A, F (S n) a) with (F (S n)) by done. apply HF. lia.
Qed.

Lemma SeriesC_fin_sum `{Countable A} (F : nat -> A -> R) n :
  (∀ k, (k <= n)%nat -> ex_seriesC (F k)) ->
  SeriesC (λ a, sum_f_R0 (λ k, F k a) n) = sum_f_R0 (λ k, SeriesC (F k)) n.
Proof.
  intros HF. induction n as [|n IHn].
  - simpl. replace (λ a : A, F 0%nat a) with (F 0%nat) by done. done.
  - rewrite tech5 SeriesC_plus.
    + rewrite IHn //. intros k Hk. apply HF. lia.
    + apply ex_seriesC_sum_f_R0. intros k Hk. apply HF. lia.
    + apply HF. lia.
Qed.

Lemma SeriesC_step_approx `{Countable A} (μ : distr A) (n : nat) (u : A -> R) :
  (0 < n)%nat ->
  SeriesC (λ a, μ a * step_approx n u a) =
  / INR n *
    sum_f_R0 (λ k, SeriesC (λ a, if @bool_decide (INR (S k) / INR n <= u a) (make_decision _) then μ a else 0))
      (pred n).
Proof.
  intro Hn. rewrite /step_approx.
  trans (SeriesC
           (λ a, / INR n * (μ a * sum_f_R0 (λ k, if @bool_decide (INR (S k) / INR n <= u a) (make_decision _) then 1 else 0) (pred n)))).
  { apply SeriesC_ext. intros. lra. }
  rewrite SeriesC_scal_l. f_equal.
  set (F := λ k a, if @bool_decide (INR (S k) / INR n <= u a) (make_decision _) then μ a else 0).
  rewrite -(SeriesC_fin_sum F (pred n)).
  2:{ intros k _. eapply ex_seriesC_le. 2: apply pmf_ex_seriesC.
      intro a. rewrite /F. case_bool_decide; real_solver. }
  apply SeriesC_ext. intro a. rewrite /F scal_sum.
  apply sum_eq. intros k.
  destruct (@bool_decide (INR (S k) / INR n <= u a) (make_decision _)); simpl; lra.
Qed.

Lemma step_approx_le `{Countable A} (n : nat) (u v : A -> R) :
  (∀ a, u a <= v a) -> ∀ a, step_approx n u a <= step_approx n v a.
Proof.
  intros Huv a. rewrite /step_approx.
  apply Rmult_le_compat_l. { apply Rinv_0_le. apply pos_INR. }
  apply sum_growing. intro k.
  destruct (bool_decide (INR (S k) / INR n <= u a)) eqn:Hu;
  destruct (bool_decide (INR (S k) / INR n <= v a)) eqn:Hv; simpl; try lra.
  exfalso. apply bool_decide_eq_true_1 in Hu. apply bool_decide_eq_false_1 in Hv.
  apply Hv. etrans ; [eassumption | apply Huv].
Qed.

(** ** Threshold counting and its closed form *)

(** [threshold_count n x] = #{k ∈ {0,...,n-1} | (k+1)/n <= x}. *)
Definition threshold_count (n : nat) (x : R) : R :=
  sum_f_R0 (λ k, if @bool_decide (INR (S k) / INR n <= x) (make_decision _) then 1 else 0) (pred n).

Lemma threshold_bool_iff (n k : nat) (x : R) :
  (0 < n)%nat -> 0 <= x <= 1 -> (k <= pred n)%nat ->
  (INR (S k) / INR n <= x <-> (Z.of_nat (S k) <= up (INR n * x) - 1)%Z).
Proof.
  intros Hn Hx Hk.
  set (r := INR n * x).
  assert (HnR : 0 < INR n) by (apply lt_0_INR; lia).
  destruct (archimed r) as [Hup_gt Hup_gap].
  split.
  - intros Hthr.
    assert (Hmul : INR (S k) <= r).
    { rewrite /r. apply (Rmult_le_reg_l (INR n)). 1: lra.
      apply Rmult_le_compat_l. 1: lra.
      rewrite Rmult_comm. apply Rle_div_l. 1: lra. done. }
    assert (Hlt : INR (S k) < IZR (up r)) by lra.
    rewrite INR_IZR_INZ in Hlt. apply lt_IZR in Hlt.
    lia.
  - intros Hz.
    assert (Hle : IZR (Z.of_nat (S k)) <= IZR (up r - 1)) by (apply IZR_le; exact Hz).
    assert (Hmul : INR (S k) <= r).
    { rewrite INR_IZR_INZ. etrans. 1: exact Hle. rewrite minus_IZR. lra. }
    rewrite /r in Hmul. apply (Rmult_le_reg_l (INR n)). 1: lra.
    apply Rmult_le_compat_l. 1: lra.
    apply Rle_div_l. 1: lra. lra.
Qed.

Lemma sum_prefix_ones (m N : nat) :
  (m <= S N)%nat ->
  sum_f_R0 (λ k, if @bool_decide (S k <= m)%nat (make_decision _) then 1 else 0) N = INR m.
Proof.
  intros Hm. induction N as [|N IHN].
  - destruct m; simpl in *. { case_bool_decide ; auto ; lia. }
    destruct m; case_bool_decide ; intuition lia.
  - rewrite tech5.
    destruct (decide (S (S N) <= m)%nat) as [Hlast|Hlast].
    + assert (m = S (S N)) by lia. subst.
      rewrite bool_decide_eq_true_2. 2: lia.
      trans (sum_f_R0 (λ _ : nat, 1) N + 1).
      { f_equal. apply sum_eq. intros k Hk. rewrite bool_decide_eq_true_2 //. lia. }
      rewrite sum_cte. real_solver.
    + rewrite IHN. 2: lia.
      rewrite bool_decide_eq_false_2. 2: lia. lra.
Qed.

(** [threshold_count n x = up(n*x) - 1] for [x ∈ [0,1]]. *)
Lemma threshold_count_closed (n : nat) (x : R) :
  (0 < n)%nat -> 0 <= x <= 1 ->
  threshold_count n x = IZR (up (INR n * x) - 1).
Proof.
  intros Hn Hx. rewrite /threshold_count.
  set (m := Z.to_nat (up (INR n * x) - 1)).
  assert (Hm_nonneg : (0 <= up (INR n * x) - 1)%Z).
  { destruct (archimed (INR n * x)) as [Hgt _].
    apply Z.sub_nonneg.
    destruct (Z_lt_ge_dec (up (INR n * x)) 1) as [Hz|Hz].
    - exfalso. assert (IZR (up (INR n * x)) <= 0) as Hle by (apply IZR_le; lia).
      assert (Hnx : (0 <= INR n * x)%R) by real_solver. lra.
    - lia. }
  rewrite (sum_eq _ (λ k, if @bool_decide (S k <= m)%nat (make_decision _) then 1 else 0) (pred n)).
  2:{ intros k Hk.
      destruct (@bool_decide (INR (S k) / INR n <= x) (make_decision _)) eqn:H1;
        destruct (@bool_decide (S k <= m)%nat (make_decision _)) eqn:H2; try done; exfalso.
      - apply bool_decide_eq_true_1 in H1. apply bool_decide_eq_false_1 in H2. apply H2.
        apply Nat2Z.inj_le. rewrite Z2Nat.id //.
        exact (proj1 (threshold_bool_iff n k x Hn Hx Hk) H1).
      - apply bool_decide_eq_false_1 in H1. apply bool_decide_eq_true_1 in H2. apply H1.
        apply (threshold_bool_iff n k x Hn Hx Hk).
        rewrite Nat2Z.inj_le Z2Nat.id // in H2. }
  assert (Hm_le_n : (m <= n)%nat).
  { apply Nat2Z.inj_le. rewrite Z2Nat.id //.
    destruct (archimed (INR n * x)) as [_ Hgap].
    assert (INR n * x <= INR n) as Hnx by real_solver.
    assert ((up (INR n * x) <= Z.of_nat n + 1)%Z) as Hup_leZ.
    { destruct (Z_le_gt_dec (up (INR n * x)) (Z.of_nat n + 1)) as [Hz|Hz]. { done. }
      exfalso.
      assert (IZR (Z.of_nat n + 1) < IZR (up (INR n * x)))%R.
      { apply IZR_lt. lia. }
      revert H.
      assert (IZR (Z.of_nat n + 1) = INR n + 1)%R as ->. 2: lra.
      rewrite plus_IZR. rewrite INR_IZR_INZ. lra.
    }
    lia.
  }
  rewrite (sum_prefix_ones m (pred n)).
  2: { destruct n; simpl in *; lia. }
  rewrite /m INR_IZR_INZ Z2Nat.id //.
Qed.

(** Sandwich bound: [x - 1/n ≤ (1/n) * threshold_count n x <= x]. *)
Lemma threshold_count_sandwich (n : nat) (x : R) :
  (0 < n)%nat -> 0 <= x <= 1 ->
  let m := threshold_count n x in
  x - / INR n <= / INR n * m <= x.
Proof.
  intros Hn Hx. rewrite threshold_count_closed //.
  destruct (archimed (INR n * x)) as [Hgt Hgap].
  assert (INR n > 0) as HnR by (apply lt_0_INR; lia).
  assert (INR n <> 0) as Hne by lra.
  split.
  - apply (Rmult_le_reg_l (INR n)). 1: lra.
    rewrite Rmult_minus_distr_l -Rmult_assoc Rinv_r // Rmult_1_l minus_IZR. lra.
  - apply (Rmult_le_reg_l (INR n)). 1: lra.
    rewrite -Rmult_assoc Rinv_r // Rmult_1_l minus_IZR. lra.
Qed.

(** ** Bounds on the staircase approximation *)

Lemma step_approx_bounds_strong `{Countable A} (n : nat) (u : A -> R) :
  (0 < n)%nat -> (∀ a, 0 <= u a <= 1) -> ∀ a, u a - / INR n <= step_approx n u a <= u a.
Proof.
  intros Hn Hu a. exact (threshold_count_sandwich n (u a) Hn (Hu a)).
Qed.

Lemma step_approx_bounds `{Countable A} (n : nat) (u : A -> R) :
  (0 < n)%nat -> (∀ a, 0 <= u a <= 1) -> ∀ a, 0 <= step_approx n u a <= u a.
Proof.
  intros Hn Hu a. split.
  - rewrite /step_approx. apply Rmult_le_pos. { apply Rinv_0_le. apply pos_INR. }
    apply cond_pos_sum. intros k. case_bool_decide; lra.
  - exact (step_approx_bounds_strong n u Hn Hu a).2.
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

(** ** Upper and lower bounds for the SeriesC of staircase approximations *)

Lemma SeriesC_step_approx_upper `{Countable A} (μ : distr A) (n : nat) (u : A -> R) :
  (0 < n)%nat -> (∀ a, 0 <= u a <= 1) ->
  SeriesC (λ a, μ a * step_approx n u a) <= SeriesC (λ a, μ a * u a).
Proof.
  intros Hn Hu. apply SeriesC_le.
  - intro a.
    destruct (step_approx_bounds_strong n u Hn Hu a) as [? Hub].
    split.
    + apply Rmult_le_pos. { apply pmf_pos. }
      apply (step_approx_bounds n u Hn Hu a).
    + exact (Rmult_le_compat_l _ _ _ (pmf_pos μ a) Hub).
  - eapply ex_seriesC_le. 2: apply (pmf_ex_seriesC μ).
    intro a.
    destruct (step_approx_bounds_strong n u Hn Hu a) as [? Hub]. real_solver.
Qed.

Lemma SeriesC_step_approx_lower `{Countable A} (μ : distr A) (n : nat) (u : A -> R) :
  (0 < n)%nat -> (∀ a, 0 <= u a <= 1) ->
  SeriesC (λ a, μ a * u a) - / INR n <= SeriesC (λ a, μ a * step_approx n u a).
Proof.
  intros Hn Hu.
  assert (0 <= / INR n <= 1) as Hc.
  { split.
    - apply Rinv_0_le. apply pos_INR.
    - apply Rmult_le_reg_l with (r := INR n). { apply lt_0_INR. lia. }
      rewrite Rmult_1_r Rinv_r. 2: apply not_0_INR; lia.
      rewrite INR_IZR_INZ. apply IZR_le. lia. }
  assert (ex_seriesC (λ a, μ a * u a)) as Hex_u.
  { apply pmf_ex_seriesC_mult_fn. exists 1. exact Hu. }
  assert (ex_seriesC (λ a, μ a * / INR n)) as Hex_c.
  { apply (ex_seriesC_scal_r _ (/ INR n)). apply pmf_ex_seriesC. }
  assert (ex_seriesC (λ a, μ a * step_approx n u a)) as Hex_step.
  {
    pose proof (pmf_ex_seriesC μ) as Hex.
    eapply ex_seriesC_le. 2: exact Hex.
    intros a. pose proof (step_approx_bounds n u Hn Hu a) as [Hlo Hhi].
    split.
    - apply Rmult_le_pos; [apply pmf_pos|exact Hlo].
    - replace (μ a) with (μ a * 1) at 2 by lra. apply Rmult_le_compat_l. 1: real_solver.
      etrans. 1: eassumption. apply Hu.
  }
  assert (SeriesC (λ a, μ a * u a) <= SeriesC (λ a, μ a * step_approx n u a + μ a * / INR n)) as Hsum.
  { apply SeriesC_le.
    2: apply ex_seriesC_plus; assumption.
    intro a.
    destruct (step_approx_bounds_strong n u Hn Hu a) as [Hlo ?].
    split; [real_solver | rewrite -Rmult_plus_distr_l; real_solver]. }
  rewrite SeriesC_plus // in Hsum.
  assert (SeriesC (λ a, μ a * / INR n) <= / INR n) as Hmass.
  2: lra.
  rewrite SeriesC_scal_r. etrans.
  2: right ; apply Rmult_1_l.
  apply Rmult_le_compat_r. 2: series. apply Hc.
Qed.

(** ** Completeness theorems *)

Lemma DPcoupl_complete
  `{Countable A, Countable B}
  (μ1 : distr A) (μ2 : distr B) (S : A -> B -> Prop)
  (ε δ : nonnegreal) :
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

Corollary DPcoupl_complete_eq `{Countable A} (μ1 μ2 : distr A) (ε δ : nonnegreal) :
  (∀ P, prob μ1 (λ a, bool_decide (P a)) <=
          exp ε * prob μ2 (λ a, bool_decide (P a)) + δ) ->
  DPcoupl μ1 μ2 eq ε δ.
Proof.
  intros h. apply DPcoupl_complete. intros P Q HPQ.
  etrans. { exact (h P). }
  apply Rplus_le_compat_r. apply Rmult_le_compat_l. { left. apply exp_pos. }
  apply SeriesC_indicator_le. intros a Ha. exact (HPQ a a eq_refl Ha).
Qed.
