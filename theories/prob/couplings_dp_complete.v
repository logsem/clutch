From Stdlib Require Import Reals Psatz.
From Stdlib.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Export base Coquelicot_ext Reals_ext stdpp_ext.
From clutch.prob Require Import couplings_exp couplings_dp differential_privacy.

Local Open Scope R.

Lemma SeriesC_indicator_le `{Countable A} (μ : distr A) (P Q : A -> Prop) :
  (forall a, P a -> Q a) ->
  Rle
  (SeriesC (fun a => if @bool_decide (P a) (make_decision _) then μ a else 0))
  (SeriesC (fun a => if @bool_decide (Q a) (make_decision _) then μ a else 0)).
Proof.
  intro HPQ.
  apply SeriesC_le.
  2:{ pose proof (pmf_ex_seriesC μ).
      eapply ex_seriesC_le. 2: eassumption.
      intros ; case_bool_decide ; real_solver.
  }
  intro a.
  destruct (bool_decide (P a)) eqn:HP;
  destruct (bool_decide (Q a)) eqn:HQ; simpl; try real_solver.
  - exfalso.
    apply bool_decide_eq_true_1 in HP.
    apply bool_decide_eq_false_1 in HQ.
    apply HQ. now apply HPQ.
Qed.

Definition step_approx `{Countable A} (n : nat) (u : A -> R) : A -> R :=
  fun a =>
    Rmult (/ INR n)%R
    (sum_f_R0
      (fun k =>
         if @bool_decide (INR (S k) / INR n <= u a)%R (make_decision _) then 1 else 0)
      (pred n)).

Lemma ex_seriesC_sum_f_R0 `{Countable A} (F : nat -> A -> R) n :
  (forall k, (k <= n)%nat -> ex_seriesC (F k)) ->
  ex_seriesC (fun a => sum_f_R0 (fun k => F k a) n).
Proof.
  intros HF.
  induction n as [|n IH].
  - simpl. replace (fun a : A => F 0%nat a) with (F 0%nat) by done.
    apply HF. lia.
  -
    setoid_rewrite tech5.
    eapply ex_seriesC_ext.
    2: {
      apply ex_seriesC_plus.
      + apply IH. intros k Hk. apply HF. lia.
      + apply HF. instantiate (1 := S n). lia.
    }
    intros a. simpl. lra.
Qed.

Lemma SeriesC_fin_sum `{Countable A} (F : nat -> A -> R) n :
  (forall k, (k <= n)%nat -> ex_seriesC (F k)) ->
  SeriesC (fun a => sum_f_R0 (fun k => F k a) n)
  =
  sum_f_R0 (fun k => SeriesC (F k)) n.
Proof.
  intros HF.
  induction n as [|n IH].
  - simpl. replace (fun a : A => F 0%nat a) with (F 0%nat) by done.
    done.
  - rewrite tech5.
    rewrite SeriesC_plus.
    + rewrite IH; [done|].
      intros k Hk. apply HF. lia.
    + apply ex_seriesC_sum_f_R0.
      intros k Hk. apply HF. lia.
    + apply HF. lia.
Qed.

Lemma SeriesC_step_approx `{Countable A} (μ : distr A) (n : nat) (u : A -> R) :
  (0 < n)%nat ->
  SeriesC (fun a => (μ a * step_approx n u a)%R)
  =
  Rmult (/ INR n)
  (sum_f_R0
    (fun k =>
       SeriesC (fun a =>
         if @bool_decide (INR (S k) / INR n <= u a)%R (make_decision _) then μ a else 0))
    (pred n)).
Proof.
  intro Hn.
  unfold step_approx.

  apply trans_eq with
    (SeriesC
       (fun a =>
          Rmult (/ n)
            (μ a *
               sum_f_R0
                 (fun k => if @bool_decide (S k / n <= u a)%R (make_decision _) then 1 else 0)
                 (pred n)))).
  1: apply SeriesC_ext ; intros ; lra.
  rewrite SeriesC_scal_l.
  apply Rmult_eq_compat_l.
  set (n' := pred n).
  set (F := (fun k a =>
       if @bool_decide (INR (S k) / INR n <= u a)%R (make_decision _) then μ a else 0)).
  opose proof (SeriesC_fin_sum F n') as h.
  rewrite -h.
  2: {
    intros k Hk.
    pose proof (pmf_ex_seriesC μ) as Hex.
    eapply ex_seriesC_le.
    2: exact Hex.
    intros a.
    unfold F ; destruct (bool_decide (INR (S k) / INR n <= u a)%R); simpl; real_solver.
  }
  apply SeriesC_ext.
  intros a.
  unfold F.
  rewrite scal_sum.
  apply sum_eq.
  intros k.
  destruct (bool_decide (INR (S k) / INR n <= u a)%R); simpl; lra.
Qed.

Lemma Rinv_0_le_compat (r : R) : 0 <= r -> 0 <= / r.
Proof.
  intros.
  rewrite -Rdiv_1_l.
  destruct (decide (r = 0)).
  1: subst ; compute. 1: right ; rewrite Rinv_0 ; lra.
  apply Rdiv_le_0_compat ; real_solver.
Qed.

Lemma step_approx_le `{Countable A} (n : nat) (u v : A -> R) :
  (forall a, u a <= v a) ->
  forall a, step_approx n u a <= step_approx n v a.
Proof.
  intro Huv.
  intro a.
  unfold step_approx.
  apply Rmult_le_compat_l. 1: apply Rinv_0_le_compat ; real_solver.
  apply sum_growing.
  (* apply sum_f_R0_le. *)
  intro k.
  destruct (bool_decide (INR (S k) / INR n <= u a)) eqn:Hu;
  destruct (bool_decide (INR (S k) / INR n <= v a)) eqn:Hv; simpl; try lra.
  exfalso.
  apply bool_decide_eq_true_1 in Hu.
  apply bool_decide_eq_false_1 in Hv.
  apply Hv.
  specialize (Huv a).
  lra.
Qed.

Lemma sum_f_R0_le :
  forall (An Bn:nat -> R) (N:nat),
    (forall n:nat, n <= N -> An n <= Bn n) -> sum_f_R0 An N <= sum_f_R0 Bn N.
Proof.
  intros ????.
  induction  N as [| N HrecN] ; intros.
  - simpl; apply H. done.
  - do 2 rewrite tech5.
    apply Rle_trans with (sum_f_R0 An N + Bn (S N)).
    + apply Rplus_le_compat_l; apply H. done.
    + do 2 rewrite <- (Rplus_comm (Bn (S N))).
      apply Rplus_le_compat_l; apply HrecN. intros. apply H. real_solver.
Qed.

Lemma step_approx_bound `{Countable A}
    (μ1 μ2 : distr A) (ε δ : R) :
  (forall P : A -> Prop,
    SeriesC (fun a => if @bool_decide (P a) (make_decision _) then μ1 a else 0)
      <= exp ε *
           SeriesC (fun a => if @bool_decide (P a) (make_decision _) then μ2 a else 0) + δ)
  ->
  forall n f g,
    (0 < n)%nat ->
    (forall a, f a <= g a) ->
    SeriesC (fun a => μ1 a * step_approx n f a)
      <=
    exp ε * SeriesC (fun a => μ2 a * step_approx n g a) + δ.
Proof.
  intros h n f g Hn Hfg.
  rewrite (SeriesC_step_approx μ1 n f Hn).
  rewrite (SeriesC_step_approx μ2 n g Hn).

  set (Tf := fun k =>
    SeriesC (fun a =>
      if @bool_decide (INR (S k) / INR n <= f a) (make_decision _) then μ1 a else 0)).
  set (Tg := fun k =>
    SeriesC (fun a =>
      if @bool_decide (INR (S k) / INR n <= g a) (make_decision _) then μ2 a else 0)).

  assert (Hk :
    forall k, (k <= pred n)%nat ->
      Tf k <= exp ε * Tg k + δ).
  {
    intros k Hkbound.
    unfold Tf, Tg.
    specialize (h (fun a => INR (S k) / INR n <= f a)).
    eapply Rle_trans; [exact h|].
    apply Rplus_le_compat_r.
    apply Rmult_le_compat_l.
    { left ; apply exp_pos. }
    apply SeriesC_indicator_le.
    intros a Hfa.
    specialize (Hfg a).
    lra.
  }

  (* Sum Hk over k = 0,...,pred n *)
  assert (Hs :
    sum_f_R0 Tf (pred n)
      <=
    sum_f_R0 (fun k => exp ε * Tg k + δ) (pred n)).
  {
    apply sum_f_R0_le.
    intros k.
    intros Hkbound.
    apply Hk. real_solver.
  }
  unshelve epose proof (Rinv_0_le_compat (INR n) _) as hn. 1: real_solver.
  eapply Rle_trans ; [eapply (Rmult_le_compat_l _ _ _ hn Hs)|].

  (* simplify the δ-part *)
  replace ((/ INR n) * sum_f_R0 (fun _ => δ) (pred n)) with δ.
  2:{
    set (sum_f_R0_const := sum_cte).
    rewrite sum_f_R0_const.
    erewrite Nat.lt_succ_pred. 2: done.
    field.
    (* split. *)
    - apply not_0_INR. lia.
    (* - lra. *)
  }

  (* simplify the exp ε part *)
  replace ((/ INR n) * sum_f_R0 (fun k => exp ε * Tg k) (pred n))
    with (exp ε * ((/ INR n) * sum_f_R0 Tg (pred n))).
  2:{
    (* rewrite sum_f_R0_mult_const. *)
    rewrite -Rmult_assoc. rewrite (Rmult_comm (exp ε)). rewrite Rmult_assoc.
    rewrite scal_sum.
    transitivity (/ n * sum_f_R0 (λ k : nat, Tg k * exp ε) (Init.Nat.pred n)).
    1: field ; apply not_0_INR ; lia.
    apply Rmult_eq_compat_l. apply sum_eq.
    intros.
    rewrite (Rmult_comm (exp ε)). done.
  }
  rewrite scal_sum.
  rewrite scal_sum.
  rewrite scal_sum.

  transitivity (sum_f_R0 (λ i : nat, ((exp ε * Tg i) * / n)  + (δ * / n)) (Init.Nat.pred n)).
  - right. apply sum_eq. intros. lra.
  - rewrite sum_plus. rewrite sum_cte.
    apply Rplus_le_compat.
    + right. apply sum_eq. intros. lra.
    + field_simplify. 2: apply not_0_INR ; lia.
      erewrite Nat.lt_succ_pred. 2: done. right. field. apply not_0_INR ; lia.
Qed.

Definition threshold_count (n : nat) (x : R) : R :=
  sum_f_R0
    (fun k =>
       if @bool_decide (INR (S k) / INR n <= x)%R (make_decision _) then 1 else 0)
    (pred n).

Lemma INR_IZR_Zofnat (m : nat) :
  INR m = IZR (Z.of_nat m).
Proof.
  rewrite INR_IZR_INZ. reflexivity.
Qed.

Lemma IZR_Zofnat_le (m n : nat) :
  (m <= n)%nat ->
  (IZR (Z.of_nat m) <= IZR (Z.of_nat n))%R.
Proof.
  intro Hmn.
  rewrite -INR_IZR_Zofnat.
  rewrite -INR_IZR_Zofnat.
  eapply le_INR.
  exact Hmn.
Qed.

Lemma IZR_Zofnat_lt (m n : nat) :
  (m < n)%nat ->
  (IZR (Z.of_nat m) < IZR (Z.of_nat n))%R.
Proof.
  intro Hmn.
  rewrite -!INR_IZR_Zofnat.
  apply lt_INR.
  exact Hmn.
Qed.

Lemma IZR_le_Zofnat_inv (m : nat) (z : Z) :
  (IZR (Z.of_nat m) <= IZR z)%R ->
  (Z.of_nat m <= z)%Z.
Proof.
  intro H.
  destruct (Z_le_gt_dec (Z.of_nat m) z) as [Hle|Hgt]; auto.
  exfalso.
  assert (IZR z < IZR (Z.of_nat m))%R.
  { apply IZR_lt. lia. }
  lra.
Qed.

Lemma IZR_lt_Zofnat_inv (m : nat) (z : Z) :
  (IZR (Z.of_nat m) < IZR z)%R ->
  (Z.of_nat m < z)%Z.
Proof.
  intro H.
  destruct (Z_lt_ge_dec (Z.of_nat m) z) as [Hlt|Hge]; auto.
  exfalso.
  assert (IZR z <= IZR (Z.of_nat m))%R.
  { apply IZR_le. lia. }
  lra.
Qed.

Lemma threshold_bool_iff (n k : nat) (x : R) :
  (0 < n)%nat ->
  0 <= x <= 1 ->
  (k <= pred n)%nat ->
  ((INR (S k) / INR n <= x)%R <->
   (Z.of_nat (S k) <= up (INR n * x) - 1)%Z).
Proof.
  intros Hn Hx Hk.
  set (r := INR n * x).
  assert (HnR : 0 < INR n) by (apply lt_0_INR; lia).
  destruct (archimed r) as [Hup_gt Hup_gap].
  split.
  - intro Hthr.
    assert (Hmul : INR (S k) <= r).
    {
      apply (Rmult_le_reg_l (INR n)); try lra.
      apply Rmult_le_compat_l. 1: lra.
      subst r.
      rewrite (Rmult_comm n x).
      apply Rle_div_l. 1: lra.
      done.
    }
    assert (Hup1 : IZR (up r) - 1 <= r) by lra.
    apply IZR_le_Zofnat_inv.

    assert (Hlt : INR (S k) < IZR (up r)).
    { lra. }
    rewrite INR_IZR_Zofnat in Hlt.
    apply IZR_lt_Zofnat_inv in Hlt.
    apply IZR_le.
    lia.
  - intro Hz.
    assert (Hle : IZR (Z.of_nat (S k)) <= IZR (up r - 1)).
    { apply IZR_le. exact Hz. }
    assert (Hup1 : IZR (up r) - 1 <= r) by lra.
    assert (Hmul : INR (S k) <= r).
    {
      rewrite -INR_IZR_Zofnat in Hle.
      etrans ; first eassumption.
      rewrite minus_IZR. done.
    }
    apply (Rmult_le_reg_l (INR n)); try lra.
    apply Rmult_le_compat_l. 1: lra.
    subst r.
    apply Rle_div_l. 1: lra.
    lra.
Qed.


Lemma sum_prefix_ones (m N : nat) :
  (m <= S N)%nat ->
  sum_f_R0 (fun k => if bool_decide (S k <= m)%nat then 1 else 0) N = INR m.
Proof.
  intros Hm.
  induction N as [|N IH].
  - destruct m; simpl in *; [reflexivity|].
    destruct m; intuition lia.
  - rewrite tech5.
    destruct (decide (S (S N) <= m)%nat) as [Hlast|Hlast].
    + assert (Hm' : m = S (S N)) by lia.
      subst m.
      rewrite bool_decide_eq_true_2. 2: by lia.
      set (F := (λ k : nat, if bool_decide (S k ≤ S (S N)) then 1 else 0)).
      pose proof (sum_eq
        F
        (fun _ : nat => 1)
        N) as h.
      rewrite h.
      2:{
        intros k Hk. unfold F.
        rewrite bool_decide_eq_true_2. 2: lia.
        reflexivity.
      }
      rewrite sum_cte.
      real_solver.
    + assert (Hm' : (m <= S N)%nat) by lia.
      rewrite IH. 2: exact Hm'.
      rewrite bool_decide_eq_false_2. 2: lia.
      real_solver.
Qed.

Lemma INR_Z2Nat (k : Z) :
  (0 <= k)%Z ->
  INR (Z.to_nat k) = IZR k.
Proof.
  intro Hk.
  replace (INR (Z.to_nat k)) with (IZR (Z.of_nat (Z.to_nat k))).
  2: symmetry; apply INR_IZR_INZ.
  rewrite Z2Nat.id. 2: by exact Hk.
  reflexivity.
Qed.

Lemma threshold_count_closed (n : nat) (x : R) :
  (0 < n)%nat ->
  0 <= x <= 1 ->
  threshold_count n x = IZR (up (INR n * x) - 1).
Proof.
  intros Hn Hx.
  unfold threshold_count.
  set (m := Z.to_nat (up (INR n * x) - 1)).


  assert (Hm_nonneg : (0 <= up (INR n * x) - 1)%Z).
  {
    destruct (archimed (INR n * x)) as [Hgt _].
    assert (Hnx : (0 <= INR n * x)%R).
    { real_solver. }
    apply Z.sub_nonneg.
    destruct (Z_lt_ge_dec (up (INR n * x)) 1) as [Hz|Hz].
    - exfalso.
      assert (IZR (up (INR n * x)) <= 0)%R.
      { apply IZR_le. lia. }
      lra.
    - lia.
  }

  rewrite (sum_eq
    _ (fun k => if bool_decide (S k <= m)%nat then 1 else 0)
    (pred n)).
  2:{
    intros k Hk.
    destruct (bool_decide (INR (S k) / INR n <= x)%R) eqn:H1;
    destruct (bool_decide (S k <= m)%nat) eqn:H2; simpl; try reflexivity;
    exfalso.
    - apply bool_decide_eq_true_1 in H1.
      apply bool_decide_eq_false_1 in H2.
      apply H2.
      unfold m.
      apply Nat2Z.inj_le.
      rewrite Z2Nat.id. 2: exact Hm_nonneg.
      apply (proj1 (threshold_bool_iff n k x Hn Hx Hk)); exact H1.
    - apply bool_decide_eq_false_1 in H1.
      apply bool_decide_eq_true_1 in H2.
      apply H1.
      apply (proj2 (threshold_bool_iff n k x Hn Hx Hk)).
      unfold m in H2.
      rewrite Nat2Z.inj_le in H2.
      rewrite Z2Nat.id in H2. 2: by exact Hm_nonneg.
      exact H2.
  }

  assert (Hm_le_n : (m <= n)%nat).
  {
    unfold m.
    apply Nat2Z.inj_le.
    rewrite Z2Nat.id.
    2: exact Hm_nonneg.
    destruct (archimed (INR n * x)) as [_ Hgap].
    assert (Hnx : (INR n * x <= INR n)%R) by real_solver.
    assert (Hup_le : (IZR (up (INR n * x)) <= INR n + 1)%R) by lra.

    assert (Hup_leZ : (up (INR n * x) <= Z.of_nat n + 1)%Z).
    {
      destruct (Z_le_gt_dec (up (INR n * x)) (Z.of_nat n + 1)) as [Hz|Hz]; auto.
      exfalso.
      assert (IZR (Z.of_nat n + 1) < IZR (up (INR n * x)))%R.
      { apply IZR_lt. lia. }
      revert H.
      assert (IZR (Z.of_nat n + 1) = INR n + 1)%R as ->. 2: lra.
      {
        rewrite plus_IZR.
        rewrite INR_IZR_Zofnat. lra. }
    }
    lia.
  }
  rewrite (sum_prefix_ones m (pred n)).
  2:{
    destruct n; simpl in *; lia.
  }
  unfold m.
  Set Printing Coercions.
  assert (forall k, (0 <= k)%Z -> INR (Z.to_nat k) = IZR k) as ->.
  3: exact Hm_nonneg. 2: reflexivity.
  intros.
  by apply INR_Z2Nat.
Qed.

Lemma threshold_count_sandwich (n : nat) (x : R) :
  (0 < n)%nat ->
  0 <= x <= 1 ->
  let m := threshold_count n x in
  x - / INR n <= / INR n * m <= x.
Proof.
  intros Hn Hx.
  rewrite threshold_count_closed.
  2,3: by assumption.
  destruct (archimed (INR n * x)) as [Hgt Hgap].
  split.
  - apply (Rmult_le_reg_l (INR n)); try (apply lt_0_INR; lia).
    rewrite Rmult_minus_distr_l.
    rewrite -Rmult_assoc Rinv_r. 2: (apply not_0_INR; lia).
    rewrite Rmult_1_l.
    replace (IZR (up (INR n * x) - 1)) with (IZR (up (INR n * x)) - 1).
    1: lra.
    rewrite minus_IZR. lra.
  - apply (Rmult_le_reg_l (INR n)); try (apply lt_0_INR; lia).
    rewrite -Rmult_assoc Rinv_r. 2: (apply not_0_INR; lia).
    rewrite Rmult_1_l.
    replace (IZR (up (INR n * x) - 1)) with (IZR (up (INR n * x)) - 1).
    2:{
      rewrite minus_IZR.
      simpl.
      ring.
    }
    lra.
Qed.


Lemma step_approx_bounds_strong `{Countable A} (n : nat) (u : A -> R) :
  (0 < n)%nat ->
  (forall a, 0 <= u a <= 1) ->
  forall a, u a - / INR n <= step_approx n u a <= u a.
Proof.
  intros Hn Hu a.
  unfold step_approx.
  apply threshold_count_sandwich; auto.
Qed.

Corollary step_approx_bounds `{Countable A} (n : nat) (u : A -> R) :
  (0 < n)%nat ->
  (forall a, 0 <= u a <= 1) ->
  forall a, 0 <= step_approx n u a <= u a.
Proof.
  intros Hn Hu a.
  split.
  - unfold step_approx.
    apply Rmult_le_pos.
    + apply Rinv_0_le_compat. apply pos_INR.
    + apply cond_pos_sum. intros k. destruct bool_decide; lra.
  - pose proof (step_approx_bounds_strong n u Hn Hu a) as [_ Hhi].
    exact Hhi.
Qed.

Lemma step_approx_bound_rel
  `{Countable A, Countable B}
  (μ1 : distr A) (μ2 : distr B) (S : A -> B -> Prop) (ε δ : R) :
  (forall P Q : _ -> Prop,
     (forall a b, S a b -> P a -> Q b) ->
     SeriesC (fun a => if @bool_decide (P a) (make_decision _) then μ1 a else 0)
       <=
       exp ε *
         SeriesC (fun b => if @bool_decide (Q b) (make_decision _) then μ2 b else 0) + δ)
  ->
  forall n f g,
    (0 < n)%nat ->
    (forall a b, S a b -> f a <= g b) ->
    SeriesC (fun a => μ1 a * step_approx n f a)
      <=
    exp ε * SeriesC (fun b => μ2 b * step_approx n g b) + δ.
Proof.
  intros h n f g Hn Hfg.
  rewrite (SeriesC_step_approx μ1 n f Hn).
  rewrite (SeriesC_step_approx μ2 n g Hn).

  set (Tf := fun k =>
    SeriesC (fun a =>
      if @bool_decide (INR (Datatypes.S k) / INR n <= f a) (make_decision _) then μ1 a else 0)).
  set (Tg := fun k =>
    SeriesC (fun b =>
      if @bool_decide (INR (Datatypes.S k) / INR n <= g b) (make_decision _) then μ2 b else 0)).

  assert (Hk :
    forall k, (k <= pred n)%nat ->
      Tf k <= exp ε * Tg k + δ).
  {
    intros k Hkbound.
    unfold Tf, Tg.
    eapply h.
    intros a b HS Hfa.
    specialize (Hfg a b HS).
    lra.
  }

  assert (Hs :
    sum_f_R0 Tf (pred n)
      <=
    sum_f_R0 (fun k => exp ε * Tg k + δ) (pred n)).
  {
    apply sum_f_R0_le.
    intros k Hkbound.
    apply Hk. real_solver.
  }

  unshelve epose proof (Rinv_0_le_compat (INR n) _) as hn.
  1: real_solver.
  eapply Rle_trans ; [eapply (Rmult_le_compat_l _ _ _ hn Hs)|].

  replace ((/ INR n) * sum_f_R0 (fun _ => δ) (pred n)) with δ.
  2:{
    set (sum_f_R0_const := sum_cte).
    rewrite sum_f_R0_const.
    erewrite Nat.lt_succ_pred. 2: done.
    field.
    apply not_0_INR. lia.
  }

  replace ((/ INR n) * sum_f_R0 (fun k => exp ε * Tg k) (pred n))
    with (exp ε * ((/ INR n) * sum_f_R0 Tg (pred n))).
  2:{
    rewrite -Rmult_assoc.
    rewrite (Rmult_comm (exp ε)).
    rewrite Rmult_assoc.
    rewrite scal_sum.
    transitivity (/ n * sum_f_R0 (λ k : nat, Tg k * exp ε) (pred n)).
    1: field ; apply not_0_INR ; lia.
    apply Rmult_eq_compat_l.
    apply sum_eq.
    intros.
    rewrite (Rmult_comm (exp ε)).
    done.
  }

  rewrite scal_sum.
  rewrite scal_sum.
  rewrite scal_sum.

  transitivity
    (sum_f_R0
       (fun i : nat => ((exp ε * Tg i) * / n) + (δ * / n))
       (pred n)).
  - right. apply sum_eq. intros. lra.
  - rewrite sum_plus. rewrite sum_cte.
    apply Rplus_le_compat.
    + right. apply sum_eq. intros. lra.
    + field_simplify. 2: apply not_0_INR ; lia.
      erewrite Nat.lt_succ_pred. 2: done.
      right. field. apply not_0_INR ; lia.
Qed.


Lemma SeriesC_step_approx_upper `{Countable A} (μ : distr A) (n : nat) (u : A -> R) :
  (0 < n)%nat ->
  (forall a, 0 <= u a <= 1) ->
  SeriesC (fun a => μ a * step_approx n u a)
  <=
  SeriesC (fun a => μ a * u a).
Proof.
  intros Hn Hu.
  apply SeriesC_le.
  2:{
    pose proof (pmf_ex_seriesC μ) as Hex.
    eapply ex_seriesC_le.
    2: exact Hex.
    intros a.
    destruct (step_approx_bounds_strong n u Hn Hu a) as [_ Hub].
    real_solver.
  }
  intros a.
  destruct (step_approx_bounds_strong n u Hn Hu a) as [_ Hub].
  real_solver_partial.
  2: apply Rmult_le_compat_l; [apply pmf_pos|].
  2: exact Hub.
  apply Rmult_le_pos. 1: real_solver.
  apply step_approx_bounds. 1: lia.
  intros. done.
Qed.

Lemma ex_seriesC_mul_bounded `{Countable A} (μ : distr A) (u : A -> R) :
  (forall a, 0 <= u a <= 1) ->
  ex_seriesC (fun a => μ a * u a).
Proof.
  intro Hu.
  pose proof (pmf_ex_seriesC μ) as Hex.
  eapply ex_seriesC_le.
  2: exact Hex.
  intros a.
  specialize (Hu a).
  split.
  - apply Rmult_le_pos; [apply pmf_pos|lra].
  - real_solver.
Qed.

Lemma ex_seriesC_mul_const_le_1 `{Countable A} (μ : distr A) (c : R) :
  0 <= c <= 1 ->
  ex_seriesC (fun a => μ a * c).
Proof.
  intros Hc.
  pose proof (pmf_ex_seriesC μ) as Hex.
  eapply ex_seriesC_le.
  2: exact Hex.
  intros a.
  split.
  - apply Rmult_le_pos; [apply pmf_pos|lra].
  - real_solver.
Qed.

Lemma SeriesC_mul_const `{Countable A} (μ : distr A) (c : R) :
  SeriesC (fun a => μ a * c) = c * SeriesC μ.
Proof.
  transitivity (SeriesC (fun a => c * μ a)).
  { apply SeriesC_ext. intro a. lra. }
  rewrite SeriesC_scal_l.
  reflexivity.
Qed.

Lemma SeriesC_step_approx_lower `{Countable A} (μ : distr A) (n : nat) (u : A -> R) :
  (0 < n)%nat ->
  (forall a, 0 <= u a <= 1) ->
  SeriesC (fun a => μ a * u a) - / INR n
  <=
  SeriesC (fun a => μ a * step_approx n u a).
Proof.
  intros Hn Hu.

  assert (Hc : 0 <= / INR n <= 1).
  {
    split.
    - apply Rinv_0_le_compat. left. apply lt_0_INR. lia.
    - apply Rmult_le_reg_l with (r := INR n).
      + apply lt_0_INR. lia.
      + rewrite Rmult_1_r.
        rewrite Rinv_r. 2: intro ; try real_solver.
        * destruct n ; try lia. qify_r ; zify_q ; lia.
        * assert (n = 0)%nat. 2: lia. by apply INR_eq.
  }

  assert (Hex_u : ex_seriesC (fun a => μ a * u a)).
  { apply ex_seriesC_mul_bounded. exact Hu. }

  assert (Hex_c : ex_seriesC (fun a => μ a * / INR n)).
  { apply ex_seriesC_mul_const_le_1. exact Hc. }

  assert (Hex_step : ex_seriesC (fun a => μ a * step_approx n u a)).
  {
    pose proof (pmf_ex_seriesC μ) as Hex.
    eapply ex_seriesC_le.
    2: exact Hex.
    intros a.
    pose proof (step_approx_bounds n u Hn Hu a) as [Hlo Hhi].
    split.
    - apply Rmult_le_pos; [apply pmf_pos|exact Hlo].
    - replace (μ a) with (μ a * 1) at 2 by lra. apply Rmult_le_compat_l. 1: real_solver.
      etrans. 1: eassumption. apply Hu.
  }

  assert (Hsum :
    SeriesC (fun a => μ a * u a)
    <=
    SeriesC (fun a => μ a * step_approx n u a + μ a * / INR n)).
  {
    apply SeriesC_le.
    2:{
      apply ex_seriesC_plus; assumption.
    }
    intro a.
    pose proof (step_approx_bounds_strong n u Hn Hu a) as [Hlo _].
    rewrite -Rmult_plus_distr_l.
    split ; real_solver.
  }

  rewrite SeriesC_plus in Hsum; [|exact Hex_step|exact Hex_c].

  assert (Hmass :
    SeriesC (fun a => μ a * / INR n) <= / INR n).
  {
    rewrite SeriesC_mul_const.
    destruct Hc as [Hc0 _].
    eapply (Rle_trans _ (/n * 1)).
    - apply Rmult_le_compat_l.
      + exact Hc0.
      + apply pmf_SeriesC.
    - right. ring.
  }

  lra.
Qed.

Lemma DPCoupl_complete_rel
  `{Countable A, Countable B}
  (μ1 : distr A) (μ2 : distr B) (S : A -> B -> Prop)
  (ε δ : nonnegreal) :
  (forall P Q : _ -> Prop,
     (forall a b, S a b -> P a -> Q b) ->
     prob μ1 (fun a => bool_decide (P a))
       <=
     exp ε * prob μ2 (fun b => bool_decide (Q b)) + δ) ->
  DPcoupl μ1 μ2 S ε δ.
Proof.
  intros h f g Hf Hg Hfg.

  assert (Hstep :
    forall n, (0 < n)%nat ->
      SeriesC (fun a => μ1 a * step_approx n f a)
      <=
      exp ε * SeriesC (fun b => μ2 b * step_approx n g b) + δ).
  {
    intros n Hn.
    eapply step_approx_bound_rel; eauto.
  }

  assert (Hleft :
    forall n, (0 < n)%nat ->
      SeriesC (fun a => μ1 a * f a) - / INR n
      <=
      SeriesC (fun a => μ1 a * step_approx n f a)).
  { intros n Hn; apply SeriesC_step_approx_lower; auto. }

  assert (Hright :
    forall n, (0 < n)%nat ->
      SeriesC (fun b => μ2 b * step_approx n g b)
      <=
      SeriesC (fun b => μ2 b * g b)).
  { intros n Hn; apply SeriesC_step_approx_upper; auto. }

  assert (Hnfinal :
    forall n, (0 < n)%nat ->
      SeriesC (fun a => μ1 a * f a) - / INR n
      <=
      exp ε * SeriesC (fun b => μ2 b * g b) + δ).
  {
    intros n Hn.
    eapply Rle_trans.
    - apply Hleft; exact Hn.
    - eapply Rle_trans.
      + apply Hstep; exact Hn.
      + apply Rplus_le_compat_r.
        apply Rmult_le_compat_l.
        * left; apply exp_pos.
        * apply Hright; exact Hn.
  }

  apply Rnot_gt_le.
  intro Hcontra.
  set (x := SeriesC (fun a => μ1 a * f a)).
  set (y := exp ε * SeriesC (fun b => μ2 b * g b) + δ).

  assert (Hxy : y < x).
  { apply Rnot_le_lt. fold x y in Hcontra. lra. }

  assert (Hgap : 0 < x - y).
  { lra. }

  destruct (archimed_cor1 (x - y) Hgap) as [m [Hm Hmpos]].
  specialize (Hnfinal m Hmpos).
  change (x - / INR m <= y) in Hnfinal.
  lra.
Qed.

Corollary DPCoupl_complete
  `{Countable A} (μ1 μ2 : distr A) (ε δ : nonnegreal) :
   (forall P,
      prob μ1 (fun a => bool_decide (P a))
        <=
      exp ε * prob μ2 (fun a => bool_decide (P a)) + δ) ->
   DPcoupl μ1 μ2 eq ε δ.
Proof.
  intros h.
  eapply DPCoupl_complete_rel.
  intros P Q HPQ.
  eapply Rle_trans.
  - apply h.
  - apply Rplus_le_compat_r.
    apply Rmult_le_compat_l.
    + left; apply exp_pos.
    + rewrite /prob.
      apply SeriesC_indicator_le.
      intros a Ha.
      eapply HPQ; [reflexivity|exact Ha].
Qed.
