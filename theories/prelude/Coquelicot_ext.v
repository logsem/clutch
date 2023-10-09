From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq.
From stdpp Require Import numbers.
From clutch.prelude Require Import base Reals_ext.
Import Hierarchy.

Local Open Scope R.

#[global] Instance Rbar_le_Transitive: Transitive Rbar_le.
Proof. intros ???. eapply Rbar_le_trans. Qed.
#[global] Instance Rbar_le_Reflexive: Reflexive Rbar_le.
Proof. intros ?. eapply Rbar_le_refl. Qed.
#[global] Instance Rbar_lt_Transitive: Transitive Rbar_lt.
Proof. intros ???. eapply Rbar_lt_trans. Qed.

Lemma Rbar_le_fin' x y: 0 <= y → Rbar_le x y → x <= real y.
Proof.
  rewrite /Rbar_le. destruct x => //=.
Qed.

Lemma Rbar_le_sandwich p q r :
  Rbar_le (Finite p) r ->
  Rbar_le r (Finite q) ->
  Finite (real r) = r.
Proof.
  intros Hp Hq.
  destruct r eqn:Hr; auto.
  - destruct Hq.
  - destruct Hp.
Qed.

Lemma Rbar_le_fin x y: 0 <= y → Rbar_le x (Finite y) → (real x) <= y.
Proof.
  rewrite /Rbar_le. destruct x => //=.
Qed.

Lemma rbar_le_finite (p : R) (q : Rbar) :
  is_finite q ->
  Rbar_le p q ->
  p <= real q.
Proof.
  intros Hq Hle.
  rewrite /is_finite/= in Hq.
  destruct q; auto; simplify_eq.
Qed.

Lemma finite_rbar_le (p : R) (q : Rbar) :
  is_finite q ->
  Rbar_le q p ->
  q <= real p.
Proof.
  intros Hq Hle.
  rewrite /is_finite/= in Hq.
  destruct q; auto; simplify_eq.
Qed.

Lemma rbar_le_rle (p : R) (q : R) :
  Rbar_le (Finite p) (Finite q) <-> Rle p q.
Proof.
  auto.
Qed.

Lemma is_finite_bounded (p q : R) (r : Rbar) :
  Rbar_le p r ->
  Rbar_le r q ->
  is_finite r.
Proof.
  intros H1 H2.
  rewrite /is_finite.
  destruct r eqn:Hr; auto.
  - destruct H2.
  - destruct H1.
Qed.

Lemma rbar_finite_real_eq (p : Rbar) :
  is_finite p ->
  Finite (real p) = p.
Proof.
  intro Hfin.
  destruct p; auto.
Qed.

Lemma rbar_le_finite_real r :
  Rbar_le (Finite 0) r ->
  Rbar_le (Finite (real r)) r.
Proof.
  intro Hpos.
  destruct r eqn:Heq; simpl; auto.
  apply Rle_refl.
Qed.

Lemma Rbar_plus_le_pos_l (a b c : Rbar) :
  Rbar_lt 0 c → Rbar_le a (Rbar_plus a c).
Proof.
  intros.
  rewrite <- (Rbar_plus_0_r a) at 1.
  apply Rbar_plus_le_compat; [ reflexivity | ].
  by apply Rbar_lt_le.
Qed.

Lemma eq_rbar_finite x y :
  Finite x = y → x = real(y).
Proof.
  intro Heq.
  destruct y; simplify_eq; auto.
Qed.

Lemma eq_rbar_finite' x y :
  x = Finite y → real x = y.
Proof.
  intro Heq.
  destruct x; simplify_eq; auto.
Qed.

Lemma Rbar_0_le_to_Rle x :
  Rbar_le 0 x → 0 <= x.
Proof.
  intro Hle.
  destruct x; simpl; auto; lra.
Qed.

Lemma Rbar_0_le_to_Rle' x :
  Rbar_le 0 (Finite x) → 0 <= x.
Proof.
  intro Hle; auto.
Qed.

Lemma rmult_finite (p q : R) :
  Finite (p * q) = Rbar_mult (Finite p) (Finite q).
Proof. reflexivity. Qed.

Lemma Rbar_le_opp (p q : Rbar) (r : R) :
  Rbar_le (Rbar_plus p r) q ↔ Rbar_le p (Rbar_plus q (Finite (-r))).
Proof.
  split.
  - intro H1.
    destruct p eqn:Hp;
      destruct q eqn:Hq;
      simpl in *; try lra.
  - intro H2.
    destruct p eqn:Hp;
      destruct q eqn:Hq;
      simpl in *; try lra.
Qed.

Lemma norm_dist_mid x y z: norm (x - y) <= norm (x - z) + norm (z - y).
Proof.
  replace (x - y) with ((x - z) + (z - y)) by field.
  etransitivity; last eapply norm_triangle.
  apply Rle_refl.
Qed.

Lemma sum_n_shift (a : nat → R) n :
  sum_n (λ m, a (S m)) n = sum_n a (S n) - a 0%nat.
Proof.
  rewrite sum_Sn /plus /=.
  induction n as [|n IH].
  - rewrite 2!sum_O /=. lra.
  - rewrite 2!sum_Sn /plus /= IH. lra.
Qed.

Lemma sum_n_shift' (a : nat → R) (n : nat) :
  sum_n a (S n) = sum_n (λ m : nat, a (S m)) n + a 0%nat.
Proof.
  rewrite sum_n_shift; lra.
Qed.

Lemma sum_n_Ropp (a : nat → R) n :
  sum_n (λ n, - a n) n = - sum_n a n.
Proof.
  revert a; induction n => a.
  - rewrite 2!sum_O //.
  - rewrite 2!sum_Sn /plus /= IHn. lra.
Qed.

Lemma sum_n_m_filter (a: nat → R) (P: nat → Prop) `{∀ x, Decision (P x)} n m :
  sum_n_m (λ n, if bool_decide (P n) then Rabs (a n) else 0) n m <= sum_n_m (Rabs ∘ a) n m.
Proof.
  apply sum_n_m_le => k.
  destruct (bool_decide (P k)) => //=; try nra.
  apply Rabs_pos.
Qed.

Lemma is_series_0 a :
  (∀ n, a n = 0) → is_series a 0.
Proof.
  intros Ha. apply (is_series_ext (λ x, 0)); auto.
  rewrite /is_series.
  apply (filterlim_ext (λ x, 0)).
  - intros m. rewrite sum_n_const Rmult_0_r //.
  - apply filterlim_const.
Qed.

Lemma Series_0 a:
  (∀ n, a n = 0) → Series a = 0.
Proof.
  intros Heq. apply is_series_unique, is_series_0. done.
Qed.

Lemma Series_le' :
  ∀ a b : nat → R, (∀ n : nat, a n <= b n) → ex_series a → ex_series b → Series a <= Series b.
Proof.
  intros a b Hle [av Hav] [bv Hbv].
  erewrite is_series_unique; [|done].
  erewrite is_series_unique; [|done].
  cut (Rbar_le av bv); auto.
  eapply @filterlim_le; eauto.
  - apply Proper_StrongProper, eventually_filter.
  - exists O => n Hn. by apply sum_n_m_le.
Qed.

Lemma is_lim_seq_pos a (v: R):
  (∀ n, 0 <= a n) →
  is_lim_seq a v →
  0 <= v.
Proof.
  rewrite /is_lim_seq => Hn; intros.
  cut (Rbar_le 0 v); first by auto.
  apply (@filterlim_le _ eventually _ (λ x, 0) a); auto.
  - exists O; intros.  auto.
  - apply filterlim_const.
Qed.

Lemma is_lim_seq_unique_series a v:
  is_series a v → Lim_seq (sum_n a) = v.
Proof.
  intros. apply is_lim_seq_unique. rewrite //=.
Qed.

Lemma is_series_partial_pos a n v:
  (∀ n, 0 <= a n) →
  is_series a v →
  sum_n a n <= v.
Proof.
  intros Hpos His_series.
  assert (Hpos' : ∀ n : nat, 0 <= sum_n a n).
  { intros n'. induction n' => //=; rewrite ?sum_O ?sum_Sn; eauto.
    specialize (Hpos (S n')). rewrite /plus//=. nra. }
  replace (sum_n a n) with (real (sum_n a n)) by auto.
  rewrite -(is_series_unique _ _ His_series).
  eapply Rbar_le_fin'.
  - case_eq (Lim_seq (sum_n a)) => //=; try nra.
    intros r Heq.
    rewrite /is_series in His_series.
    assert (ex_lim_seq (sum_n a)).
    { exists v. eauto. }
    eapply is_lim_seq_pos; eauto.
    rewrite -Heq. apply Lim_seq_correct; eauto.
  -  rewrite -Lim_seq_const.
     case_eq (Lim_seq (sum_n a)) => //=; try nra.
     * intros r Heq. rewrite -Heq.
       apply Lim_seq_le_loc. exists n.
       intros m; induction 1.
       ** nra.
       ** rewrite sum_Sn /plus//=. specialize (Hpos (S m)). nra.
     * intros Heq_infty. apply is_lim_seq_unique_series in His_series. exfalso.
       rewrite Heq_infty in His_series. congruence.
     * intros Heq_infty. apply is_lim_seq_unique_series in His_series. exfalso.
       rewrite Heq_infty in His_series. congruence.
Qed.

Lemma is_series_singleton_hd v :
  is_series (λ n, if bool_decide (n = 0)%nat then v else 0) v.
Proof.
  apply is_series_decr_1=>/=.
  rewrite plus_opp_r.
  by apply is_series_0.
Qed.

Lemma is_series_singleton m v :
  is_series (λ n, if bool_decide (n = m) then v else 0) v.
Proof.
  induction m.
  - apply is_series_singleton_hd.
  - apply is_series_decr_1=>/=.
    rewrite opp_zero plus_zero_r.
    eapply is_series_ext; [|done].
    intros ? => //=.
    do 2 case_bool_decide; auto with lia.
Qed.

Lemma Series_bump m v :
  Series (λ n, if bool_decide (n = m) then v else 0) = v.
Proof.
  apply is_series_unique, is_series_singleton.
Qed.

Lemma ex_series_singleton (m : nat) v :
  ex_series (λ (n : nat), if bool_decide (n = m) then v else 0).
Proof. eexists. eapply is_series_singleton. Qed.

Lemma Series_singleton (m : nat) (v : R) :
  Series (λ n, if bool_decide (n = m) then v else 0) = v.
Proof. apply is_series_unique, is_series_singleton. Qed.

Lemma ex_series_leq N v :
  ex_series (λ n, if bool_decide (n < N)%nat then v else 0).
Proof.
  induction N as [|N IHN].
  - eexists; by apply is_series_0.
  - eapply ex_series_ext; last first.
    + eapply (ex_series_plus _ _ IHN (ex_series_singleton N v)).
    + intro n. simpl. rewrite /plus /=.
      repeat case_bool_decide; lra || lia.
Qed.

Lemma SeriesC_leq (N : nat) (v : R) :
  Series (λ (n : nat), if bool_decide (n < N)%nat then v else 0) = INR N * v.
Proof.
  induction N as [|N IHN].
  - rewrite Series_0 //=; lra.
  - assert (INR (S N) = (INR N + 1)) as ->; [apply S_INR | ].
    rewrite Rmult_plus_distr_r Rmult_1_l.
    rewrite -IHN.
    rewrite -(Series_singleton (N)%nat v).
    erewrite <- Series_plus; [ | apply ex_series_leq | apply ex_series_singleton].
    apply Series_ext; intro n.
    repeat case_bool_decide; simplify_eq; try (lra || lia).
    rewrite Rplus_0_l.
    apply Series_singleton.
Qed.

Lemma sum_n_partial_pos a :
  (∀ n, 0 <= a n) →
  ∀ n : nat, 0 <= sum_n a n.
Proof.
  intros Hpos n'; induction n' => //=; rewrite ?sum_O ?sum_Sn; eauto.
  specialize (Hpos (S n')). rewrite /plus //=. nra.
Qed.

Lemma is_series_chain s1 s2 v :
  is_series s2 (Series s1) → is_series s1 v → is_series s2 v.
Proof.
  intros Hs2 Hs1. apply is_series_unique in Hs1. rewrite -Hs1. done.
Qed.

Lemma Series_correct' a v:
  Series a = v → ex_series a → is_series a v.
Proof. by intros <- ?; apply Series_correct. Qed.

#[global] Instance is_series_Proper:
  Proper (pointwise_relation nat (@eq R) ==> @eq R ==> iff) is_series.
Proof.
  intros ?? ? ?? ?; subst; split; eapply is_series_ext; eauto.
Qed.

#[global] Instance ex_series_Proper:
  Proper (pointwise_relation nat (@eq R) ==> iff) ex_series.
Proof.
  intros ?? ?; split; eapply ex_series_ext; eauto.
Qed.

#[global] Instance Series_Proper:
  Proper (pointwise_relation nat (@eq R) ==> eq) Series.
Proof.
  intros ?? ?; eapply Series_ext; eauto.
Qed.
