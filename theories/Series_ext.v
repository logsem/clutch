From Coq Require Import Reals Psatz ssreflect Utf8.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Import tactics.
Import Hierarchy.

Open Scope R.

Global Instance : Transitive Rle.
Proof. rewrite /Transitive; eapply Rle_trans. Qed.

Lemma Rbar_le_fin' x y: 0 <= y → Rbar_le x y → Rle x (real y).
Proof.
  rewrite /Rbar_le. destruct x => //=.
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

Lemma sum_n_partial_pos a :
  (∀ n, 0 <= a n) →
   ∀ n : nat, 0 <= sum_n a n.
Proof.
  intros Hpos n'; induction n' => //=; rewrite ?sum_O ?sum_Sn; eauto.
  specialize (Hpos (S n')). rewrite /plus //=. nra.
Qed.
