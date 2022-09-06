From Coq Require Import Reals Psatz ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Import countable.
Import Hierarchy.

Section countable_sum.
  Context `{Countable A}.

  Implicit Types f g : A → R.

  Open Scope R.

  (** * Countable sums *)
  Definition countable_sum f :=
    λ n : nat, oapp f R0 (decode_nat n).

  Lemma countable_sum_0 f m :
    (∀ n, f n = 0) → countable_sum f m = 0.
  Proof. intros. rewrite /countable_sum. destruct (decode_nat _); eauto. Qed.

  Lemma countable_sum_ext f g m :
    (∀ n, f n = g n) → countable_sum f m = countable_sum g m.
  Proof. intros ?. rewrite /countable_sum. destruct (decode_nat _) => //=. Qed.

  Lemma countable_sum_le f g m :
    (∀ n, f n <= g n) → countable_sum f m <= countable_sum g m.
  Proof. intros ?. rewrite /countable_sum. destruct (decode_nat _) =>//=. lra. Qed.

  Lemma countable_sum_scal c f n :
    countable_sum (λ x, scal c (f x)) n = scal c (countable_sum f n).
  Proof.
    intros. rewrite //= /countable_sum /scal //= /mult //=.
    destruct (decode_nat _) => //=; nra.
  Qed.

  Lemma countable_sum_plus f g n :
    countable_sum (λ x, f x + g x) n = countable_sum f n + countable_sum g n.
  Proof.
    intros. rewrite //=/countable_sum; destruct (decode_nat) => //=. nra.
  Qed.

  Lemma countable_sum_Rabs f n :
    countable_sum (λ x, Rabs (f x)) n = Rabs (countable_sum f n).
  Proof.
    intros. rewrite //=/countable_sum; destruct (decode_nat _) => //=. rewrite Rabs_R0 //=.
  Qed.

  Lemma countable_sum_scal_l f c n :
    countable_sum (λ x, c * f x) n = c * countable_sum f n.
  Proof. apply countable_sum_scal. Qed.

  Lemma countable_sum_scal_r f c n :
    countable_sum (λ x, f x * c) n = countable_sum f n * c.
  Proof.
    intros. rewrite //=/countable_sum; destruct (decode_nat) => //=. nra. Qed.

  (* TODO: move *)
  Lemma is_series_0 a :
    (∀ n, a n = 0) → is_series a 0.
  Proof.
    intros Ha. apply (is_series_ext (λ x, 0)); auto.
    rewrite /is_series.
    apply (filterlim_ext (λ x, 0)).
    - intros m. rewrite sum_n_const Rmult_0_r //.
    - apply filterlim_const.
  Qed.

  (** * Series  *)
  Definition is_seriesC f := is_series (countable_sum f).
  Definition ex_seriesC f := ex_series (countable_sum f).
  Definition SeriesC f := Series (countable_sum f).

  Lemma is_seriesC_0 f :
    (∀ n, f n = 0) → is_seriesC f 0.
  Proof.
    intros ?. apply is_series_0=> n.
    rewrite /countable_sum/oapp. destruct (decode_nat _); auto.
  Qed.

  Lemma is_seriesC_ext f g l :
    (∀ n, f n = g n) → is_seriesC f l → is_seriesC f l.
  Proof.
    intros ?. apply is_series_ext=> n. by apply countable_sum_ext.
  Qed.

  Lemma ex_seriesC_ext f g :
    (∀ n, f n = g n) → ex_seriesC f → ex_seriesC g.
  Proof.
    intros ?. apply ex_series_ext=> n. by apply countable_sum_ext.
  Qed.

  Global Instance is_series_Proper:
    Proper (pointwise_relation nat (@eq R) ==> @eq R ==> iff) is_series.
  Proof.
    intros ?? ? ?? ?; subst; split; eapply is_series_ext; eauto.
  Qed.

  Global Instance ex_series_Proper:
    Proper (pointwise_relation nat (@eq R) ==> iff) ex_series.
  Proof.
    intros ?? ?; split; eapply ex_series_ext; eauto.
  Qed.

  Global Instance Series_Proper:
    Proper (pointwise_relation nat (@eq R) ==> eq) Series.
  Proof.
    intros ?? ?; eapply Series_ext; eauto.
  Qed.

  Global Instance countable_sum_Proper:
    Proper (pointwise_relation A (@eq R) ==> pointwise_relation nat (@eq R)) countable_sum.
  Proof.
    intros ?? ? x. rewrite /countable_sum. destruct (decode_nat _); eauto.
  Qed.

  Global Instance countable_sum_Proper' :
    Proper (pointwise_relation A (@eq R) ==> eq ==> eq) countable_sum.
  Proof.
    intros ?? ? ? ??. subst. eapply countable_sum_ext; eauto.
  Qed.

  Implicit Types P Q : A → bool.

  Lemma is_seriesC_filter_pos f P (v : R):
    (∀ n, f n >= 0) →
    is_seriesC f v →
    ex_seriesC (λ n, if P n then f n else 0).
  Proof.
    intros Hge Hconv.
    apply: ex_series_le; last by (exists v; eauto).
    intros n. rewrite /norm /= /abs /countable_sum /=.
    destruct (decode_nat _) as [x|] => //=.
    - destruct (P x); rewrite Rabs_right => //=; try nra.
      specialize (Hge x); nra.
    - rewrite Rabs_right; nra.
  Qed.

  Lemma is_seriesC_filter_impl f P Q (v : R):
    (∀ n, f n >= 0) →
    is_seriesC (λ n, if P n then f n else 0) v →
    (∀ n, Q n → P n) →
    ex_seriesC (λ n, if Q n then f n else 0).
  Proof.
    intros Hge Hconv Himp. apply ex_series_Rabs.
    apply: ex_series_le; last by (exists v; eauto).
    intros n. rewrite /norm//=/abs//=.
    rewrite /countable_sum//=.
    destruct (decode_nat _) as [x|] => //=.
    - specialize (Himp x); specialize (Hge x).
      destruct (P x), (Q x); rewrite Rabs_Rabsolu Rabs_right => //=; try nra.
      exfalso. by apply Himp.
    - rewrite Rabs_Rabsolu Rabs_right; nra.
  Qed.

  Lemma ex_seriesC_filter_impl f P Q :
    (∀ n, f n >= 0) →
    ex_seriesC (λ n, if P n then f n else 0) →
    (∀ n, Q n → P n) →
    ex_seriesC (λ n, if Q n then f n else 0).
  Proof. intros ? [? ?] ?. eapply is_seriesC_filter_impl; eauto. Qed.

  Lemma ex_seriesC_filter_pos f P :
    (∀ n, f n >= 0) →
    ex_seriesC f →
    ex_seriesC (λ n, if P n then f n else 0).
  Proof. intros ? [v His]. by eapply is_seriesC_filter_pos. Qed.

  Lemma is_seriesC_filter_union f P Q (v: R):
    (∀ n, f n >= 0) →
    is_seriesC (λ n, if P n || Q n then f n else 0) v →
    SeriesC (λ n, if P n then f n else 0) +
    SeriesC (λ n, if Q n then f n else 0) -
    SeriesC (λ n, if P n && Q n then f n else 0) = v.
  Proof.
    intros Hge Hexists.
    rewrite -Series_plus;
      try (eapply (is_seriesC_filter_impl _ _ _ _ Hge Hexists); eauto;
           try (intros n; destruct (P n), (Q n); auto)).
    rewrite -Series_minus;
      try (eapply (is_seriesC_filter_impl _ _ _ _ Hge Hexists); eauto;
           try (intros n; destruct (P n), (Q n); auto)).
    - rewrite -(is_series_unique _ v Hexists).
      apply Series_ext => n.
      rewrite /countable_sum//=.
      destruct (decode_nat _) as [x|] => //=; last by nra.
      destruct (P x) => //=; nra.
    - apply: (ex_series_le _ (countable_sum (λ n, scal 2 (if P n || Q n then f n else 0)))).
      + intros n.
        rewrite /countable_sum//=.
        rewrite /norm //= /abs //= /scal//= /mult/=.
        destruct (decode_nat _) as [x|] => //=.
        * specialize (Hge x).
          destruct (P x), (Q x) => //=; rewrite Rabs_right; nra.
        * rewrite Rabs_right; nra.
      + exists (scal 2 v).
        apply (is_series_ext _ _ _
                 (λ n, Logic.eq_sym (countable_sum_scal 2 (λ x, if P x || Q x then f x else 0) n))).
        by apply: is_series_scal.
  Qed.

  (* TODO: move *)
  Lemma Series_0 a: (∀ n, a n = 0) → Series a = 0.
  Proof.
    intros Heq. apply is_series_unique, is_series_0. done.
  Qed.

  Lemma SeriesC_0 f :
    (∀ x, f x = 0) → SeriesC f = 0.
  Proof. intros Heq0. apply Series_0=> ?. by apply countable_sum_0. Qed.

  Lemma SeriesC_ext f g :
    (∀ n, f n = g n) → SeriesC f = SeriesC g.
  Proof. intros Hext. apply Series_ext => // n. by apply countable_sum_ext. Qed.

  Lemma SeriesC_le f g :
    (∀ n, 0 <= f n <= g n) →
    ex_seriesC g →
    SeriesC f <= SeriesC g.
  Proof.
    intros Hrange Hex. apply Series_le => // n.
    rewrite /countable_sum.
    destruct (decode_nat _) => //=; nra.
  Qed.

  (* TODO: move *)
  Lemma Series_le' f g :
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

  Lemma SeriesC_le' f g :
    (∀ n, f n <= g n) →
    ex_seriesC f →
    ex_seriesC g →
    SeriesC f <= SeriesC g.
  Proof.
    intros ???. apply Series_le' => //= n. rewrite /countable_sum.
    destruct (decode_nat _) => //=. nra.
  Qed.

  Lemma SeriesC_scal_l f c :
    SeriesC (λ x, c * f x) = c * SeriesC f.
  Proof.
    intros. rewrite -Series_scal_l. apply Series_ext. apply countable_sum_scal_l.
  Qed.

  Lemma SeriesC_scal_r f c :
    SeriesC (λ x, f x * c) = Series (countable_sum f) * c.
  Proof.
    intros. rewrite -Series_scal_r. apply Series_ext. apply countable_sum_scal_r.
  Qed.

  Lemma ex_seriesC_le f g :
    (∀ n, 0 <= f n <= g n) →
    ex_seriesC g →
    ex_seriesC f.
  Proof.
    intros Hle Hex.
    eapply @ex_series_le; [|eauto].
    intros n. rewrite /norm//=/abs//=.
    rewrite -countable_sum_Rabs. apply countable_sum_le.
    intros x. destruct (Hle x); eauto. rewrite Rabs_right; eauto; nra.
  Qed.

  Lemma ex_seriesC_scal_l f c :
    ex_seriesC f →
    ex_series (countable_sum (λ x, c * f x)).
  Proof.
    intros. eapply ex_series_ext.
    { intros n. rewrite countable_sum_scal_l. done. }
    by eapply @ex_series_scal_l.
  Qed.

  Lemma ex_seriesC_scal_r f c :
    ex_seriesC f →
    ex_seriesC (λ x, f x * c).
  Proof.
    intros. eapply ex_series_ext.
    { intros n. rewrite countable_sum_scal_r. done. }
    apply: ex_series_scal_r; eauto.
  Qed.

  Lemma ex_seriesC_plus f g :
    ex_seriesC f →
    ex_seriesC g →
    ex_seriesC (λ x, f x + g x).
  Proof.
    intros. eapply ex_series_ext.
    { intros n. rewrite countable_sum_plus. done. }
    apply: ex_series_plus; eauto.
  Qed.

  Lemma is_seriesC_scal_l f c v :
    is_seriesC f v →
    is_seriesC (λ x, c * f x) (c * v).
  Proof.
    intros. eapply is_series_ext.
    { intros n. rewrite countable_sum_scal_l. done. }
    apply: is_series_scal_l; eauto.
  Qed.

  Lemma is_seriesC_scal_r f c v:
    is_seriesC f v →
    is_seriesC (λ x, f x * c) (v * c).
  Proof.
    intros. eapply is_series_ext.
    { intros n. rewrite countable_sum_scal_r. done. }
    apply: is_series_scal_r; eauto.
  Qed.

  Lemma is_seriesC_plus f g v1 v2:
    is_seriesC f v1 →
    is_seriesC g v2 →
    is_seriesC (λ x, f x + g x) (v1 + v2).
  Proof.
    intros. eapply is_series_ext.
    { intros n. rewrite countable_sum_plus. done. }
    apply: is_series_plus; eauto.
  Qed.

  Lemma ex_seriesC_Rabs f :
    ex_seriesC (λ x, Rabs (f x)) →
    ex_seriesC f.
  Proof.
    intros. eapply ex_series_Rabs.
    eapply ex_series_ext.
    { intros n. rewrite -countable_sum_Rabs. done. }
    eauto.
  Qed.

End countable_sum.
