From Coq Require Import Reals Psatz.
From Coquelicot Require Import Series Lim_seq Rbar Rcomplements.
From stdpp Require Export countable.
From clutch.prelude Require Import base Coquelicot_ext stdpp_ext classical.
From discprob.prob Require Import double.
Set Default Proof Using "Type*".
Import Hierarchy.

Open Scope R.

Lemma ex_series_eventually0 (a: nat → R):
  (∃ N, ∀ n, n ≥ N → a n = 0) → ex_series a.
Proof.
  intros (N & Hev0). apply: ex_series_Cauchy.
  rewrite /Cauchy_series => eps. exists N => n m Hlen Hlem.
  assert (Heq: sum_n_m a n m = 0).
  { rewrite /sum_n_m.
    rewrite (Iter.iter_nat_ext_loc _ _ _ (λ x, 0)).
    - rewrite /plus/zero//=/Iter.iter_nat Iter.iter_const; nra.
    - intros k (?&?). apply Hev0. lia. }
  rewrite /norm //= /abs //=. destruct eps =>//=. rewrite Heq Rabs_right; nra.
Qed.

Lemma mon_succ_to_mon (h : nat → R) :
  (∀ p, h p <= h (S p)) →
  (∀ m n, (m <= n)%nat → h m <= h n).
Proof.
  intros Hmon m.
  induction m; intro n; induction n.
  - intros; apply Rle_refl.
  - intro. apply (Rle_trans _ (h n)); auto with arith.
  - intro Haux.
    inversion Haux.
  - intro Haux.
    destruct (decide ((S m <= n)%nat)) as [Hle | Hgt].
    + apply (Rle_trans _ (h n)); auto with arith.
    + assert (S m = S n) as ->; [ | apply Rle_refl].
      assert ((n < S m)%nat); auto with arith.
      apply not_le; auto.
Qed.

Lemma partial_sum_pos (h : nat → R) p :
  (∀ n, 0 <= h n) →
  0 <= sum_n h p.
Proof.
  intros Hpos.
  rewrite /sum_n.
  induction p.
  - rewrite sum_n_n; auto.
  - rewrite sum_n_Sm; auto with arith.
    apply Rplus_le_le_0_compat; auto.
Qed.

Lemma partial_sum_elem (h : nat → R) p :
  (∀ n, 0 <= h n) →
  h p <= sum_n h p.
Proof.
  intros Hpos.
  rewrite /sum_n.
  induction p.
  - rewrite sum_n_n; auto.
    apply Rle_refl.
  - rewrite sum_n_Sm; auto with arith.
    assert (h (S p) = 0 + h (S p)) as Haux; try lra.
    rewrite {1}Haux.
    apply Rplus_le_compat; [apply partial_sum_pos | apply Rle_refl]; auto.
Qed.

Lemma partial_sum_mon (h : nat → R) p q :
  (∀ n, 0 <= h n) →
  p ≤ q →
  sum_n h p <= sum_n h q.
Proof.
  intros Hge Hpq.
  rewrite /sum_n.
  induction q.
  - assert (p = 0%nat); auto with arith.
    simplify_eq; done.
  - destruct (PeanoNat.Nat.le_gt_cases p q) as [H1 | H1].
    + specialize (IHq H1).
      rewrite sum_n_Sm; auto with arith.
      rewrite /plus /=.
      specialize (Hge (S q)).
      lra.
    + assert (p = S q) as ->; auto with arith.
      lra.
Qed.

Lemma is_series_ge0 (h : nat → R) r:
  (∀ n, 0 <= h n) →
  is_series h r →
  0 <= r.
Proof.
  intros Hge Hs.
  erewrite <- (Series_0 (λ y, 0)); auto.
  rewrite  <- (is_series_unique _ _ Hs).
  eapply (Series_le).
  { intro n; split; auto; lra. }
  rewrite /ex_series.
  exists r; auto.
Qed.

Lemma lim_is_sup (h: nat → R) r :
  (∀ n, 0 <= h n) →
  is_series h r →
  is_sup_seq (sum_n h) (Finite r).
Proof.
  intros Hge Hs.
  rewrite /is_sup_seq.
  pose proof (is_series_partial_pos h) as Hpart.
  pose proof (is_series_ge0 _ _ Hge Hs) as Hr.
  intro eps; split.
  - intro n.
    specialize (Hpart n r Hge Hs).
    rewrite /Rbar_lt.
    assert (eps > 0); try lra.
    pose proof (cond_pos eps); lra.
  - pose proof (Hs) as Hs'.
    specialize (Hs (ball r eps)).
    assert (∃ N : nat, ∀ n : nat, N ≤ n → ball r eps (sum_n h n)) as (N & HN).
    {apply Hs. exists eps. auto. }
    exists N; simpl.
    specialize (HN N (Nat.le_refl N)).
    specialize (Hpart N r Hge Hs').
    rewrite /ball /= /AbsRing_ball in HN.
    cut (r - (sum_n h N) < eps); try lra.
    rewrite abs_minus /abs /= in HN.
    assert (Rabs (minus r (sum_n h N)) = minus r (sum_n h N)) as Habs.
    { apply Rabs_right.
      rewrite /minus /plus /= /opp /=.
      lra. }
    rewrite Habs in HN.
    rewrite /minus /plus /= /opp /= in HN.
    lra.
Qed.

Lemma sup_is_lim (h: nat → R) r :
  (∀ n, 0 <= h n) →
  is_sup_seq (sum_n h) (Finite r) →
  is_series h r.
Proof.
  intros Hge Hsup.
  rewrite /is_sup_seq in Hsup.
  intros P (eps & Heps).
  rewrite /ball /= /AbsRing_ball in Heps.
  destruct (Hsup eps) as (HsupFor & (N & HsupN)).
  exists N; intros n Hn.
  specialize (HsupFor n).
  specialize (Heps (sum_n h n)).
  assert (sum_n h N <= sum_n h n) as HNn.
  { by apply partial_sum_mon. }
  apply Heps.
  rewrite /Rbar_lt in HsupFor.
  rewrite /Rbar_lt in HsupN.
  assert (r - eps < sum_n h n); [try lra | ].
  rewrite /abs /= /Rabs /minus /plus /= /opp /=.
  destruct Rcase_abs; lra.
Qed.

Lemma lim_is_sup' (h: nat → R) :
  (∀ n, 0 <= h n) →
  ex_series h →
  Series h = real (Sup_seq (sum_n h)).
Proof.
  intros Hpos Hex.
  apply Series_correct, lim_is_sup, is_sup_seq_unique in Hex; auto.
  apply eq_rbar_finite; auto.
Qed.

Lemma lim_is_sup'' (h: nat → R) :
  (∀ n, 0 <= h n) →
  ex_series h →
  is_series h (real (Sup_seq (sum_n h))).
Proof.
  intros Hpos Hex.
  rewrite <- lim_is_sup'; auto.
  apply Series_correct; auto.
Qed.

Lemma sup_is_upper_bound (h : nat → Rbar) n :
  Rbar_le (h n) (Sup_seq h).
Proof.
  apply is_sup_seq_major.
  apply Sup_seq_correct.
Qed.

Lemma sup_is_upper_bound' (h : nat → R) n r :
  is_sup_seq h (Finite r) →
  h n <= r.
Proof.
  intro Hr.
  assert (Rbar_le (Finite (real (h n))) (Finite r)); auto.
  assert (real (Finite (h n)) = h n) as ->; auto.
  apply (is_sup_seq_major (fun x : nat => Finite (h x)) (Finite r)); auto.
Qed.

Lemma upper_bound_ge_sup (h : nat → Rbar) r :
  (∀ n, Rbar_le (h n) r) →
  Rbar_le (Sup_seq h) r.
Proof.
  intro H2.
  pose proof (is_sup_seq_lub h (Sup_seq h) (Sup_seq_correct h)) as H3.
  rewrite /Lub.Rbar_is_lub in H3.
  apply H3.
  rewrite /Lub.Rbar_is_upper_bound.
  intros q (n & Hn).
  rewrite Hn; auto.
Qed.

Lemma upper_bound_ge_sup' (h : nat → R) r l :
  is_sup_seq h (Finite l) →
  (∀ n, h n <= r) →
  l <= r.
Proof.
  intros Hsup H2.
  assert (Rbar_le (Finite l) (Finite r)); auto.
  rewrite <- (is_sup_seq_unique (λ x : nat, h x) l); auto.
  apply (upper_bound_ge_sup (λ x : nat, h x) r); auto.
Qed.

Lemma sup_seq_eq_antisym (h1 h2 : nat → R) :
  (∀ m, ∃ n, h1 m <= h2 n) →
  (∀ m, ∃ n, h2 m <= h1 n) →
  Sup_seq h1 = Sup_seq h2.
Proof.
  intros H1 H2.
  apply Rbar_le_antisym.
  + apply upper_bound_ge_sup; intro n.
    destruct (H1 n) as (m & ?).
    apply (Sup_seq_minor_le _ _ m); auto.
  + apply upper_bound_ge_sup; intro n.
    destruct (H2 n) as (m & ?).
    apply (Sup_seq_minor_le _ _ m); auto.
Qed.

Lemma sup_seq_swap (h : nat * nat → R) :
  Sup_seq (λ n, Sup_seq (λ m, h (n , m))) =
    Sup_seq (λ m, Sup_seq (λ n, h (n , m))).
Proof.
  apply Rbar_le_antisym.
  + apply upper_bound_ge_sup; intro n.
    apply upper_bound_ge_sup; intro m.
    apply (Sup_seq_minor_le _ _ m).
    apply (Sup_seq_minor_le _ _ n).
    simpl; lra.
  + apply upper_bound_ge_sup; intro n.
    apply upper_bound_ge_sup; intro m.
    apply (Sup_seq_minor_le _ _ m).
    apply (Sup_seq_minor_le _ _ n).
    simpl; lra.
Qed.

Lemma Series_real_sup (h: nat → R) :
  (∀ n, 0 <= h n) →
  Series h = (real (Sup_seq (sum_n h))).
Proof.
  intros Hpos.
  rewrite /Series.
  f_equal.
  apply is_lim_seq_unique.
  apply is_LimSup_LimInf_lim_seq.
  - apply is_LimSup_infSup_seq.
    apply Rbar_is_glb_inf_seq.
    rewrite /Lub.Rbar_is_glb/=;split.
    + rewrite /Lub.Rbar_is_lower_bound.
      intros x (n&->).
      apply Sup_seq_le.
      intro; simpl.
      apply partial_sum_mon; auto; lia.
    + rewrite /Lub.Rbar_is_lower_bound.
      intros b Hb.
      apply Hb.
      exists 0%nat. apply Sup_seq_ext; intro.
      by rewrite Nat.add_0_r.
  - apply is_LimInf_supInf_seq.
    eapply (is_sup_seq_ext (λ n : nat, sum_n h (n))).
    + intro n; symmetry.
      apply is_inf_seq_unique.
      rewrite /is_inf_seq.
      intro eps; split.
      * intro n0; simpl.
        eapply (Rlt_le_trans _ (sum_n h n));
          [ | apply partial_sum_mon; auto; lia].
        apply Rlt_minus_l.
        rewrite <- Rplus_0_r at 1.
        apply Rplus_lt_compat_l.
        apply cond_pos.
      * exists 0%nat; simpl.
        rewrite <- Rplus_0_r at 1.
        apply Rplus_lt_compat_l.
        apply cond_pos.
    + apply Sup_seq_correct.
Qed.

Lemma ex_pos_bounded_series (h : nat → R) :
  (∀ n, 0 <= h n) →
  (∃ l, ∀ n, sum_n h n <= l) →
  ex_series h.
Proof.
  intros Hpos (l & Hl).
  exists (real (Sup_seq (λ n, sum_n h n))).
  apply sup_is_lim; auto.
  rewrite (Rbar_le_sandwich 0 l).
  - apply Sup_seq_correct.
  - apply (Rbar_le_trans _ (sum_n h 0%nat)).
    + rewrite sum_O.
      assert (0 <= (h 0%nat)); auto.
    + apply (sup_is_upper_bound (λ n : nat, sum_n h n) 0%nat).
  - destruct (Sup_seq (λ n : nat, sum_n h n)) eqn:Hsup; simpl; auto.
    + assert (Rbar_le (Finite r) (Finite l)); auto.
      rewrite <- Hsup.
      apply upper_bound_ge_sup.
      intro n; auto.
      specialize (Hl n); auto.
    + assert (Rbar_le (p_infty) (Finite l)); auto.
      rewrite <- Hsup.
      apply upper_bound_ge_sup.
      intro n; auto.
      specialize (Hl n); auto.
Qed.

Lemma double_sup_diag (h : nat * nat → R) :
  (∀ n m n', (n <= n')%nat → h (n, m) <= h (n' , m)) →
  (∀ n m m', (m <= m')%nat → h (n, m) <= h (n , m')) →
  Sup_seq (λ n, Sup_seq (λ m, h (n, m))) =
    Sup_seq (λ n, h (n, n)).
Proof.
  intros Hmon1 Hmon2.
  apply Rbar_le_antisym.
  - apply upper_bound_ge_sup.
    intro n.
    apply upper_bound_ge_sup.
    intro m.
    eapply Rbar_le_trans; last first.
    + apply (sup_is_upper_bound _ (n `max` m)).
    + apply (Rbar_le_trans _ (h ((n `max` m), m))).
      * apply Hmon1, Nat.le_max_l.
      * apply Hmon2, Nat.le_max_r.
  - apply upper_bound_ge_sup.
    intro n.
    eapply Rbar_le_trans; last first.
    + apply (sup_is_upper_bound _ n).
    +  eapply Rbar_le_trans; last first.
       * apply (sup_is_upper_bound _ n).
       * apply Rbar_le_refl.
Qed.

Lemma double_major_ex_series (h1 : nat → R) (h2 : nat → R) :
  (∀ n, 0 <= h1 n) →
  (∀ n, 0 <= h2 n) →
  (∀ n, ∃ m,  sum_n h1 n <= sum_n h2 m) →
  (∀ n, ∃ m,  sum_n h2 n <= sum_n h1 m) →
  ex_series h1 →
  ex_series h2.
Proof.
  intros Hpos1 Hpos2 Hmaj1 Hmaj2 Hex.
  epose proof (Series_correct _ Hex) as Hsup1.
  exists (Series h1).
  apply sup_is_lim; auto.
  apply lim_is_sup in Hsup1; auto.
  apply is_sup_seq_unique in Hsup1.
  assert (Sup_seq (λ n : nat, sum_n h1 n) = Sup_seq (λ n : nat, sum_n h2 n)) as Haux; last first.
  { rewrite -Hsup1 Haux.
    apply Sup_seq_correct. }
  apply sup_seq_eq_antisym; auto.
Qed.

Lemma double_major_Series (h1 : nat → R) (h2 : nat → R) :
  (∀ n, 0 <= h1 n) →
  (∀ n, 0 <= h2 n) →
  (∀ n, ∃ m,  sum_n h1 n <= sum_n h2 m) →
  (∀ n, ∃ m,  sum_n h2 n <= sum_n h1 m) →
  ex_series h1 →
  Series h1 = Series h2.
Proof.
  intros Hpos1 Hpos2 Hmaj1 Hmaj2 Hex.
  rewrite lim_is_sup'; auto.
  rewrite lim_is_sup'; auto; last first.
  { by apply (double_major_ex_series h1 h2). }
  f_equal.
  apply sup_seq_eq_antisym; auto.
Qed.

Lemma is_series_chain s1 s2 v:
  is_series s2 (Series s1) → is_series s1 v → is_series s2 v.
Proof.
  intros Hs2 Hs1.
  rewrite -(is_series_unique s1 v); auto.
Qed.

Lemma series_ge_0 (h : nat → R):
  (∀ a, 0 <= h a) → 0 <= Series h.
Proof.
  intro Hpos.
  rewrite /Series /Lim_seq.
  assert (Rbar_le 0 (LimSup_seq (sum_n h))).
  { rewrite <- (LimSup_seq_const 0).
    apply LimSup_le.
    exists 0%nat; intros.
    apply partial_sum_pos; auto. }
  assert (Rbar_le 0 (LimInf_seq (sum_n h))).
  { rewrite <- (LimInf_seq_const 0).
    apply LimInf_le.
    exists 0%nat; intros.
    apply partial_sum_pos; auto. }
  rewrite /Rbar_div_pos.
  case_match eqn:Heq.
  - apply Rcomplements.Rdiv_le_0_compat; auto.
    + apply Rbar_0_le_to_Rle'.
      rewrite <- (Rbar_plus_0_r 0).
      rewrite <- Heq.
      apply Rbar_plus_le_compat; auto.
    + apply Rlt_R0_R2.
  - apply Rle_refl.
  - rewrite <- Heq.
    apply Rbar_0_le_to_Rle.
    rewrite <- (Rbar_plus_0_r 0).
    apply Rbar_plus_le_compat; auto.
Qed.

Lemma LimSup_incr_seq (h : nat → R) k :
  (∀ n, h n <= h (S n)) →
  is_finite (LimSup_seq h) →
  h k <= LimSup_seq h.
Proof.
  intros Hmon Hfin.
  apply rbar_le_finite; auto.
  rewrite -(LimSup_seq_const (h k)).
  apply LimSup_le.
  rewrite /eventually.
  rewrite /LimSup_seq.
  exists k. intros n H1. induction n.
  - inversion H1. lra.
  - inversion H1; simplify_eq; try lra.
    etrans; [ | apply Hmon].
    apply IHn; auto.
Qed.

Lemma Series_gt_0_ex_series (h : nat → R) :
  (∀ n, 0 <= h n) →
  0 < Series h → ex_series h.
Proof.
  rewrite /Series.
  intros Hlt Hl.
  assert (ex_lim_seq (sum_n h)) as Haux.
  { apply ex_lim_seq_incr.
    intro; rewrite sum_Sn.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat_l; auto. }
  apply ex_lim_LimSup_LimInf_seq in Haux.
  rewrite /Lim_seq Haux in Hl.
  destruct (LimInf_seq (sum_n h)) eqn:Heq.
  - apply ex_pos_bounded_series; auto.
    exists r; intro n.
    pose proof Haux as Haux2.
    apply eq_rbar_finite' in Haux.
    rewrite -Haux.
    apply LimSup_incr_seq.
    + intro. apply partial_sum_mon; auto.
    + rewrite Haux2.
      rewrite /is_finite; auto.
  - simpl in Hl; lra.
  - simpl in Hl; lra.
Qed.

Lemma fubini_fin_sum (h : nat * nat → R) n m:
  sum_n (λ a, sum_n (λ b, h (a, b)) n ) m
  = sum_n (λ b, sum_n (λ a, h (a, b)) m ) n.
Proof. intros. apply sum_n_switch. Qed.

Lemma sum_n_le (h g: nat → R) n:
  (∀ m, h m <= g m) →
  sum_n h n <= sum_n g n.
Proof.
  intro Hle.
  induction n.
  - rewrite 2!sum_O //.
  - rewrite 2!sum_Sn.
    by apply Rplus_le_compat.
Qed.

Lemma series_pos_partial_le (h : nat → R) n:
  (∀ a, 0 <= h a) →
  ex_series h →
  sum_n h n <= Series h.
Proof.
  intros Hpos Hex.
  rewrite lim_is_sup'; auto.
  destruct Hex as (l & Hl).
  apply lim_is_sup in Hl; auto.
  assert (Rbar_le (Finite (sum_n h n)) (Sup_seq (λ n0 : nat, sum_n h n0))) as Hle.
  - apply (is_sup_seq_major (λ n0 : nat, sum_n h n0)).
    apply Sup_seq_correct.
  - rewrite (is_sup_seq_unique _ l) //.
    rewrite (is_sup_seq_unique _ l) // in Hle.
Qed.

Lemma series_pos_elem_le (h : nat → R) n:
  (∀ a, 0 <= h a) →
  ex_series h →
  h n <= Series h.
Proof.
  intros Hpos Hex.
  eapply Rle_trans; [apply partial_sum_elem | ]; auto.
  apply series_pos_partial_le; auto.
Qed.

Lemma fubini_fin_inf (h : nat * nat → R) n:
  (∀ a b, 0 <= h (a, b)) →
  (∀ b, ex_series (λ a, h (a, b))) →
  Series (λ a, sum_n (λ b, h (a, b)) n )
  = sum_n (λ b, Series (λ a, h (a, b)) ) n.
Proof.
  intros Hpos Hex.
  induction n.
  - rewrite sum_O.
    apply Series_ext.
    intro; rewrite sum_O; auto.
  - rewrite sum_Sn.
    rewrite <- IHn.
    rewrite <- Series_plus; auto.
    + apply Series_ext; intro;
        rewrite sum_Sn; auto.
    + apply ex_pos_bounded_series.
      * intro.
        apply partial_sum_pos; auto.
      * exists (sum_n (λ b, Series (λ a : nat, h (a, b))) n).
        intro m.
        rewrite fubini_fin_sum.
        apply sum_n_le.
        intro p.
        apply series_pos_partial_le; auto.
Qed.

Lemma fubini_pos_series_ex (h : nat * nat → R) :
  (∀ a b, 0 <= h (a, b)) →
  (∀ a, ex_series (λ b, h (a, b))) →
  (ex_series (λ a, Series (λ b, h (a, b)))) →
  (∀ b, ex_series (λ a, h (a, b))).
Proof.
  intros Hpos Hex1 Hex2 b.
  apply (ex_series_le (λ a : nat, h (a, b)) (λ a : nat, Series (λ b : nat, h (a, b)))); auto.
  intro a.
  rewrite /norm/=.
  rewrite /abs/=/Rabs/=.
  destruct (Rcase_abs (h (a, b))) as [H1 | H2].
  - destruct (Hpos a b); lra.
  - rewrite <- (Series_bump b (h(a, b))).
    apply Series_le'; auto.
    + intro; case_bool_decide; simplify_eq; auto.
      apply Rle_refl.
    + exists (h(a,b)).
      apply is_series_singleton.
Qed.

Lemma fubini_pos_series_ex_double (h : nat * nat → R) :
  (∀ a b, 0 <= h (a, b)) →
  (∀ a, ex_series (λ b, h (a, b))) →
  (ex_series (λ a, Series (λ b, h (a, b)))) →
  (ex_series (λ b, Series (λ a, h (a, b)))).
Proof.
  intros Hpos Hex1 Hex2.
  pose proof (fubini_pos_series_ex h Hpos Hex1 Hex2) as Hex3.
  pose proof Hex2 as Hex2'.
  destruct Hex2 as (l & Hl).
  apply ex_pos_bounded_series.
  - intro n. apply series_ge_0; auto.
  - exists l; intro n.
    rewrite <- fubini_fin_inf; auto.
    rewrite <- (is_series_unique (λ a : nat, Series (λ b : nat, h (a, b))) l); auto.
    apply Series_le; auto.
    intro m.
    split.
    + apply partial_sum_pos; auto.
    + apply series_pos_partial_le; auto.
Qed.

Lemma series_bounded (h : nat → R) l :
  (∀ a, 0 <= h a) →
  (∀ n, sum_n h n <= l) →
  ex_series h →
  Series h <= l.
Proof.
  intros Hpos Hle Hex.
  rewrite lim_is_sup'; auto.
  apply (upper_bound_ge_sup' (λ n : nat, sum_n h n) l); auto.
  assert (Finite (real (Sup_seq (λ n : nat, sum_n h n))) =
            Sup_seq (λ n : nat, sum_n h n)) as ->.
  { apply (Rbar_le_sandwich 0 l).
    - apply (Rbar_le_trans _ (sum_n h 0%nat)).
      + rewrite sum_O; simpl; auto.
      + apply (sup_is_upper_bound (λ n : nat, sum_n h n)).
    - apply upper_bound_ge_sup; auto.
  }
  apply (Sup_seq_correct (λ x : nat, sum_n h x)).
Qed.

Lemma series_bounded_rbar (h : nat → R) (l : Rbar) :
  (∀ a, 0 <= h a) →
  (∀ n, Rbar_le (sum_n h n) l) →
  ex_series h →
  Rbar_le (Series h) l.
Proof.
  intros Hpos Hle Hex.
  destruct l eqn:Hl; simpl; auto.
  - by apply series_bounded.
  - by apply (Hle 0%nat).
Qed.

Lemma fubini_pos_series (h : nat * nat → R) :
  (∀ a b, 0 <= h (a, b)) →
  (∀ a, ex_series (λ b, h (a, b))) →
  (ex_series (λ a, Series (λ b, h (a, b)))) →
  Series (λ b, Series (λ a, h (a, b))) =
    Series (λ a, Series (λ b, h (a, b))).
Proof.
  intros Hpos Hex1 Hex2.
  pose proof (fubini_pos_series_ex _ Hpos Hex1 Hex2) as Hex3.
  pose proof (fubini_pos_series_ex_double _ Hpos Hex1 Hex2) as Hex4.
  apply Rle_antisym.
  - apply series_bounded; auto.
    + intro; apply series_ge_0; auto.
    + intro.
      rewrite <- fubini_fin_inf; auto.
      apply Series_le; auto.
      intro; split; auto.
      * apply partial_sum_pos; auto.
      * apply series_pos_partial_le; auto.
  - apply series_bounded; auto.
    + intro; apply series_ge_0; auto.
    + intro.
      rewrite <- (fubini_fin_inf (λ '(b, a), h (a, b))) ; auto.
      apply Series_le; auto.
      intro; split; auto.
      * apply partial_sum_pos; auto.
      * apply series_pos_partial_le; auto.
Qed.

(** Monotone convergence theorem  *)
Lemma mon_sup_succ (h : nat → R) :
  (∀ n, h n <= h (S n)) →
  Sup_seq h = Sup_seq (λ n, h (S n)).
Proof.
  intro Hmon.
  apply Rbar_le_antisym.
  - apply upper_bound_ge_sup.
    intro n.
    apply (Sup_seq_minor_le _ _ n), Hmon.
  - apply upper_bound_ge_sup.
    intro n.
    apply (Sup_seq_minor_le _ _ (S (S n))), Hmon.
Qed.

Lemma sup_seq_const (r : R) :
  real (Sup_seq (λ n, r)) = r.
Proof.
  assert (is_finite (Sup_seq (λ n, r))) as Haux.
  { apply (Rbar_le_sandwich r r); auto.
    - apply (Sup_seq_minor_le _ _ 0%nat); apply Rbar_le_refl.
    - apply upper_bound_ge_sup; intro; apply Rbar_le_refl. }
  apply Rle_antisym.
  - apply finite_rbar_le; auto.
    apply (upper_bound_ge_sup); intro; apply Rbar_le_refl.
  - apply rbar_le_finite; auto.
    apply (Sup_seq_minor_le _ _ 0%nat); apply Rbar_le_refl.
Qed.

Lemma Sup_seq_bounded_plus_l (f : nat → R) (b r : R) :
  (∀ n, 0 <= f n <= b) →
  Sup_seq (λ a, r + (f a)) = r + real (Sup_seq f).
Proof.
  intro Hf.
  apply Rbar_le_antisym.
  - apply upper_bound_ge_sup.
    intro n.
    simpl.
    apply Rplus_le_compat; [apply Rle_refl | ].
    + apply sup_is_upper_bound'.
      rewrite -> (Rbar_le_sandwich 0 b); auto.
      * apply Sup_seq_correct.
      * apply (Sup_seq_minor_le _ _ 0%nat), Hf.
      * apply (upper_bound_ge_sup _ b), Hf.
  - rewrite /Sup_seq.
    destruct ex_sup_seq as (p & Hp).
    destruct ex_sup_seq as (q & Hq).
    assert (is_finite p) as Hfinp.
    { apply (Rbar_le_sandwich 0 b).
      + eapply (Rbar_le_trans _ (Finite (f 0%nat))).
        * apply (proj1 (Hf 0%nat)).
        * rewrite <- (is_sup_seq_unique f p); auto.
          apply (Sup_seq_minor_le _ _ 0%nat), Rle_refl.
      + rewrite <- (is_sup_seq_unique f p); auto.
        apply (upper_bound_ge_sup _ b), Hf. }
    assert (is_finite q) as Hfinq.
    { apply (Rbar_le_sandwich r (r + b)).
      + eapply (Rbar_le_trans _ (Finite (r + f 0%nat))).
        * assert (r = r + 0) as Haux; [lra | ].
          rewrite {1}Haux.
          apply (Rbar_plus_le_compat r r 0 (f 0%nat)); [apply Rbar_le_refl | ].
          apply (proj1 (Hf 0%nat)).
        * rewrite <- (is_sup_seq_unique (λ a : nat, r + f a) q); auto.
          apply (Sup_seq_minor_le _ _ 0%nat), Rle_refl.
      + rewrite <- (is_sup_seq_unique (λ a : nat, r + f a) q); auto.
        apply (upper_bound_ge_sup _ (r + b)).
        intro n; apply (Rbar_plus_le_compat r r (f n) b); [apply Rbar_le_refl | ].
        apply Hf. }
    simpl proj1_sig.
    apply is_sup_seq_lub in Hp.
    apply is_sup_seq_lub in Hq.
    destruct Hp as (Hp1 & Hp2).
    destruct Hq as (Hq1 & Hq2).
    apply is_finite_correct in Hfinp.
    destruct Hfinp as (p' & ->).
    apply is_finite_correct in Hfinq.
    destruct Hfinq as (q' & ->).
    simpl.
    assert (p' <= q' + (opp r)) as H; last first.
    {
      apply (Rplus_le_compat r r) in H; [ | apply Rle_refl].
      apply (Rle_trans (r + p') (r + (q' + opp r)) q'); auto.
      rewrite (Rplus_comm q' (opp r)).
      rewrite <- Rplus_assoc.
      assert (r + opp r = 0) as ->.
      + apply (plus_opp_r r).
      + rewrite Rplus_0_l.
        apply Rle_refl.
    }
    assert (Rbar_le p' (q' + opp r)); auto.
    apply Hp2.
    intros _ (n & ->).
    apply (Rbar_le_trans _ (r + f n + opp r)).
    { simpl.
      rewrite (Rplus_comm r (f n)).
      rewrite (Rplus_assoc).
      assert (r + opp r = 0) as ->.
      + apply (plus_opp_r r).
      + rewrite Rplus_0_r.
        apply Rle_refl.
    }
    simpl.
    apply Rplus_le_compat; [ | apply Rle_refl ].
    assert (Rbar_le (r + f n) q'); auto.
    apply Hq1.
    exists n; auto.
Qed.

Lemma Sup_seq_bounded_plus_r (f : nat -> R) (b r : R) :
  (∀ n, 0 <= f n <= b) →
  Sup_seq (λ a, (f a) + r) = real (Sup_seq f) + r.
Proof.
  intro Hf.
  rewrite Rplus_comm.
  erewrite Sup_seq_ext; last first.
  - intro; rewrite Rplus_comm; done.
  - eapply Sup_seq_bounded_plus_l; eauto.
Qed.

Lemma Sup_seq_bounded_plus_sup (f g : nat → R) (b r : R) :
  (∀ n, 0 <= f n <= b) →
  (∀ n, 0 <= g n <= b) →
  (∀ n, f n <= f (S n)) →
  (∀ n, g n <= g (S n)) →
  Sup_seq (λ a, (f a) + (g a)) = real (Sup_seq f) + (Sup_seq g).
Proof.
  intros Hfb Hgb Hfmon Hgmon.
  apply Rbar_le_antisym.
  - apply upper_bound_ge_sup.
    intro n.
    simpl.
    apply Rplus_le_compat.
    + apply sup_is_upper_bound'.
      rewrite -> (Rbar_le_sandwich 0 b); auto.
      * apply Sup_seq_correct.
      * apply (Sup_seq_minor_le _ _ 0%nat), Hfb.
      * apply (upper_bound_ge_sup _ b), Hfb.
    + apply sup_is_upper_bound'.
      rewrite -> (Rbar_le_sandwich 0 b); auto.
      * apply Sup_seq_correct.
      * apply (Sup_seq_minor_le _ _ 0%nat), Hgb.
      * apply (upper_bound_ge_sup _ b), Hgb.
  - rewrite <- (Sup_seq_bounded_plus_r _ b); auto.
    apply upper_bound_ge_sup.
    intro n.
    rewrite <- (Sup_seq_bounded_plus_l _ b); auto.
    apply upper_bound_ge_sup.
    intro m.
    eapply Rbar_le_trans; last first.
    + apply (sup_is_upper_bound _ (n `max` m)).
    + simpl.
      apply Rplus_le_compat.
      * pose proof (mon_succ_to_mon f Hfmon) as Haux.
        apply Haux, Nat.le_max_l.
      * pose proof (mon_succ_to_mon g Hgmon) as Haux.
        apply Haux, Nat.le_max_r.
Qed.

Lemma MCT_aux1 (h : nat → nat → R) (l : nat → R) (r : R) (M : nat) :
  (∀ n a, 0 <= (h n a)) →
  (∀ n a, (h n a) <= (h (S n) a)) →
  (∀ a, ∃ s, ∀ n, h n a <= s ) →
  (∀ n, is_series (h n) (l n)) →
  is_sup_seq l (Finite r) →
  Finite ((sum_n (λ a : nat, real (Sup_seq (λ n : nat, h n a))) M)) =
    (Sup_seq (λ n, sum_n (λ a : nat, h n a) M)).
Proof.
  intros Hpos Hmon Hbd Hseries Hsup.
  assert (∀ a b, Finite (a + b) = Finite a + Finite b) as Haux; auto.
  induction M.
  - rewrite sum_O.
    destruct (Hbd 0%nat) as (s & Hs).
    rewrite (Rbar_le_sandwich 0 s).
    + apply Sup_seq_ext; intro; rewrite sum_O; auto.
    + apply (Sup_seq_minor_le (λ n0 : nat, h n0 0%nat) 0 0%nat).
      apply Hpos.
    + apply upper_bound_ge_sup; auto.
  - rewrite sum_Sn.
    rewrite Haux.
    rewrite IHM.
    symmetry.
    erewrite Sup_seq_ext; last first.
    + intro; rewrite sum_Sn. done.
    + rewrite Haux; simpl.
      erewrite <- (Sup_seq_bounded_plus_sup _ _ r); auto; intros; try split.
      * apply partial_sum_pos; auto.
      * eapply Rle_trans.
        -- apply series_pos_partial_le; auto.
           exists (l n); auto.
        -- rewrite (is_series_unique _ _ (Hseries n)).
           apply (sup_is_upper_bound'); auto.
      * auto.
      * eapply Rle_trans.
        -- apply series_pos_elem_le; auto.
           exists (l n); auto.
        -- rewrite (is_series_unique _ _ (Hseries n)).
           apply (sup_is_upper_bound'); auto.
      * apply sum_n_le.
        intro m; auto.
Qed.

Lemma MCT_aux2 (h : nat → nat → R) (l : nat → R) (r : R) :
  (∀ n a, 0 <= (h n a)) →
  (∀ n a, (h n a) <= (h (S n) a)) →
  (∀ a, exists s, ∀ n, h n a <= s ) →
  (∀ n, is_series (h n) (l n)) →
  is_sup_seq l (Finite r) →
  Rbar_le (Sup_seq (λ m, sum_n (λ a, real (Sup_seq (λ n, h n a))) m)) r.
Proof.
  intros Hpos Hmon Hbd Hseries Hsup.
  apply upper_bound_ge_sup.
  intro M.
  erewrite MCT_aux1; eauto.
  apply upper_bound_ge_sup => n.
  apply (Rbar_le_trans _ (Series (λ a : nat, h n a))).
  - apply series_pos_partial_le; auto.
    exists (l n); auto.
  - apply (Rbar_le_trans _ (l n)).
    + rewrite <- (is_series_unique (λ a : nat, h n a) (l n)); auto.
      apply Rbar_le_refl.
    + erewrite <- is_sup_seq_unique; eauto.
      apply (sup_is_upper_bound (λ x : nat, l x)).
Qed.

Lemma MCT_aux3 (h : nat → nat → R) (l : nat → R) (r : R) :
  (∀ n a, 0 <= (h n a)) →
  (∀ n a, (h n a) <= (h (S n) a)) →
  (∀ a, exists s, ∀ n, h n a <= s ) →
  (∀ n, is_series (h n) (l n)) →
  is_sup_seq l (Finite r) →
  Rbar_le r (Sup_seq (λ m, sum_n (λ a, real (Sup_seq (λ n, h n a))) m)).
Proof.
  intros Hpos Hmon Hbd Hseries Hsup.
  rewrite <- (is_sup_seq_unique _ _ Hsup).
  apply upper_bound_ge_sup.
  intro n.
  rewrite <- (is_series_unique _ _ (Hseries n)).
  apply series_bounded_rbar; auto; [ | (exists (l n)); auto].
  intro m.
  apply (Sup_seq_minor_le _ _ m).
  erewrite MCT_aux1; eauto.
  apply (sup_is_upper_bound (λ n0 : nat, sum_n (λ a : nat, h n0 a) m)).
Qed.

Lemma MCT_aux4 (h : nat → nat → R) (l : nat → R) (r : R) :
  (∀ n a, 0 <= (h n a)) →
  (∀ n a, (h n a) <= (h (S n) a)) →
  (∀ a, exists s, ∀ n, h n a <= s ) →
  (∀ n, is_series (h n) (l n)) →
  is_sup_seq l (Finite r) →
  is_finite
    (Sup_seq
       (λ n : nat,
           Finite
             (sum_n (λ a : nat, real (Sup_seq (λ n0 : nat, Finite (h n0 a)))) n))).
Proof.
  intros Hpos Hmon Hbd Hseries Hsup.
  apply (is_finite_bounded 0 r).
  - apply (Sup_seq_minor_le _ _ 0%nat).
    destruct (Hbd 0%nat) as (s & Hs).
    rewrite sum_O.
    rewrite (Rbar_le_sandwich 0 s).
    + apply (Sup_seq_minor_le (λ n0 : nat, h n0 0%nat) 0 0%nat).
      apply Hpos.
    + apply (Sup_seq_minor_le (λ n0 : nat, h n0 0%nat) 0 0%nat).
      apply Hpos.
    + apply upper_bound_ge_sup; auto.
  - rewrite <- (is_sup_seq_unique l r); auto.
    apply upper_bound_ge_sup; intro n.
    erewrite MCT_aux1; eauto.
    apply Sup_seq_le; intro m.
    rewrite <- (is_series_unique (h m) (l m)); auto.
    apply series_pos_partial_le; auto.
    exists (l m); auto.
Qed.

Lemma MCT_series (h : nat → nat → R) (l : nat → R) (r : R) :
  (∀ n a, 0 <= (h n a)) →
  (∀ n a, (h n a) <= (h (S n) a)) →
  (∀ a, exists s, ∀ n, h n a <= s ) →
  (∀ n, is_series (h n) (l n)) →
  is_sup_seq l (Finite r) →
  Series (λ a, Sup_seq (λ n, h n a)) = r.
Proof.
  intros Hpos Hmon Hbd Hseries Hsup.
  rewrite lim_is_sup'; auto.
  - apply Rle_antisym.
    + apply finite_rbar_le; [eapply MCT_aux4 | eapply MCT_aux2 ]; eauto.
    + apply rbar_le_finite; [eapply MCT_aux4| eapply MCT_aux3 ]; eauto.
  - intro n.
    apply Rbar_0_le_to_Rle.
    apply (Sup_seq_minor_le _ _ 0%nat); auto.
    apply Hpos.
  - apply ex_pos_bounded_series.
    + intro.
      apply Rbar_0_le_to_Rle.
      apply (Sup_seq_minor_le _ _ 0%nat); auto.
      apply Hpos.
    + exists r.
      intro m.
      apply rbar_le_rle.
      assert
        (Rbar_le
           (@sum_n R_AbelianGroup (fun a : nat => real (Sup_seq (fun n : nat => Finite (h n a)))) m) r);
        auto.
      erewrite MCT_aux1; eauto.
      rewrite <- (is_sup_seq_unique _ r Hsup).
      apply Sup_seq_le.
      intro n.
      rewrite <- (is_series_unique (h n) (l n)); auto.
      apply series_pos_partial_le; auto.
      exists (l n); auto.
Qed.

Lemma MCT_ex_series (h : nat → nat → R) (l : nat → R) (r : R) :
  (∀ n a, 0 <= (h n a)) →
  (∀ n a, (h n a) <= (h (S n) a)) →
  (∀ a, exists s, ∀ n, h n a <= s ) →
  (∀ n, is_series (h n) (l n)) →
  is_sup_seq l (Finite r) →
  ex_series (λ a, real (Sup_seq (λ n, h n a))).
Proof.
  intros Hpos Hmon Hbd Hseries Hsup.
  apply ex_pos_bounded_series.
  - intro n.
    apply rbar_le_finite.
    + destruct (Hbd n) as (s & Hs).
      apply (Rbar_le_sandwich 0 s).
      * apply (Sup_seq_minor_le _ _ 0%nat); auto.
        simpl; auto.
      * apply upper_bound_ge_sup; intro; simpl; auto.
    + apply (Sup_seq_minor_le (λ n0 : nat, h n0 n) _ 0%nat);
        apply Hpos.
  - exists r.
    intro n.
    assert (Rbar_le (sum_n (λ a : nat, real (Sup_seq (λ n0 : nat, h n0 a))) n) r); auto.
    rewrite (MCT_aux1 h l r n); auto.
    rewrite <- (is_sup_seq_unique _ r Hsup).
    apply Sup_seq_le.
    intro m.
    rewrite <- (is_series_unique _ (l m) (Hseries m)).
    rewrite lim_is_sup'; auto; last first.
    + exists (l m); auto.
    + apply sup_is_upper_bound'.
      rewrite rbar_finite_real_eq.
      * apply Sup_seq_correct.
      * apply (Rbar_le_sandwich 0 (l m)).
        -- apply (Sup_seq_minor_le _ _ 0%nat); auto.
           rewrite sum_O; simpl; auto.
        -- apply upper_bound_ge_sup; intro; simpl; auto.
           rewrite <- (is_series_unique _ (l m) (Hseries m)).
           apply series_pos_partial_le; auto.
           exists (l m); auto.
Qed.

(** Double series *)
Definition double_summable a :=
  ∃ (r: R), ∀ n, sum_n (λ j, sum_n (λ k, a (j, k)) n) n <= r.

Definition double_summable_nm a :=
  ∃ (r: R), ∀ n m, sum_n (λ j, sum_n (λ k, a (j, k)) n) m <= r.

Definition double_summable_n_Series a :=
  ∃ (r: R), ∀ n, sum_n (λ j, Series (λ k, a (j, k))) n <= r.

Lemma DS_n_to_nm a :
  (∀ n m, 0 <= a(n,m)) →
  double_summable a → double_summable_nm a.
Proof.
  intros Hpos (r&Hr).
  exists r; intros n m.
  specialize (Hr (n `max` m));
    etrans; eauto.
  etrans; last first.
  {
    apply partial_sum_mon; [ | apply Nat.le_max_r].
    intro.
    apply sum_n_partial_pos; auto.
  }
  apply sum_n_le.
  intro.
  apply partial_sum_mon; [ | apply Nat.le_max_l].
  intro; auto.
Qed.


Lemma double_summable_mono_cond a:
  (∀ n m, 0 <= a(n,m)) →
  (∃ (r: R), ∃ N, ∀ n, n ≥ N → sum_n (λ j, sum_n (λ k, a (j, k)) n) n <= r) →
  double_summable a.
Proof.
  intros Hpos (r&N&Hcond).
  exists r => n.
  destruct (le_ge_dec N n) as [Hle|Hge].
  - apply Hcond. lia.
  - transitivity (sum_n (λ j, sum_n (λ k, a (j, k)) N) N).
    { clear Hcond.
      induction Hge; first reflexivity.
      etransitivity; first eapply IHHge.
      rewrite sum_Sn /plus//=.
      rewrite -[a in a <= _]Rplus_0_r.
      apply Rplus_le_compat.
      * rewrite ?sum_n_bigop.
        apply sum_n_le => k.
        rewrite sum_Sn.
        rewrite <- Rplus_0_r at 1.
        apply Rplus_le_compat_l; auto.
      * apply partial_sum_pos; eauto => ?.
    }
    eauto.
Qed.

Lemma double_summable_by_flip a:
  double_summable a →
  double_summable (λ xy, a (snd xy, fst xy)).
Proof.
  intros (r&Hle).
  exists r => n. rewrite sum_n_switch => //=.
Qed.

Lemma double_summable_flip a:
  double_summable (λ xy, a (snd xy, fst xy)) → double_summable a.
Proof.
  intros (r&Hle).
  exists r => n. rewrite sum_n_switch => //=.
Qed.

Lemma ex_series_rows_ds a:
  (∀ n m, 0 <= a(n,m)) →
  (∀ j, ex_series (λ k, a (j, k))) →
  ex_series (λ j, Series (λ k,  a (j, k))) →
  double_summable a.
Proof.
  intros Hpos Hrows Hex.
  destruct Hex as (r&Hseries).
  exists r => n.
  transitivity (sum_n (λ j, Series (λ k, a (j, k))) n).
  {  rewrite ?sum_n_bigop. apply sum_n_le. intros j.
     edestruct (Hrows j) as (v&Hrow). rewrite (is_series_unique _ _ Hrow).
     apply is_series_partial_pos; auto.
  }
  apply is_series_partial_pos; eauto.
  intros j.
  apply series_ge_0; auto.
Qed.

Lemma ex_series_columns_ds a:
  (∀ n m, 0 <= a(n,m)) →
  (∀ k, ex_series (λ j, a (j, k))) →
  ex_series (λ k, Series (λ j,  a (j, k))) →
  double_summable a.
Proof.
  intros. apply double_summable_flip, ex_series_rows_ds; auto.
Qed.

Lemma ex_series_row a (DS: double_summable a) j:
  (∀ n m, 0 <= a(n,m)) →
  ex_series (λ k, a (j, k)).
Proof.
  intros Hpos.
  apply DS_n_to_nm in DS; auto.
  destruct DS as (r&Hr).
  apply ex_pos_bounded_series; auto.
  exists r; intro n.
  specialize (Hr n j).
  etrans; eauto.
  rewrite fubini_fin_sum.
  apply sum_n_le.
  intro m.
  apply (partial_sum_elem (λ x, a (x, m))).
  auto.
Qed.

Lemma ex_series_column a (DS: double_summable a) k:
  (∀ n m, 0 <= a(n,m)) →
  ex_series (λ j, a (j, k)).
Proof.
  intros Hpos.
  set (flip := λ (x : nat * nat), (snd x, fst x)).
  eapply ex_series_ext; last first.
  { eapply ex_series_row.
    - apply double_summable_by_flip => //=.
    - intros; simpl; auto. }
  intros n => //=.
Qed.

Lemma ex_series_row_col a (DS : double_summable a) :
  (∀ n m, 0 <= a(n,m)) →
  ex_series (λ j, Series (λ k, a (j, k))).
Proof.
  intros Hpos.
  pose proof (DS_n_to_nm a Hpos DS) as (r&Hr).
  apply ex_pos_bounded_series.
  - intro; apply series_ge_0; auto.
  - exists r; intro n.
    rewrite -(fubini_fin_inf (λ '(x,y), a(y,x))).
    + apply series_bounded.
      * intro; apply partial_sum_pos; auto.
      * intro. rewrite (fubini_fin_sum ((λ '(x,y), a(y,x)))); auto.
      * apply ex_pos_bounded_series.
        ** intro; apply partial_sum_pos; auto.
        ** exists r; intro.
           rewrite (fubini_fin_sum ((λ '(x,y), a(y,x)))); auto.
    + intros; auto.
    + intros.
      apply (ex_series_column (λ '(x,y), a(y,x))).
      * exists r; intros.
        rewrite (fubini_fin_sum ((λ '(x,y), a(y,x)))); auto.
      * intros; auto.
Qed.


Lemma ex_series_col_row a (DS : double_summable a) :
  (∀ n m, 0 <= a(n,m)) →
  ex_series (λ k, Series (λ j, a (j, k))).
Proof.
  intros Hpos.
  pose proof (DS_n_to_nm a Hpos DS) as (r&Hr).
  apply ex_pos_bounded_series.
  - intro; apply series_ge_0; auto.
  - exists r; intro n.
    rewrite -(fubini_fin_inf).
    + apply series_bounded.
      * intro; apply partial_sum_pos; auto.
      * intro; auto.
      * apply ex_pos_bounded_series.
        ** intro; apply partial_sum_pos; auto.
        ** exists r; intro; auto.
    + intros; auto.
    + intros.
      apply ex_series_column; auto.
Qed.

Section prod1.
  Variable (a: nat * nat → R).
  Variable (σ: nat → nat * nat).

  Variable (POS: ∀ n n', 0 <= a (n, n')).
  Variable (INJ: ∀ n n', a (σ n) <> 0 → σ n = σ n' → n = n').
  Variable (COV: ∀ n, a n <> 0 → ∃ m, σ m = n).

  Lemma inj_nat_cover1:
    ∀ N, ∃ K, ∀ n, n ≤ N → (fst (σ n) ≤ K ∧ snd (σ n) ≤ K).
  Proof.
    induction N.
    - exists (max (fst (σ O)) (snd (σ O))); intros n Hle; inversion Hle; split.
      + apply Nat.le_max_l.
      + apply Nat.le_max_r.
    - edestruct IHN as (K&HK).
      exists (max (max (fst (σ (S N))) (snd (σ (S N)))) K); intros n Hle; inversion Hle.
      + split.
        * etransitivity; last apply Nat.le_max_l. apply Nat.le_max_l.
        * etransitivity; last apply Nat.le_max_l. apply Nat.le_max_r.
      + split.
        * etransitivity; last apply Nat.le_max_r. edestruct HK; eauto.
        * etransitivity; last apply Nat.le_max_r. edestruct HK; eauto.
  Qed.

  Lemma inj_nat_cover2:
    ∀ K1 K2, ∃ N, ∀ l m, l ≤ K1 → m ≤ K2 →
    (∃ n, n ≤ N ∧ σ n = (l, m)) ∨ a (l, m) = 0.
  Proof.
    induction K1.
    - induction K2.
      + destruct (Req_dec (a (O, O)) 0) as [|Hneq].
        * exists O => l m. inversion 1; subst. inversion 1; subst.
          right. done.
        * edestruct (COV _ Hneq) as (N&?).
          exists N => l m. inversion 1; subst. inversion 1; subst.
          left. exists N; split; auto.
      + destruct IHK2 as (N&HN).
        destruct (Req_dec (a (O, S K2)) 0) as [|Hneq].
        * exists N => l m. inversion 1; subst. inversion 1; subst.
          ** right. done.
          ** eapply HN; auto.
        * edestruct (COV _ Hneq) as (N'&?).
          exists (max N N') => l m. inversion 1; subst. inversion 1; subst.
          ** left. exists N'. split; auto. apply Nat.le_max_r.
          ** edestruct (HN O m) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N; auto.
             apply Nat.le_max_l.
    - induction K2.
      + destruct (IHK1 O) as (N&HN).
        destruct (Req_dec (a (S K1, O)) 0) as [|Hneq].
        * exists N => l m. inversion 1; subst; inversion 1; subst.
          ** right. done.
          ** eapply HN; auto.
        * edestruct (COV _ Hneq) as (N'&?).
          exists (max N N') => l m. inversion 1; subst; inversion 1; subst.
          ** left. exists N'. split; auto. apply Nat.le_max_r.
          ** edestruct (HN l O) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N; auto.
             apply Nat.le_max_l.
      + destruct (IHK1 (S K2)) as (N1&HN1).
        destruct IHK2 as (N2&HN2).
        destruct (Req_dec (a (S K1, S K2)) 0) as [|Hneq].
        * exists (max N1 N2) => l m. inversion 1; subst; inversion 1; subst.
          ** right. done.
          ** edestruct (HN2 (S K1) m) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N2; auto.
             apply Nat.le_max_r.
          ** edestruct (HN1 l (S K2)) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N1; auto.
             apply Nat.le_max_l.
          ** edestruct (HN1 l m) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N1; auto.
             apply Nat.le_max_l.
        * edestruct (COV _ Hneq) as (N'&?).
          exists (max (max N1 N2) N') => l m. inversion 1; subst; inversion 1; subst.
          ** left.  exists N'; split; auto.
             apply Nat.le_max_r.
          ** edestruct (HN2 (S K1) m) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N2; auto.
             etransitivity; first apply Nat.le_max_r; apply Nat.le_max_l.
          ** edestruct (HN1 l (S K2)) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N1; auto.
             etransitivity; first apply Nat.le_max_l; apply Nat.le_max_l.
          ** edestruct (HN1 l m) as [(n&?&?)|]; eauto.
             left. exists n. split; auto. transitivity N1; auto.
             etransitivity; first apply Nat.le_max_l; apply Nat.le_max_l.
  Qed.

  Lemma sum_n_m_cover_diff_double_pos:
    ∀ N, ∃ K, ∀ l m, l ≥ K → m ≥ K →
    ∃ n, n ≥ N ∧ Rabs (sum_n (λ j, sum_n (λ k, a (j, k)) m) l - sum_n (a ∘ σ) N)
                 <= sum_n_m (a ∘ σ) (S N) n.
  Proof.
    intro N.
    destruct (pre_converge.sum_n_m_cover_diff_double a σ INJ COV N) as (K&HK).
    exists K.
    intros l m Hl Hm.
    destruct (HK l m Hl Hm) as (n&Hn1&Hn2).
    exists n; split; auto.
    etrans; [apply Hn2 | ].
    apply sum_n_m_le.
    intro k; simpl.
    rewrite Rabs_pos_eq; try lra.
    destruct (σ k); auto.
  Qed.

  Lemma sum_n_filter_leq (h : nat → R) n :
    sum_n h n = sum_n (λ i, if bool_decide (i <= n)%nat then h i else 0) n.
  Proof.
    revert h.
    induction n; intro h.
    - do 2 rewrite sum_O.
      rewrite bool_decide_eq_true_2; auto.
    - do 2 rewrite sum_Sn.
      rewrite IHn.
      f_equal.
      + rewrite (IHn (λ i : nat, if bool_decide (i ≤ S n) then h i else 0)).
        apply sum_n_ext.
        intro m.
        case_bool_decide; auto.
        rewrite bool_decide_eq_true_2; auto.
      + rewrite bool_decide_eq_true_2; auto.
  Qed.

  Lemma sum_n_m_leq_covering1 n :
    ∃ m, sum_n (λ j : nat, sum_n (λ k : nat, a (j, k)) n) n <= sum_n (a ∘ σ) m.
  Proof.
    destruct (sum_n_m_cover_diff_double_pos n) as (m&Hm).
    destruct (Hm (n `max` m) (n `max` m) ) as (x&Hx1&Hx2); try lia.
    destruct (decide (0 <= sum_n (λ j : nat, sum_n (λ k : nat, a (j, k)) (n `max` m)) (n `max` m) - sum_n (a ∘ σ) n))
      as [Hle | Hgt].
    - rewrite Rabs_pos_eq in Hx2; [ | lra].
      apply Rle_minus_l in Hx2.
      exists x.
      rewrite {3}/sum_n.
      rewrite (sum_n_m_Chasles _ 0 n x); try lia.
      rewrite /plus/= Rplus_comm.
      etrans; [ | apply Hx2 ].
      etrans; last first.
      + apply partial_sum_mon; [ | apply Nat.le_max_l].
        intros; by apply partial_sum_pos.
      + apply sum_n_le.
        intros; by apply partial_sum_mon; [ | lia ].
    - apply Rnot_le_gt,
        Rgt_lt,
        Rlt_minus_l,
        Rlt_le in Hgt.
      rewrite Rplus_0_l in Hgt.
      exists n.
      etrans; [ | apply Hgt ].
      etrans; last first.
      + apply partial_sum_mon; [ | apply Nat.le_max_l].
        intros; by apply partial_sum_pos.
      + apply sum_n_le.
        intros; by apply partial_sum_mon; [ | lia ].
  Qed.

  Lemma sum_n_m_leq_covering2 m :
    ∃ n, sum_n (a ∘ σ) m <= sum_n (λ j : nat, sum_n (λ k : nat, a (j, k)) n) n.
  Proof.
    destruct (inj_nat_cover1 m) as (n&Hn).
    exists n.
    assert (sum_n (a ∘ σ) m
            = sum_n (λ x, if bool_decide ((fst (σ x) <= n)%nat ∧ (snd (σ x) <= n)%nat)
                          then a (σ x) else 0) m) as ->.
    { rewrite {1}sum_n_filter_leq.
      rewrite (sum_n_filter_leq (λ x, if bool_decide _ then a (σ x) else 0)).
      apply sum_n_ext.
      intro n0.
      case_bool_decide; [|done].
      rewrite bool_decide_eq_true_2 //.
      by apply Hn. }
    destruct (inj_nat_cover2 n n) as (x&HX).
    rewrite (pre_converge.sum_n_m_cover_diff_double_aux a σ INJ m n n x); auto.
    etrans; last first.
    - apply partial_sum_mon; [ | apply Nat.le_max_r ].
      intro n0.
      destruct (ssrnat.leq (σ n0).1 n && ssrnat.leq (σ n0).2 n); try lra.
      destruct (σ n0); auto.
    - apply sum_n_le => m0.
      case_bool_decide as H.
      + by destruct H as [->%SSR_leq ->%SSR_leq].
      + apply not_and_or_not in H as [H1 | H2].
        * rewrite andb_false_intro1; [lra|].
          apply Is_true_false_1.
          intros Hleq. apply H1.
          apply SSR_leq, Is_true_true_1. done.
        * rewrite andb_false_intro2; [lra|].
          apply Is_true_false_1.
          intro HLeq. apply H2.
          apply SSR_leq, Is_true_true_1. done.
  Qed.

  Lemma summable_ds_helper:
    Sup_seq (λ n : nat, sum_n (λ j : nat, sum_n (λ k : nat, a (j, k)) n) n) =
      Sup_seq (λ n, sum_n (a ∘ σ) n).
  Proof.
    apply sup_seq_eq_antisym.
    - apply sum_n_m_leq_covering1.
    - apply sum_n_m_leq_covering2.
  Qed.

  Lemma ds_implies_exseries :
    double_summable a → ex_series (a ∘ σ).
  Proof.
    intros (r & Hr).
    apply ex_pos_bounded_series.
    - intro n; simpl; destruct (σ n); auto.
    - exists (Sup_seq (λ n, sum_n (λ j : nat, sum_n (λ k : nat, a (j, k)) n) n) ).
      intro n.
      apply rbar_le_finite.
      + apply (is_finite_bounded 0 r).
        * apply (Sup_seq_minor_le _ _ 0).
          rewrite /=sum_O/=sum_O//.
        * by apply upper_bound_ge_sup.
      + rewrite summable_ds_helper.
        apply (sup_is_upper_bound (λ n0 : nat, sum_n (a ∘ σ) n0)).
  Qed.

End prod1.

Section prod2.
  Variable (a: nat * nat → R).
  Variable (σ: nat → nat * nat).

  Variable (POS: ∀ n n', 0 <= a (n, n')).
  Variable (INJ: ∀ n n', a (σ n) <> 0 → σ n = σ n' → n = n').
  Variable (COV: ∀ n, a n <> 0 → ∃ m, σ m = n).
  Variable (EXS: ex_series (a ∘ σ)).

  Lemma summable_implies_ds:
    double_summable a.
  Proof.
    rewrite /double_summable.
    exists (Sup_seq (λ n, sum_n (a ∘ σ) n)).
    intro.
    apply rbar_le_finite.
    - apply (is_finite_bounded 0 (Series (a ∘ σ))).
      * apply (Sup_seq_minor_le _ _ 0).
        rewrite /=sum_O//.
        simpl; destruct (σ 0). auto.
      * apply upper_bound_ge_sup.
        intro n0; simpl.
        apply series_pos_partial_le; auto.
        intro m; simpl; destruct (σ m); auto.
    - rewrite -summable_ds_helper; auto.
      apply (sup_is_upper_bound (λ n0 : nat, sum_n (λ j : nat, sum_n (λ k : nat, a (j, k)) n0) n0)).
  Qed.

  Lemma is_lim_seq_sum_n (f: nat * nat → R) (h: nat → R) l:
    (∀ j, j ≤ l → is_lim_seq (λ m, sum_n (λ k, f (j, k)) m) (h j)) →
    is_lim_seq (λ m, sum_n (λ j, sum_n (λ k, f (j, k)) m) l) (sum_n h l).
  Proof.
    intros Hh.
    induction l => //=.
    - intros. rewrite sum_O => //=. apply (is_lim_seq_ext (λ m, sum_n (λ k, f (O, k)) m)).
      * intros. rewrite sum_O. done.
      * by apply Hh.
    - rewrite sum_Sn.
      apply (is_lim_seq_ext (λ m, plus (sum_n (λ j, sum_n (λ k, f (j, k)) m) l)
                                    (sum_n (λ k, f (S l, k)) m))).
      * intros. by rewrite sum_Sn.
      * apply: is_lim_seq_plus; eauto.
        rewrite //=.
  Qed.

  Lemma is_lim_seq_fin_abs:
    ∀ (u : nat → R) (l : R), is_lim_seq u l → is_lim_seq (λ n : nat, Rabs (u n)) (Rabs l).
  Proof.
    intros.
    assert (Rabs l = Rbar_abs l) as -> by auto.
    by apply (is_lim_seq_abs u (Finite l)).
  Qed.

  (* TODO: factor out some of the proofs of is_finite_bounded, clean up *)
  Lemma is_series_double_covering:
    is_series (λ j, Series (λ k, a (j, k))) (Series (a ∘ σ)).
  Proof.
    pose proof (summable_implies_ds) as DS.
    destruct (DS_n_to_nm a POS DS) as (r&Hr).
    destruct (EXS) as (v'&Hconv).
    apply sup_is_lim.
    - intros; apply series_ge_0; auto.
    - rewrite lim_is_sup'; auto; last first.
      + intro n; simpl; destruct (σ n); auto.
      + eapply is_sup_seq_ext.
        {
          intro n.
          rewrite -(fubini_fin_inf (λ '(x,y), a(y,x))); auto.
          intro.
          apply ex_series_row; auto.
        }
        rewrite -summable_ds_helper; auto.
        apply Rbar_is_lub_sup_seq.
        rewrite /Lub.Rbar_is_lub; split.
        * rewrite /Lub.Rbar_is_upper_bound.
          intros x (n&->).
          rewrite rbar_finite_real_eq; last first.
          {
            apply (is_finite_bounded 0 r).
            - apply (Sup_seq_minor_le _ _ 0).
              rewrite /=sum_O/=sum_O//.
            - apply upper_bound_ge_sup.
              intro; simpl; auto.
          }
          rewrite Series_real_sup; last first.
          { intros; apply partial_sum_pos; auto. }
          rewrite rbar_finite_real_eq; last first.
          {
            apply (is_finite_bounded 0 r).
            - apply (Sup_seq_minor_le _ _ 0).
              rewrite //=sum_O.
              by apply partial_sum_pos.
            - apply upper_bound_ge_sup.
              intro; simpl.
              by rewrite -fubini_fin_sum.
          }
          apply upper_bound_ge_sup.
          intro m.
          apply (Sup_seq_minor_le _ _ (n `max` m)).
          simpl.
          etrans.
          ** apply partial_sum_mon; [ intro; apply partial_sum_pos; auto | ].
             by apply (Nat.le_max_r n).
          ** rewrite {1}fubini_fin_sum.
             apply sum_n_le.
             intros. apply partial_sum_mon; [ intro; auto | ].
             lia.
        * rewrite /Lub.Rbar_is_upper_bound.
          intros b Hb.
          rewrite rbar_finite_real_eq; last first.
          {
            apply (is_finite_bounded 0 r).
            - apply (Sup_seq_minor_le _ _ 0).
              rewrite /=sum_O/=sum_O//.
            - apply upper_bound_ge_sup.
              intro; simpl; auto.
          }
          apply upper_bound_ge_sup.
          intro n.
          etrans; last first.
          ** apply Hb.
             exists n. reflexivity.
          ** simpl.
             rewrite fubini_fin_sum.
             apply series_pos_partial_le; [ intro; apply partial_sum_pos; auto | ].
             apply ex_pos_bounded_series; [ intro; apply partial_sum_pos; auto | ].
             exists r.
             intro.
             rewrite -fubini_fin_sum; auto.
  Qed.

  Lemma is_series_double_covering':
    is_series (a ∘ σ) (Series (λ j, Series (λ k, a (j, k)))).
  Proof.
    specialize (is_series_unique _ _ (is_series_double_covering)) => ->.
    by apply Series_correct.
  Qed.

  Lemma Series_double_covering:
    Series (λ j, Series (λ k, a (j, k))) = (Series (a ∘ σ)).
  Proof.
    apply is_series_unique, is_series_double_covering.
  Qed.

  Lemma double_summable_fubini f:
    (∀ n m, 0 <= f(n,m)) →
    double_summable f →
    Series (λ n, Series (λ m, f (n, m))) = Series (λ m, Series (λ n, f (n, m))).
  Proof.
    intros Hpos DS.
    rewrite fubini_pos_series; auto.
    - intro.
      apply ex_series_row; auto.
    - apply ex_series_row_col; auto.
  Qed.

End prod2.
