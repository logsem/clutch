From Coq Require Import Reals Psatz.
From Coquelicot Require Import Series Lim_seq Rbar.
From stdpp Require Export countable.
From clutch.prelude Require Import base Coquelicot_ext.
Import Hierarchy.

Open Scope R.

Section rbar_extra.

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

End rbar_extra.

Lemma ex_series_eventually0 (a: nat → R):
  (∃ N, ∀ n, n ≥ N → a n = 0) → ex_series a.
Proof.
  intros (N & Hev0). apply: ex_series_Cauchy.
  rewrite /Cauchy_series => eps. exists N => n m Hlen Hlem.
  assert (Heq: sum_n_m a n m = 0).
  {
    rewrite /sum_n_m.
    rewrite (Iter.iter_nat_ext_loc _ _ _ (λ x, 0)).
    - rewrite /plus/zero//=/Iter.iter_nat Iter.iter_const; nra.
    - intros k (?&?). apply Hev0. lia.
  }
  rewrite /norm //= /abs //=. destruct eps =>//=. rewrite Heq Rabs_right; nra.
Qed.

Section positive.

  (* Results about positive (non-negative) series *)

  Context `{Countable A}.
  Implicit Types f g : A → R.

  Lemma mon_succ_to_mon (h : nat -> R) :
    (∀ p, h p <= h (S p)) ->
    (∀ m n, (m <= n)%nat -> h m <= h n).
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
    (∀ n, 0 <= h n) ->
    0 <= sum_n h p.
  Proof.
    intros Hpos.
    rewrite /sum_n.
    induction p.
    + rewrite sum_n_n; auto.
    + rewrite sum_n_Sm; auto with arith.
      apply Rplus_le_le_0_compat; auto.
  Qed.


  Lemma partial_sum_elem (h : nat → R) p :
    (∀ n, 0 <= h n) ->
    h p <= sum_n h p.
  Proof.
    intros Hpos.
    rewrite /sum_n.
    induction p.
    + rewrite sum_n_n; auto.
      apply Rle_refl.
    + rewrite sum_n_Sm; auto with arith.
      assert (h (S p) = 0 + h (S p)) as Haux; try lra.
      rewrite {1}Haux.
      apply Rplus_le_compat; [apply partial_sum_pos | apply Rle_refl]; auto.
  Qed.

  Lemma partial_sum_mon (h : nat → R) p q :
    (∀ n, 0 <= h n) ->
    (p ≤ q) →
    sum_n h p <= sum_n h q.
  Proof.
    intros Hge Hpq.
    rewrite /sum_n.
    induction q.
    + assert (p = 0%nat); auto with arith.
      simplify_eq; done.
    + destruct (PeanoNat.Nat.le_gt_cases p q) as [H1 | H1].
      ++ specialize (IHq H1).
         rewrite sum_n_Sm; auto with arith.
         rewrite /plus /=.
         specialize (Hge (S q)).
         lra.
      ++ assert (p = S q); auto with arith.
         rewrite -> H0; auto.
         lra.
  Qed.

  (* TODO: move to [prelude/Coquelicot_ext.v] *)
  (* Strangely, this was not in Coquelicot *)
  Lemma is_series_ge0 (h : nat → R) r:
    (∀ n, 0 <= h n) ->
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

  Lemma rmult_finite (p q : R) :
    Finite (p * q) = Rbar_mult (Finite p) (Finite q).
  Proof.
    auto.
  Qed.

  Lemma lim_is_sup (h: nat -> R) r :
    (∀ n, 0 <= h n) ->
    is_series h r →
    is_sup_seq (sum_n h) (Finite r).
  Proof.
    intros Hge Hs.
    rewrite /is_sup_seq.
    pose proof (is_series_partial_pos h) as Hpart.
    pose proof (is_series_ge0 _ _ Hge Hs) as Hr.
    intro eps; split.
    + intro n.
      specialize (Hpart n r Hge Hs).
      rewrite /Rbar_lt.
      assert (eps > 0); try lra.
      pose proof (cond_pos eps); lra.
    + pose proof (Hs) as Hs'.
      (* rewrite /is_series in Hs.
      rewrite /locally /eventually in Hs.
      rewrite /filterlim in Hs.
      rewrite /filter_le in Hs.
      rewrite /filtermap in Hs. *)
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
        lra.
      }
      rewrite Habs in HN.
      rewrite /minus /plus /= /opp /= in HN.
      lra.
  Qed.


  Lemma sup_is_lim (h: nat -> R) r :
    (∀ n, 0 <= h n) ->
    is_sup_seq (sum_n h) (Finite r) ->
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

  Lemma eq_rbar_finite x y :
    (Finite x) = y -> x = real(y).
  Proof.
    intro Heq.
    destruct y; simplify_eq; auto.
  Qed.

  Lemma Rbar_0_le_to_Rle x :
    Rbar_le 0 x -> 0 <= x.
  Proof.
    intro Hle.
    destruct x; simpl; auto; lra.
  Qed.


  Lemma Rbar_0_le_to_Rle' x :
    Rbar_le 0 (Finite x) -> 0 <= x.
  Proof.
    intro Hle; auto.
  Qed.

  Lemma lim_is_sup' (h: nat -> R) :
    (∀ n, 0 <= h n) ->
    ex_series h →
    Series h = real (Sup_seq (sum_n h)).
  Proof.
    intros Hpos Hex.
    apply Series_correct, lim_is_sup, is_sup_seq_unique in Hex; auto.
    apply eq_rbar_finite; auto.
  Qed.


  Lemma lim_is_sup'' (h: nat -> R) :
    (∀ n, 0 <= h n) ->
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
    is_sup_seq h (Finite r) ->
    (h n) <= r.
  Proof.
    intro Hr.
    assert (Rbar_le (Finite (real (h n))) (Finite r)); auto.
    assert (real (Finite (h n)) = h n) as ->; auto.
    apply (is_sup_seq_major (fun x : nat => Finite (h x)) (Finite r)); auto.
  Qed.

  Lemma upper_bound_ge_sup (h : nat → Rbar) r :
    (∀ n, Rbar_le (h n) r) ->
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
    is_sup_seq h (Finite l) ->
    (∀ n, h n <= r) ->
    l <= r.
  Proof.
    intros Hsup H2.
    assert (Rbar_le (Finite l) (Finite r)); auto.
    rewrite <- (is_sup_seq_unique (λ x : nat, h x) l); auto.
    apply (upper_bound_ge_sup (λ x : nat, h x) r); auto.
  Qed.

  Lemma sup_seq_eq_antisym (h1 h2 : nat -> R) :
    (∀ m, exists n, h1 m <= h2 n) ->
    (∀ m, exists n, h2 m <= h1 n) ->
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


  (* Maybe can be proven from partial_summation_R *)
  Lemma ex_pos_bounded_series (h : nat -> R) :
    (∀ n, 0 <= h n) ->
    (exists l, ∀ n, sum_n h n <= l) ->
    ex_series h.
  Proof.
    intros Hpos (l & Hl).
    exists (real (Sup_seq (λ n, sum_n h n))).
    apply sup_is_lim; auto.
    rewrite (Rbar_le_sandwich 0 l).
    + apply Sup_seq_correct.
    + apply (Rbar_le_trans _ (sum_n h 0%nat)).
      ++ rewrite sum_O.
         assert (0 <= (h 0%nat)); auto.
      ++ apply (sup_is_upper_bound (λ n : nat, sum_n h n) 0%nat).
    + destruct (Sup_seq (λ n : nat, sum_n h n)) eqn:Hsup; simpl; auto.
      ++ assert (Rbar_le (Finite r) (Finite l)); auto.
         rewrite <- Hsup.
         apply upper_bound_ge_sup.
         intro n; auto.
         specialize (Hl n); auto.
      ++ assert (Rbar_le (p_infty) (Finite l)); auto.
         rewrite <- Hsup.
         apply upper_bound_ge_sup.
         intro n; auto.
         specialize (Hl n); auto.
  Qed.

  Lemma Rbar_le_opp (p q : Rbar) (r : R) :
    Rbar_le (Rbar_plus p r) q <-> Rbar_le p (Rbar_plus q (Finite (-r))).
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

  Lemma double_sup_diag (h : nat * nat → R) :
    (∀ n m n', (n <= n')%nat -> h (n, m) <= h (n' , m)) ->
    (∀ n m m', (m <= m')%nat -> h (n, m) <= h (n , m')) ->
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


  Lemma series_ge_0 (h : nat -> R):
    (∀ a, 0 <= h a) ->
    0 <= Series h.
  Proof.
    intro Hpos.
    rewrite /Series /Lim_seq.
    assert (Rbar_le 0 (LimSup_seq (sum_n h))).
    { rewrite <- (LimSup_seq_const 0).
      apply LimSup_le.
      exists 0%nat; intros.
      apply partial_sum_pos; auto.
    }
    assert (Rbar_le 0 (LimInf_seq (sum_n h))).
    {
      rewrite <- (LimInf_seq_const 0).
      apply LimInf_le.
      exists 0%nat; intros.
      apply partial_sum_pos; auto.
    }
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

  Fixpoint max_seq (f : nat -> nat) n :=
    match n with
      | 0 => f 0%nat
      | S m => max (f (S m)) (max_seq f m)
    end.

  Lemma sum_max_seq (f : nat -> R) h n `{Bij nat nat h}:
   (forall n, 0 <= f n) ->
   (sum_n (λ n0 : nat, f (h n0)) n) <= (sum_n (λ n0 : nat, f n0) (max_seq h n)).
  Admitted.
   (*
    intro.
    apply partial_sum_mon.
    intro; induction n.
    - rewrite sum_O /max_seq.
      destruct (h 0%nat).
      + rewrite sum_O; lra.
      + rewrite sum_Sn.
        etrans; [ | apply Rplus_le_compat_r, partial_sum_pos; auto].
        lra.
   - rewrite sum_Sn.
     unfold max_seq.
     fold max_seq.
     etrans; [ apply Rplus_le_compat_r, IHn | ].
     apply Nat.max_case.
   *)

  Lemma is_series_bijection (f : nat -> R) h v `{Bij nat nat h} :
    (forall n, 0 <= f n) ->
    is_series f v ->
    is_series (λ n, f (h n)) v.
  Proof.
    intros Hpos Hf.
    unfold is_series.
    rewrite /is_series.
    apply sup_is_lim; auto.
    apply lim_is_sup in Hf; auto.
    intro eps; split.
    - assert (forall n, (sum_n (λ n0 : nat, f (h n0)) n) <= (sum_n (λ n0 : nat, f n0) (max_seq h n))) as Haux.
      {
        intro; eapply sum_max_seq; eauto.
        (*
        induction n.
        - rewrite sum_O/=.
          apply partial_sum_elem; auto.
        - rewrite sum_Sn/=.
          destruct (Nat.le_dec (h (S n)) (max_seq h n)) as [H1 | H2].
          + pose proof (PeanoNat.Nat.max_r_iff (h (S n)) (max_seq h n)) as [? ->]; auto.
            apply (Rle_trans _ (sum_n (λ n0 : nat, f n0) (max_seq h n) + f (h (S n))));
              [apply Rplus_le_compat_r; auto | ].
            admit.
          + admit.
        *)
      }
      intro n.
      eapply Rbar_le_lt_trans; [apply rbar_le_rle, Haux | apply Hf ].
    -
  Abort.

  Lemma fubini_fin_sum (h : nat * nat → R) n m:
    sum_n (λ a, sum_n (λ b, h (a, b)) n ) m
    = sum_n (λ b, sum_n (λ a, h (a, b)) m ) n.
  Proof.
    intros.
    apply sum_n_switch.
  Qed.

  Lemma sum_n_le (h g: nat -> R) n:
    (∀ m, h m <= g m) ->
    sum_n h n <= sum_n g n.
  Proof.
    intro Hle.
    induction n.
    - do 2 rewrite sum_O; auto.
    - do 2 rewrite sum_Sn.
      apply Rplus_le_compat; auto.
  Qed.

  Lemma series_pos_partial_le (h : nat -> R) n:
    (∀ a, 0 <= h a) ->
    ex_series h ->
    sum_n h n <= Series h.
  Proof.
    intros Hpos Hex.
    rewrite lim_is_sup'; auto.
    destruct Hex as (l & Hl).
    apply lim_is_sup in Hl; auto.
    assert (Rbar_le (Finite (sum_n h n)) (Sup_seq (λ n0 : nat, sum_n h n0))); auto.
    - apply (is_sup_seq_major (λ n0 : nat, sum_n h n0)).
      apply Sup_seq_correct.
    - rewrite (is_sup_seq_unique _ l); auto.
      rewrite (is_sup_seq_unique _ l) in H0; auto.
  Qed.

  Lemma series_pos_elem_le (h : nat -> R) n:
    (∀ a, 0 <= h a) ->
    ex_series h ->
    h n <= Series h.
  Proof.
    intros Hpos Hex.
    eapply Rle_trans; [apply partial_sum_elem | ]; auto.
    apply series_pos_partial_le; auto.
  Qed.

  Lemma fubini_fin_inf (h : nat * nat → R) n:
    (∀ a b, 0 <= h (a, b)) ->
    (∀ b, ex_series (λ a, h (a, b))) ->
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
    (∀ a b, 0 <= h (a, b)) ->
    (∀ a, ex_series (λ b, h (a, b))) ->
    (ex_series (λ a, Series (λ b, h (a, b)))) ->
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
    (∀ a b, 0 <= h (a, b)) ->
    (∀ a, ex_series (λ b, h (a, b))) ->
    (ex_series (λ a, Series (λ b, h (a, b)))) ->
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

  Lemma series_bounded (h : nat -> R) l :
    (∀ a, 0 <= h a) ->
    (∀ n, sum_n h n <= l) ->
    ex_series h ->
    Series h <= l.
  Proof.
    intros Hpos Hle Hex.
    rewrite lim_is_sup'; auto.
    apply (upper_bound_ge_sup' (λ n : nat, sum_n h n) l); auto.
    assert (Finite (real (Sup_seq (λ n : nat, sum_n h n))) =
              Sup_seq (λ n : nat, sum_n h n)) as ->.
    {
      apply (Rbar_le_sandwich 0 l).
      + apply (Rbar_le_trans _ (sum_n h 0%nat)).
        * rewrite sum_O; simpl; auto.
        * apply (sup_is_upper_bound (λ n : nat, sum_n h n)).
      + apply upper_bound_ge_sup; auto.
    }
    apply (Sup_seq_correct (λ x : nat, sum_n h x)).
  Qed.

  Lemma series_bounded_rbar (h : nat -> R) (l : Rbar) :
    (∀ a, 0 <= h a) ->
    (∀ n, Rbar_le (sum_n h n) l) ->
    ex_series h ->
    Rbar_le (Series h) l.
  Proof.
    intros Hpos Hle Hex.
    destruct l eqn:Hl; simpl; auto.
    - apply series_bounded; auto.
    - apply (Hle 0%nat); auto.
  Qed.

  Lemma fubini_pos_series (h : nat * nat → R) :
    (∀ a b, 0 <= h (a, b)) ->
    (∀ a, ex_series (λ b, h (a, b))) ->
    (ex_series (λ a, Series (λ b, h (a, b)))) ->
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

End positive.

Section mct.

  Lemma mon_sup_succ (h : nat -> R) :
    (∀ n, h n <= h (S n)) ->
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
    {
      apply (Rbar_le_sandwich r r); auto.
      + apply (Sup_seq_minor_le _ _ 0%nat); apply Rbar_le_refl.
      + apply upper_bound_ge_sup; intro; apply Rbar_le_refl.
    }
    apply Rle_antisym.
    + apply finite_rbar_le; auto.
      apply (upper_bound_ge_sup); intro; apply Rbar_le_refl.
    + apply rbar_le_finite; auto.
      apply (Sup_seq_minor_le _ _ 0%nat); apply Rbar_le_refl.
  Qed.

  (* This is quite convoluted, I wonder if it can be simplified *)
  Lemma Sup_seq_bounded_plus_l (f : nat -> R) (b r : R) :
    (∀ n, 0 <= f n <= b) ->
    Sup_seq (λ a, r + (f a)) =
      r + real (Sup_seq f).
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
          apply (upper_bound_ge_sup _ b), Hf.
      }
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
          apply Hf.
      }
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
    (∀ n, 0 <= f n <= b) ->
    Sup_seq (λ a, (f a) + r) =
      real (Sup_seq f) + r.
  Proof.
    intro Hf.
    rewrite Rplus_comm.
    erewrite Sup_seq_ext; last first.
    - intro; rewrite Rplus_comm; done.
    - eapply Sup_seq_bounded_plus_l; eauto.
  Qed.

  Lemma Sup_seq_bounded_plus_sup (f g : nat -> R) (b r : R) :
    (∀ n, 0 <= f n <= b) ->
    (∀ n, 0 <= g n <= b) ->
    (∀ n, f n <= f (S n)) ->
    (∀ n, g n <= g (S n)) ->
    Sup_seq (λ a, (f a) + (g a)) =
      real (Sup_seq f) + (Sup_seq g).
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

  Lemma MCT_aux1 (h : nat -> nat → R) (l : nat -> R) (r : R) (M : nat) :
    (∀ n a, 0 <= (h n a)) ->
    (∀ n a, (h n a) <= (h (S n) a)) ->
    (∀ a, exists s, ∀ n, h n a <= s ) ->
    (∀ n, is_series (h n) (l n)) ->
    is_sup_seq l (Finite r) ->
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

  Lemma MCT_aux2 (h : nat -> nat → R) (l : nat -> R) (r : R) :
    (∀ n a, 0 <= (h n a)) ->
    (∀ n a, (h n a) <= (h (S n) a)) ->
    (∀ a, exists s, ∀ n, h n a <= s ) ->
    (∀ n, is_series (h n) (l n)) ->
    is_sup_seq l (Finite r) ->
    Rbar_le (Sup_seq (λ m, sum_n (λ a, real (Sup_seq (λ n, h n a))) m)) r.
  Proof.
    intros Hpos Hmon Hbd Hseries Hsup.
    apply upper_bound_ge_sup.
    intro M.
    erewrite MCT_aux1; eauto.
    apply upper_bound_ge_sup.
    intro n.
    apply (Rbar_le_trans _ (Series (λ a : nat, h n a))).
    - apply series_pos_partial_le; auto.
      exists (l n); auto.
    - apply (Rbar_le_trans _ (l n)).
      + rewrite <- (is_series_unique (λ a : nat, h n a) (l n)); auto.
        apply Rbar_le_refl.
      + erewrite <- is_sup_seq_unique; eauto.
        apply (sup_is_upper_bound (λ x : nat, l x)).
  Qed.

  Lemma MCT_aux3 (h : nat -> nat → R) (l : nat -> R) (r : R) :
    (∀ n a, 0 <= (h n a)) ->
    (∀ n a, (h n a) <= (h (S n) a)) ->
    (∀ a, exists s, ∀ n, h n a <= s ) ->
    (∀ n, is_series (h n) (l n)) ->
    is_sup_seq l (Finite r) ->
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

  Lemma MCT_aux4 (h : nat -> nat → R) (l : nat -> R) (r : R) :
    (∀ n a, 0 <= (h n a)) ->
    (∀ n a, (h n a) <= (h (S n) a)) ->
    (∀ a, exists s, ∀ n, h n a <= s ) ->
    (∀ n, is_series (h n) (l n)) ->
    is_sup_seq l (Finite r) ->
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


  Lemma MCT_series (h : nat -> nat → R) (l : nat -> R) (r : R) :
    (∀ n a, 0 <= (h n a)) ->
    (∀ n a, (h n a) <= (h (S n) a)) ->
    (∀ a, exists s, ∀ n, h n a <= s ) ->
    (∀ n, is_series (h n) (l n)) ->
    is_sup_seq l (Finite r) ->
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

  Lemma MCT_ex_series (h : nat -> nat → R) (l : nat -> R) (r : R) :
    (∀ n a, 0 <= (h n a)) ->
    (∀ n a, (h n a) <= (h (S n) a)) ->
    (∀ a, exists s, ∀ n, h n a <= s ) ->
    (∀ n, is_series (h n) (l n)) ->
    is_sup_seq l (Finite r) ->
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

End mct.
