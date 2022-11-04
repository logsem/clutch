From Coq Require Import Reals Psatz.
From Coquelicot Require Import Series Hierarchy Lim_seq Rbar.
From stdpp Require Import option.
From stdpp Require Export countable.
From self.prelude Require Import base Coquelicot_ext stdpp_ext classical.
Import Hierarchy.

Open Scope R.

(** A theory of (in)finite series over countable types.  *)
Section countable_sum.
  Context `{Countable A}.

  Implicit Types f g : A → R.

  (** 'Traverses' the type in the order given by decoding [0, 1, 2, ...] *)
  Definition countable_sum (f : A → R) :=
    λ (n : nat), from_option f 0 (encode_inv_nat n).

  Lemma countable_sum_0 f m :
    (∀ n, f n = 0) → countable_sum f m = 0.
  Proof. intros. rewrite /countable_sum. destruct (encode_inv_nat _); eauto. Qed.

  Lemma countable_sum_ge_0 f m :
    (∀ n, 0 <= f n) → 0 <= countable_sum f m.
  Proof. intros. rewrite /countable_sum. destruct (encode_inv_nat _)=>//=. Qed.

  Lemma countable_sum_ext f g m :
    (∀ n, f n = g n) → countable_sum f m = countable_sum g m.
  Proof. intros ?. rewrite /countable_sum. destruct (encode_inv_nat _) => //=. Qed.

  Lemma countable_sum_le f g m :
    (∀ n, f n <= g n) → countable_sum f m <= countable_sum g m.
  Proof. intros ?. rewrite /countable_sum. destruct (encode_inv_nat _) =>//=. Qed.

  Lemma countable_sum_scal c f n :
    countable_sum (λ x, scal c (f x)) n = scal c (countable_sum f n).
  Proof.
    intros. rewrite //= /countable_sum /scal //= /mult //=.
    destruct (encode_inv_nat _) => //=; lra.
  Qed.

  Lemma countable_sum_plus f g n :
    countable_sum (λ x, f x + g x) n = countable_sum f n + countable_sum g n.
  Proof.
    intros. rewrite //=/countable_sum; destruct (encode_inv_nat) => //=. lra.
  Qed.

  Lemma countable_sum_minus f g n :
    countable_sum (λ x, f x - g x) n = countable_sum f n - countable_sum g n.
  Proof.
    intros. rewrite //=/countable_sum; destruct (encode_inv_nat) => //=. lra.
  Qed.

  Lemma countable_sum_mult f g n :
    countable_sum (λ x, f x * g x) n = countable_sum f n * countable_sum g n.
  Proof.
    intros. rewrite //=/countable_sum; destruct (encode_inv_nat) => //=. lra.
  Qed.

  Lemma countable_sum_Rabs f n :
    countable_sum (λ x, Rabs (f x)) n = Rabs (countable_sum f n).
  Proof.
    intros. rewrite //=/countable_sum; destruct (encode_inv_nat _) => //=. rewrite Rabs_R0 //=.
  Qed.

  Lemma countable_sum_scal_l f c n :
    countable_sum (λ x, c * f x) n = c * countable_sum f n.
  Proof. apply countable_sum_scal. Qed.

  Lemma countable_sum_scal_r f c n :
    countable_sum (λ x, f x * c) n = countable_sum f n * c.
  Proof.
    intros. rewrite //=/countable_sum; destruct (encode_inv_nat) => //=. lra. Qed.

  Global Instance countable_sum_Proper:
    Proper (pointwise_relation A (@eq R) ==> pointwise_relation nat (@eq R)) countable_sum.
  Proof. intros ?? ? x. rewrite /countable_sum. destruct (encode_inv_nat _); eauto. Qed.

  Global Instance countable_sum_Proper' :
    Proper (pointwise_relation A (@eq R) ==> eq ==> eq) countable_sum.
  Proof. intros ?? ? ? ??. subst. eapply countable_sum_ext; eauto. Qed.

  (** TODO: more lifted lemmas on [sumC] *)
  Definition sumC_n (f : A → R) := sum_n (countable_sum f).

End countable_sum.


Section series.
  Context `{Countable A}.

  Implicit Types f g : A → R.

  (** Lifting of the Coquliecot predicates for working with series *)
  Definition is_seriesC f := is_series (countable_sum f).
  Definition ex_seriesC f := ∃ a, is_seriesC f a.
  Definition SeriesC f := Series (countable_sum f).

  Lemma is_seriesC_0 f :
    (∀ n, f n = 0) → is_seriesC f 0.
  Proof.
    intros ?. apply is_series_0=> n.
    rewrite /countable_sum. destruct (encode_inv_nat _)=>/=; auto.
  Qed.

  Lemma is_seriesC_ext f g l :
    (∀ n, f n = g n) → is_seriesC g l → is_seriesC f l.
  Proof.
    intros ?. apply is_series_ext=> n. by apply countable_sum_ext.
  Qed.

  Lemma is_seriesC_unique f l :
    is_seriesC f l → SeriesC f = l.
  Proof.
    apply is_series_unique.
  Qed.

  Lemma ex_seriesC_ext f g :
    (∀ n, f n = g n) → ex_seriesC f → ex_seriesC g.
  Proof.
    intros ?. apply ex_series_ext=> n. by apply countable_sum_ext.
  Qed.

  Lemma is_seriesC_chain f g v : is_seriesC g (SeriesC f) → is_seriesC f v → is_seriesC g v.
  Proof.
    intros Hs2 Hs1. apply is_seriesC_unique in Hs1. rewrite -Hs1. done.
  Qed.

  Lemma SeriesC_correct f :
    ex_seriesC f → is_seriesC f (SeriesC f).
  Proof. apply Series_correct. Qed.

  Lemma SeriesC_correct' a v:
    SeriesC a = v → ex_seriesC a → is_seriesC a v.
  Proof. by intros <- ?; apply SeriesC_correct. Qed.

  Lemma SeriesC_0 f :
    (∀ x, f x = 0) → SeriesC f = 0.
  Proof. intros Heq0. apply Series_0=> ?. by apply countable_sum_0. Qed.

  Lemma SeriesC_ge_0 (f : A → R) :
    (∀ x, 0 <= f x) →
    ex_seriesC f →
    0 <= SeriesC f.
  Proof.
    intros Heq0 Hex.
    rewrite -(SeriesC_0 (λ _ : A, 0)); [|done].
    apply Series_le; [|done].
    intros n. split.
    + apply countable_sum_ge_0. intros ?; lra.
    + by apply countable_sum_le.
  Qed.

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
    destruct (encode_inv_nat _) => //=; lra.
  Qed.

  Lemma SeriesC_le' f g :
    (∀ n, f n <= g n) →
    ex_seriesC f →
    ex_seriesC g →
    SeriesC f <= SeriesC g.
  Proof.
    intros ???. apply Series_le' => //= n.
    rewrite /countable_sum.
    destruct (encode_inv_nat _) => //=.
  Qed.

  Lemma SeriesC_scal_l f c :
    SeriesC (λ x, c * f x) = c * SeriesC f.
  Proof.
    intros. rewrite -Series_scal_l. apply Series_ext. apply countable_sum_scal_l.
  Qed.

  Lemma SeriesC_scal_r f c :
    SeriesC (λ x, f x * c) = SeriesC f * c.
  Proof.
    intros. rewrite -Series_scal_r. apply Series_ext. apply countable_sum_scal_r.
  Qed.

  Lemma SeriesC_plus f g :
    ex_seriesC f →
    ex_seriesC g →
    SeriesC (λ x, f x + g x) = SeriesC f + SeriesC g.
  Proof.
    intros. rewrite -Series_plus //. apply Series_ext. apply countable_sum_plus.
  Qed.

  Lemma SeriesC_minus f g :
    ex_seriesC f →
    ex_seriesC g →
    SeriesC (λ x, f x - g x) = SeriesC f - SeriesC g.
  Proof.
    intros. rewrite -Series_minus //. apply Series_ext. apply countable_sum_minus.
  Qed.

  Lemma ex_seriesC_0 :
    ex_seriesC (λ _, 0).
  Proof.
    eexists; by eapply is_seriesC_0.
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
    intros x. destruct (Hle x); eauto. rewrite Rabs_right; eauto; lra.
  Qed.

  Lemma ex_seriesC_scal_l f c :
    ex_seriesC f →
    ex_seriesC (λ x, c * f x).
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

  Global Instance is_series_Proper:
    Proper (pointwise_relation A (@eq R) ==> @eq R ==> iff) is_seriesC.
  Proof. intros ?? ? ?? ?; subst; split; eapply is_seriesC_ext; eauto. Qed.

  Global Instance ex_series_Proper:
    Proper (pointwise_relation A (@eq R) ==> iff) ex_seriesC.
  Proof. intros ?? ?; split; eapply ex_seriesC_ext; eauto. Qed.

  Global Instance Series_Proper:
    Proper (pointwise_relation A (@eq R) ==> eq) SeriesC.
  Proof. intros ?? ?; eapply SeriesC_ext; eauto. Qed.

End series.

Section filter.
  Context `{Countable A}.

  Implicit Types P Q : A → Prop.

  Lemma is_seriesC_singleton (a : A) v :
    is_seriesC (λ (n : A), if bool_decide (n = a) then v else 0) v.
  Proof.
    rewrite /is_seriesC.
    eapply is_series_ext; [|apply (is_series_singleton (encode_nat a))].
    intros n =>/=. rewrite /countable_sum.
    case_bool_decide as Hneq=>/=; subst.
    - rewrite encode_inv_encode_nat //= bool_decide_eq_true_2 //.
    - destruct (encode_inv_nat _) eqn:Heq=>//=.
      case_bool_decide; [|done]; subst.
      exfalso. apply Hneq. symmetry. by apply encode_inv_Some_nat.
  Qed.

  Lemma ex_seriesC_singleton (a : A) v :
    ex_seriesC (λ (n : A), if bool_decide (n = a) then v else 0).
  Proof. eexists. eapply is_seriesC_singleton. Qed.

  Lemma SeriesC_singleton (a : A) v :
    SeriesC (λ n, if bool_decide (n = a) then v else 0) = v.
  Proof. apply is_series_unique, is_seriesC_singleton. Qed.

  Lemma SeriesC_ge_elem  (f : A → R) (a : A) :
    (∀ x, 0 <= f x) →
    ex_seriesC f →
    f a <= SeriesC f.
  Proof.
    intros Hf Hex.
    rewrite -(SeriesC_singleton a (f a)).
    apply SeriesC_le; [|done].
    intros a'. specialize (Hf a').
    case_bool_decide; simplify_eq; lra.
  Qed.

  (* These are sometimes convenient *)
  Lemma ex_seriesC_singleton' (a : A) v :
    ex_seriesC (λ (n : A), if bool_decide (a = n) then v else 0).
  Proof.
    apply (ex_seriesC_ext (λ n : A, if bool_decide (n = a) then v else 0)
                          (λ n : A, if bool_decide (a = n) then v else 0)).
    + intro a'; rewrite (bool_decide_ext (a = a') (a' = a)); done.
    + apply ex_seriesC_singleton.
  Qed.

  Lemma SeriesC_singleton' (a : A) v :
    SeriesC (λ n, if bool_decide (a = n) then v else 0) = v.
  Proof.
    rewrite (SeriesC_ext (λ n : A, if bool_decide (a = n) then v else 0)
             (λ n : A, if bool_decide (n = a) then v else 0)).
    + apply SeriesC_singleton.
    + intro a'; rewrite (bool_decide_ext (a = a') (a' = a)); done.
  Qed.

  Lemma is_seriesC_filter_pos f v P `{∀ x, Decision (P x)} :
    (∀ n, 0 <= f n) →
    is_seriesC f v →
    ex_seriesC (λ n, if bool_decide (P n) then f n else 0).
  Proof.
    intros Hge Hconv.
    apply: ex_seriesC_le; last by (exists v; eauto).
    intros n. rewrite /norm /= /abs.
    specialize (Hge n). case_bool_decide; lra.
  Qed.

  Lemma is_seriesC_filter_impl f v P Q `{∀ x, Decision (P x), ∀ x, Decision (Q x)} :
    (∀ n, 0 <= f n) →
    is_seriesC (λ n, if bool_decide (P n) then f n else 0) v →
    (∀ n, Q n → P n) →
    ex_seriesC (λ n, if bool_decide (Q n) then f n else 0).
  Proof.
    intros Hge Hconv Himp. apply ex_seriesC_Rabs.
    apply: ex_seriesC_le; last by (exists v; eauto).
    intros n. rewrite /norm//=/abs//=.
    specialize (Hge n). specialize (Himp n).
    do 2 case_bool_decide; try (rewrite Rabs_right; auto; lra).
    tauto.
  Qed.

  Lemma ex_seriesC_filter_impl f P Q `{∀ x, Decision (P x), ∀ x, Decision (Q x)} :
    (∀ n, 0 <= f n) →
    ex_seriesC (λ n, if bool_decide (P n) then f n else 0) →
    (∀ n, Q n → P n) →
    ex_seriesC (λ n, if bool_decide (Q n) then f n else 0).
  Proof. intros ? [? ?] ?. eapply is_seriesC_filter_impl; eauto. Qed.

  Lemma ex_seriesC_filter_pos f P `{∀ x, Decision (P x)} :
    (∀ n, 0 <= f n) →
    ex_seriesC f →
    ex_seriesC (λ n, if bool_decide (P n) then f n else 0).
  Proof. intros ? [v His]. by eapply is_seriesC_filter_pos. Qed.

  (* TODO: make a [SeriesC_minus] lemma and cleanup proof *)
  Lemma is_seriesC_filter_union f v P Q `{∀ x, Decision (P x), ∀ x, Decision (Q x)} :
    (∀ n, 0 <= f n) →
    is_seriesC (λ n, if bool_decide (P n ∨ Q n) then f n else 0) v →
    SeriesC (λ n, if bool_decide (P n) then f n else 0) +
    SeriesC (λ n, if bool_decide (Q n) then f n else 0) -
    SeriesC (λ n, if bool_decide (P n ∧ Q n) then f n else 0) = v.
  Proof.
    intros Hge Hexists.
    rewrite -SeriesC_plus; last first.
    {apply (is_seriesC_filter_impl  _ _ _ _ Hge Hexists); eauto. }
    { apply (is_seriesC_filter_impl  _ _ _ _ Hge Hexists); eauto. }
    rewrite -SeriesC_minus.
    - rewrite -(is_seriesC_unique _ v Hexists).
      apply SeriesC_ext => n.
      do 2 repeat case_bool_decide=>//=; try tauto; lra.
    - apply: (ex_seriesC_le _ (λ a, scal 2 (if bool_decide (P a ∨ Q a) then f a else 0))).
      + intros a. rewrite /scal /= /mult /=.
        specialize (Hge a). do 3 case_bool_decide => /=; try (lra || tauto).
      + eexists. by eapply is_seriesC_scal_l.
    - eapply (is_seriesC_filter_impl  _ _ _ _ Hge Hexists). intros ? []; auto.
  Qed.

  Lemma ex_seriesC_split_elem f (a0 : A) :
    ex_seriesC (λ a, if bool_decide (a ≠ a0) then f a else 0) → ex_seriesC f.
  Proof.
    intros Ha0.
    eapply (ex_seriesC_ext (λ a, (λ a, if bool_decide (a = a0) then f a else 0) a +
                                   (λ a, if bool_decide (a ≠ a0) then f a else 0) a)).
    { intros a. case_bool_decide; simplify_eq.
      - rewrite bool_decide_eq_false_2; [lra|auto].
      - rewrite bool_decide_eq_true_2 //. lra. }
    eapply ex_seriesC_plus; [|done].
    eapply ex_seriesC_ext; [|eapply (ex_seriesC_singleton a0 (f a0))].
    intros a. simpl. by case_bool_decide; simplify_eq.
  Qed.

  Lemma SeriesC_split_elem f (a0 : A) :
    (∀ a, 0 <= f a) →           (* TODO: this requirements should not be necessary? *)
    ex_seriesC f →
    SeriesC f = SeriesC (λ a, if bool_decide (a = a0) then f a else 0) +
                SeriesC (λ a, if bool_decide (a ≠ a0) then f a else 0).
  Proof.
    intros Hle Hex.
    erewrite SeriesC_ext.
    { eapply SeriesC_plus; [by eapply ex_seriesC_filter_pos|].
      eapply (ex_seriesC_le _ f); [|done].
      intros a'. case_bool_decide; split; (done || lra). }
    intros a. simpl. case_bool_decide as Heq.
    - rewrite bool_decide_eq_false_2; [lra|]. eauto.
    - rewrite bool_decide_eq_true_2 //. lra.
  Qed.

End filter.

Section rearrange.
  Context `{Countable A}.

  (* TODO: prove this (using the [Series] version from rearrange.v)  *)
  Lemma SeriesC_rearrange_covering (σ: A → A) (f : A → R) :
    (* no "collisions" in [f ∘ σ] *)
    (∀ a a', f (σ a) ≠ 0 → σ a = σ a' → a = a') →
    (* [σ] is surjective on the support of [f] *)
    (∀ a, f a ≠ 0 → ∃ a', σ a' = a) →
    ex_seriesC (λ a, Rabs (f a)) →
    SeriesC f = SeriesC (f ∘ σ).
  Proof. Admitted.

End rearrange.

Section strict.
  Context `{Countable A}.

  Implicit Types f g : A → R.

  (** Some extra theorems about strict inequalities, etc. **)
  Lemma SeriesC_lt f g :
  (∀ n, 0 <= f n <= g n) →
  (∃ m, f m < g m) →
   ex_seriesC g → SeriesC f < SeriesC g.
  Proof.
    intros Hle Hlt Hg.
    assert (ex_seriesC f) as Hf.
    { apply (ex_seriesC_le f g); auto. }
    destruct Hlt as (m & Hlt).
    assert (g m - f m > 0) as Hgtz ; try lra.
    set (d := g m - f m).
    set (h := (λ n, if bool_decide (n = m) then d else 0) ).
    assert (ex_seriesC h) as Hh.
    { apply ex_seriesC_singleton. }
    assert (SeriesC h > 0) as Hhgt.
    { rewrite SeriesC_singleton; auto. }
    assert (SeriesC f + SeriesC h <= SeriesC g); try lra.
    rewrite <- SeriesC_plus; auto.
    apply SeriesC_le; auto.
    intro n.
    specialize (Hle n) as (Hle1 & Hle2).
    rewrite /h /d.
    case_bool_decide as Hnm; split; try lra.
    rewrite Hnm; lra.
  Qed.

 (* Classical proof. This may be provable constructively, but
  for now this works *)
  Lemma SeriesC_const0 f :
  (∀ n, 0 <= f n) →
  is_seriesC f 0 →
  (∀ n, f n = 0).
  Proof.
   intros Hf Hz n.
   pose proof (is_seriesC_unique _ _ Hz) as Hz'.
   pose proof (Rtotal_order (f n) 0) as Htri.
   destruct Htri as [H1 | [H2 | H3]] ; try lra.
   + specialize (Hf n); lra.
   + assert (0 < SeriesC f); try lra.
     assert (SeriesC (λ _ : A, 0) = 0) as H4.
     { apply SeriesC_0; auto. }
     destruct H4.
     eapply (SeriesC_lt (λ n, 0) f).
     ++ intro n0; specialize (Hf n0); lra.
     ++ exists n; lra.
     ++ exists 0; done.
  Qed.

  Lemma SeriesC_gtz_ex f :
  (∀ n, 0 <= f n) →
  (SeriesC f > 0) →
  (exists n, f n > 0).
  Proof.
    intro Hf.
    eapply contrapositive. intros Hna.
    assert (∀ a, f a = 0) as Hz.
    { intros a.
      pose proof (not_exists_forall_not _ _ Hna a).
      specialize (Hf a); lra.
    }
    apply Rge_not_gt. rewrite SeriesC_0 //.
   Qed.


End strict.

Section positive.

 (* Results about positive (non-negative) series *)

  Context `{Countable A}.
  Implicit Types f g : A → R.

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

  (*
  Lemma Series_ge0 (h : nat → R):
    (∀ n, 0 <= h n) ->
    0 <= Series h.
  Proof.
  Admitted.
  *)


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
    (*    rewrite /is_series
       /locally /eventually
       /filterlim
       /filter_le
       /filtermap.*)
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


  Lemma sup_is_upper_bound (h : nat → Rbar) n :
    Rbar_le (h n) (Sup_seq h).
  Proof.
    apply is_sup_seq_major.
    apply Sup_seq_correct.
  Qed.

  Lemma upper_bound_ge_sup (h : nat → Rbar) r :
    (forall n, Rbar_le (h n) r) ->
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


  Lemma swap_sup_seq (h : nat * nat → R) :
    Sup_seq (λ m, Sup_seq (λ n, h (n, m))) =
    Sup_seq (λ n, Sup_seq (λ m, h (n, m))).
  Proof.
    apply Rbar_le_antisym.
    + apply upper_bound_ge_sup.
      intro m.
      apply upper_bound_ge_sup.
      intro n.
      eapply Rbar_le_trans; last first.
      ++ apply (sup_is_upper_bound _ n).
      ++ apply (sup_is_upper_bound (λ x, h(n, x)) m).
    + apply upper_bound_ge_sup.
      intro n.
      apply upper_bound_ge_sup.
      intro m.
      eapply Rbar_le_trans; last first.
      ++ apply (sup_is_upper_bound _ m).
      ++ apply (sup_is_upper_bound (λ x, h(x, m)) n).
  Qed.

(*
  Lemma fubini_pos_ex_series_r (h : nat * nat → R) :
    (forall n m, h (n, m) >= 0) ->
    (∃ (r: R), ∀ n, sum_n (λ j, sum_n (λ k, Rabs (h (j, k))) n) n <= r) ->
    ∀ b, ex_series (λ a, h (a, b)).
  Proof.
    intros Hpos (r & HDS) b.
    rewrite /ex_series /is_series.

  Lemma fubini_pos_series (h : nat * nat → R) v :
    (forall n m, h (n, m) >= 0) ->
    (∃ (r: R), ∀ n, sum_n (λ j, sum_n (λ k, Rabs (h (j, k))) n) n <= r) ->
    is_series (λ b, Series (λ a, h (a, b))) v ->
    is_series (λ a, Series (λ b, h (a, b))) v .
  Proof.
    intros Hpos (r & HDS) Hse.
    apply sup_is_lim.
    + admit.
    + apply lim_is_sup; auto.
      Search Series.
      { rewrite /Series. admit. }

  Admitted.



  (** Lifting of the Coquliecot predicates for limits *)
  Definition is_sup_seqC f r := is_sup_seq (countable_sum f) r.

  Lemma limC_is_sup (h: A -> R) r :
    (∀ n, 0 <= h n) ->
    is_seriesC h r →
    is_sup_seq (sum_n (countable_sum h) ) (Finite r).
  Proof.
    intros Hge Hs.
    rewrite /is_seriesC in Hs.
    rewrite /is_series in Hs.
    eapply (lim_is_sup (countable_sum h) r).
    + rewrite /countable_sum. destruct (encode_inv_nat _); eauto.

    rewrite /is_seriesC.
    assert (0 <= r) as Hr.
    {
      rewrite <- (is_seriesC_unique _ _ Hs).
      apply SeriesC_ge_0; auto. exists r; auto.}
    intro eps; split.
    + induction n; rewrite /countable_sum.
      ++ destruct (encode_inv_nat _) =>//=; try lra; admit.
      ++
*)

End positive.
