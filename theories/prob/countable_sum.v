From Coq Require Import Reals Psatz.
From Coquelicot Require Import Series Hierarchy Lim_seq Rbar.
From stdpp Require Import option.
From stdpp Require Export countable.
From self.prelude Require Import base Coquelicot_ext stdpp_ext classical.
From self.prob Require Export series_extra.
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

  Lemma SeriesC_ge_0' (f : A → R) :
    (∀ x, 0 <= f x) →
    0 <= SeriesC f.
  Proof.
    intros Heq0.
    apply series_ge_0=> ?.
    apply countable_sum_ge_0; intros; auto.
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

(*
Section subset.

Context `{Countable A, Countable B}.

Lemma subset_ex_series (f : A -> R) (g : B -> R) (e : A -> B) (d : B -> option A) :
  (forall a, 0 <= f a ) ->
  (forall b, 0 <= g b ) ->
  (forall a, d (e a) = Some a) ->
  (forall a, f a  = g (e a)) ->
  ex_seriesC g ->
  ex_seriesC f.
Proof.


End subset.
*)

(* Section rearrange. *)
(*   Context `{Countable A}. *)

(*   (* TODO: prove this (using the [Series] version from rearrange.v)  *) *)
(*   Lemma SeriesC_rearrange_covering (σ: A → A) (f : A → R) : *)
(*     (* no "collisions" in [f ∘ σ] *) *)
(*     (∀ a a', f (σ a) ≠ 0 → σ a = σ a' → a = a') → *)
(*     (* [σ] is surjective on the support of [f] *) *)
(*     (∀ a, f a ≠ 0 → ∃ a', σ a' = a) → *)
(*     ex_seriesC (λ a, Rabs (f a)) → *)
(*     SeriesC f = SeriesC (f ∘ σ). *)
(*   Proof. Admitted. *)

(* End rearrange. *)

Section strict.
  Context `{Countable A}.

  Implicit Types f g : A → R.

  (** Some extra theorems about strict inequalities, etc. **)
  Lemma SeriesC_lt f g :
  (∀ n, 0 <= f n <= g n) →
  (∃ m, f m < g m) →
  ex_seriesC g →
  SeriesC f < SeriesC g.
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
    SeriesC f > 0 →
    ∃ n, f n > 0.
  Proof.
    intro Hf.
    eapply contrapositive. intros Hna.
    assert (∀ a, f a = 0) as Hz.
    { intros a.
      pose proof (not_exists_forall_not _ _ Hna a).
      specialize (Hf a); lra. }
    apply Rge_not_gt. rewrite SeriesC_0 //.
   Qed.

End strict.

Section positive.

 (* Results about positive (non-negative) series *)

  (** Lifting of the Coquliecot predicates for limits *)
  Context `{Countable A}.
  Implicit Types f g : A → R.

  Definition is_sup_seqC f r := is_sup_seq (countable_sum f) r.

  Lemma limC_is_sup (h: A -> R) r :
    (∀ n, 0 <= h n) ->
    is_seriesC h r →
    is_sup_seq (sum_n (countable_sum h)) (Finite r).
  Proof.
    intros Hge Hs.
    rewrite /is_seriesC in Hs.
    eapply (lim_is_sup (countable_sum h) r); auto.
    (* AA: For some reason, Coq is unable to infer the parameters of encode_inv_nat *)
    intro n. rewrite /countable_sum /from_option; edestruct (@encode_inv_nat A _ H n); auto ; lra.
  Qed.

  Lemma sup_is_limC (h: A → R) r :
    (∀ n, 0 <= h n) ->
    is_sup_seq (sum_n (countable_sum h)) (Finite r) ->
    is_seriesC h r.
  Proof.
    intros Hge Hsup.
    rewrite /is_seriesC.
    eapply (sup_is_lim); auto.
    intro n; rewrite /countable_sum /from_option; destruct (encode_inv_nat _); auto; lra.
  Qed.

End positive.

Section fubini.

  Context `{Countable A, Countable B}.


  (*
     The following three lemmas have been proven for
     Series, so the only missing part is lifting them
     to SeriesC
  *)

 Lemma fubini_pos_seriesC_ex (h : A * B → R) :
    (forall a b, 0 <= h (a, b)) ->
    (forall a, ex_seriesC (λ b, h (a, b))) ->
    (ex_seriesC (λ a, SeriesC (λ b, h (a, b)))) ->
    (forall b, ex_seriesC (λ a, h (a, b))).
 Admitted.

 Lemma fubini_pos_seriesC_ex_double (h : A * B → R) :
    (forall a b, 0 <= h (a, b)) ->
    (forall a, ex_seriesC (λ b, h (a, b))) ->
    (ex_seriesC (λ a, SeriesC (λ b, h (a, b)))) ->
    (ex_seriesC (λ b, SeriesC (λ a, h (a, b)))).
 Admitted.

 Lemma fubini_pos_seriesC (h : A * B → R) :
    (forall a b, 0 <= h (a, b)) ->
    (forall a, ex_seriesC (λ b, h (a, b))) ->
    (ex_seriesC (λ a, SeriesC (λ b, h (a, b)))) ->
    SeriesC (λ b, SeriesC (λ a, h (a, b))) =
    SeriesC (λ a, SeriesC (λ b, h (a, b))).
 Admitted.

 (*
    The rest of the lemmas are admitted without a direct counterpart
    for Series. They should only rely on showing that if a set of
    nonnegative real numbers has a finite sum, then (1) every reordering
    of the sum has the same result and (2) every subset has a sum bounded
    by the sum of the whole set. Both can be derived by proving that the
    sum of a set is the sup of the sums of the finite subsets.
 *)

 (*
 Lemma ex_seriesC_nat (h : nat -> R) :
   ex_seriesC h <-> ex_series h.
 Admitted.

 Lemma SeriesC_nat (h : nat -> R) :
   SeriesC h = Series h.
 Admitted.

 Lemma fubini_pos_seriesC_prod_nat (h : nat * nat -> R) :
    (forall a b, 0 <= h (a, b)) ->
    Sup_seq (sum_n (countable_sum h)) =
    Sup_seq (λ n, Sup_seq (λ m, h (n, m))).
 Admitted.
 *)

 Lemma fubini_pos_seriesC_prod_ex_lr (h : A * B -> R) b :
    (forall a b, 0 <= h (a, b)) ->
    (ex_seriesC h) ->
    ex_seriesC (λ a, SeriesC (λ b, h(a, b))).
 Admitted.

 Lemma fubini_pos_seriesC_prod_ex_rl (h : A * B -> R) b :
    (forall a b, 0 <= h (a, b)) ->
    (ex_seriesC h) ->
    ex_seriesC (λ b, SeriesC (λ a, h(a, b))).
 Admitted.

 Lemma fubini_pos_seriesC_prod_lr (h : A * B -> R) :
    (forall a b, 0 <= h (a, b)) ->
    (ex_seriesC h) ->
    SeriesC h = SeriesC (λ a, SeriesC (λ b, h(a, b))).
 Admitted.

 Lemma fubini_pos_seriesC_prod_rl (h : A * B -> R) :
    (forall a b, 0 <= h (a, b)) ->
    (ex_seriesC h) ->
    SeriesC h = SeriesC (λ b, SeriesC (λ a, h(a, b))).
 Admitted.

 Lemma ex_seriesC_lmarg (h : A * B -> R) a :
    (forall a b, 0 <= h (a, b)) ->
    (ex_seriesC h) ->
    ex_seriesC (λ b, h (a, b)).
 Admitted.

 Lemma seriesC_lmarg_le (h : A * B -> R) a :
    (forall a b, 0 <= h (a, b)) ->
    (ex_seriesC h) ->
    SeriesC (λ b, h (a, b)) <= SeriesC h.
 Admitted.

 Lemma ex_seriesC_rmarg (h : A * B -> R) b :
    (forall a b, 0 <= h (a, b)) ->
    (ex_seriesC h) ->
    ex_seriesC (λ a, h (a, b)).
 Admitted.

 Lemma seriesC_rmarg_le (h : A * B -> R) b :
    (forall a b, 0 <= h (a, b)) ->
    (ex_seriesC h) ->
    SeriesC (λ a, h (a, b)) <= SeriesC h.
 Admitted.

 Lemma ex_seriesC_prod (h: A * B -> R) :
    (forall a, ex_seriesC (λ b, h(a,b))) ->
    ex_seriesC (λ a, SeriesC (λ b, h(a,b))) ->
    ex_seriesC h.
  Proof. Admitted.

 End fubini.


Section mct.

  Context `{Countable A}.


  (* TODO: Lift the proof from Series_extra *)
  Lemma MCT_seriesC (h : nat -> A → R) (l : nat -> R) (r : R) :
  (forall n a, 0 <= (h n a)) ->
  (forall n a, (h n a) <= (h (S n) a)) ->
  (forall a, exists s, forall n, h n a <= s ) ->
  (forall n, is_seriesC (h n) (l n)) ->
  is_sup_seq l (Finite r) ->
  SeriesC (λ a, Sup_seq (λ n, h n a)) = r.
  Admitted.


  (* TODO: Lift the proof from Series_extra *)
  Lemma MCT_ex_seriesC (h : nat -> A → R) (l : nat -> R) (r : R) :
  (forall n a, 0 <= (h n a)) ->
  (forall n a, (h n a) <= (h (S n) a)) ->
  (forall a, exists s, forall n, h n a <= s ) ->
  (forall n, is_seriesC (h n) (l n)) ->
  is_sup_seq l (Finite r) ->
  ex_seriesC (λ a, Sup_seq (λ n, h n a)).
  Admitted.

End mct.



