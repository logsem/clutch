From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable.
From proba.prelude Require Export Series_ext Reals_ext.
From proba.prob Require Export countable_sum.
Set Default Proof Using "Type".
Global Set Bullet Behavior "Strict Subproofs".

Record distr (A : Type) `{Countable A} := MkDistr {
  μ :> A → R;
  distr_measure_pos   : ∀ a, 0 <= μ a;
  distr_measure_sum_1 : is_seriesC μ 1
}.

Arguments MkDistr {_ _ _}.
Arguments μ {_ _ _ _}.

#[global] Hint Resolve distr_measure_pos distr_measure_sum_1 : core.

Notation Decidable P := (∀ x, Decision (P x)).

Section distributions.
  Context `{Countable A}.

  Open Scope R.

  Implicit Types μ d : distr A.

  Lemma distr_SeriesC d : SeriesC d = 1.
  Proof. by apply is_seriesC_unique. Qed.

  Lemma distr_ex_seriesC d : ex_seriesC d.
  Proof. eexists; eapply distr_measure_sum_1. Qed.

  Hint Resolve distr_ex_seriesC : core.

  Lemma distr_sum_n d n :
    sum_n (countable_sum d) n ≤ 1.
  Proof.
    apply is_series_partial_pos; [|by apply distr_measure_sum_1].
    intros ?. by apply countable_sum_ge_0.
  Qed.

  Lemma distr_measure_le_1 μ a : μ a ≤ 1.
  Proof.
    rewrite -(is_seriesC_unique μ 1) //.
    assert (SeriesC (λ a', if bool_decide (a' = a) then μ a else 0) = μ a) as <-.
    { eapply SeriesC_singleton. }
    apply SeriesC_le; [|done].
    intros a'. case_bool_decide; subst; split; try (nra || done).
  Qed.

  Implicit Types P Q : A → Prop.

  (* TODO: useful for anything? *)
  Definition support (μ : distr A) :=
    { x : A | 0 < μ x  }%R.

  Definition pr (d : distr A) (P : A → Prop) `{Decidable P} :=
    SeriesC (λ a, if bool_decide (P a) then d a else 0)%R.

  Lemma pr_ex_seriesC d P `{Decidable P} :
    ex_seriesC (λ a, if bool_decide (P a) then d a else 0).
  Proof. by eapply is_seriesC_filter_pos. Qed.

  Lemma distr_ex_seriesC_mult (μ1 μ2 : distr A) :
    ex_seriesC (λ a : A, μ1 a * μ2 a).
  Proof.
    eapply (ex_seriesC_le _ (λ a, μ1 a * 1)); [|by apply ex_seriesC_scal_r].
    intros a.
    pose proof (distr_measure_le_1 μ2 a).
    pose proof (distr_measure_pos _ μ1 a).
    pose proof (distr_measure_pos _ μ2 a).
    split; nra.
  Qed.

  Lemma pr_ge_0 d P `{Decidable P} :
    0 ≤ pr d P.
  Proof.
    transitivity (SeriesC (λ (_ : A), 0)).
    - right. symmetry. by apply SeriesC_0.
    - apply SeriesC_le.
      + intros n. case_bool_decide; [|nra].
        split; [nra|]. done.
      + apply pr_ex_seriesC.
  Qed.

  Lemma pr_le_1 d P `{Decidable P} :
    pr d P ≤ 1.
  Proof.
    transitivity (SeriesC d).
    - apply SeriesC_le.
      + intros n. case_bool_decide; split; (nra || done).
      + apply distr_ex_seriesC.
    - right. apply distr_SeriesC.
  Qed.

  Lemma pr_True d :
    pr d (λ _, True) = 1.
  Proof. apply is_seriesC_unique, distr_measure_sum_1. Qed.

  Lemma pr_False d :
    pr d (λ _, False) = 0.
  Proof. rewrite /pr SeriesC_0 //. Qed.

  Lemma pr_iff d P Q `{Decidable P, Decidable Q} :
    (∀ a, P a ↔ Q a) →
    pr d P = pr d Q.
  Proof.
    rewrite /pr => Hext.
    apply SeriesC_ext=> n.
    specialize (Hext n).
    do 2 case_bool_decide; tauto.
  Qed.

  Lemma pr_le_impl d P Q `{Decidable P, Decidable Q} :
    (∀ a, P a → Q a) →
    pr d P ≤ pr d Q.
  Proof.
    rewrite /pr => Himpl.
    apply SeriesC_le.
    - intros a. specialize (Himpl a).
      case_bool_decide as HQ.
      + rewrite bool_decide_eq_true_2; [|tauto]. split; [done|nra].
      + split; [nra|]. case_bool_decide; [done|nra].
    - by eapply is_seriesC_filter_pos.
  Qed.

  Lemma pr_union d P Q `{Decidable P, Decidable Q} :
    pr d (λ a, P a ∨ Q a) =
    pr d P + pr d Q - pr d (λ a, P a ∧ Q a).
  Proof.
    rewrite /pr. symmetry; eapply is_seriesC_filter_union; [done|].
    apply SeriesC_correct, pr_ex_seriesC.
  Qed.

  Lemma pr_le_union d P Q `{Decidable P, Decidable Q} :
    pr d (λ a, P a ∨ Q a) ≤ pr d P + pr d Q.
  Proof.
    rewrite pr_union. pose (pr_ge_0 d (λ a, P a ∧ Q a)). nra.
  Qed.

End distributions.

#[global] Hint Resolve distr_ex_seriesC : core.

Section monadic.
  Context `{Countable A}.

  Definition dret_μ (a : A) : A → R :=
    λ (a' : A), if bool_decide (a' = a) then 1 else 0.

  Program Definition dret (a : A) : distr A := MkDistr (dret_μ a) _ _.
  Next Obligation. intros. rewrite /dret_μ. case_bool_decide; nra. Qed.
  Next Obligation. intros. eapply is_seriesC_singleton. Qed.

  Context `{Countable B}.

  Lemma foo (f : A → distr B) (a : A) :
    is_seriesC (f a) 1.
  Proof. done. Qed.

  Lemma bar (h : A → B → R) :
    is_seriesC (λ a : A, SeriesC (λ b : B, h a b)) 1 →
    is_seriesC (λ b : B, SeriesC (λ a : A, h a b)) 1.
  Proof.
    (* This general formulation is not true - Fubini's theorem? *)
    intros Ha.
    rewrite /is_seriesC /SeriesC.
    rewrite /is_series. rewrite /Series.
  Admitted.

  Lemma baz μ f :
    is_seriesC (λ a : A, μ a * SeriesC (λ b : B, f a b)) 1  →
    is_seriesC (λ a : A, SeriesC (λ b : B, μ a * f a b)) 1.
  Proof.
    eapply is_seriesC_ext.
    intros a. rewrite SeriesC_scal_l //.
  Qed.

  Definition dbind_μ (f : A → distr B) (μ : distr A) : B → R :=
    λ (b : B), SeriesC (λ (a : A), μ a * f a b).

  Program Definition dbind (f : A → distr B) (μ : distr A) : distr B :=
    MkDistr (dbind_μ f μ) _ _.
  Next Obligation.
    intros f μ b. rewrite /dbind_μ.
    apply SeriesC_ge_0.
    - intros a. by apply Rmult_le_pos.
    - eapply (ex_seriesC_le _ (λ a, μ a * 1)); [|by apply ex_seriesC_scal_r].
      intros a. split; [by apply Rmult_le_pos|].
      eapply Rmult_le_compat_l; [done|].
      eapply distr_measure_le_1.
  Qed.
  Next Obligation.
    intros f μ. rewrite /dbind_μ.
    apply bar.
    apply baz.
    apply (is_seriesC_ext _ (λ a : A, μ a * 1)).
    { intros a.
      pose proof (foo f a).
      apply is_seriesC_unique in H1.
      rewrite H1 //. }
    apply (is_seriesC_ext _ (λ a : A, μ a)).
    { intros a. rewrite Rmult_1_r //. }
    done.
  Qed.

End monadic.

Notation "m ≫= f" := (dbind f m) (at level 60, right associativity) : stdpp_scope.
Notation "( m ≫=.)" := (λ f, dbind f m) (only parsing) : stdpp_scope.
Notation "(.≫= f )" := (dbind f) (only parsing) : stdpp_scope.
Notation "(≫=)" := (λ m f, dbind f m) (only parsing) : stdpp_scope.

Notation "x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.

Notation "' x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200, only parsing) : stdpp_scope.
