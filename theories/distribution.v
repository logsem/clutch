From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Import countable.
From proba Require Import Series_ext Reals_ext countable_sum.

Open Scope R.

Record distr (A : Type) `{Countable A} := Distr {
  μ :> A → R;
  μ_pos  : ∀ a, 0 <= μ a;
  μ_sum1 : is_seriesC μ 1
}.

Arguments μ {_ _ _ _}.

Hint Resolve μ_pos μ_sum1 : core.

Notation Decidable P := (∀ x, Decision (P x)).

Section distributions.
  Context `{Countable A}.

  Implicit Types d : distr A.

  Lemma distr_SeriesC d : SeriesC d = 1.
  Proof. by apply is_seriesC_unique. Qed.

  Lemma distr_ex_seriesC d : ex_seriesC d.
  Proof. eexists; eapply μ_sum1. Qed.

  Lemma distr_sum_n d n :
    sum_n (countable_sum d) n ≤ 1.
  Proof.
    apply is_series_partial_pos; [|by apply μ_sum1].
    intros ?. by apply countable_sum_ge_0.
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
  Proof.
    apply is_seriesC_unique, μ_sum1.
  Qed.

  Lemma pr_False d :
    pr d (λ _, False) = 0.
  Proof.
    rewrite /pr SeriesC_0 //.
  Qed.

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
