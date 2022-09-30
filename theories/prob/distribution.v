From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect ssrfun.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable.
From self.prelude Require Export base Coquelicot_ext Reals_ext classical.
From self.prob Require Export countable_sum double.

Record distr (A : Type) `{Countable A} := MkDistr {
  pmf :> A → R;
  pmf_pos : ∀ a, 0 <= pmf a;
  pmf_ex_seriesC : ex_seriesC pmf;
  pmf_SeriesC : SeriesC pmf <= 1;
}.

Arguments MkDistr {_ _ _}.
Arguments pmf {_ _ _ _}.
Arguments pmf_pos {_ _ _}.
Arguments pmf_ex_seriesC {_ _ _}.
Arguments pmf_SeriesC {_ _ _}.

#[global] Hint Resolve pmf_pos pmf_ex_seriesC pmf_SeriesC : core.
Notation Decidable P := (∀ x, Decision (P x)).

Open Scope R.

Section distributions.
  Context `{Countable A}.

  Implicit Types μ d : distr A.

  Lemma pmf_le_1 μ a : μ a <= 1.
  Proof.
    assert (SeriesC (λ a', if bool_decide (a' = a) then μ a else 0) = μ a) as <-.
    { eapply SeriesC_singleton. }
    etransitivity; [|eapply (pmf_SeriesC μ)].
    apply SeriesC_le; [|done].
    intros a'. case_bool_decide; subst; split; try (lra || done).
  Qed.

  Lemma pmf_SeriesC_ge_0 μ : 0 <= SeriesC μ.
  Proof.
    transitivity (SeriesC (λ (_ : A), 0)).
    { apply SeriesC_ge_0; [done|]. apply ex_seriesC_0. }
    apply SeriesC_le'; auto. apply ex_seriesC_0.
  Qed.

  Lemma pmf_ex_seriesC_mult (μ1 μ2 : distr A) :
    ex_seriesC (λ a, μ1 a * μ2 a).
  Proof.
    eapply (ex_seriesC_le _ (λ a, μ1 a * 1)); [|by apply ex_seriesC_scal_r].
    intros a.
    split; [by apply Rmult_le_pos|].
    eapply Rmult_le_compat_l; [done|].
    apply pmf_le_1.
  Qed.

End distributions.

#[global] Hint Resolve pmf_ex_seriesC : core.

Section monadic.
  Context `{Countable A}.

  Definition dret_pmf (a : A) : A → R :=
    λ (a' : A), if bool_decide (a' = a) then 1 else 0.

  Program Definition dret (a : A) : distr A := MkDistr (dret_pmf a) _ _ _.
  Next Obligation. intros. rewrite /dret_pmf. case_bool_decide; nra. Qed.
  Next Obligation. intros. apply ex_seriesC_singleton. Qed.
  Next Obligation. intros. rewrite SeriesC_singleton //. Qed.

  Context `{Countable B}.

  Definition dbind_pmf (f : A → distr B) (μ : distr A) : B → R :=
    λ (b : B), SeriesC (λ (a : A), μ a * f a b).

  Program Definition dbind (f : A → distr B) (μ : distr A) : distr B :=
    MkDistr (dbind_pmf f μ) _ _ _.
  Next Obligation.
    intros f μ b. rewrite /dbind_pmf.
    apply SeriesC_ge_0.
    - intros a'. by apply Rmult_le_pos.
    - eapply (ex_seriesC_le _ (λ a, μ a * 1)); [|by apply ex_seriesC_scal_r].
      intros a. split; [by apply Rmult_le_pos|].
      eapply Rmult_le_compat_l; [done|].
      eapply pmf_le_1.
  Qed.
  Next Obligation.
    intros f μ. rewrite /dbind_pmf.
    eapply (ex_seriesC_double_swap_impl (λ '(a, b), _)).
    eapply (ex_seriesC_ext (λ j, μ j * SeriesC (λ k, f j k))).
    { intros a. rewrite SeriesC_scal_l //. }
    apply (ex_seriesC_le _ (λ a : A, μ a * 1)); [|by apply ex_seriesC_scal_r].
    intros a. split.
    - apply Rmult_le_pos; [done|].
      apply SeriesC_ge_0; auto.
    - by apply Rmult_le_compat_l.
  Qed.
  Next Obligation.
    intros f μ. rewrite /dbind_pmf.
    rewrite (SeriesC_double_swap (λ '(a, b), _)).
    rewrite -(SeriesC_ext (λ k, μ k * SeriesC (λ j, f k j))); last first.
    { intros a. rewrite SeriesC_scal_l //. }
    transitivity (SeriesC μ); [|done].
    eapply SeriesC_le; [|done].
    intros a.
    split.
    - apply Rmult_le_pos; [done|].
      apply SeriesC_ge_0; auto.
    - rewrite -{2}(Rmult_1_r (μ a)).
      by apply Rmult_le_compat_l.
  Qed.

End monadic.

(* Notation "m ≫= f" := (dbind f m) (at level 60, right associativity) : stdpp_scope. *)
(* Notation "( m ≫=.)" := (λ f, dbind f m) (only parsing) : stdpp_scope. *)
(* Notation "(.≫= f )" := (dbind f) (only parsing) : stdpp_scope. *)
(* Notation "(≫=)" := (λ m f, dbind f m) (only parsing) : stdpp_scope. *)

(* Notation "x ← y ; z" := (y ≫= (λ x : _, z)) *)
(*   (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope. *)

(* Notation "' x ← y ; z" := (y ≫= (λ x : _, z)) *)
(*   (at level 20, x pattern, y at level 100, z at level 200, only parsing) : stdpp_scope. *)


Section dmap.
  Context `{Countable A, Countable B}.

  Definition dmap (f : A → B) (μ : distr A) : distr B :=
    dbind (λ a, dret (f a)) μ.
End dmap.

Section strength.
  Context `{Countable A, Countable B}.

  Definition strength_l (a : A) (μ : distr B) : distr (A * B) :=
    dbind (λ b, dret (a, b)) μ.

End strength.

Section monadic_theory.
  Context `{Countable A, Countable B}.

  Lemma dret_id_left_pmf (f : A → distr B) a b :
    (dbind f (dret a)) b = (f a) b.
  Proof.
    rewrite /= /dbind_pmf /= /dret_pmf.
    rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then f a b else 0)).
    { rewrite SeriesC_singleton //. }
    intros a'. case_bool_decide; simplify_eq; lra.
  Qed.

  Lemma dret_id_right_pmf (μ : distr A) a :
    (dbind (λ x, dret x) μ) a = μ a.
  Proof.
    rewrite /= /dbind_pmf /= /dret_pmf.
    rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then μ a else 0)).
    { rewrite SeriesC_singleton //. }
    intros a'. case_bool_decide; simplify_eq.
    - rewrite bool_decide_eq_true_2 //. lra.
    - rewrite bool_decide_eq_false_2 //. lra.
  Qed.

  Lemma dbind_pos_support (f : A → distr B) (μ : distr A) (b : B) :
    dbind f μ b > 0 ↔ ∃ a, f a b > 0 ∧ μ a > 0.
  Proof.
    rewrite /= /dbind_pmf. split.
    - eapply contrapositive. intros Hna.
      assert (∀ a, μ a * f a b = 0) as Hz.
      { intros a.
        pose proof (not_exists_forall_not _ _ Hna a) as [Hne | Hne]%not_and_or_not.
        - pose proof (pmf_pos (f a) b). assert (f a b = 0) as ->; lra.
        - pose proof (pmf_pos μ a). assert (μ a = 0) as ->; lra. }
      apply Rge_not_gt. rewrite SeriesC_0 //.
    - intros (a & Hf & Hμ). eapply Rlt_gt.
      eapply (Rlt_le_trans _ (SeriesC (λ a', if bool_decide (a' = a) then μ a * f a b else 0))).
      { rewrite SeriesC_singleton. eapply Rmult_gt_0_compat; lra. }
      eapply SeriesC_le.
      + intros ?. case_bool_decide; simplify_eq; split; done || by eapply Rmult_le_pos.
      + apply (ex_seriesC_le _ (λ a : A, μ a * 1)); [|by apply ex_seriesC_scal_r].
        intros a'. split.
        * by apply Rmult_le_pos.
        * apply Rmult_le_compat_l; [done|]. eapply pmf_le_1.
  Qed.

  Lemma dmap_dret_pmf (f : A → B) a b :
    dmap f (dret a) b = dret (f a) b.
  Proof. rewrite /dmap dret_id_left_pmf //. Qed.

End monadic_theory.
