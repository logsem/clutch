From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Export countable finite.
From clutch.prelude Require Export base stdpp_ext Reals_ext Coquelicot_ext Series_ext classical uniform_list.
From clutch.prob Require Export countable_sum.

Record distr (A : Type) `{Countable A} := MkDistr {
  pmf :> A → R;
  pmf_pos : ∀ a, 0 <= pmf a;
  pmf_ex_seriesC : ex_seriesC pmf;
  pmf_SeriesC : SeriesC pmf <= 1;
}.

Global Arguments MkDistr {_ _ _}.
Global Arguments pmf {_ _ _ _} _ : simpl never.
Global Arguments pmf_pos {_ _ _}.
Global Arguments pmf_ex_seriesC {_ _ _}.
Global Arguments pmf_SeriesC {_ _ _}.

#[global] Hint Resolve pmf_pos pmf_ex_seriesC pmf_SeriesC : core.

#[local] Open Scope R.

Section distributions.
  Context `{Countable A}.

  Implicit Types μ d : distr A.

  Global Instance distr_dec μ1 μ2 : Decision (μ1 = μ2).
  Proof. apply make_decision. Qed.

  Lemma pmf_le_1 μ a : μ a <= 1.
  Proof.
    assert (SeriesC (λ a', if bool_decide (a' = a) then μ a else 0) = μ a) as <-.
    { eapply SeriesC_singleton. }
    etransitivity; [|eapply (pmf_SeriesC μ)].
    apply SeriesC_le; [|done].
    real_solver.
  Qed.

  Lemma pmf_SeriesC_ge_0 μ : 0 <= SeriesC μ.
  Proof.
    transitivity (SeriesC (λ (_ : A), 0)).
    { apply SeriesC_ge_0; [done|]. apply ex_seriesC_0. }
    apply SeriesC_le'; [done| |done]. apply ex_seriesC_0.
  Qed.

  Hint Resolve pmf_le_1 : core.
  Hint Resolve pmf_SeriesC_ge_0 : core.

  Lemma pmf_ex_seriesC_mult_fn μ (f : A → R) :
    (∃ n, ∀ a, 0 <= f a <= n) →
    ex_seriesC (λ a, μ a * f a).
  Proof.
    intros [n Hf].
    eapply (ex_seriesC_le _ (λ a, μ a * n)); [|by apply ex_seriesC_scal_r].
    intros a.
    specialize (Hf a); real_solver.
  Qed.

  Lemma pmf_ex_seriesC_mult (μ1 μ2 : distr A) :
    ex_seriesC (λ a, μ1 a * μ2 a).
  Proof.
    eapply pmf_ex_seriesC_mult_fn.
    exists 1. real_solver.
  Qed.

  Lemma pmf_le_SeriesC `{Countable A} (μ : distr A) (a : A) :
    μ a <= SeriesC μ.
  Proof. by eapply SeriesC_ge_elem. Qed.

  Lemma pmf_1_eq_SeriesC (μ : distr A) (a : A) :
    μ a = 1 → μ a = SeriesC μ.
  Proof.
    intros Hμ.
    assert (1 <= SeriesC μ).
    { rewrite -Hμ. eapply pmf_le_SeriesC. }
    pose proof (pmf_SeriesC μ). lra.
  Qed.

  Lemma pmf_plus_neq_SeriesC `{Countable A} (μ : distr A) (a a' : A) :
    a ≠ a' → μ a + μ a' <= SeriesC μ.
  Proof.
    intros Ha.
    rewrite (SeriesC_split_elem _ a); [|done|done].
    eapply Rle_plus_plus.
    - erewrite SeriesC_ext; [by erewrite (SeriesC_singleton a (μ a))|].
      real_solver.
    - rewrite (SeriesC_split_elem _ a'); last first.
      + eapply ex_seriesC_le; [|eapply (pmf_ex_seriesC μ)].
        real_solver.
      + real_solver.
      + apply Rle_plus_l.
        * erewrite SeriesC_ext; [by erewrite (SeriesC_singleton a' (μ a'))|].
          real_solver.
        * eapply SeriesC_ge_0.
          { real_solver. }
          eapply ex_seriesC_le; [|eapply (pmf_ex_seriesC μ)].
          real_solver.
  Qed.

  Lemma pmf_1_supp_eq (μ : distr A) (a a' : A) :
    μ a = 1 → μ a' > 0 → a = a'.
  Proof.
    intros Ha Ha'.
    destruct (decide (a = a')) as [|Hneq]; [done|].
    pose proof (pmf_le_SeriesC μ a').
    pose proof (pmf_1_eq_SeriesC _ _ Ha).
    pose proof (pmf_plus_neq_SeriesC μ a a' Hneq).
    lra.
  Qed.

  (* N.B. uses [functional_extensionality] and [proof_irrelevance] axioms  *)
  Lemma distr_ext (d1 d2 : distr A) :
    (∀ a, d1.(pmf) a = d2.(pmf) a) → d1 = d2.
  Proof.
    destruct d1 as [pmf1 ?], d2 as [pmf2 ?] =>/=. intros Ha.
    assert (pmf1 = pmf2) as ->; [by extensionality b|].
    f_equal; apply proof_irrelevance.
  Qed.


  Lemma distr_ext_pmf (d1 d2 : distr A) :
    d1.(pmf)  = d2.(pmf) → d1 = d2.
  Proof.
    destruct d1 as [pmf1 ?], d2 as [pmf2 ?] =>/=.
    rewrite /pmf. intros ->.
    f_equal; apply proof_irrelevance.
  Qed.


  Lemma pmf_eq_0_le (μ : distr A) (a : A):
    μ a <= 0 → μ a = 0.
  Proof. by intros [Hlt%(Rle_not_gt _ _ (pmf_pos μ a)) |]. Qed.

  Lemma pmf_eq_0_not_gt_0 (μ : distr A) (a : A):
    ¬ (μ a > 0) → μ a = 0.
  Proof. intros ?%Rnot_gt_ge%Rge_le. by apply pmf_eq_0_le. Qed.

  Context `{Countable B}.
  Lemma pmf_mult_eq_0 (μ : distr A) (μ' : distr B) a b:
    (μ a > 0 -> μ a * μ' b = 0) -> μ a * μ' b = 0.
  Proof.
    intros. destruct (pmf_pos μ a) as [|<-]; last lra.
    naive_solver.
  Qed.

End distributions.


#[global] Hint Resolve pmf_le_1 : core.
#[global] Hint Resolve pmf_SeriesC_ge_0 : core.

(** * Sum-swapping equalities for distributions *)
Lemma distr_double_swap_ex `{Countable A, Countable B} (f : A → distr B) (μ : distr A) :
  ex_seriesC (λ a : A, SeriesC (λ b : B, μ a * f a b)) ->
  ex_seriesC (λ b : B, SeriesC (λ a : A, μ a * f a b)).
Proof.
  intro Hex.
  apply (fubini_pos_seriesC_ex_double (λ '(a, b), μ a * f a b)); [| |done].
  - real_solver.
  - intros. apply (ex_seriesC_le _ (f a)); [|done].
    real_solver.
Qed.

Lemma distr_double_swap `{Countable A, Countable B} (f : A → distr B) (μ : distr A) :
  SeriesC (λ b : B, SeriesC (λ a : A, μ a * f a b)) =
  SeriesC (λ a : A, SeriesC (λ b : B, μ a * f a b)).
Proof.
  apply (fubini_pos_seriesC (λ '(a, b), μ a * f a b)).
  - real_solver.
  - intros a. apply (ex_seriesC_le _ (f a)); [|done].
    real_solver.
  - eapply (ex_seriesC_ext (λ j, μ j * SeriesC (λ k, f j k))).
    { intros a. rewrite SeriesC_scal_l //. }
    apply (ex_seriesC_le _ (λ a : A, μ a * 1)); [|by apply ex_seriesC_scal_r].
    real_solver.
Qed.

Lemma distr_double_lr `{Countable A, Countable B} (f : A → distr B) (μ : distr A) :
  SeriesC (λ '(a, b), μ a * f a b) =
  SeriesC (λ a : A, SeriesC (λ b : B, μ a * f a b)).
Proof.
  apply (fubini_pos_seriesC_prod_lr (λ '(a, b), μ a * f a b)).
  - real_solver.
  - apply ex_seriesC_prod.
    + real_solver.
    + intro. by apply ex_seriesC_scal_l.
    + setoid_rewrite SeriesC_scal_l.
      apply (ex_seriesC_le _ μ); [|done].
      real_solver.
Qed.

Lemma distr_double_rl `{Countable A, Countable B} (f : A → distr B) (μ : distr A) :
  SeriesC (λ '(a, b), μ a * f a b) =
  SeriesC (λ b : B, SeriesC (λ a : A, μ a * f a b)).
Proof.
  apply (fubini_pos_seriesC_prod_rl (λ '(a, b), μ a * f a b)).
  - real_solver.
  - apply ex_seriesC_prod.
    + real_solver.
    + intro. by apply ex_seriesC_scal_l.
    + setoid_rewrite SeriesC_scal_l.
      apply (ex_seriesC_le _ μ); [|done].
      real_solver.
Qed.

Lemma distr_double_swap_rmarg_ex `{Countable A, Countable B, Countable B'}
  (f : A → distr (B * B')) (μ : distr A) b' :
  ex_seriesC (λ a : A, SeriesC (λ b : B, μ a * f a (b, b'))) →
  ex_seriesC (λ b : B, SeriesC (λ a : A, μ a * f a (b, b'))).
Proof.
  intro Hex.
  apply (fubini_pos_seriesC_ex_double (λ '(a, b), μ a * f a (b, b'))); [| |done].
  - real_solver.
  - intros a. apply ex_seriesC_scal_l.
    apply (ex_seriesC_rmarg (f a)); [|done].
    real_solver.
Qed.

Lemma distr_double_swap_rmarg `{Countable A, Countable B, Countable B'}
  (f : A → distr (B * B')) (μ : distr A) b' :
  SeriesC (λ a : A, SeriesC (λ b : B, μ a * f a (b, b'))) =
  SeriesC (λ b : B, SeriesC (λ a : A, μ a * f a (b, b'))).
Proof.
  rewrite (fubini_pos_seriesC (λ '(a, b), μ a * f a (b, b'))); [done| | |].
  - real_solver.
  - intros. apply ex_seriesC_scal_l.
    apply (ex_seriesC_rmarg (f a)); [real_solver|done].
  - setoid_rewrite SeriesC_scal_l.
    apply (ex_seriesC_le _ μ); [|done].
    intro a; split.
    + apply Rmult_le_pos; [done|].
      apply SeriesC_ge_0; [done|].
      by apply (ex_seriesC_rmarg (f a)).
    + rewrite -{2}(Rmult_1_r (μ _)).
      apply Rmult_le_compat_l; [done|].
      apply (Rle_trans _ (SeriesC (f a))); [|done].
      apply (seriesC_rmarg_le (f a)); [real_solver|done].
Qed.

Lemma distr_double_swap_lmarg_ex `{Countable A, Countable B, Countable B'}
  (f : A → distr (B * B')) (μ : distr A) (b : B) :
  ex_seriesC (λ a : A, SeriesC (λ b' : B', μ a * f a (b, b'))) →
  ex_seriesC (λ b' : B', SeriesC (λ a : A, μ a * f a (b, b'))).
Proof.
  intro Hex.
  apply (fubini_pos_seriesC_ex_double (λ '(a, b'), μ a * f a (b, b'))); auto.
  - real_solver.
  - intros. apply ex_seriesC_scal_l.
    apply (ex_seriesC_lmarg (f a)); [real_solver|done].
Qed.

Lemma distr_double_swap_lmarg `{Countable A, Countable B, Countable B'}
  (f : A → distr (B * B')) (μ : distr A) (b : B) :
  SeriesC (λ a : A, SeriesC (λ b' : B', μ a * f a (b, b'))) =
  SeriesC (λ b' : B', SeriesC (λ a : A, μ a * f a (b, b'))).
Proof.
  rewrite (fubini_pos_seriesC (λ '(a, b'), μ a * f a (b, b'))); [done| | |].
  - real_solver.
  - intros . apply ex_seriesC_scal_l.
    apply (ex_seriesC_lmarg (f a)); [real_solver|done].
  - setoid_rewrite SeriesC_scal_l.
    apply (ex_seriesC_le _ μ); [|done].
    intro a; split.
    + apply Rmult_le_pos; [done|].
      apply SeriesC_ge_0; [done|].
      by apply (ex_seriesC_lmarg (f a)).
    + rewrite -{2}(Rmult_1_r (μ _)).
      apply Rmult_le_compat_l; [done|].
      apply (Rle_trans _ (SeriesC (f a))); [|done].
      apply (seriesC_lmarg_le (f a)); [real_solver|done].
Qed.

(** * Monadic return  *)
Definition dret_pmf `{Countable A} (a : A) : A → R :=
  λ (a' : A), if bool_decide (a' = a) then 1 else 0.

Program Definition dret `{Countable A} (a : A) : distr A := MkDistr (dret_pmf a) _ _ _.
Next Obligation. intros. rewrite /dret_pmf. case_bool_decide; nra. Qed.
Next Obligation. intros. apply ex_seriesC_singleton. Qed.
Next Obligation. intros. rewrite SeriesC_singleton //. Qed.

Section dret.
  Context `{Countable A}.

  Lemma dret_pmf_unfold (a a':A):
    dret a a' = if bool_decide (a' = a) then 1%R else 0%R.
  Proof. done. Qed. 

  Lemma dret_1 (a a' : A) :
    a = a' ↔ dret a a' = 1.
  Proof.
    split.
    - intros ->. rewrite /pmf /= /dret_pmf bool_decide_eq_true_2 //.
    - rewrite /pmf /= /dret_pmf. case_bool_decide; [done|lra].
  Qed.

  Lemma dret_1_1 (a a' : A) :
    a = a' → dret a a' = 1.
  Proof. apply dret_1. Qed.

  Lemma dret_1_2 (a a' : A) :
    dret a a' = 1 → a = a'.
  Proof. apply dret_1. Qed.

  Lemma dret_0 (a a' : A) :
    a' ≠ a → dret a a' = 0.
  Proof. intros ?. rewrite /pmf /= /dret_pmf bool_decide_eq_false_2 //. Qed.

  Lemma dret_pos (a a' : A) :
    dret a a' > 0 → a' = a.
  Proof. rewrite /pmf /= /dret_pmf. intros ?. case_bool_decide; [done|lra]. Qed.

  Lemma dret_pmf_map (f : A → A)  `{Inj A A (=) (=) f} (a a' : A) :
    dret (f a) (f a') = dret a a'.
  Proof.
    rewrite /pmf /= /dret_pmf. case_bool_decide as Hcase.
    - apply (inj f) in Hcase as ->. rewrite bool_decide_eq_true_2 //.
    - case_bool_decide; [|done]. simplify_eq.
  Qed.

  Lemma pmf_1_eq_dret (μ : distr A) (a : A) :
    μ a = 1 → μ = dret a.
  Proof.
    intros Hμ.
    apply distr_ext.
    intros a'.
    destruct (decide (a = a')) as [<- | Hneq].
    { rewrite dret_1_1 //. }
    rewrite dret_0 //.
    destruct (decide (μ a' > 0)) as [Ha'|].
    - rewrite (pmf_1_supp_eq _ _ _ Hμ Ha') // in Hneq.
    - by apply pmf_eq_0_not_gt_0.
  Qed.

  Lemma pmf_1_not_eq (μ : distr A) (a a' : A) :
    a ≠ a' → μ a = 1 → μ a' = 0.
  Proof.
    intros Hneq ->%pmf_1_eq_dret. by apply dret_0.
  Qed.

  Lemma dret_mass (a : A) :
    SeriesC (dret a) = 1.
  Proof. rewrite SeriesC_singleton //. Qed.

End dret.

(** * Monadic bind  *)
Definition dbind_pmf `{Countable A, Countable B} (f : A → distr B) (μ : distr A) : B → R :=
  λ (b : B), SeriesC (λ (a : A), μ a * f a b).

Program Definition dbind `{Countable A, Countable B} (f : A → distr B) (μ : distr A) : distr B :=
  MkDistr (dbind_pmf f μ) _ _ _.
Next Obligation.
  intros ?????? f μ b. rewrite /dbind_pmf.
  apply SeriesC_ge_0.
  - real_solver.
  - eapply (ex_seriesC_le _ (λ a, μ a * 1)); [|by apply ex_seriesC_scal_r].
    real_solver.
Qed.
Next Obligation.
  intros ?????? f μ. rewrite /dbind_pmf.
  apply (distr_double_swap_ex f μ).
  eapply (ex_seriesC_ext (λ j, μ j * SeriesC (λ k, f j k))).
  { intros a. rewrite SeriesC_scal_l //. }
  apply (ex_seriesC_le _ (λ a : A, μ a * 1)); [|by apply ex_seriesC_scal_r].
  real_solver.
Qed.
Next Obligation.
  intros ?????? f μ. rewrite /dbind_pmf.
  rewrite distr_double_swap.
  rewrite -(SeriesC_ext (λ k, μ k * SeriesC (λ j, f k j))); last first.
  { intros a. rewrite SeriesC_scal_l //. }
  transitivity (SeriesC μ); [|done].
  eapply SeriesC_le; [|done].
  real_solver.
Qed.

Lemma dbind_pmf_ext `{Countable A, Countable B} (μ1 μ2 : distr A) (f g : A → distr B) (b1 b2 : B) :
  (∀ a b, f a b = g a b) →
  μ1 = μ2 →
  b1 = b2 →
  dbind f μ1 b1 = dbind g μ2 b2.
Proof.
  intros Hfg -> ->=>/=. rewrite /pmf /= /dbind_pmf.
  eapply SeriesC_ext=>a. rewrite Hfg //.
Qed.

Lemma dbind_ext_right `{Countable A, Countable B} (μ : distr A) (f g : A → distr B) :
  (∀ a, f a = g a) →
  dbind f μ = dbind g μ.
Proof.
  intro Heq.
  apply distr_ext=> a.
  apply dbind_pmf_ext; [|done|done].
  intros.
  rewrite Heq //.
Qed.

Lemma dbind_ext_right_strong `{Countable A, Countable B} (μ : distr A) (f g : A → distr B) :
  (∀ a, μ a > 0 -> f a = g a) →
  dbind f μ = dbind g μ.
Proof.
  intro Heq.
  apply distr_ext=> a.
  rewrite /dbind/dbind_pmf{1 4}/pmf.
  apply SeriesC_ext.
  intros n.
  pose proof pmf_pos μ n as [|<-]; last lra.
  by rewrite Heq.
Qed.

Lemma dbind_ext_right' `{Countable A, Countable B} (μ1 μ2 : distr A) (f g : A → distr B) :
  (∀ a, f a = g a) →
  μ1 = μ2 ->
  dbind f μ1 = dbind g μ2.
Proof.
  intros Heq ->.
  by apply dbind_ext_right.
Qed. 

#[global] Instance Proper_dbind `{Countable A, Countable B} :
  Proper (pointwise_relation A (=) ==> (=) ==> (=)) (@dbind A _ _ B _ _).
Proof. intros ?? Hp ?? ->. f_equal. extensionality a. done. Qed.

(* TODO: generalize to distributions with countable support so that we can use
   the [stdpp] typeclasses *)
Notation "m ≫= f" := (dbind f m) (at level 60, right associativity) : stdpp_scope.
Notation "( m ≫=.)" := (λ f, dbind f m) (only parsing) : stdpp_scope.
Notation "(.≫= f )" := (dbind f) (only parsing) : stdpp_scope.
Notation "(≫=)" := (λ m f, dbind f m) (only parsing) : stdpp_scope.

Notation "x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.

Notation "' x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, x pattern, y at level 100, z at level 200, only parsing) : stdpp_scope.

(** * Lemmas about the interplay of monadic bind and return  *)
Section monadic.
  Context `{Countable A}.

  Lemma dret_id_right_pmf (μ : distr A) (a : A) :
    (a ← μ; dret a) a = μ a.
  Proof.
    rewrite {1}/pmf /= /dbind_pmf {2}/pmf /= /dret_pmf.
    rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then μ a else 0)).
    { rewrite SeriesC_singleton //. }
    real_solver.
  Qed.

  Lemma dret_id_right (μ : distr A) :
    (a ← μ; dret a) = μ.
  Proof. apply distr_ext, dret_id_right_pmf. Qed.

  Context `{Countable B}.

  Lemma dbind_unfold_pmf μ1 (μ2 : A -> distr B) (b : B):
    (μ1 ≫= μ2) b = SeriesC (λ a : A, μ1 a * μ2 a b).
  Proof.
    done.
  Qed.
  
  Lemma dret_id_left_pmf (f : A → distr B) (a : A) (b : B) :
    (a' ← dret a; f a') b = f a b.
  Proof.
    rewrite {1}/pmf /= /dbind_pmf {1}/pmf /= /dret_pmf.
    rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then f a b else 0)).
    { rewrite SeriesC_singleton //. }
    real_solver.
  Qed.

  Lemma dret_id_left (f : A → distr B) (a : A) :
    (a' ← dret a; f a') = f a.
  Proof. apply distr_ext, dret_id_left_pmf. Qed.

  Lemma dret_id_left' (f : A → distr B) (a : A) :
    (dret a ≫= f) = f a.
  Proof. apply distr_ext, dret_id_left_pmf. Qed.

  Lemma dret_const (μ : distr A) (b : B) :
    SeriesC μ = 1 →
    (a ← μ; dret b) = dret b.
  Proof.
    intro HSeries.
    apply distr_ext; intro a.
    rewrite {1}/pmf/=/dbind_pmf.
    rewrite SeriesC_scal_r HSeries; lra.
  Qed.

  Lemma dbind_dret_pmf_map (μ : distr A) (a : A) (f : A → B) `{Inj A B (=) (=) f} :
    (μ ≫= (λ a', dret (f a'))) (f a) = μ a.
  Proof.
    rewrite {1}/pmf /= /dbind_pmf {2}/pmf /= /dret_pmf.
    rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then μ a else 0)).
    { rewrite SeriesC_singleton //. }
    real_solver.
  Qed.

  Lemma dbind_dret_pmf_map_ne (μ : distr A) (b : B) (f : A → B) `{Inj A B (=) (=) f} :
    ¬ (∃ a, μ a > 0 ∧ f a = b) →
    (μ ≫= (λ a, dret (f a))) b = 0.
  Proof.
    intros Hnex.
    rewrite {1}/pmf /= /dbind_pmf {2}/pmf /= /dret_pmf.
    apply SeriesC_0.
    intros a'.
    case_bool_decide; [|lra].
    destruct (decide (μ a' > 0)) as [|Hn]; [exfalso; eauto|].
    apply pmf_eq_0_not_gt_0 in Hn as ->; lra.
  Qed.

  Lemma dbind_assoc_pmf `{Countable B'} (f : A → distr B) (g : B → distr B') (μ : distr A) c :
    (a ← μ ; b ← f a; g b) c = (b ← (a ← μ; f a); g b) c.
  Proof.
    rewrite !/pmf /= /dbind_pmf.
    assert (SeriesC (λ a, μ a * SeriesC (λ a0 : B, f a a0 * g a0 c)) =
            SeriesC (λ a, SeriesC (λ a0 : B, μ a * f a a0 * g a0 c))) as Heq1.
    { apply SeriesC_ext=> a.
      rewrite -SeriesC_scal_l.
      apply SeriesC_ext; real_solver. }
    rewrite Heq1.
    rewrite -(fubini_pos_seriesC (λ '(a ,a0), μ a * f a a0 * g a0 c)).
    - apply SeriesC_ext=> b.
      rewrite {4}/pmf /= /dbind_pmf.
      rewrite -SeriesC_scal_r //.
    - real_solver.
    - intro; apply (ex_seriesC_le _ (f a)); [|done].
      real_solver.
    - setoid_rewrite Rmult_assoc.
      setoid_rewrite SeriesC_scal_l.
      apply (ex_seriesC_le _ μ); [|done].
      intro; split.
      + apply Rmult_le_pos; [done|].
        apply SeriesC_ge_0'=> b. real_solver.
      + transitivity (μ n * (SeriesC (f n))).
        * apply Rmult_le_compat; [done| |done|].
          -- apply SeriesC_ge_0'=>b. real_solver.
          -- apply SeriesC_le; [|done]. real_solver.
        * real_solver.
  Qed.

  Lemma dbind_assoc `{Countable B'} (f : A → distr B) (g : B → distr B') (μ : distr A) :
    (a ← μ ; b ← f a; g b) = (b ← (a ← μ; f a); g b).
  Proof. apply distr_ext, dbind_assoc_pmf. Qed.

  Lemma dbind_assoc' `{Countable B'} (f : A → distr B) (g : B → distr B') (μ : distr A) :
    μ ≫= (λ a, f a ≫= g) = (μ ≫= f) ≫= g.
  Proof. rewrite dbind_assoc //. Qed.

  Lemma dbind_comm `{Countable B'} (f : A → B → distr B') (μ1 : distr A) (μ2 : distr B):
    (a ← μ1 ; b ← μ2; f a b) = (b ← μ2; a ← μ1; f a b).
  Proof.
    apply distr_ext=> b'. rewrite /pmf/=/dbind_pmf.
    erewrite SeriesC_ext; last first.
    { intro; rewrite {2}/pmf/=/dbind_pmf/=.
      rewrite -SeriesC_scal_l //. }
    symmetry.
    erewrite SeriesC_ext; last first.
    { intro b; rewrite {2}/pmf/=/dbind_pmf/=.
      rewrite -SeriesC_scal_l.
      setoid_rewrite <-Rmult_assoc at 1.
      setoid_rewrite (Rmult_comm (μ2 _) (μ1 _)) at 1.
      setoid_rewrite Rmult_assoc at 1.
      done. }
    apply (fubini_pos_seriesC (λ '(a, b), μ1 a * (μ2 b * f a b b'))).
    - real_solver.
    - intros a.
      apply (ex_seriesC_le _ μ2); [|done].
      real_solver.
    - apply (ex_seriesC_le _ μ1); [|done].
      intro a; split.
      + apply SeriesC_ge_0'=> b. real_solver.
      + rewrite SeriesC_scal_l.
        rewrite -{2}(Rmult_1_r (μ1 _)).
        apply Rmult_le_compat; [done| |done|].
        * apply SeriesC_ge_0'=> b. real_solver.
        * apply (Rle_trans _ (SeriesC μ2)); [|done].
          apply SeriesC_le; [|done].
          real_solver.
   Qed.

  Lemma dbind_pos (f : A → distr B) (μ : distr A) (b : B) :
    dbind f μ b > 0 ↔ ∃ a, f a b > 0 ∧ μ a > 0.
  Proof.
    rewrite {1}/pmf /= /dbind_pmf. split.
    - eapply contrapositive. intros Hna.
      assert (∀ a, μ a * f a b = 0) as Hz.
      { intros a.
        pose proof (not_exists_forall_not _ _ Hna a) as [Hne | Hne]%not_and_or_not.
        - pose proof (pmf_pos (f a) b). assert (f a b = 0) as ->; lra.
        - pose proof (pmf_pos μ a). assert (μ a = 0) as ->; lra. }
      apply Rge_not_gt. rewrite SeriesC_0 //.
    - intros (a & Hf & Hμ). eapply Rlt_gt.
      eapply (Rlt_le_trans _ (SeriesC (λ a', if bool_decide (a' = a) then μ a * f a b else 0))).
      { rewrite SeriesC_singleton. real_solver. }
      eapply SeriesC_le.
      + real_solver.
      + apply (ex_seriesC_le _ (λ a : A, μ a * 1)); [|by apply ex_seriesC_scal_r].
        real_solver.
  Qed.

  Lemma dbind_eq (f g : A → distr B) (μ1 μ2 : distr A) :
    (∀ a, μ1 a > 0 → f a = g a) →
    (∀ a, μ1 a = μ2 a) →
    dbind f μ1 = dbind g μ2.
  Proof.
    intros Heq Hμ.
    eapply distr_ext. intros b.
    rewrite /pmf /= /dbind_pmf. eapply SeriesC_ext.
    intros a. rewrite -Hμ.
    destruct (decide (μ1 a > 0)) as [|Hngt].
    { rewrite Heq //. }
    apply pmf_eq_0_not_gt_0 in Hngt as ->.
    lra.
  Qed.

  Lemma dbind_inhabited (f : A → distr B) (μ : distr A) :
    SeriesC μ > 0 →
    (∀ a, SeriesC (f a) > 0) →
    SeriesC (dbind f μ) > 0.
  Proof.
    intros Hμ Hf.
    rewrite /pmf /= /dbind_pmf.
    rewrite (distr_double_swap f μ).
    setoid_rewrite SeriesC_scal_l.
    apply Rlt_gt. rewrite -(SeriesC_0 (λ _ : A, 0)); [|done].
    eapply SeriesC_lt.
    - real_solver.
    - apply SeriesC_gtz_ex in Hμ as [a Ha]; [|done].
      exists a. real_solver.
    - eapply pmf_ex_seriesC_mult_fn. eauto.
  Qed.


  Lemma dbind_inhabited_ex (f : A → distr B) (μ : distr A) :
    (exists a, μ a > 0 /\ SeriesC (f a) > 0) →
    SeriesC (dbind f μ) > 0.
  Proof.
    intros [a [Ha1 Ha2]].
    rewrite /pmf /= /dbind_pmf.
    rewrite (distr_double_swap f μ).
    setoid_rewrite SeriesC_scal_l.
    apply Rlt_gt. rewrite -(SeriesC_0 (λ _ : A, 0)); [|done].
    eapply SeriesC_lt.
    - real_solver.
    - exists a. nra.
    - eapply pmf_ex_seriesC_mult_fn. eauto.
  Qed.

  Lemma dbind_dret_pair_left `{Countable A'}
    (μ : distr A) (a' : A') (b : A) :
    (μ ≫= (λ a, dret (a, a'))) (b, a') = μ b.
  Proof.
    rewrite {1}/pmf/=/dbind_pmf.
    erewrite SeriesC_ext; [apply SeriesC_singleton'|].
    intros a. rewrite {2}/pmf/=/dret_pmf.
    real_solver.
  Qed.

  Lemma dbind_dret_pair_right `{Countable A'}
    (μ : distr A') (a : A) (b : A') :
    (μ ≫= (λ a', dret (a, a'))) (a, b) = μ b.
  Proof.
    rewrite {1}/pmf/=/dbind_pmf.
    erewrite SeriesC_ext; [apply SeriesC_singleton'|].
    intro. rewrite {2}/pmf/=/dret_pmf.
    real_solver.
  Qed.

  Lemma dbind_mass (μ : distr A) (f : A → distr B) :
    SeriesC (μ ≫= f) = SeriesC (λ a, μ a * SeriesC (f a)).
  Proof.
    rewrite {1}/pmf /= /dbind_pmf.
    rewrite distr_double_swap.
    eapply SeriesC_ext. intros. rewrite SeriesC_scal_l //.
  Qed.

  Lemma dbind_det (μ : distr A) (f : A → distr B) :
    SeriesC μ = 1 →
    (∀ a, μ a > 0 → SeriesC (f a) = 1) →
    SeriesC (μ ≫= f) = 1.
  Proof.
    intros Hμ Hf.
    rewrite {1}/pmf /= /dbind_pmf.
    rewrite dbind_mass.
    rewrite -Hμ.
    eapply SeriesC_ext => a.
    destruct (decide (μ a > 0)) as [Hgt | ->%pmf_eq_0_not_gt_0]; [|lra].
    rewrite Hf //. lra.
  Qed.

  Lemma dbind_det_inv_l (μ1 : distr A) (f : A → distr B) (b : B) :
    (μ1 ≫= f) b = 1 →
    SeriesC μ1 = 1.
  Proof.
    rewrite {1}/pmf /= /dbind_pmf.
    intros Hbind.
    apply Rle_antisym; [done|].
    rewrite -Hbind.
    apply SeriesC_le; [|done].
    real_solver.
  Qed.

  Lemma dbind_det_inv_r (μ1 : distr A) (f : A → distr B) (b : B) :
    (μ1 ≫= f) b = 1 →
    (∀ a, μ1 a > 0 → f a b = 1).
  Proof.
    rewrite {1}/pmf /= /dbind_pmf.
    intros Hbind a Ha.
    assert (SeriesC (λ a', μ1 a' * (if bool_decide (a' = a) then 1 else f a' b )) =
            SeriesC (λ a' : A, μ1 a' * f a' b)) as Haux.
    { apply Rle_antisym.
      - rewrite Hbind.
        transitivity (SeriesC μ1); [|done].
        apply SeriesC_le; [|done].
        real_solver.
      - apply SeriesC_le.
        + real_solver.
        + apply (ex_seriesC_le _ μ1); [|done]. real_solver. }
    rewrite (SeriesC_split_elem _ a) in Haux; first last.
    - apply (ex_seriesC_le _ μ1); [|done]. real_solver.
    - real_solver.
    - rewrite (SeriesC_split_elem (λ a', μ1 a' * f a' b) a) in Haux; first last.
      + apply (ex_seriesC_le _ μ1); [|done]. real_solver.
      + real_solver.
      + (* We do this kind of rewrite often enough that it could be a lemma *)
        assert (SeriesC (λ a0 : A, if bool_decide (a0 = a) then μ1 a0 * f a0 b else 0)
              = SeriesC (λ a0 : A, if bool_decide (a0 = a) then μ1 a * f a b else 0)) as Hrw1.
        { apply SeriesC_ext. real_solver. }
        rewrite Hrw1 in Haux.
        rewrite SeriesC_singleton in Haux.
        assert (SeriesC (λ a0 : A, if bool_decide (a0 = a) then μ1 a0 * (if bool_decide (a0 = a) then 1 else f a0 b) else 0) =
                SeriesC (λ a0 : A, if bool_decide (a0 = a) then μ1 a else 0)) as Hrw2.
        { apply SeriesC_ext; real_solver. }
        rewrite Hrw2 in Haux.
        rewrite SeriesC_singleton in Haux.
        assert (SeriesC (λ a0 : A, if bool_decide (a0 ≠ a) then μ1 a0 * (if bool_decide (a0 = a) then 1 else f a0 b) else 0) =
                SeriesC (λ a0 : A, if bool_decide (a0 ≠ a) then μ1 a0 * f a0 b else 0)) as Hrw3.
        { apply SeriesC_ext; real_solver. }
        rewrite Hrw3 in Haux.
        real_solver.
  Qed.

End monadic.

Section probabilities.
  Context `{Countable A}.
  Implicit Types μ d : distr A.

  Definition prob (μ : distr A) (P : A → bool) : R :=
    SeriesC (λ a : A, if (P a) then μ a else 0).

  Lemma prob_le_1 (μ : distr A) (P : A → bool) :
    prob μ P <= 1.
  Proof.
    transitivity (SeriesC μ); [|done].
    apply SeriesC_le; [|done].
    real_solver.
  Qed.

  Lemma prob_ge_0 (μ : distr A) (P : A → bool) :
    0 <= prob μ P.
  Proof. apply SeriesC_ge_0'=> a. real_solver. Qed.

End probabilities.

Section probability_lemmas.
  Context `{Countable A}.

  Lemma prob_dret_true (a : A) (P : A → bool) :
    P a = true → prob (dret a) P = 1.
  Proof.
    intro HP.
    rewrite /prob/pmf/=/dret_pmf/=.
    erewrite SeriesC_ext; [apply SeriesC_singleton|].
    real_solver.
  Qed.

  Lemma prob_dret_false (a : A) (P : A → bool) :
    P a = false → prob (dret a) P = 0.
  Proof.
    intro HP.
    rewrite /prob/pmf/=/dret_pmf/=.
    apply SeriesC_0. real_solver.
  Qed.

  Lemma prob_dbind `{Countable B} (μ : distr A) (f : A → distr B) (P : B → bool) :
    prob (dbind f μ) P = SeriesC (λ a, μ a * prob (f a) P).
  Proof.
    rewrite /prob{1}/pmf/=/dbind_pmf/=.
    assert (∀ a,
               (if P a then SeriesC (λ a0 : A, μ a0 * f a0 a) else 0) =
               SeriesC (λ a0 : A, if P a then μ a0 * f a0 a else 0)) as Haux.
    {intro a. destruct (P a); [done|]. rewrite SeriesC_0 //. }
    setoid_rewrite Haux.
    rewrite -(fubini_pos_seriesC (λ '(a, a0), if P a then μ a0 * f a0 a else 0)).
    - apply SeriesC_ext=> a.
      rewrite -SeriesC_scal_l.
      apply SeriesC_ext; intro b.
      real_solver.
    - real_solver.
    - intro b.
      apply (ex_seriesC_le _ μ); [|done].
      real_solver.
    - apply (ex_seriesC_le _ (λ a : B, SeriesC (λ b : A, μ b * f b a))).
      + intro b; split.
        * apply SeriesC_ge_0'. real_solver.
        * apply SeriesC_le; [real_solver|].
          apply pmf_ex_seriesC_mult_fn.
          exists 1. real_solver.
      + apply (pmf_ex_seriesC (dbind f μ)).
  Qed.

  Lemma union_bound (μ : distr A) (P Q : A → bool) :
    prob μ (λ a, orb (P a) (Q a)) <= prob μ P + prob μ Q.
  Proof.
    rewrite /prob.
    rewrite -SeriesC_plus.
    - apply SeriesC_le.
      + intro n.
        pose proof (pmf_pos μ n).
        destruct (P n); destruct (Q n); real_solver.
      + apply (ex_seriesC_le _ (λ x, 2 * μ x)).
        * intro n.
          pose proof (pmf_pos μ n).
          destruct (P n); destruct (Q n); real_solver.
        * by apply ex_seriesC_scal_l.
    - by apply ex_seriesC_filter_bool_pos.
    - by apply ex_seriesC_filter_bool_pos.
  Qed.

End probability_lemmas.


Section probabilities_prop.
  Context `{Countable A}.
  Context (μ : distr A).
  Context (P : A -> Prop).
  Context `{forall a, Decision (P a)}.

  Definition probp : R :=
    SeriesC (λ a : A, if (bool_decide (P a)) then μ a else 0).

  Lemma probp_le_1 :
    probp <= 1.
  Proof.
    transitivity (SeriesC μ); [|done].
    apply SeriesC_le; [|done].
    real_solver.
  Qed.

  Lemma probp_ge_0 :
    0 <= probp.
  Proof. apply SeriesC_ge_0'=> a. real_solver. Qed.

End probabilities_prop.

Section probability_prop_lemmas.
  Context `{Countable A}.

  Lemma probp_dret_true (a : A) (P : A → Prop) `{forall a, Decision (P a)}:
    P a → probp (dret a) P = 1.
  Proof.
    intro HP.
    rewrite /probp/pmf/=/dret_pmf/=.
    erewrite SeriesC_ext; [apply SeriesC_singleton|].
    real_solver.
  Qed.

  Lemma probp_dret_false (a : A) (P : A → Prop) `{forall a, Decision (P a)}:
    ¬ (P a) → probp (dret a) P = 0.
  Proof.
    intro HP.
    rewrite /probp/pmf/=/dret_pmf/=.
    apply SeriesC_0; real_solver.
  Qed.

  Lemma probp_dbind `{Countable B} (μ : distr A) (f : A → distr B) (P : B → Prop) `{forall a, Decision (P a)}:
    probp (dbind f μ) P = SeriesC (λ a, μ a * probp (f a) P).
  Proof.
    rewrite /probp{1}/pmf/=/dbind_pmf/=.
    assert (∀ a,
               (if (bool_decide (P a)) then SeriesC (λ a0 : A, μ a0 * f a0 a) else 0) =
               SeriesC (λ a0 : A, if (bool_decide (P a)) then μ a0 * f a0 a else 0)) as Haux.
    {intro a. case_bool_decide; [done|]. rewrite SeriesC_0 //. }
    setoid_rewrite Haux.
    rewrite -(fubini_pos_seriesC (λ '(a, a0), if (bool_decide (P a)) then μ a0 * f a0 a else 0)).
    - apply SeriesC_ext=> a.
      rewrite -SeriesC_scal_l.
      apply SeriesC_ext; intro b.
      real_solver.
    - real_solver.
    - intro b.
      apply (ex_seriesC_le _ μ); [|done].
      real_solver.
    - apply (ex_seriesC_le _ (λ a : B, SeriesC (λ b : A, μ b * f b a))).
      + intro b; split.
        * apply SeriesC_ge_0'. real_solver.
        * apply SeriesC_le; [real_solver|].
          apply pmf_ex_seriesC_mult_fn.
          exists 1. real_solver.
      + apply (pmf_ex_seriesC (dbind f μ)).
  Qed.

  Lemma union_bound_prop (μ : distr A) (P Q : A → Prop) `{forall a, Decision (P a)} `{forall a, Decision (Q a)} :
    probp μ (λ a, (P a) \/ (Q a)) <= probp μ P + probp μ Q.
  Proof.
    rewrite /probp.
    rewrite -SeriesC_plus.
    - apply SeriesC_le.
      + intro n.
        pose proof (pmf_pos μ n).
        do 3 case_bool_decide; try real_solver.
        destruct_or?; done.
      + apply (ex_seriesC_le _ (λ x, 2 * μ x)).
        * intro n.
          pose proof (pmf_pos μ n).
          do 2 case_bool_decide; real_solver.
        * by apply ex_seriesC_scal_l.
    - by apply ex_seriesC_filter_bool_pos.
    - by apply ex_seriesC_filter_bool_pos.
  Qed.

End probability_prop_lemmas.


Section subset_distribution.
  Context `{Countable A}.
  Context (P : A -> bool).
  Implicit Types μ d : distr A.

  Definition ssd_pmf (μ : distr A) :=
    λ a : A, if P a then μ a else 0.

  Program Definition ssd (μ : distr A) := MkDistr (ssd_pmf μ) _ _ _.
  Next Obligation.
    move=> μ a.
    rewrite /ssd_pmf. by (destruct (P a)).
  Qed.
  Next Obligation.
    move=> μ. rewrite /ssd_pmf.
    eapply (ex_seriesC_le _ μ); try done.
    move=> n. split; by (destruct (P n)).
  Qed.
  Next Obligation.
    move=> μ.
    etrans.
    - eapply (SeriesC_le _ μ); try done. rewrite /ssd_pmf.
      split; by (destruct (P n)).
    - done.
  Qed.

End subset_distribution.


Declare Scope predicate_scope.
Delimit Scope predicate_scope with P.
Notation "∽ K " := (λ a, negb (K a)) (at level 70, right associativity) : predicate_scope.

Section subset_distribution_lemmas.
  Context `{Countable A}.
  Implicit Type P : A -> bool.
  Implicit Types μ : distr A.

  Lemma ssd_ret_pos P μ (a : A) : ssd P μ a > 0 -> P a.
  Proof.
    rewrite /ssd /ssd_pmf /pmf. move=> H0.
    destruct (P a); [done|lra].
  Qed.

  Lemma ssd_sum P μ (a : A) : μ a = ssd P μ a + ssd (∽ P)%P μ a.
  Proof.
    rewrite /ssd /ssd_pmf /pmf /=.
    destruct (P a) => /=; lra.
  Qed.

  Lemma ssd_remove P μ : (∀ a, negb (P a) -> μ a = 0) -> ssd P μ = μ.
  Proof.
    move=> H0.
    apply distr_ext. move=> a. destruct (P a) eqn:H'.
    - by rewrite /ssd{1}/pmf/ssd_pmf H'.
    - rewrite /ssd{1}/pmf/ssd_pmf H'. rewrite H0; [done|by rewrite H'].
  Qed.

End subset_distribution_lemmas.

Section bind_lemmas.
  Context `{Countable A, Countable B}.
  Implicit Types μ: distr A.
  Implicit Types ν: A -> distr B.

  Lemma bind_split_sum (μ μ1 μ2 : distr A) ν:
    (∀ a, μ a = μ1 a + μ2 a) ->
    (∀ b, (μ ≫= λ a', ν a') b = (μ1 ≫= λ a', ν a') b + (μ2 ≫= λ a', ν a') b).
  Proof.
    move=> H1 b.
    rewrite /pmf /= /dbind_pmf.
    rewrite -SeriesC_plus; last first.
    { eapply (ex_seriesC_le _ (λ a, μ2 a)); [intros n; split|apply pmf_ex_seriesC].
      - real_solver.
      - rewrite <-Rmult_1_r. by apply Rmult_le_compat_l.
    }
    { eapply (ex_seriesC_le _ (λ a, μ1 a)); [intros n; split|apply pmf_ex_seriesC].
      - real_solver.
      - rewrite <-Rmult_1_r. by apply Rmult_le_compat_l.
    }
    f_equal. apply functional_extensionality_dep => a.
    replace (_*_+_*_) with ((μ1 a + μ2 a) * ν a b); last real_solver.
    by rewrite -H1.
  Qed.

  Lemma ssd_bind_split_sum μ ν P :
    ∀ b, (μ ≫= λ a', ν a') b = (ssd P μ ≫= λ a', ν a') b + (ssd (∽ P)%P μ ≫= λ a', ν a')b.
  Proof.
    move=> b.
    erewrite <-bind_split_sum; first done.
    intros. apply ssd_sum.
  Qed.


  (** *strengthen following lemma? *)
  Lemma ssd_bind_constant P μ ν (b : B) k:
    (∀ a, P a = true -> ν a b = k) -> (ssd P μ ≫= λ a', ν a') b = k * SeriesC (ssd P μ).
  Proof.
    move=> H1.
    rewrite {1}/pmf /= /dbind_pmf.
    rewrite -SeriesC_scal_l.
    f_equal. apply functional_extensionality_dep => a.
    destruct (P a) eqn:H'.
    - apply H1 in H'. rewrite H'. real_solver.
    - rewrite /ssd /pmf /ssd_pmf H'. real_solver.
  Qed.

  Lemma ssd_fix_value μ (v : A):
    SeriesC (ssd (λ a, bool_decide (a = v)) μ) = μ v.
  Proof.
    erewrite <-(SeriesC_singleton v).
    f_equal.
    apply functional_extensionality_dep => a.
    rewrite /ssd/pmf/ssd_pmf/pmf. case_bool_decide; eauto.
    by rewrite H1.
  Qed.


  Lemma ssd_chain μ (P Q: A -> bool):
    ssd P (ssd Q μ) = ssd (λ a, P a && Q a) μ.
  Proof.
    apply distr_ext => a.
    rewrite /ssd/pmf/ssd_pmf/pmf.
    destruct (P a) eqn:H1; destruct (Q a) eqn:H2; eauto.
  Qed.

End bind_lemmas.


Section exp_val.

  Context `{Countable A}.
  Implicit Types μ : distr A.
  Implicit Types f : A -> R.

  Definition ex_expval μ f :=
    ex_seriesC (λ a, μ a * f a).

  Definition Expval μ f :=
    SeriesC (λ a, μ a * f a).

End exp_val.

Section exp_val_prop.

  Context `{Countable A, Countable B}.
  Implicit Types μ : distr A.
  Implicit Types f : A -> R.

  Lemma ex_expval_dret f a :
    ex_expval (dret a) f.
  Proof.
    rewrite /ex_expval/pmf/=/dret_pmf.
    assert (forall a0, ((if bool_decide (a0 = a) then 1 else 0) * f a0) = (if bool_decide (a0 = a) then f a else 0)) as Haux.
    { intro x; real_solver. }
    setoid_rewrite Haux.
    apply ex_seriesC_singleton.
  Qed.

  Lemma Expval_dret f a :
    Expval (dret a) f = f a.
  Proof.
    rewrite /Expval/pmf/=/dret_pmf.
    assert (forall a0, ((if bool_decide (a0 = a) then 1 else 0) * f a0) = (if bool_decide (a0 = a) then f a else 0)) as Haux.
    { intro x; real_solver. }
    setoid_rewrite Haux.
    apply SeriesC_singleton.
  Qed.

  Lemma ex_expval_const μ c :
    ex_expval μ (λ x, c).
  Proof.
    rewrite /ex_expval.
    apply ex_seriesC_scal_r; auto.
  Qed.

  Lemma Expval_const μ c :
    (0 <= c) ->
    Expval μ (λ x, c) = c * (SeriesC μ).
  Proof.
    intros Hpos.
    rewrite /Expval SeriesC_scal_r; lra.
  Qed.

  Lemma ex_expval_le μ f g :
    (forall x, 0 <= f x <= g x) ->
    ex_expval μ g ->
    ex_expval μ f.
  Proof.
    intros Hleq Hex.
    apply (ex_seriesC_le _ (λ x, μ x * g x)); auto.
    intro x; specialize (Hleq x); real_solver.
  Qed.


  Lemma Expval_le μ f g :
    (forall x, 0 <= f x <= g x) ->
    ex_expval μ g ->
    Expval μ f <= Expval μ g.
  Proof.
    intros Hleq Hex.
    apply SeriesC_le; auto.
    intro x; specialize (Hleq x); real_solver.
  Qed.

  Lemma ex_expval_bounded μ f c :
    (forall x, 0 <= f x <= c) ->
    ex_expval μ f.
  Proof.
    intros Hleq.
    eapply ex_expval_le; [ | apply (ex_expval_const _ c) ]; auto.
  Qed.


  Lemma Expval_bounded μ f c :
    (0 <= c) ->
    (forall x, 0 <= f x <= c) ->
    Expval μ f <= c.
  Proof.
    intros Hpos Hleq.
    etransitivity.
    - apply Expval_le; [ | apply (ex_expval_const _ c)].
      auto.
    - rewrite Expval_const;
      real_solver.
  Qed.

  Lemma ex_expval_dbind (μ : distr A) (f : A → distr B) h :
    (∀ a, 0 <= h a) →
    ex_expval μ (λ a, Expval (f a) h) →
    (∀ a, ex_expval (f a) h) →
    ex_expval (μ ≫= f) h.
  Proof.
    intros Hh Hμ Hf.
    rewrite /ex_expval.
    rewrite /pmf /= /dbind_pmf /=.
    setoid_rewrite <- SeriesC_scal_r.
    eapply (fubini_pos_seriesC_ex_double (λ '(x, a), μ x * f x a * h a)).
    { real_solver. }
    { intros a.
      setoid_rewrite Rmult_assoc.
      eapply ex_seriesC_scal_l. eapply Hf. }
    setoid_rewrite Rmult_assoc.
    setoid_rewrite SeriesC_scal_l.
    eapply Hμ.
  Qed.

  (*
     Should hold without the positivity assumption, but then
     we don't get Fubini
  *)
  Lemma Expval_dbind μ (k : A -> distr B) (f : B -> R):
    (forall b, 0 <= f b) ->
    ex_expval (μ ≫= k) f ->
    Expval (μ ≫= k) f = Expval μ (λ a, Expval (k a) f).
  Proof.
    intros Hpos Hex.
    rewrite /Expval {1}/pmf/=/dbind_pmf.
    setoid_rewrite <- SeriesC_scal_l.
    setoid_rewrite <- SeriesC_scal_r.
    setoid_rewrite Rmult_assoc.
    rewrite (fubini_pos_seriesC (λ '(a,x), μ x * (k x a * f a))); auto.
    - real_solver.
    - intros.
      setoid_rewrite <- Rmult_assoc.
      apply ex_seriesC_scal_r.
      apply (ex_seriesC_le _ μ); auto; real_solver.
    - setoid_rewrite <- Rmult_assoc.
      setoid_rewrite SeriesC_scal_r; auto.
  Qed.

  Lemma Expval_scal_l μ f c :
    Expval μ (λ x, c * f x) = c * Expval μ f.
  Proof.
    rewrite /Expval.
    rewrite -SeriesC_scal_l.
    apply SeriesC_ext; intro; lra.
  Qed.

  Lemma Expval_scal_r μ f c :
    Expval μ (λ x, f x * c) = Expval μ f * c.
  Proof.
    rewrite /Expval.
    rewrite -SeriesC_scal_r.
    apply SeriesC_ext; intro; lra.
  Qed.

  Lemma Expval_plus μ f g :
    ex_expval μ f ->
    ex_expval μ g ->
    Expval μ (λ x, f x + g x) = Expval μ f + Expval μ g.
  Proof.
    intros Hex1 Hex2.
    rewrite /Expval.
    rewrite -SeriesC_plus; auto.
    apply SeriesC_ext; intro; lra.
  Qed.


  Lemma Expval_ge_0 μ f :
    (forall a, 0 <= f a) ->
    ex_expval μ f ->
    0 <= Expval μ f.
  Proof.
    intros Hleq Hex.
    apply SeriesC_ge_0; auto.
    intros; real_solver.
  Qed.

  Lemma Expval_ge_0' μ f :
    (forall a, 0 <= f a) ->
    0 <= Expval μ f.
  Proof.
    intros Hleq.
    rewrite /Expval; apply SeriesC_ge_0'.
    real_solver.
  Qed.

  Lemma Expval_convex_le μ f r :
    (forall a, 0 <= r <= f a) ->
    ex_expval μ f ->
    SeriesC μ = 1 ->
    r <= Expval μ f.
  Proof.
    intros Hleq Hex Htot.
    replace r with (Expval μ (λ a, r)).
    - apply SeriesC_le; auto.
      intro a. specialize (Hleq a); real_solver.
    - rewrite /Expval SeriesC_scal_r; nra.
  Qed.

  Lemma Expval_convex_lt μ f r :
    (forall a, 0 <= r < f a) ->
    ex_expval μ f ->
    SeriesC μ = 1 ->
    r < Expval μ f.
  Proof.
    intros Hleq Hex Htot.
    replace r with (Expval μ (λ a, r)).
    - apply SeriesC_lt; auto.
      + intro a. specialize (Hleq a); real_solver.
      + assert (exists a, 0 < μ a) as [a Ha].
        { apply SeriesC_gtz_ex; auto; lra. }
        exists a. specialize (Hleq a); real_solver.
    - rewrite /Expval SeriesC_scal_r; nra.
  Qed.

  Lemma Expval_convex_ex_le μ f r :
    (forall a, 0 <= f a) ->
    ex_expval μ f ->
    SeriesC μ = 1 ->
    Expval μ f <= r ->
    exists a', 0 < μ a' /\ f a' <= r.
  Proof.
    intros Hleq Hex Htot Hub.
    apply NNP_P.
    intro H2.
    assert (forall a, μ a = 0 \/ 0 <= r < f a) as Hleq'.
    {
      intro a.
      pose proof (not_exists_forall_not _ (λ a, 0 < μ a ∧ f a <= r) H2 a) as Haux.
      simpl in Haux.
      apply not_and_or_not in Haux as [? | ?]; [left | right].
      - pose proof (pmf_pos μ a); lra.
      - split; [ | lra].
        eapply Rle_trans; [ apply (Expval_ge_0 μ f) | ]; auto.
    }
    assert (r < Expval μ f); [ | lra].
    replace r with (Expval μ (λ a, r));
      [ | rewrite /Expval SeriesC_scal_r; nra ].
    apply SeriesC_lt; auto.
    - intro a.
      specialize (Hleq' a) as [->| ]; [lra | real_solver].
    - assert (exists a, 0 < μ a) as [a Ha].
        { apply SeriesC_gtz_ex; auto; lra. }
        exists a.
        specialize (Hleq' a) as [|]; [lra | real_solver].
  Qed.

  Lemma Expval_convex_ge μ f r :
    (forall a, 0 <= f a <= r) ->
    ex_expval μ f ->
    SeriesC μ = 1 ->
    Expval μ f <= r.
  Proof.
    intros Hleq Hex Htot.
    replace r with (Expval μ (λ a, r)).
    - apply SeriesC_le; auto.
      + intro a. specialize (Hleq a); real_solver.
      + apply ex_seriesC_scal_r; auto.
    - rewrite /Expval SeriesC_scal_r; nra.
  Qed.

  Lemma markov_ineq μ f r :
    (forall a, 0 <= f a) ->
    ( 0 <= r ) ->
    ex_expval μ f ->
    r * Expval μ (λ a, if bool_decide (r <= f a) then 1 else 0) <= Expval μ f.
  Proof.
    intros Hpos Hr Hex.
    rewrite /Expval.
    rewrite -SeriesC_scal_l.
    assert (∀ x,
      (r * (μ x * (if bool_decide (r <= f x) then 1 else 0))) =
      (μ x * (if bool_decide (r <= f x) then r else 0))) as Haux.
    { real_solver. }
    setoid_rewrite Haux.
    apply SeriesC_le; auto.
    intro a; split; real_solver.
  Qed.

End exp_val_prop.


(** * Monadic map *)
Definition dmap `{Countable A, Countable B} (f : A → B) (μ : distr A) : distr B :=
    a ← μ; dret (f a).

Section dmap.
  Context `{Countable A}.

  Lemma dmap_id (μ : distr A) :
    dmap (λ x, x) μ = μ.
  Proof. rewrite /dmap dret_id_right //. Qed.

  Context `{Countable B}.
  
  Lemma dmap_unfold_pmf (f: A -> B) μ (b:B):
    dmap f μ b = SeriesC (λ a : A, μ a * (if bool_decide (b = f a) then 1 else 0)).
  Proof.
    done.
  Qed.

  Lemma dmap_fold (f:A -> B) μ:
    μ ≫= (λ a, dret (f a)) = dmap f μ.
  Proof. done. Qed.
  
  Context `{Countable X}.

  Lemma dmap_dret_pmf (f : A → B) (a : A) (b : B) :
    dmap f (dret a) b = dret (f a) b.
  Proof. rewrite /dmap dret_id_left_pmf //. Qed.

  Lemma dmap_dret (f : A → B) a :
    dmap f (dret a) = dret (f a) .
  Proof. apply distr_ext, dmap_dret_pmf. Qed.

  Lemma dmap_dbind_pmf (f : B → X) (g : A → distr B) (μ : distr A) (x : X) :
    dmap f (dbind g μ) x = dbind (λ a, dmap f (g a)) μ x.
  Proof. rewrite /dmap dbind_assoc_pmf //. Qed.

  Lemma dmap_dbind (f : B → X) (g : A → distr B) (μ : distr A) :
    dmap f (dbind g μ) = dbind (λ a, dmap f (g a)) μ.
  Proof. apply distr_ext, dmap_dbind_pmf. Qed.

  Lemma dmap_comp `{Countable D} (f : A → B) (g : B → D) (μ : distr A) :
    dmap g (dmap f μ) = dmap (g ∘ f) μ.
  Proof.
    rewrite /dmap.
    rewrite -dbind_assoc.
    apply dbind_eq; [|done].
    intros ??. rewrite dret_id_left //.
  Qed.

  Lemma dmap_eq (f g : A → B) (μ1 μ2 : distr A) :
    (∀ a, μ1 a > 0 → f a = g a) →
    (∀ a, μ1 a = μ2 a) →
    dmap f μ1 = dmap g μ2.
  Proof.
    intros Hfg Hμ.
    rewrite /dmap. apply dbind_eq; [|done].
    intros. rewrite Hfg //.
  Qed.

  Lemma dmap_eq_pmf (f g : A → B) (μ1 μ2 : distr A) x:
    (∀ a, μ1 a > 0 → f a = g a) →
    (∀ a, μ1 a = μ2 a) →
    dmap f μ1 x= dmap g μ2 x.
  Proof.
    intros Hfg Hμ.
    rewrite /dmap!dbind_unfold_pmf.
    apply SeriesC_ext.
    intros n.
    rewrite -Hμ.
    destruct (pmf_pos μ1 n) as [|<-].
    - by rewrite Hfg.
    - lra.
  Qed.

  Lemma dmap_mass (μ : distr A) (f : A → B):
    SeriesC (dmap f μ) = SeriesC μ.
  Proof.
    rewrite /dmap {1}/pmf /= /dbind_pmf.
    rewrite (distr_double_swap (λ a, dret (f a)) μ).
    apply SeriesC_ext=> a.
    rewrite {2}/pmf /= /dret_pmf.
    rewrite SeriesC_scal_l.
    rewrite SeriesC_singleton.
    lra.
  Qed.

  Lemma dmap_pos (μ : distr A) (f : A → B) (b : B) :
    dmap f μ b > 0 ↔ ∃ a, b = f a ∧ μ a > 0.
  Proof.
    split.
    - intros [a [Hr%dret_pos ?]]%dbind_pos; eauto.
    - intros [a [-> Ha]]. apply dbind_pos.
      exists a. rewrite dret_1_1 //. real_solver.
  Qed.

  Lemma dmap_elem_eq (μ : distr A) (a : A) (b : B) (f : A → B) `{Inj A B (=) (=) f} :
    b = f a → dmap f μ b = μ a.
  Proof. intros ->. rewrite dbind_dret_pmf_map //. Qed.

  Lemma dmap_elem_ne (μ : distr A) (b : B) (f : A → B) `{Inj A B (=) (=) f} :
    ¬ (∃ a, μ a > 0 ∧ f a = b) → dmap f μ b = 0.
  Proof. intros. rewrite /dmap dbind_dret_pmf_map_ne //. Qed.

  Lemma dmap_rearrange `{Countable A} (μ1 μ2 : distr A) (f : A → A) `{Inj A A (=) (=) f} :
    (∀ a, μ1 a > 0 → ∃ a', f a' = a) →
    (∀ a, μ1 (f a) = μ2 a) →
    μ1 = dmap f μ2.
  Proof.
    intros Hcov Hμ.
    eapply distr_ext=> a. rewrite /dmap {2}/pmf /= /dbind_pmf.
    destruct (ExcludedMiddle (∃ a', f a' = a)) as [[a' <-]|].
    - rewrite (SeriesC_ext _ (λ a, if bool_decide (a = a') then μ2 a' else 0)).
      { rewrite SeriesC_singleton //. }
      intros a. case_bool_decide; subst.
      + rewrite dret_1_1 //; lra.
      + rewrite dret_0 //; [lra|]. intros [=]; simplify_eq.
    - destruct (decide (μ1 a > 0)) as [Hz|Hz]; [by specialize (Hcov a Hz)|].
      rewrite SeriesC_0 //.
      { pose proof (pmf_pos μ1 a). lra. }
      intros a'. rewrite dret_0; [lra|].
      intros [=]. eauto.
  Qed.

  Lemma Expval_dmap (μ : distr A) (f : A → B) (g : B → R) :
    (∀ b, 0 <= g b) →
    ex_expval μ (g ∘ f) →
    Expval (dmap f μ) g = Expval μ (g ∘ f).
  Proof.
    intros Hg Hex.
    rewrite Expval_dbind; [|done|].
    - apply SeriesC_ext => a.
      rewrite Expval_dret //.
    - apply ex_expval_dbind; [done| |].
      + eapply ex_seriesC_ext; [|done].
        intros ?. rewrite Expval_dret //.
      + intros a. apply ex_expval_dret.
  Qed.
  
End dmap.



(** * Monadic strength  *)
Definition strength_l `{Countable A, Countable B} (a : A) (μ : distr B) : distr (A * B) :=
  dmap (λ b, (a, b)) μ.

Definition strength_r `{Countable A, Countable B} (μ : distr A) (b : B) : distr (A * B) :=
  dmap (λ a, (a, b)) μ.

Lemma dbind_strength_l `{Countable A, Countable B, Countable D} (f : A*B → distr D) (a : A) (μ : distr B) :
  (strength_l a μ) ≫= f = μ ≫= (λ b, f (a, b)).
Proof.
  rewrite /strength_l /dmap.
  rewrite -dbind_assoc.
  by setoid_rewrite (dret_id_left _ (a, _)).
Qed.

Lemma dbind_strength_r `{Countable A, Countable B, Countable D} (f : A * B → distr D)
  (μ : distr A) (b : B) :
  (strength_r μ b) ≫= f = μ ≫= (λ a, f (a, b)).
Proof.
  rewrite /strength_r /dmap.
  rewrite -dbind_assoc.
  by setoid_rewrite (dret_id_left _ (_, b)) .
Qed.

Lemma strength_l_dbind `{Countable A, Countable B, Countable D} (f : B → distr D) (a : A) (μ : distr B) :
  strength_l a (dbind f μ) = μ ≫= (λ b, strength_l a (f b)).
Proof. rewrite /strength_l /dmap -dbind_assoc //. Qed.

Lemma strength_r_dbind `{Countable A, Countable B, Countable D} (f : A → distr D) (μ : distr A) (b : B) :
  strength_r (dbind f μ) b = μ ≫= (λ a, strength_r (f a) b).
Proof. rewrite /strength_r /dmap -dbind_assoc //. Qed.

Lemma strength_comm `{Countable A, Countable B} (f : A → distr A) (g : B → distr B) (a : A) (b : B) :
  strength_l a (g b) ≫= (λ '(a',b'), strength_r (f a') b') =
  strength_r (f a) b ≫= (λ '(a',b'), strength_l a' (g b')).
Proof.
  rewrite dbind_strength_l.
  rewrite dbind_strength_r.
  rewrite /strength_l /strength_r /dmap.
  apply distr_ext.
  intros (a' & b').
  rewrite /pmf/=/dbind_pmf/=.
  rewrite {2 4}/pmf/=/dbind_pmf/=.
  setoid_rewrite <- SeriesC_scal_l.
  rewrite (fubini_pos_seriesC (λ '(x, a0), g b a0 * (f a x * dret (x, a0) (a', b')))).
  - apply SeriesC_ext => a''.
    apply SeriesC_ext => b''.
    rewrite /pmf /=; lra.
  - real_solver.
  - intros. apply (ex_seriesC_le _ (g b)); [|done]. real_solver.
  - eapply (ex_seriesC_le _ (λ a0 : A, SeriesC (λ b0 : B, g b b0 * (f a a0)))).
    + intros. split.
      * apply SeriesC_ge_0; [real_solver|].
        apply (ex_seriesC_le _ (g b)); [|done].
        real_solver.
      * apply SeriesC_le; [real_solver|].
        by apply ex_seriesC_scal_r.
    + setoid_rewrite SeriesC_scal_r.
      apply (ex_seriesC_le _ (f a)); [|done].
      real_solver.
Qed.

(** * Monadic fold left  *)
Definition foldlM {A B} `{Countable B} (f : B → A → distr B) (b : B) (xs : list A) : distr B :=
  foldr (λ a m b, f b a ≫= m) dret xs b.

Section foldlM.
  Context {A : Type} `{Countable B}.

  Lemma foldlM_nil (f : B → A → distr B) (b : B) :
    foldlM f b [] = dret b.
  Proof. done. Qed.

  Lemma foldlM_cons (f : B → A → distr B) (b : B) (x : A) (xs : list A) :
    foldlM f b (x :: xs) = f b x ≫= (λ b', foldlM f b' xs).
  Proof. done. Qed.

End foldlM.

(** * Monadic itereration  *)
Fixpoint iterM {A} `{Countable A} (n : nat) (f : A → distr A) (a : A) : distr A :=
  match n with O => dret a | S n => f a ≫= iterM n f end.

Section iterM.
  Context `{Countable A}.

  Lemma iterM_O (f : A → distr A) (a : A) :
    iterM 0 f a = dret a.
  Proof. done. Qed.

  Lemma iterM_Sn (f : A → distr A) (a : A) (n : nat) :
    iterM (S n) f a = f a ≫= iterM n f.
  Proof. done. Qed.

  Lemma iterM_plus (f : A → distr A) (a : A) (n m : nat) :
    iterM (n + m) f a = iterM n f a ≫= iterM m f.
  Proof.
    revert a; induction n as [|n IH]; intros a.
    - rewrite plus_O_n iterM_O dret_id_left //.
    - rewrite /=.
      rewrite -dbind_assoc -/iterM.
      f_equal. extensionality a'.
      rewrite IH //.
  Qed.

  Lemma iterM_mono (f g : A → distr A) n a a':
    (∀ a a', f a a'<= g a a') → iterM n f a a' <= iterM n g a a'.
  Proof.
    revert a a'.
    induction n; intros a a' Ha; simpl.
    - lra.
    - rewrite /dbind/pmf/dbind_pmf. apply SeriesC_le; last first.
      { apply pmf_ex_seriesC_mult_fn. exists 1. naive_solver. }
      intros. real_solver.
  Qed.

End iterM.

(** * Coins  *)
Program Definition fair_coin : distr bool := MkDistr (λ _, 0.5) _ _ _.
Next Obligation. intros []; lra. Qed.
Next Obligation. apply ex_seriesC_finite. Qed.
Next Obligation. rewrite SeriesC_finite_mass /=. lra. Qed.

Lemma fair_coin_mass:
  SeriesC fair_coin = 1.
Proof.
  rewrite /pmf /= /fair_coin /=.
  rewrite SeriesC_finite_mass /=. lra.
Qed.

Lemma fair_coin_pmf b :
  fair_coin b = 0.5.
Proof. done. Qed.

Lemma fair_coin_dbind_mass `{Countable A} (f : bool → distr A) :
  SeriesC (fair_coin ≫= f) = 1 / 2 * SeriesC (f true) + 1 / 2 * SeriesC (f false).
Proof.
  rewrite {1}/pmf /= /dbind_pmf.
  rewrite (fubini_pos_seriesC (λ '(a, b), fair_coin a * f a b)).
  - rewrite SeriesC_bool.
    rewrite 2!SeriesC_scal_l.
    rewrite {1 3}/pmf /=. lra.
  - real_solver.
  - intros b. by apply ex_seriesC_scal_l.
  - eapply ex_seriesC_finite.
Qed.

Lemma ex_expval_fair_coin_dbind `{Countable A} (f : bool → distr A) h :
  (∀ b, ex_expval (f b) h) →
  ex_expval (fair_coin ≫= f) h.
Proof.
  intros Hf.
  rewrite /ex_expval.
  rewrite /pmf /= /dbind_pmf /=.
  setoid_rewrite SeriesC_bool.
  rewrite !fair_coin_pmf.
  setoid_rewrite Rmult_plus_distr_r.
  eapply ex_seriesC_plus.
  - setoid_rewrite Rmult_assoc.
    eapply ex_seriesC_scal_l.
    eapply Hf.
  - setoid_rewrite Rmult_assoc.
    eapply ex_seriesC_scal_l.
    eapply Hf.
Qed.

Lemma Expval_fair_coin f :
  Expval fair_coin f = 0.5 * f (true) + 0.5 * f (false).
Proof.
  rewrite /Expval/pmf/= SeriesC_scal_l SeriesC_bool; lra.
Qed.

(* We may need this generality later, but I think it is better to define the fair coin explicitly *)
Definition biased_coin_pmf r : bool → R :=
  λ b, if b then r else 1-r.
Program Definition biased_coin r (P : 0 <= r <= 1) : distr bool := MkDistr (biased_coin_pmf r) _ _ _.
Next Obligation. intros r P b. rewrite /biased_coin_pmf. destruct b; lra. Qed.
Next Obligation.
  intros r P.
  apply (ex_seriesC_ext  (λ b, (if bool_decide (b = true) then r else 0) + if bool_decide (b = false) then 1-r else 0)); auto.
  { intro b; destruct b; rewrite /biased_coin_pmf /=; lra. }
  eapply ex_seriesC_plus; eapply ex_seriesC_singleton. Qed.
Next Obligation.
  intros r P.
  rewrite (SeriesC_ext _ (λ b, (if bool_decide (b = true) then r else 0) + if bool_decide (b = false) then 1-r else 0)).
  2 : { intro b; destruct b; rewrite /biased_coin_pmf /= ; lra. }
  erewrite SeriesC_plus; [|eapply ex_seriesC_singleton.. ].
  rewrite 2!SeriesC_singleton. lra. Qed.

(* Convex combinations *)
Definition fair_conv_comb `{Countable A} (μ1 μ2 : distr A) : distr A :=
  dbind (λ b, if b then μ1 else μ2) fair_coin.

Section conv_prop.
  Context `{Countable A, Countable B}.

  Lemma fair_conv_comb_pmf `{Countable D} (μ1 μ2 : distr D) (a : D) :
    fair_conv_comb μ1 μ2 a = 0.5 * (μ1 a) + 0.5 * (μ2 a).
  Proof.
    rewrite {1}/pmf /= /dbind_pmf.
    rewrite (SeriesC_ext _ (λ b, (if bool_decide (b = true) then 0.5 * μ1 a else 0) +
                                  if bool_decide (b = false) then 0.5 * μ2 a else 0)).
    2: { intros []; rewrite /= /pmf /=; lra. }
    erewrite SeriesC_plus; [|eapply ex_seriesC_singleton.. ].
    rewrite 2!SeriesC_singleton /=. lra.
  Qed.

  Definition dbind_fair_conv_comb (f1 f2 : A → distr B) (μ : distr A) :
    μ ≫= (λ a, fair_conv_comb (f1 a) (f2 a)) = fair_conv_comb (μ ≫= f1) (μ ≫= f2).
  Proof.
    apply distr_ext.
    intro b.
    rewrite {1}/pmf /= /dbind_pmf.
    rewrite (fair_conv_comb_pmf (μ ≫= f1) (μ ≫= f2) b).
    assert (∀ a, μ a * fair_conv_comb (f1 a) (f2 a) b = 0.5 * (μ a * (f1 a) b + μ a * (f2 a) b)) as Heq.
    { intro a; rewrite fair_conv_comb_pmf; lra. }
    setoid_rewrite Heq.
    rewrite SeriesC_scal_l.
    rewrite <- Rmult_plus_distr_l.
    rewrite {5 6}/pmf /= /dbind_pmf.
    rewrite SeriesC_plus //.
    - apply (ex_seriesC_le _ μ); [| apply pmf_ex_seriesC].
      real_solver.
    - apply (ex_seriesC_le _ μ); [| apply pmf_ex_seriesC].
      real_solver.
  Qed.

  Lemma dbind_dret_coin_zero (f : bool→ A) (a : A) :
    (∀ b, f b ≠ a) →
    (fair_coin ≫= (λ b, dret (f b))) a = 0.
  Proof.
    intro.
    rewrite /pmf/=/dbind_pmf.
    apply SeriesC_0; intro.
    rewrite /pmf/=/dret_pmf.
    rewrite bool_decide_eq_false_2 //. lra.
  Qed.

  Lemma dbind_dret_coin_nonzero (f : bool → A) (a : A) `{Inj bool A (=) (=) f} :
    (∃ b, f b = a) →
    (fair_coin ≫= (λ b, dret (f b))) a = 0.5 .
  Proof.
    intros Hex.
    rewrite /pmf/=/dbind_pmf.
    rewrite (SeriesC_ext _ (λ b, if bool_decide (f b = a) then 0.5 else 0)); last first.
    - intro. rewrite /pmf/=/dret_pmf. real_solver.
    - by apply SeriesC_singleton_inj.
  Qed.

  Lemma fair_conv_comb_mass `{Countable A} (μ1 μ2 : distr A) :
    SeriesC (fair_conv_comb μ1 μ2) = 0.5 * (SeriesC μ1 + SeriesC μ2).
  Proof.
    rewrite -SeriesC_plus // -SeriesC_scal_l.
    apply SeriesC_ext => a.
    rewrite fair_conv_comb_pmf.
    lra.
  Qed.

End conv_prop.

(** * The zero distribution  *)
Program Definition dzero `{Countable A} : distr A := MkDistr (λ _, 0) _ _ _.
Next Obligation. done. Qed.
Next Obligation. intros. eapply ex_seriesC_0. Qed.
Next Obligation. intros. rewrite SeriesC_0 //. lra. Qed.

Section dzero.
  Context `{Countable A}.
  
  Global Instance distr_inhabited : Inhabited (distr A) := populate (dzero).
  
  Lemma dzero_ext (μ : distr A) :
    (∀ a, μ a = 0) → μ = dzero.
  Proof. intros ?; by apply distr_ext. Qed.

  Lemma dzero_0 `{Countable A} (a : A) :
    dzero a = 0.
  Proof. done. Qed.

  Lemma dzero_supp_empty (a : A) :
    ¬ (dzero a > 0).
  Proof. rewrite /pmf /=. lra. Qed.

  Lemma dzero_mass :
    SeriesC (@dzero A _ _) = 0.
  Proof. rewrite SeriesC_0 //. Qed.

  Lemma SeriesC_zero_dzero (μ : distr A) :
    SeriesC μ = 0 → μ = dzero.
  Proof.
    intros ?.
    apply dzero_ext.
    apply SeriesC_const0; [done|].
    by apply SeriesC_correct'.
  Qed.

  Lemma not_dzero_gt_0 (μ : distr A) :
    μ ≠ dzero → SeriesC μ > 0.
  Proof.
    intros Hz.
    destruct (Req_dec (SeriesC μ) 0).
    - exfalso. by apply Hz, SeriesC_zero_dzero.
    - pose proof (pmf_SeriesC_ge_0 μ). lra.
  Qed.

  Lemma dret_not_dzero (a : A) :
    dret a ≠ dzero.
  Proof.
    intros Heq.
    assert (Ha: dret a a = dzero a) by rewrite Heq //.
    rewrite dret_1_1 // /pmf /dzero in Ha.
    lra.
  Qed.

  Lemma dbind_dzero_pmf `{Countable B} (f : A → distr B) (b : B) :
    (a ← dzero; f a) b = 0.
  Proof.
    rewrite /pmf /= /dbind_pmf {1}/pmf /= /dzero.
    apply SeriesC_0=>?. lra.
  Qed.

  Lemma dzero_dbind_pmf `{Countable B} (μ : distr A) (b : B):
    (a ← μ; dzero) b = dzero b.
  Proof.
    rewrite /pmf /= /dbind_pmf {2}/pmf /=.
    apply SeriesC_0=>?. lra.
  Qed.

  Lemma dzero_dbind `{Countable A'} (μ : distr A) :
    (a ← μ; dzero) = dzero (A := A').
  Proof. apply distr_ext, dzero_dbind_pmf. Qed.

  Lemma dbind_dzero `{Countable B} (f : A → distr B) :
    (a ← dzero; f a) = dzero.
  Proof. apply distr_ext, dbind_dzero_pmf. Qed.

  Lemma dmap_dzero `{Countable B} (f : A → B):
    dmap f dzero = dzero.
  Proof.
    apply dbind_dzero.
  Qed.

  Lemma Expval_dzero `{Countable A} (h : A → R) :
    Expval dzero h = 0.
  Proof. eapply SeriesC_0 => a. rewrite dzero_0. lra. Qed.

End dzero.

Lemma dmap_dzero_inv `{Countable A, Countable B} (f : A → B) (μ : distr A) :
  dmap f μ = dzero → μ = dzero.
Proof.
  intros Hf.
  apply SeriesC_zero_dzero.
  rewrite -(dmap_mass _ f).
  rewrite Hf dzero_mass //.
Qed.

(** * Diagonal *)
Program Definition ddiag `{Countable A} (μ : distr A) : distr (A * A) :=
  MkDistr (λ '(a, b), if bool_decide (a = b) then μ a else 0) _ _ _.
Next Obligation. intros ???? [a b]=>/=. case_bool_decide; auto; lra. Qed.
Next Obligation.
  intros A?? μ =>/=.
  apply ex_seriesC_prod.
  - real_solver.
  - intro a. apply ex_seriesC_singleton'.
  - eapply ex_seriesC_ext; [|done].
    intro. rewrite SeriesC_singleton' //.
Qed.
Next Obligation.
  intros A?? μ =>/=.
  rewrite fubini_pos_seriesC_prod_lr.
  - by setoid_rewrite SeriesC_singleton'.
  - real_solver.
  - apply ex_seriesC_prod.
    + real_solver.
    + intro a. apply ex_seriesC_singleton'.
    + by setoid_rewrite SeriesC_singleton'.
Qed.

Lemma ddiag_pmf `{Countable A} (μ : distr A) (p : A * A) :
  ddiag μ p = if bool_decide (p.1 = p.2) then μ p.1 else 0.
Proof.
  destruct p as (a1 & a2). by destruct (bool_decide (a1 = a2)).
Qed.

(** * Products  *)
Definition dprod `{Countable A, Countable B} (μ1 : distr A) (μ2 : distr B) : distr (A * B) :=
  a ← μ1;
  b ← μ2;
  dret (a, b).

Lemma dprod_pmf `{Countable A, Countable B} (μ1 : distr A) (μ2 : distr B) a b :
  dprod μ1 μ2 (a, b) = μ1 a * μ2 b.
Proof.
  rewrite {1}/pmf /= /dbind_pmf.
  rewrite {2}/pmf /= /dbind_pmf.
  erewrite SeriesC_ext; last first.
  { intros a'.
    erewrite (SeriesC_ext _ (λ b', if bool_decide (b' = b) then μ2 b * dret (a', b) (a, b) else 0)).
    - rewrite SeriesC_singleton //.
    - intros b'. case_bool_decide; simplify_eq=>//=.
      rewrite dret_0; [lra|]. by intros [=]. }
  erewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then μ1 a * μ2 b else 0)).
  - rewrite SeriesC_singleton //.
  - intros a'. case_bool_decide; simplify_eq=>/=.
    + rewrite dret_1_1 //. lra.
    + rewrite dret_0; [lra|]. by intros [=].
Qed.

Section dprod.
  Context `{Countable A, Countable B}.
  Variable (μ1 : distr A) (μ2 : distr B).

  Lemma dprod_pos (a : A) (b : B) :
    dprod μ1 μ2 (a, b) > 0 ↔ μ1 a > 0 ∧ μ2 b > 0.
  Proof.
    rewrite dprod_pmf /=.
    split; [|real_solver].
    destruct (decide (μ1 a > 0)) as [| ->%pmf_eq_0_not_gt_0]; [|lra].
    destruct (decide (μ2 b > 0)) as [| ->%pmf_eq_0_not_gt_0]; [|lra].
    done.
  Qed.

  Lemma dprod_mass :
    SeriesC (dprod μ1 μ2) = SeriesC μ1 * SeriesC μ2.
  Proof.
    rewrite {1}(SeriesC_ext _ (λ '(a, b), μ1 a * μ2 b)); last first.
    { intros [a' b']. rewrite dprod_pmf //. }
    rewrite distr_double_lr.
    erewrite SeriesC_ext; [|intro; rewrite SeriesC_scal_l //].
    rewrite SeriesC_scal_r //.
  Qed.

End dprod.

(** * swap  *)
Definition dswap `{Countable A, Countable B} (μ : distr (A * B)) : distr (B * A) :=
  dmap (λ '(a, b), (b, a)) μ.

Lemma dswap_pos `{Countable A, Countable B} (μ : distr (A * B)) a b :
  (dswap μ (b, a) > 0 → μ (a, b) > 0)%R.
Proof. by intros ([] & [= <- <-] & ?)%dmap_pos. Qed.

(** * Marginals  *)
Definition lmarg `{Countable A, Countable B} (μ : distr (A * B)) : distr A :=
  dmap fst μ.

Definition rmarg `{Countable A, Countable B} (μ : distr (A * B)) : distr B :=
  dmap snd μ.

Section marginals.
  Context `{Countable A, Countable B}.

  Lemma lmarg_pmf (μ : distr (A * B)) (a : A) :
    lmarg μ a = SeriesC (λ b, μ (a, b)).
  Proof.
    rewrite {1}/pmf /= /dbind_pmf.
    rewrite fubini_pos_seriesC_prod_rl.
    - apply SeriesC_ext; intro b.
      rewrite {2}/pmf /= /dret_pmf /=.
      erewrite SeriesC_ext; [apply (SeriesC_singleton' a)|].
      real_solver.
    - real_solver.
    - apply (ex_seriesC_le _ μ); [|done].
      real_solver.
  Qed.

  Lemma rmarg_pmf (μ : distr (A * B)) (b : B):
    rmarg μ b = SeriesC (λ a, μ (a, b)).
  Proof.
    rewrite {1}/pmf /= /dbind_pmf.
    rewrite fubini_pos_seriesC_prod_lr.
    - apply SeriesC_ext=> a.
      rewrite {2}/pmf /= /dret_pmf /=.
      erewrite SeriesC_ext; [apply (SeriesC_singleton' b)|].
      real_solver.
    - real_solver.
    - apply (ex_seriesC_le _ μ); [|done]. real_solver.
  Qed.

  Lemma ex_distr_lmarg (μ : distr (A * B)) (a : A) :
    ex_seriesC (λ b, μ (a, b)).
  Proof. by eapply ex_seriesC_lmarg. Qed.

  Lemma ex_distr_rmarg (μ : distr (A * B)) (b : B) :
    ex_seriesC (λ a, μ (a, b)).
  Proof. by eapply ex_seriesC_rmarg. Qed.

  Lemma lmarg_dprod_pmf (μ1 : distr A) (μ2 : distr B) (a : A) :
    lmarg (dprod μ1 μ2) a = μ1 a * SeriesC μ2.
  Proof.
    rewrite lmarg_pmf.
    erewrite SeriesC_ext; [|intros ?; rewrite dprod_pmf //].
    rewrite SeriesC_scal_l //.
  Qed.

  Lemma lmarg_dprod (μ1 : distr A) (μ2 : distr B) :
    SeriesC μ2 = 1 →
    lmarg (dprod μ1 μ2) = μ1.
  Proof.
    intro Hμ2. eapply distr_ext=> a.
    rewrite lmarg_dprod_pmf Hμ2. lra.
  Qed.

  Lemma lmarg_dswap (μ : distr (A * B)) :
    lmarg (dswap μ) = rmarg μ.
  Proof.
    rewrite /lmarg /dswap dmap_comp.
    assert ((fst ∘ (λ '(a, b), (b : B, a : A))) = snd) as ->.
    { extensionality b. by destruct b. }
    done.
  Qed.

  Lemma rmarg_dswap (μ : distr (A * B)) :
    rmarg (dswap μ) = lmarg μ.
  Proof.
    rewrite /rmarg /dswap dmap_comp.
    assert ((snd ∘ (λ '(a, b), (b : B, a : A))) = fst) as ->.
    { extensionality b. by destruct b. }
    done.
  Qed.

  Lemma rmarg_dprod_pmf (μ1 : distr A) (μ2 : distr B) (b : B) :
    rmarg (dprod μ1 μ2) b = μ2 b * SeriesC μ1.
  Proof.
    rewrite rmarg_pmf.
    erewrite SeriesC_ext; [|intros ?; rewrite dprod_pmf //].
    rewrite SeriesC_scal_r; lra.
  Qed.

  Lemma rmarg_dprod (μ1 : distr A) (μ2 : distr B) :
    SeriesC μ1 = 1 →
    rmarg (dprod μ1 μ2) = μ2.
  Proof.
    intro Hμ1. eapply distr_ext=> a.
    rewrite rmarg_dprod_pmf Hμ1.  lra.
  Qed.

End marginals.

Lemma ddiag_lmarg `{Countable A} (μ : distr A):
  lmarg (ddiag μ) = μ.
Proof.
  apply distr_ext=> a.
  rewrite lmarg_pmf.
  setoid_rewrite ddiag_pmf.
  simpl.
  rewrite SeriesC_singleton' //.
Qed.

Lemma ddiag_rmarg `{Countable A} (μ : distr A):
  rmarg (ddiag μ) = μ.
Proof.
  apply distr_ext=> a.
  rewrite rmarg_pmf.
  setoid_rewrite ddiag_pmf.
  simpl.
  erewrite SeriesC_ext; [apply SeriesC_singleton|].
  real_solver.
Qed.

Lemma lmarg_dzero `{Countable A, Countable B} :
  lmarg (dzero (A := (A * B))) = dzero.
Proof. rewrite /lmarg dmap_dzero //. Qed.

Lemma rmarg_dzero `{Countable A, Countable B} :
  rmarg (dzero (A := (A * B))) = dzero.
Proof. rewrite /rmarg dmap_dzero //. Qed.

(** * Pointwise order  *)
Definition distr_le `{Countable A} (μ1 μ2 : distr A) : Prop :=
  ∀ a, (μ1 a <= μ2 a)%R.

Section order.
  Context `{Countable A}.

  Lemma distr_le_dzero (μ : distr A) :
    distr_le dzero μ.
  Proof.
    rewrite /distr_le.
    intro a; apply pmf_pos.
  Qed.

  Lemma distr_le_refl (μ : distr A) :
    distr_le μ μ.
  Proof.
    rewrite /distr_le.
    intro a; lra.
  Qed.

  Lemma distr_le_trans (μ1 μ2 μ3 : distr A) :
    distr_le μ1 μ2 → distr_le μ2 μ3 → distr_le μ1 μ3.
  Proof.
    rewrite /distr_le.
    intros H1 H2 a.
    by transitivity (μ2 a).
  Qed.

  Lemma distr_le_antisym (μ1 μ2 : distr A):
    distr_le μ1 μ2 → distr_le μ2 μ1 → μ1 = μ2.
  Proof.
    rewrite /distr_le.
    intros H1 H2.
    apply distr_ext=> a.
    by apply Rle_antisym.
  Qed.

  Lemma distr_le_dbind `{Countable B} (μ1 μ2 : distr A) (f1 f2 : A → distr B) :
    distr_le μ1 μ2 →
    (∀ a, distr_le (f1 a) (f2 a)) →
    distr_le (dbind f1 μ1) (dbind f2 μ2).
  Proof.
    intros Hle Hf.
    pose proof (pmf_ex_seriesC (μ2 ≫= f2)) as Hex.
    rewrite /distr_le /pmf /= /dbind_pmf /=.
    intro b.
    apply SeriesC_le; last first.
    - eapply pmf_ex_seriesC_mult_fn. eauto.
    - rewrite /distr_le in Hle, Hf. real_solver.
  Qed.

  Lemma distr_le_dmap_1 `{Countable B} (μ1 μ2 : distr A) (f : A → B) :
    distr_le μ1 μ2 → distr_le (dmap f μ1) (dmap f μ2).
  Proof.
    intros Hμ. apply distr_le_dbind; [done|].
    rewrite /distr_le //.
  Qed.

  Lemma distr_le_dmap_2 `{Countable B} (μ1 μ2 : distr A) (f : A → B) `{Inj A B (=) (=) f} :
    distr_le (dmap f μ1) (dmap f μ2) → distr_le μ1 μ2.
  Proof.
    intros Hm a.
    specialize (Hm (f a)).
    by erewrite 2!dmap_elem_eq in Hm.
  Qed.

End order.

(** * Scaled distribution  *)
Program Definition distr_scal `{Countable A} (r : R) (μ : distr A)
  (Hr : 0 <= r ∧ r * SeriesC μ <= 1) := MkDistr (λ a, r * μ a) _ _ _.
Next Obligation.
  intros ????? [] a. pose proof (pmf_pos μ a). real_solver.
Qed.
Next Obligation. intros. by apply ex_seriesC_scal_l. Qed.
Next Obligation. intros ????? []. rewrite SeriesC_scal_l //. Qed.

(** * Limit distribution  *)
Section convergence.
  Context `{Countable A}.

  Program Definition lim_distr (h : nat → distr A) (_ : ∀ n a, h n a <= h (S n) a) :=
    MkDistr (λ a, Sup_seq (λ n, h n a)) _ _ _.
  Next Obligation.
    intros h Hmon a.
    simpl.
    transitivity (h 0%nat a); [done|].
    apply rbar_le_finite.
    - apply (Rbar_le_sandwich 0 1).
      + by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      + by apply upper_bound_ge_sup=>/=.
    - apply (sup_is_upper_bound (λ n : nat, h n a) 0%nat).
  Qed.
  Next Obligation.
    intros h Hmon.
    assert (is_finite (Sup_seq (λ x : nat, SeriesC (h x)))) as Haux.
    { apply (Rbar_le_sandwich 0 1).
      - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      - by apply upper_bound_ge_sup=>/=. }
    apply (MCT_ex_seriesC h (λ n, SeriesC (h n))
             (Sup_seq (λ x : nat, SeriesC (h x)))); [done|done|eauto| |].
    - intros n. by apply SeriesC_correct.
    - rewrite rbar_finite_real_eq //. apply Sup_seq_correct.
  Qed.
  Next Obligation.
    intros h Hmon.
    assert (is_finite (Sup_seq (λ x : nat, SeriesC (h x)))) as Haux.
    { apply (Rbar_le_sandwich 0 1).
      - by apply (Sup_seq_minor_le _ _ 0%nat)=>/=.
      - by apply upper_bound_ge_sup=>/=. }
    rewrite (MCT_seriesC h (λ n, SeriesC (h n)) (Sup_seq (λ x : nat, SeriesC (h x))));
      [|done|eauto|eauto|eauto|].
    - apply finite_rbar_le; [done|].
      by apply (upper_bound_ge_sup (λ x : nat, SeriesC (h x)) 1)=>/=.
    - intros. by eapply SeriesC_correct.
    - rewrite rbar_finite_real_eq //. apply Sup_seq_correct.
  Qed.

  Lemma lim_distr_pmf (h : nat → distr A) Hmon (a : A) :
    lim_distr h Hmon a = Sup_seq (λ n, h n a).
  Proof. done. Qed.

  (* TODO: extract some general lemmas from [exec.v] *)

 End convergence.

(** * Uniform sampling *)
Section uniform.

  Program Definition dunif (N : nat) : distr (fin N) := MkDistr (λ _, /N) _ _ _.
  Next Obligation.
    intros => /=.
    destruct N; [rewrite Rinv_0 //|].
    left.
    replace (INR (S N)) with (INR (N + 1)); [|f_equal; lia].
    rewrite plus_INR.
    apply RinvN_pos.
  Qed.
  Next Obligation. intros. eapply ex_seriesC_finite. Qed.
  Next Obligation.
    intro N.
    destruct N.
    { rewrite SeriesC_0 ?Rinv_0 //. lra. }
    right.
    rewrite SeriesC_finite_mass.
    rewrite fin_card Rinv_r //.
    apply not_0_INR. lia.
  Qed.

  Lemma dunif_pmf N (n : fin N) :
    dunif N n = / N.
  Proof. done. Qed.

  Lemma dunif_mass (N : nat) :
    (N ≠ 0)%nat →
    SeriesC (dunif N) = 1.
  Proof.
    intros HN.
    rewrite /pmf /= /dunif /=.
    rewrite SeriesC_finite_mass.
    rewrite fin_card Rinv_r //.
    by apply not_0_INR.
  Qed.

  Lemma dmap_unif_zero `{Countable A} (N : nat) (f : fin N → A) (a : A) :
    (∀ n, f n ≠ a) → dmap f (dunif N) a = 0.
  Proof.
    intro Hf.
    rewrite /pmf/=/dbind_pmf.
    apply SeriesC_0; intro x.
    rewrite /pmf/=/dret_pmf.
    rewrite bool_decide_eq_false_2; [lra|].
    intro; simplify_eq.
    by apply (Hf x).
  Qed.

  Lemma dmap_unif_nonzero `{Countable A} (N : nat) (n : fin N) (f : fin N → A) (a : A) `{Inj (fin N) A (=) (=) f} :
    f n = a →
    dmap f (dunif N) a = /N.
  Proof.
    intros Hf.
    rewrite /pmf/=/dbind_pmf.
    rewrite (SeriesC_ext _ (λ n, if bool_decide (f n = a) then /N else 0)); last first.
    - intros m. rewrite -Hf.
      case_bool_decide; simplify_eq.
      + rewrite dret_1_1 // dunif_pmf. lra.
      + rewrite dret_0 //. lra.
    - rewrite -Hf.
      rewrite SeriesC_singleton_inj //. eauto.
  Qed.

  Lemma dunif_fair_conv_comb :
    dunif 2 = fair_conv_comb (dret 1%fin) (dret 0%fin).
  Proof.
    apply distr_ext. intros n.
    rewrite dunif_pmf fair_conv_comb_pmf.
    inv_fin n.
    - rewrite dret_0 // dret_1_1 //=. lra.
    - intros m. inv_fin m.
      + rewrite dret_1_1 // dret_0 //=. lra.
      + intros i. inv_fin i.
  Qed.

  (* To avoid the case [N = 0] where [dunif 0 = dzero] it is convenient
     sometimes convenient to use [N + 1] *)
  Definition dunifP (N : nat) : distr (fin (S N)) := dunif (S N).

  Lemma dunifP_pos N n :
    dunifP N n > 0.
  Proof. rewrite dunif_pmf /=. apply RinvN_pos'. Qed.

  Lemma dunifP_mass N :
    SeriesC (dunifP N) = 1.
  Proof. apply dunif_mass. lia. Qed.

  Lemma dunifP_not_dzero N :
    dunifP N ≠ dzero.
  Proof.
    intros Hf.
    assert (Hunif : SeriesC (dunifP N) = 0).
    { rewrite Hf dzero_mass //. }
    rewrite dunifP_mass in Hunif.
    lra.
  Qed.

End uniform.

(** Uniform fin lists *)
Section uniform_fin_lists.
  Program Definition dunifv (N p: nat): distr (list (fin (S N))) :=
    MkDistr (λ x, if (bool_decide (length x = p)) then /(S N^p)%nat else 0) _ _ _.
  Next Obligation.
    intros. simpl.
    case_bool_decide; last done.
    rewrite -Rdiv_1_l. apply Rdiv_le_0_compat; first lra.
    replace 0 with (INR 0) by done.
    apply lt_INR.
    apply PeanoNat.Nat.lt_le_trans with (S N ^ 0)%nat; first by (simpl; lia).
    apply Nat.pow_le_mono_r; lia.
  Qed.
  Next Obligation.
    intros.
    eapply ex_seriesC_ext; last apply ex_seriesC_list.
    simpl. intros. erewrite bool_decide_ext; first done.
    by erewrite elem_of_enum_uniform_fin_list.
  Qed.
  Next Obligation.
    intros N p.
    erewrite SeriesC_ext. 
    - erewrite SeriesC_list_2; last apply NoDup_enum_uniform_fin_list.
      rewrite enum_uniform_fin_list_length.
      erewrite Rinv_l; first done.
      apply not_0_INR.
      apply Nat.pow_nonzero.
      lia.
    - intros. erewrite bool_decide_ext; first done.
      by erewrite elem_of_enum_uniform_fin_list.
  Qed.
  
  Lemma dunifv_pmf N p v:
    dunifv N p v= if (bool_decide (length v = p)) then / (S N^p)%nat else 0.
  Proof. done. Qed.

  Lemma dunifv_mass N p:
    SeriesC (dunifv N p) = 1.
  Proof.
    erewrite SeriesC_ext.
    - erewrite SeriesC_list_2; last apply NoDup_enum_uniform_fin_list.
      rewrite enum_uniform_fin_list_length.
      erewrite Rinv_l; first done.
      apply not_0_INR.
      apply Nat.pow_nonzero. lia.
    - intros.
      rewrite /dunifv_pmf.
      erewrite bool_decide_ext; first done.
      by erewrite elem_of_enum_uniform_fin_list.
  Qed. 

  Lemma dunifv_pos N p v:
    length v = p <-> 
    dunifv N p v > 0.
  Proof.
    split.
    - rewrite dunifv_pmf /=.
      intros. 
      rewrite bool_decide_eq_true_2; last done.
      apply Rinv_pos.
      apply Rlt_gt.
      apply lt_0_INR.
      apply PeanoNat.Nat.lt_le_trans with (S N ^ 0)%nat; first by (simpl; lia).
      apply Nat.pow_le_mono_r; lia.
    - rewrite /dunifv/pmf/=.
      case_bool_decide; last lra.
      done.
  Qed.
  
End uniform_fin_lists.

Section laplace.
  Definition laplace_f_nat (ε:posreal) (n:nat) := exp (- INR n * ε).
  Definition laplace_f (ε:posreal) (z:Z) := laplace_f_nat ε (Z.to_nat (Z.abs z)).
  
  Lemma laplace_f_nat_pos ε n: 0<=laplace_f_nat ε n.
  Proof.
    left. apply exp_pos.
  Qed.
  
  Lemma ex_seriesC_laplace_f_nat ε: ex_seriesC (λ n, laplace_f_nat ε n).
  Proof.
    rewrite /laplace_f_nat. eapply (ex_seriesC_ext (λ n, (exp (-ε)) ^ n)).
    - intros.
      rewrite exp_pow. f_equal. lra.
    - rewrite -ex_seriesC_nat. apply ex_series_geom.
      apply Rabs_def1.
      + rewrite exp_Ropp.
        rewrite -Rdiv_1_l. rewrite -Rdiv_lt_1; last apply exp_pos.
        replace 1 with (exp 0); last apply exp_0.
        apply exp_increasing. apply cond_pos. 
      + trans 0; [lra|apply exp_pos].
  Qed.
  
  Lemma ex_seriesC_laplace_f ε: ex_seriesC (λ z, laplace_f ε z).
  Proof.
    pose (h:=(λ '(n,z), if Z.to_nat (Z.abs z) =?  n then laplace_f_nat ε n else 0)).
    apply (ex_seriesC_ext (λ z, SeriesC (λ n, h (n,z)))).
    { rewrite /h.
      intros z.
      erewrite SeriesC_ext; first erewrite (SeriesC_singleton_dependent (Z.to_nat (Z.abs z)) (laplace_f_nat ε)); first done.
      simpl.
      intros n.
      case_match eqn:H.
      - apply Nat.eqb_eq in H. subst. by rewrite bool_decide_eq_true_2.
      - apply Nat.eqb_neq in H. by rewrite bool_decide_eq_false_2.
    }
    apply fubini_pos_seriesC_ex_double.
    - rewrite /h. intros. case_match; last done.
      rewrite /laplace_f_nat. left. apply exp_pos.
    - rewrite /h.
      intros n.
      destruct n.
      + eapply ex_seriesC_ext; last apply (ex_seriesC_singleton 0%Z).
        simpl.
        intros z.
        case_bool_decide; subst; simpl; first done.
        case_match eqn :H'; last done.
        apply Nat.eqb_eq in H'. lia.
      + apply (ex_seriesC_ext (λ b, if bool_decide (b∈ [Z.of_nat (S n); (- (Z.of_nat (S n)))%Z]) then laplace_f_nat ε (S n) else 0)); last apply ex_seriesC_list.
        intros. case_bool_decide as H.
        * set_unfold. destruct H as [| [|[]]]; subst; simpl.
          -- by rewrite -Zabs2Nat.abs_nat_spec Zabs2Nat.id/=Nat.eqb_refl.
          -- by rewrite Z.abs_opp -Zabs2Nat.abs_nat_spec Zabs2Nat.id/=Nat.eqb_refl.
        * case_match eqn:H'; last done.
          exfalso. apply H.
          apply Nat.eqb_eq in H'.
          set_unfold. lia.
    - rewrite /h.
      apply (ex_seriesC_ext (λ n, if bool_decide (n=0)%nat then laplace_f_nat ε 0 else 2 * laplace_f_nat ε n)).
      + intros.
        case_bool_decide as H1.
        * erewrite SeriesC_ext; first (erewrite (SeriesC_singleton 0%Z); first done).
          intros z. simpl. subst.
          case_bool_decide; subst; simpl; first done.
          case_match eqn :H'; last done.
          apply Nat.eqb_eq in H'. lia.
        * erewrite (SeriesC_ext _ (λ b, if bool_decide (b∈ [Z.of_nat (n); (- (Z.of_nat (n)))%Z]) then laplace_f_nat ε (n) else 0)).
          -- rewrite SeriesC_list/=.
             ++ lra. 
             ++ assert (Z.of_nat (n) ≠ -Z.of_nat (n))%Z by lia.
                repeat constructor; set_solver.
          -- intros. case_bool_decide as H.
             ++ set_unfold. destruct H as [| [|[]]]; subst; simpl.
                ** by rewrite -Zabs2Nat.abs_nat_spec Zabs2Nat.id/=Nat.eqb_refl.
                ** by rewrite Z.abs_opp -Zabs2Nat.abs_nat_spec Zabs2Nat.id/=Nat.eqb_refl.
             ++ case_match eqn:H'; last done.
                exfalso. apply H.
                apply Nat.eqb_eq in H'.
                set_unfold. lia.
      + apply (ex_seriesC_le _ (λ n, 2*laplace_f_nat ε n)).
        * intros n. pose proof laplace_f_nat_pos ε n. case_bool_decide; split; subst; lra.
        * apply ex_seriesC_scal_l, ex_seriesC_laplace_f_nat.
  Qed.
  
  Program Definition laplace' ε : distr (Z) :=
    MkDistr (λ z, laplace_f ε z / SeriesC (λ z, laplace_f ε z)) _ _ _.
  Next Obligation.
    intros. rewrite /laplace_f.
    apply Rdiv_le_0_compat.
    - left. apply exp_pos.
    - eapply Rlt_le_trans; last eapply (SeriesC_ge_elem _ 0%Z).
      + apply exp_pos.
      + intros; left. apply exp_pos.
      + apply ex_seriesC_laplace_f.
  Qed.
  Next Obligation.
    intros.
    setoid_rewrite Rdiv_def.
    apply ex_seriesC_scal_r, ex_seriesC_laplace_f.
  Qed.
  Next Obligation.
    intros.
    setoid_rewrite Rdiv_def.
    rewrite SeriesC_scal_r.
    rewrite Rinv_r; first done.
    assert (0<SeriesC (laplace_f ε)) as ?; last lra.
    eapply Rlt_le_trans; last eapply (SeriesC_ge_elem _ 0%Z).
      - apply exp_pos.
      - intros; left. apply exp_pos.
      - apply ex_seriesC_laplace_f.
  Qed.

  Program Definition laplace ε m :distr (Z) :=
    MkDistr (λ z, laplace' ε (z-m)%Z) _ _ _.
  Next Obligation.
    simpl; intros.
    apply pmf_pos.
  Qed.
  Next Obligation.
    intros.
    pose (h:= (λ '(z1, z2), if bool_decide (z2 -z1 = m)%Z then laplace' ε z1 else 0)).
    apply (ex_seriesC_ext (λ z2, SeriesC (λ z1, h (z1, z2)))).
    { rewrite /h.
      intros z2.
      erewrite SeriesC_ext; first apply SeriesC_singleton_dependent.
      simpl. intros; repeat case_bool_decide; try done; lia.
    }
    apply fubini_pos_seriesC_ex_double; rewrite /h.
    - intros. case_bool_decide; [apply pmf_pos|done].
    - intros. eapply ex_seriesC_ext; last apply (ex_seriesC_singleton (m+a)%Z).
      intros. simpl. repeat case_bool_decide; try lia; done.
    - eapply ex_seriesC_ext; last apply (pmf_ex_seriesC (laplace' ε)).
      intros n.
      erewrite SeriesC_ext; first by erewrite (SeriesC_singleton (n+m)%Z).
      intros. simpl. repeat case_bool_decide; try lia; done.
  Qed.
  Next Obligation.
    intros.
    pose (h:= (λ '(z1, z2), if bool_decide (z2 -z1 = m)%Z then laplace' ε z1 else 0)).
    rewrite (SeriesC_ext _ (λ z, SeriesC (λ n, h (n,z)))).
    - rewrite fubini_pos_seriesC.
      + rewrite /h.
        erewrite (SeriesC_ext _ (laplace' ε)).
        * apply pmf_SeriesC.
        * intros n.
          erewrite (SeriesC_ext _ (λ b, if bool_decide (b=n+m)%Z then laplace' ε n else 0)); first by rewrite SeriesC_singleton.
          intros. repeat case_bool_decide; try lia; done.
      + rewrite /h. intros. case_bool_decide; last done.
        apply pmf_pos.
      + rewrite /h.
        intros n. apply (ex_seriesC_ext (λ b, if bool_decide (b=n+m)%Z then laplace' ε n else 0));
          last apply ex_seriesC_singleton.
        intros. repeat case_bool_decide; try lia; done.
      + rewrite /h.
        apply (ex_seriesC_ext (laplace' ε)); last apply pmf_ex_seriesC.
        intros n. erewrite (SeriesC_ext _ (λ b, if bool_decide (b=n+m)%Z then laplace' ε n else 0)); first by rewrite SeriesC_singleton.
        intros. repeat case_bool_decide; try lia; done.
    - intros n. rewrite /h.
      erewrite (SeriesC_ext _ (λ b, if bool_decide (b=n-m)%Z then laplace' ε b else 0)); first by rewrite SeriesC_singleton_dependent.
      intros. repeat case_bool_decide; try lia; done.
  Qed.
End laplace.

Ltac inv_distr :=
  repeat
    match goal with
    | H : dzero.(pmf) _ > 0 |- _ => exfalso; by eapply dzero_supp_empty
    | H : (dret _).(pmf) _ > 0 |- _ => apply dret_pos in H; simplify_eq
    | H : (dbind _ _).(pmf) _ > 0 |- _ => apply dbind_pos in H as (?&?&?)
    | H : (dmap _ _).(pmf) _ > 0 |- _ => apply dmap_pos in H as (?&?&?); simplify_eq
    end.

Ltac solve_distr :=
  repeat
    match goal with
    | |- (dret _).(pmf) _ > 0 => rewrite dret_1_1 //; lra
    | |- (dret ?x).(pmf) ?x = 1 => by apply dret_1_1
    | |- (dbind _ _).(pmf) _ > 0 => apply dbind_pos; eexists; split
    | |- (dmap _ _).(pmf) _ > 0 =>
        apply dmap_pos; eexists; (split; [done|]); try done
    | |- (dunifP _).(pmf) _ > 0 => apply dunifP_pos
    | |- (dunifv _ _).(pmf) _ > 0 => apply dunifv_pos
    end.

Ltac solve_distr_mass :=
  match goal with
  | |- SeriesC (dret _).(pmf) = 1 => rewrite SeriesC_singleton //
  | |- SeriesC (dret _).(pmf) > 0 => rewrite dret_mass; lra
  | |- SeriesC (dmap _ _).(pmf) = 1 => rewrite dmap_mass //
  | |- SeriesC (dunif _).(pmf) = 1 => rewrite dunif_mass //
  | |- SeriesC (dunifP _).(pmf) = 1 => rewrite dunifP_mass //
  | |- SeriesC (dunifv _ _).(pmf) = 1 => rewrite dunifv_mass //
  end .

Ltac inv_dzero :=
  repeat
    match goal with
    | H : dret _ = dzero |- _ => by apply dret_not_dzero in H
    | H : dmap _ _ = dzero |- _ => apply dmap_dzero_inv in H
    | H : dunifP _ = dzero |- _ => by apply dunifP_not_dzero in H
    end.
