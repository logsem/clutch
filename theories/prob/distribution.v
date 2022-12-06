From Coq Require Import Reals Psatz.
From Coq.ssr Require Import ssreflect.
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

Global Arguments MkDistr {_ _ _}.
Global Arguments pmf {_ _ _ _} _ : simpl never.
Global Arguments pmf_pos {_ _ _}.
Global Arguments pmf_ex_seriesC {_ _ _}.
Global Arguments pmf_SeriesC {_ _ _}.

#[global] Hint Resolve pmf_pos pmf_ex_seriesC pmf_SeriesC : core.

Notation Decidable P := (∀ x, Decision (P x)).

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
    intros a'. case_bool_decide; subst; split; try (lra || done).
  Qed.

  Lemma pmf_SeriesC_ge_0 μ : 0 <= SeriesC μ.
  Proof.
    transitivity (SeriesC (λ (_ : A), 0)).
    { apply SeriesC_ge_0; [done|]. apply ex_seriesC_0. }
    apply SeriesC_le'; auto. apply ex_seriesC_0.
  Qed.

  Lemma pmf_ex_seriesC_mult_fn μ (f : A → R) :
    (∃ n, ∀ a, 0 <= f a <= n) →
    ex_seriesC (λ a, μ a * f a).
  Proof.
    intros [n Hf].
    eapply (ex_seriesC_le _ (λ a, μ a * n)); [|by apply ex_seriesC_scal_r].
    intros a. split.
    - apply Rmult_le_pos; [done|]. eapply Hf.
    - eapply Rmult_le_compat_l; [done|]. eapply Hf.
  Qed.

  Lemma pmf_ex_seriesC_mult (μ1 μ2 : distr A) :
    ex_seriesC (λ a, μ1 a * μ2 a).
  Proof.
    eapply pmf_ex_seriesC_mult_fn.
    exists 1. intros a; split; [apply pmf_pos|apply pmf_le_1].
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
      intros; do 2 case_bool_decide; simplify_eq; done.
    - rewrite (SeriesC_split_elem _ a'); last first.
      + eapply ex_seriesC_le; [|eapply (pmf_ex_seriesC μ)].
        intros; repeat case_bool_decide; split; (lra || done).
      + intros; by case_bool_decide.
      + apply Rle_plus_l.
        * erewrite SeriesC_ext; [by erewrite (SeriesC_singleton a' (μ a'))|].
          intros; do 2 case_bool_decide; simplify_eq=>//.
          rewrite bool_decide_eq_true_2 //.
        * eapply SeriesC_ge_0.
          { intros; repeat case_bool_decide; (lra || done). }
          eapply ex_seriesC_le; [|eapply (pmf_ex_seriesC μ)].
          intros. repeat case_bool_decide; split; (lra || done).
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


  Definition fair_coin_pmf : bool → R :=
    λ b, 0.5.

  Program Definition fair_coin : distr bool := MkDistr (fair_coin_pmf) _ _ _.
  Next Obligation. intros b. rewrite /fair_coin_pmf. destruct b; lra. Qed.
  Next Obligation.
  apply (ex_seriesC_ext  (λ b, (if bool_decide (b = true) then 0.5 else 0) + if bool_decide (b = false) then 0.5 else 0)); auto.
  { intro b; destruct b; rewrite /fair_coin_pmf /=; lra. }
  eapply ex_seriesC_plus; eapply ex_seriesC_singleton. Qed.
  Next Obligation.
  rewrite (SeriesC_ext _ (λ b, (if bool_decide (b = true) then 0.5 else 0) + if bool_decide (b = false) then 0.5 else 0)).
  2 : { intro b; destruct b; rewrite /fair_coin_pmf /= ; lra. }
  erewrite SeriesC_plus; [|eapply ex_seriesC_singleton.. ].
  rewrite 2!SeriesC_singleton. lra. Qed.



(* AA: We may need this generality later, but I think it is better to define the fair coin
   explicitly *)
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



End distributions.

#[global] Hint Resolve pmf_le_1 : core.
#[global] Hint Resolve pmf_SeriesC_ge_0 : core.

(** * Monadic return  *)
Definition dret_pmf `{Countable A} (a : A) : A → R :=
  λ (a' : A), if bool_decide (a' = a) then 1 else 0.

Program Definition dret `{Countable A} (a : A) : distr A := MkDistr (dret_pmf a) _ _ _.
Next Obligation. intros. rewrite /dret_pmf. case_bool_decide; nra. Qed.
Next Obligation. intros. apply ex_seriesC_singleton. Qed.
Next Obligation. intros. rewrite SeriesC_singleton //. Qed.

Section dret.
  Context `{Countable A}.

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
    - apply (inj f) in Hcase as ->.  rewrite bool_decide_eq_true_2 //.
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

  Lemma dret_inhabited `{Countable A} (a : A) :
    SeriesC (dret a) > 0.
  Proof. rewrite SeriesC_singleton. lra. Qed.

End dret.

(** * Monadic bind  *)
Definition dbind_pmf `{Countable A, Countable B} (f : A → distr B) (μ : distr A) : B → R :=
  λ (b : B), SeriesC (λ (a : A), μ a * f a b).

Program Definition dbind `{Countable A, Countable B} (f : A → distr B) (μ : distr A) : distr B :=
  MkDistr (dbind_pmf f μ) _ _ _.
Next Obligation.
  intros ?????? f μ b. rewrite /dbind_pmf.
  apply SeriesC_ge_0.
  - intros a'. by apply Rmult_le_pos.
  - eapply (ex_seriesC_le _ (λ a, μ a * 1)); [|by apply ex_seriesC_scal_r].
    intros a. split; [by apply Rmult_le_pos|].
    eapply Rmult_le_compat_l; [done|].
    eapply pmf_le_1.
Qed.
Next Obligation.
  intros ?????? f μ. rewrite /dbind_pmf.
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
  intros ?????? f μ. rewrite /dbind_pmf.
  rewrite (SeriesC_double_swap (λ '(a, b), _)).
  rewrite -(SeriesC_ext (λ k, μ k * SeriesC (λ j, f k j))); last first.
  { intros a. rewrite SeriesC_scal_l //. }
  transitivity (SeriesC μ); [|done].
  eapply SeriesC_le; [|done].
  intros a. split.
  - apply Rmult_le_pos; [done|].
    apply SeriesC_ge_0; auto.
  - rewrite -{2}(Rmult_1_r (μ a)).
    by apply Rmult_le_compat_l.
Qed.


Lemma dbind_pmf_ext `{Countable A, Countable B} (μ1 μ2 : distr A) (f g : A → distr B) (b1 b2 : B) :
  (∀ a b, f a b = g a b) →
  μ1 = μ2 →
  b1 = b2 →
  dbind f μ1 b1 = dbind g μ2 b2.
Proof.
  intros Hfg -> ->=>/=. rewrite /pmf /= /dbind_pmf.
  setoid_rewrite Hfg. done.
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
    intros a'. case_bool_decide; simplify_eq.
    - rewrite bool_decide_eq_true_2 //. lra.
    - rewrite bool_decide_eq_false_2 //. lra.
  Qed.

  Lemma dret_id_right (μ : distr A) :
    (a ← μ; dret a) = μ.
  Proof. apply distr_ext, dret_id_right_pmf. Qed.

  Context `{Countable B}.

  Lemma dret_id_left_pmf (f : A → distr B) (a : A) (b : B) :
    (a' ← dret a; f a') b = f a b.
  Proof.
    rewrite {1}/pmf /= /dbind_pmf {1}/pmf /= /dret_pmf.
    rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then f a b else 0)).
    { rewrite SeriesC_singleton //. }
    intros a'. case_bool_decide; simplify_eq; lra.
  Qed.

  Lemma dret_id_left (f : A → distr B) (a : A) :
    (a' ← dret a; f a') = f a.
  Proof. apply distr_ext, dret_id_left_pmf. Qed.

  Lemma dbind_dret_pmf_map (μ : distr A) (a : A) (f : A → B) `{Inj A B (=) (=) f} :
    (μ ≫= (λ a', dret (f a'))) (f a) = μ a.
  Proof.
    rewrite {1}/pmf /= /dbind_pmf {2}/pmf /= /dret_pmf.
    rewrite (SeriesC_ext _ (λ a', if bool_decide (a' = a) then μ a else 0)).
    { rewrite SeriesC_singleton //. }
    intros a'. case_bool_decide as Heq; simplify_eq.
    - rewrite bool_decide_eq_true_2 //. lra.
    - rewrite bool_decide_eq_false_2; [lra|].
      by intros ->.
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
    assert (SeriesC (λ a : A, μ a * SeriesC (λ a0 : B, f a a0 * g a0 c)) =
              SeriesC (λ a : A, SeriesC (λ a0 : B, μ a * f a a0 * g a0 c))) as Heq1.
    { apply SeriesC_ext; intro a.
      rewrite <- SeriesC_scal_l.
      apply SeriesC_ext; intros n; lra. }
    rewrite Heq1.
    pose proof (SeriesC_double_swap (λ '(a ,a0), μ a * f a a0 * g a0 c)) as Heq2.
    simpl in Heq2.
    rewrite Heq2.
    apply SeriesC_ext.
    intro b.
    rewrite {4}/pmf /= /dbind_pmf.
    rewrite -SeriesC_scal_r //.
  Qed.

  Lemma dbind_assoc `{Countable B'} (f : A → distr B) (g : B → distr B') (μ : distr A) :
    (a ← μ ; b ← f a; g b) = (b ← (a ← μ; f a); g b).
  Proof. apply distr_ext, dbind_assoc_pmf. Qed.

  Lemma dbind_pos_support (f : A → distr B) (μ : distr A) (b : B) :
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
      { rewrite SeriesC_singleton. eapply Rmult_gt_0_compat; lra. }
      eapply SeriesC_le.
      + intros ?. case_bool_decide; simplify_eq; split; done || by eapply Rmult_le_pos.
      + apply (ex_seriesC_le _ (λ a : A, μ a * 1)); [|by apply ex_seriesC_scal_r].
        intros a'. split.
        * by apply Rmult_le_pos.
        * apply Rmult_le_compat_l; [done|]. eapply pmf_le_1.
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

  Lemma dbind_inhabited `{Countable A, Countable B} (f : A → distr B) (μ : distr A) :
    SeriesC μ > 0 →
    (∀ a, SeriesC (f a) > 0) →
    SeriesC (dbind f μ) > 0.
  Proof.
    intros Hμ Hf.
    rewrite /pmf /= /dbind_pmf.
    rewrite (SeriesC_double_swap (λ '(a, b), _)).
    setoid_rewrite SeriesC_scal_l.
    apply Rlt_gt. rewrite -(SeriesC_0 (λ _ : A, 0)); [|done].
    eapply SeriesC_lt.
    - intros ?. split; [done|]. by apply Rmult_le_pos.
    - apply SeriesC_gtz_ex in Hμ as [a Ha]; [|done].
      exists a. by apply Rmult_lt_0_compat, Rgt_lt.
    - eapply pmf_ex_seriesC_mult_fn. eauto.
  Qed.

End monadic.

  (* Convex combinations *)
  (* AA: There may be a better place to define this *)
  Definition fair_conv_comb `{Countable A} (μ1 μ2 : distr A) : distr A :=
    dbind (λ b, if b then μ1 else μ2) fair_coin.

Section conv_prop.

  Context `{Countable A, Countable B}.

  Lemma fair_conv_comb_pmf `{Countable D} (μ1 μ2 : distr D) (a : D) :
    fair_conv_comb μ1 μ2 a = 0.5 * (μ1 a) + 0.5 * (μ2 a).
  Proof.
    rewrite /pmf /fair_coin_pmf /= /dbind_pmf.
    rewrite (SeriesC_ext _ (λ b, (if bool_decide (b = true) then 0.5 * μ1 a else 0) + if bool_decide (b = false) then 0.5 * μ2 a else 0)).
    2: { intro b; destruct b; simpl; rewrite /pmf /fair_coin_pmf /= /fair_coin_pmf; simpl; lra. }
    erewrite SeriesC_plus; [|eapply ex_seriesC_singleton.. ].
    rewrite 2!SeriesC_singleton; simpl.
    (* AA: This is strange *)
    rewrite /pmf; lra.
  Qed.

  Definition dbind_fair_conv_comb (f1 f2 : A → distr B) (μ : distr A) :
    dbind (λ a, fair_conv_comb (f1 a) (f2 a)) μ = fair_conv_comb (dbind f1 μ) (dbind f2 μ).
  Proof.
    apply distr_ext.
    intro b.
    rewrite {1}/pmf /= /dbind_pmf.
    rewrite (fair_conv_comb_pmf (μ ≫= f1) (μ ≫= f2) b).
    assert (forall a, μ a * fair_conv_comb (f1 a) (f2 a) b = 0.5 * (μ a * (f1 a) b + μ a * (f2 a) b)) as Heq.
    { intro a; rewrite fair_conv_comb_pmf; lra. }
    setoid_rewrite Heq.
    rewrite SeriesC_scal_l.
    rewrite <- Rmult_plus_distr_l.
    rewrite {5 6}/pmf /= /dbind_pmf.
    rewrite -> SeriesC_plus; auto.
    (* TODO: Clean this up *)
    + apply (ex_seriesC_le _ μ); [ | apply pmf_ex_seriesC].
      intro a.
      pose proof (pmf_pos μ a).
      pose proof (pmf_pos (f1 a) b).
      pose proof (pmf_le_1 μ a).
      pose proof (pmf_le_1 (f1 a) b).
      split.
      ++ apply Rmult_le_pos; auto.
      ++ rewrite <- (Rmult_1_r (μ a)).
         apply Rmult_le_compat; lra.
    + apply (ex_seriesC_le _ μ); [ | apply pmf_ex_seriesC].
      intro a.
      pose proof (pmf_pos μ a).
      pose proof (pmf_pos (f2 a) b).
      pose proof (pmf_le_1 μ a).
      pose proof (pmf_le_1 (f2 a) b).
      split.
      ++ apply Rmult_le_pos; auto.
      ++ rewrite <- (Rmult_1_r (μ a)).
         apply Rmult_le_compat; lra.
  Qed.


End conv_prop.

(** * Monadic map *)
Definition dmap `{Countable A, Countable B} (f : A → B) (μ : distr A) : distr B :=
    a ← μ; dret (f a).

Section dmap.
  Context `{Countable A, Countable B}.

  Lemma dmap_dret_pmf (f : A → B) (a : A) (b : B) :
    dmap f (dret a) b = dret (f a) b.
  Proof. rewrite /dmap dret_id_left_pmf //. Qed.

  Lemma dmap_dret (f : A → B) a :
    dmap f (dret a) = dret (f a) .
  Proof. apply distr_ext, dmap_dret_pmf. Qed.

  Lemma dmap_dbind_pmf (f : A → B) (g : A → distr A) (μ : distr A) (b : B) :
    dmap f (dbind g μ) b = dbind (λ a, dmap f (g a)) μ b.
  Proof. rewrite /dmap dbind_assoc_pmf //. Qed.

  Lemma dmap_dbind (f : A → B) (g : A → distr A) (μ : distr A) :
    dmap f (dbind g μ) = dbind (λ a, dmap f (g a)) μ.
  Proof. apply distr_ext, dmap_dbind_pmf. Qed.

  Lemma dmap_mass (μ : distr A) (f : A → B):
    SeriesC μ = SeriesC (dmap f μ).
  Proof.
    rewrite /dmap {2}/pmf /= /dbind_pmf.
    rewrite <- (SeriesC_double_swap (λ '(a , b), (μ a * dret (f a) b) )).
    apply SeriesC_ext=> a.
    rewrite {3}/pmf /= /dret_pmf.
    rewrite SeriesC_scal_l.
    rewrite SeriesC_singleton.
    lra.
  Qed.

  Lemma dmap_pos (μ : distr A) (f : A → B) (b : B) :
    dmap f μ b > 0 ↔ ∃ a, b = f a ∧ μ a > 0.
  Proof.
    split.
    - intros [a [Hr%dret_pos ?]]%dbind_pos_support; eauto.
    - intros [a [-> Ha]]. apply dbind_pos_support.
      exists a. rewrite dret_1_1 //. split; [lra|done].
  Qed.

  Lemma dmap_eq (μ : distr A) (a : A) (b : B) (f : A → B) `{Inj A B (=) (=) f} :
    b = f a → dmap f μ b = μ a.
  Proof. intros ->. rewrite dbind_dret_pmf_map //. Qed.

  Lemma dmap_ne (μ : distr A) (b : B) (f : A → B) `{Inj A B (=) (=) f} :
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

End dmap.

(** * Monadic strength  *)
Definition strength_l `{Countable A, Countable B} (a : A) (μ : distr B) : distr (A * B) :=
  dmap (λ b, (a, b)) μ.

Definition strength_r `{Countable A, Countable B} (μ : distr A) (b : B) : distr (A * B) :=
  dmap (λ a, (a, b)) μ.

Lemma dbind_strength `{Countable A, Countable B, Countable D} (f : A*B → distr D) (a : A) (μ : distr B) :
  dbind f (strength_l a μ) = dbind (λ b, f (a, b)) μ.
Proof.
  rewrite /strength_l /dmap.
  rewrite <- dbind_assoc.
  setoid_rewrite dret_id_left; auto.
Qed.


Lemma dbind_strength_r `{Countable A, Countable B, Countable D} (f : A*B → distr D) (μ : distr A) (b : B) :
  dbind f (strength_r μ b) = dbind (λ a, f (a, b)) μ.
Proof.
  rewrite /strength_r /dmap.
  rewrite <- dbind_assoc.
  setoid_rewrite dret_id_left; auto.
Qed.


Lemma strength_dbind `{Countable A, Countable B, Countable D} (f : B → distr D) (a : A) (μ : distr B) :
  strength_l a (dbind f μ) = dbind (λ b, strength_l a (f b)) μ.
Proof.
  rewrite /strength_l /dmap.
  rewrite <- dbind_assoc; auto.
Qed.


Lemma strength_r_dbind `{Countable A, Countable B, Countable D} (f : A → distr D) (μ : distr A) (b : B) :
  strength_r (dbind f μ) b = dbind (λ a, strength_r (f a) b) μ.
Proof.
  rewrite /strength_r /dmap.
  rewrite <- dbind_assoc; auto.
Qed.

Lemma strength_comm `{Countable A, Countable B} (f : A -> distr A) (g : B -> distr B) (a : A) (b : B) :
  dbind (λ '(a',b'), strength_r (f a') b' ) (strength_l a (g b)) = dbind (λ '(a',b'), strength_l a' (g b')) (strength_r (f a) b).
Proof.
  rewrite dbind_strength.
  rewrite dbind_strength_r.
  rewrite /strength_l /strength_r /dmap.
  apply distr_ext.
  intros (a' & b').
  rewrite /pmf/=/dbind_pmf/=.
  rewrite /pmf/=/dbind_pmf/=.
  setoid_rewrite <- SeriesC_scal_l.
  rewrite (SeriesC_double_swap ((λ '(a0, x), (let (pmf0, _, _, _) := g b in pmf0) a0 * (f a x * dret (x, a0) (a', b'))))).
  apply SeriesC_ext.
  intro a''.
  apply SeriesC_ext.
  intro b''.
  rewrite /pmf /=; lra.
Qed.

(** * Monadic fold left  *)
Definition foldlM {A B} `{Countable B} (f : B → A → distr B) (b : B) (xs : list A) : distr B :=
  foldr (λ a m b, f b a ≫= m) dret xs b.

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

End iterM.

(** * The zero distribution  *)
Program Definition dzero `{Countable A} : distr A := MkDistr (λ _, 0) _ _ _.
Next Obligation. done. Qed.
Next Obligation. intros. eapply ex_seriesC_0. Qed.
Next Obligation. intros. rewrite SeriesC_0 //. lra. Qed.

Section dzero.
  Context `{Countable A}.

  Lemma dzero_ext (μ : distr A) :
    (∀ a, μ a = 0) → μ = dzero.
  Proof. intros ?; apply distr_ext; auto. Qed.

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

  Context `{Countable B}.

  Lemma dbind_dzero_pmf (f : A → distr B) (b : B) :
    (a ← dzero; f a) b = 0.
  Proof.
    rewrite /pmf /= /dbind_pmf {1}/pmf /= /dzero.
    apply SeriesC_0=>?. lra.
  Qed.

  Lemma dbind_dzero (f : A → distr B) :
    (a ← dzero; f a) = dzero.
  Proof. apply distr_ext, dbind_dzero_pmf. Qed.

  Lemma dmap_dzero (f : A → B):
    dmap f dzero = dzero.
  Proof.
    apply dbind_dzero.
  Qed.

End dzero.

(** * Diagonal *)
Program Definition ddiag `{Countable A} (μ : distr A) : distr (A * A) :=
  MkDistr (λ '(a, b), if bool_decide(a=b) then μ b else 0) _ _ _.
Next Obligation. intros ???? [a b]=>/=. case_bool_decide; auto; lra. Qed.
Next Obligation.
  intros A?? μ =>/=.
  (* TODO *)
  Admitted.

Next Obligation.
  intros A?? μ =>/=.
  rewrite SeriesC_double_prod_rl.
  erewrite SeriesC_ext.
  { apply (pmf_SeriesC μ). }
  intro. apply SeriesC_singleton.
Qed.

(** * Products  *)
Program Definition dprod `{Countable A, Countable B} (μ1 : distr A) (μ2 : distr B) : distr (A * B) :=
  MkDistr (λ '(a, b), μ1 a * μ2 b) _ _ _.
Next Obligation. intros ???????? [a b]=>/=. by eapply Rmult_le_pos. Qed.
Next Obligation.
  intros A ?? B ?? μ1 μ2=>/=.
  (* TODO: needs some rearranging lemmas like [SeriesC_double_swap] *)
Admitted.
Next Obligation.
  intros A ?? B ?? μ1 μ2 => /=.
  rewrite SeriesC_double_prod_rl.
  rewrite -(SeriesC_double_swap (λ '(a, b), μ1 a * μ2 b)).
  rewrite -(SeriesC_ext (λ a, μ1 a * SeriesC μ2)); last first.
  { intros a. rewrite SeriesC_scal_l //. }
  transitivity (SeriesC μ1); [|done].
  eapply SeriesC_le; [|done].
  intros a. split.
  - apply Rmult_le_pos; [done|].
    apply SeriesC_ge_0; auto.
  - rewrite -{2}(Rmult_1_r (μ1 a)).
    by apply Rmult_le_compat_l.
Qed.

Section dprod.
  Context `{Countable A, Countable B}.
  Variable (μ1 : distr A) (μ2 : distr B).

  Lemma dprod_pos (a : A) (b : B) :
    dprod μ1 μ2 (a, b) > 0 ↔ μ1 a > 0 ∧ μ2 b > 0.
  Proof.
    rewrite {1}/pmf /=.
    split.
    - destruct (decide (μ1 a > 0)) as [| ->%pmf_eq_0_not_gt_0]; [|lra].
      destruct (decide (μ2 b > 0)) as [| ->%pmf_eq_0_not_gt_0]; [|lra].
      done.
    - intros []. by apply Rmult_gt_0_compat.
  Qed.

End dprod.

(** * Margignals  *)
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
    rewrite SeriesC_double_prod_rl.
    apply SeriesC_ext; intro b.
    rewrite {2}/pmf /= /dret_pmf /=.
    erewrite SeriesC_ext; [apply (SeriesC_singleton' a)|].
    intro a'; simpl; case_bool_decide; simplify_eq; lra.
  Qed.

  Lemma rmarg_pmf (μ : distr (A * B)) (b : B):
    rmarg μ b = SeriesC (λ a, μ (a, b)).
  Proof.
    rewrite {1}/pmf /= /dbind_pmf.
    rewrite SeriesC_double_prod_lr.
    apply SeriesC_ext; intro a.
    rewrite {2}/pmf /= /dret_pmf /=.
    erewrite SeriesC_ext; [apply (SeriesC_singleton' b)|].
    intro b'; simpl; case_bool_decide; simplify_eq; lra.
  Qed.

  Lemma ex_seriesC_lmarg (μ : distr (A * B)) (a : A) :
    ex_seriesC (λ b, μ (a, b)).
  Proof. eapply ex_seriesC_double_pos_l; auto. Qed.

  Lemma ex_seriesC_rmarg (μ : distr (A * B)) (b : B) :
    ex_seriesC (λ a, μ (a, b)).
  Proof. eapply ex_seriesC_double_pos_r; auto. Qed.

  Lemma lmarg_dprod_pmf (μ1 : distr A) (μ2 : distr B) (a : A) :
    lmarg (dprod μ1 μ2) a = μ1 a.
  Proof.
    rewrite lmarg_pmf.
  Admitted.

  Lemma lmarg_dprod (μ1 : distr A) (μ2 : distr B) :
    lmarg (dprod μ1 μ2) = μ1.
  Proof. eapply distr_ext, lmarg_dprod_pmf. Qed.

  Lemma rmarg_dprod_pmf (μ1 : distr A) (μ2 : distr B) (b : B) :
    rmarg (dprod μ1 μ2) b = μ2 b.
  Proof.
    rewrite rmarg_pmf.
  Admitted.

  Lemma rmarg_dprod (μ1 : distr A) (μ2 : distr B) :
    rmarg (dprod μ1 μ2) = μ2.
  Proof. eapply distr_ext, rmarg_dprod_pmf. Qed.

End marginals.


Definition distr_le `{Countable A} (μ1 μ2 : distr A) : Prop :=
  ∀ a, (μ1 a <= μ2 a)%R.

Section order.

(* There may be a way to reformulate this section using refinement couplings *)

Context `{Countable A, Countable B}.


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
  distr_le μ1 μ2 -> distr_le μ2 μ3 -> distr_le μ1 μ3.
Proof.
  rewrite /distr_le.
  intros H1 H2 a.
  apply (Rle_trans (μ1 a) (μ2 a)); auto.
Qed.

Lemma distr_le_antisym (μ1 μ2 : distr A):
  distr_le μ1 μ2 -> distr_le μ2 μ1 -> μ1 = μ2.
Proof.
  rewrite /distr_le.
  intros H1 H2.
  apply distr_ext; intro a.
  apply Rle_antisym; auto.
Qed.


Lemma distr_le_dbind (μ1 μ2 : distr A) (f1 f2 : A → distr B) :
  (distr_le μ1 μ2) -> (∀ a, distr_le (f1 a) (f2 a)) → distr_le (dbind f1 μ1) (dbind f2 μ2).
Proof.
  intros Hle Hf.
  pose proof (pmf_ex_seriesC (μ2 ≫= f2)) as Hex.
  rewrite /distr_le /pmf /= /dbind_pmf /=.
  intro b.
  (* We do enough of this kind of reasoning that it should be a lemma, so that we don't have to prove the exSeriesC everytime *)
  apply SeriesC_le; last first.
  + eapply ex_seriesC_le; [ |apply (pmf_ex_seriesC μ2)].
    intro a;  split.
    ++ apply Rmult_le_pos; auto.
    ++ rewrite <- Rmult_1_r; apply Rmult_le_compat_l; auto.
  + intro a; split.
    ++ apply Rmult_le_pos; auto.
    ++ rewrite /distr_le in Hle.
       rewrite /distr_le in Hf.
       eapply Rmult_le_compat; auto.
Qed.

End order.
