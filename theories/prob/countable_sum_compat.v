From Coq Require Import Reals Psatz.
From clutch.prelude Require Import base Reals_ext Coquelicot_ext Series_ext stdpp_ext classical.
From discprob.basic Require sval base Reals_ext Series_Ext stdpp_ext.
From discprob.prob Require countable rearrange.

From mathcomp Require Import bigop fintype choice.
From mathcomp Require Import eqtype.

Section Countable_countType.

Lemma Countable_to_pcancel {T: Type} `{EqDecision T} (HC: Countable T):
    ssrfun.pcancel (λ x : T, (@encode_nat _ _ HC x))
                   (λ x, @decode_nat _ _ HC x).
Proof.
  rewrite /ssrfun.pcancel.
  intros x.
  specialize (pos_INR_nat_of_P (countable.encode x)).
  destruct HC => //=.
  rewrite /countable.decode/countable.encode.
  rewrite decode_encode_nat.
  intros. reflexivity.
Defined.

Definition StdppCountEqMixin {T : Type} `{EqDecision T}:
  Countable T → eqtype.Equality.mixin_of T.
Proof.
  intros HC.
  eapply (@PcanEqMixin T [countType of nat] (λ x, (@encode_nat _ _ HC x))
                       (λ x, @decode_nat _ _ HC x)).
  apply Countable_to_pcancel.
Defined.

Definition StdppCountChoiceMixin {T : Type} `{EqDecision T}:
  Countable T → Choice.mixin_of T.
Proof.
  intros HC.
  eapply (@PcanChoiceMixin [countType of nat] _ (λ x, (@encode_nat _ _ HC x))
                       (λ x, @decode_nat _ _ HC x)).
  apply Countable_to_pcancel.
Defined.

Definition StdppCountCountMixin {T : Type} `{EqDecision T}:
  Countable T → Countable.mixin_of T.
Proof.
  intros HC.
  eapply (@PcanCountMixin [countType of nat] _ (λ x, @encode_nat _ _ HC x)
                       (λ x, @decode_nat _ _ HC x)).
  apply Countable_to_pcancel.
Defined.

Definition StdppCountCountClass {T : Type} `{EqDecision T}:
  Countable T → Countable.class_of T.
Proof.
  split.
  - split.
    * apply StdppCountEqMixin. apply _.
    * apply StdppCountChoiceMixin. apply _.
  - apply StdppCountCountMixin. apply _.
Defined.

#[local] Instance sig_eqdecision {T : Type} `{EqDecision T} (P: T → Prop):
  EqDecision T → EqDecision {x : T | P x}.
Proof.
  intros Heq (x&Hpf1) (y&Hpf2).
  - destruct (Heq x y).
    * rewrite /Decision. left. subst. apply sval.sval_inj_pi => //=.
    * right. inversion 1; subst; eauto.
Defined.

Definition sig_countable {T : Type} `{EqDecision T} (P: T → Prop):
  Countable T → Countable {x : T | P x}.
Proof.
  intros [enc dec Hed].
  unshelve (eexists).
  * intros (x&Hp). exact (enc x).
  * intros n. apply dec in n.
    destruct n as [t|].
    ** destruct (ClassicalEpsilon.excluded_middle_informative (P t)).
       *** apply Some; exists t; eauto. 
       *** apply None.
    ** apply None.
  * intros (x&Hp) => //=.
    rewrite Hed. destruct ClassicalEpsilon.excluded_middle_informative; eauto.
    ** f_equal. apply sval.sval_inj_pi => //=.
    ** exfalso; eauto.
Qed.

End Countable_countType.

From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy Markov.
From clutch.prob Require Import countable_sum.

Notation dcountable_sum := discprob.prob.countable.countable_sum.

Lemma is_seriesC_is_series_countable_sum
  {A} `{COUNT: Countable A} (f: A → R) v :
  is_seriesC f v →
  is_series (dcountable_sum (λ x : (Countable.Pack (StdppCountCountClass COUNT)), f x)) v.
Proof.
  intros Hseries.
  rewrite /is_seriesC in Hseries.
  rewrite /countable_sum in Hseries.
  rewrite /dcountable_sum/=.
  rewrite /pickle_inv/=/unpickle/=.
  eapply is_series_ext; try eassumption.
  intros n. rewrite /=.
  rewrite /ssrfun.Option.apply //=.
  rewrite /ssrfun.Option.bind //=.
  rewrite /ssrfun.Option.apply //=.
  rewrite /ssrfun.pcomp //=.
  destruct (encode_inv_nat n) as [|] eqn:Heq.
  - apply encode_inv_Some_nat in Heq.
    rewrite -Heq decode_encode_nat /=.
    rewrite /pickle/=/pickle/=.
    rewrite eq_refl //.
  - destruct (decode_nat n) as [|] eqn:Hdecode => //=.
    rewrite /pickle/=/pickle/=.
    case: (@eq_op ssrnat.nat_eqType (encode_nat a) n) / eqP.
    * intros Hfalse. rewrite -Hfalse in Heq.
      rewrite encode_inv_encode_nat in Heq. congruence.
    * nra.
Qed.

Lemma is_seriesC_is_series_countable_sum_alt
  {A} `{COUNT: Countable A} (CLASS: Countable.class_of A) (f: A → R) (g : Countable.Pack CLASS → R) v
  (HEQ: ∀ x, g x = f x)
  (Hfnonneg: ∀ x, 0 <= f x) :
  is_seriesC f v →
  is_series (dcountable_sum g) v.
Proof.
  intros Hseries.
  rewrite /is_seriesC in Hseries.
  apply is_seriesC_is_series_countable_sum in Hseries; auto.
  assert (Hsupp: ∀ x, g x ≠ 0 → f x ≠ 0).
  { intros. rewrite -HEQ. eauto. }
  set (σ := λ x : {x : Countable.Pack CLASS  | g x ≠ 0},
           (exist _ (`x) (Hsupp (`x) (proj2_sig x)) : {x : _ | f x ≠ 0})).
  unshelve (eapply (rearrange.countable_series_rearrange_covering_match); try eassumption).
  { intros (x&?); exists x; rewrite -HEQ; done. }
  { eauto. }
  { intros. rewrite HEQ. eauto. }
  { intros (?&?) (?&?) => //=. inversion 1. subst.
    apply sval.sval_inj_pi; auto. }
  { intros (?&?).
    unshelve (eexists (exist _ x _)).
    { simpl. rewrite HEQ //=. }
    rewrite //=. apply sval.sval_inj_pi; auto. }
  { intros (?&?) => //=.  }
Qed.

Lemma is_series_countable_sum_is_seriesC
  {A} `{COUNT: Countable A} (f: A → R) v :
  is_series (dcountable_sum (λ x : (Countable.Pack (StdppCountCountClass COUNT)), f x)) v →
  is_seriesC f v.
Proof.
  rewrite /is_seriesC.
  rewrite /countable_sum.
  rewrite /dcountable_sum/=.
  rewrite /pickle_inv/=/unpickle/=.
  intros Hseries.
  eapply is_series_ext; try eassumption.
  intros n. rewrite /=.
  move: Hseries.
  rewrite /ssrfun.Option.apply //=.
  rewrite /ssrfun.Option.bind //=.
  rewrite /ssrfun.Option.apply //=.
  rewrite /ssrfun.pcomp //=.
  destruct (encode_inv_nat n) as [|] eqn:Heq.
  - apply encode_inv_Some_nat in Heq.
    rewrite -Heq decode_encode_nat /=.
    rewrite /pickle/=/pickle/=.
    rewrite eq_refl //.
  - destruct (decode_nat n) as [|] eqn:Hdecode => //=.
    rewrite /pickle/=/pickle/=.
    case: (@eq_op ssrnat.nat_eqType (encode_nat a) n) / eqP.
    * intros Hfalse. rewrite -Hfalse in Heq.
      rewrite encode_inv_encode_nat in Heq. congruence.
    * nra.
Qed.

Lemma is_series_countable_sum_is_seriesC_alt
  {A} `{COUNT: Countable A} (CLASS: Countable.class_of A) (f: A → R) (g : Countable.Pack CLASS → R) v
  (HEQ: ∀ x, g x = f x)
  (Hfnonneg: ∀ x, 0 <= f x) :
  is_series (dcountable_sum g) v →
  is_seriesC f v.
Proof.
  intros Hseries.
  apply is_series_countable_sum_is_seriesC.
  assert (Hsupp: ∀ x, f x ≠ 0 → g x ≠ 0).
  { intros. rewrite HEQ. eauto. }
  set (σ := λ x : {x : Countable.Pack CLASS  | f x ≠ 0},
           (exist _ (`x) (Hsupp (`x) (proj2_sig x)) : {x : _ | g x ≠ 0})).
  unshelve (eapply (rearrange.countable_series_rearrange_covering_match); try eassumption).
  { intros (x&?); exists x; rewrite HEQ; done. }
  { intros. rewrite HEQ. eauto. }
  { auto. }
  { intros (?&?) (?&?) => //=. inversion 1. subst.
    apply sval.sval_inj_pi; auto. }
  { intros (?&?).
    unshelve (eexists (exist _ x _)).
    { simpl. rewrite -HEQ //=. }
    rewrite //=. apply sval.sval_inj_pi; auto. }
  { intros (?&?) => //=.  }
Qed.
