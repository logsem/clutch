From clutch.prelude Require Import base Reals_ext Coquelicot_ext Series_ext stdpp_ext classical.
From discprob.basic Require sval base Reals_ext Series_Ext stdpp_ext.
From discprob.prob Require countable.

From mathcomp Require Import bigop fintype choice.
From mathcomp Require Import eqtype.

Lemma Countable_to_pcancel {T: Type} `{EqDecision T} (HC: Countable T):
    ssrfun.pcancel (λ x : T, Pos.to_nat (@encode _ _ HC x))
                   (λ x, @decode _ _ HC (Pos.of_nat x)).
Proof.
  rewrite /ssrfun.pcancel.
  intros x.
  destruct HC => //=.
  rewrite /countable.decode/countable.encode.
  rewrite Pos2Nat.id decode_encode //=.
Qed.

Definition StdppCountEqMixin {T : Type} `{EqDecision T}:
  Countable T → eqtype.Equality.mixin_of T.
Proof.
  intros HC.
  eapply (@PcanEqMixin T [countType of nat] (λ x, Pos.to_nat (@encode _ _ HC x))
                       (λ x, @decode _ _ HC (Pos.of_nat x))).
  apply Countable_to_pcancel.
Qed.

Definition StdppCountChoiceMixin {T : Type} `{EqDecision T}:
  Countable T → Choice.mixin_of T.
Proof.
  intros HC.
  eapply (@PcanChoiceMixin [countType of nat] _ (λ x, Pos.to_nat (@encode _ _ HC x))
                       (λ x, @decode _ _ HC (Pos.of_nat x))).
  apply Countable_to_pcancel.
Qed.

Definition StdppCountCountMixin {T : Type} `{EqDecision T}:
  Countable T → Countable.mixin_of T.
Proof.
  intros HC.
  eapply (@PcanCountMixin [countType of nat] _ (λ x, Pos.to_nat (@encode _ _ HC x))
                       (λ x, @decode _ _ HC (Pos.of_nat x))).
  apply Countable_to_pcancel.
Qed.

#[local] Instance sig_eqdecision {T : Type} `{EqDecision T} (P: T → Prop):
  EqDecision T → EqDecision {x : T | P x}.
Proof.
  intros Heq (x&Hpf1) (y&Hpf2).
  - destruct (Heq x y).
    * rewrite /Decision. left. subst. apply sval.sval_inj_pi => //=.
    * right. inversion 1; subst; eauto.
Qed.

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


