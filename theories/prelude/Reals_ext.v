From Coq Require Import Reals Psatz.
From clutch.prelude Require Import base.

(* Notation "x ≤ y" := (Rle x y) (at level 70, no associativity) : R_scope. *)
(* Notation "x ≥ y" := (Rge x y) (at level 70, no associativity) : R_scope. *)

#[local] Open Scope R.

#[global] Instance Rge_Transitive: Transitive Rge.
Proof. intros ???. eapply Rge_trans. Qed.
#[global] Instance Rle_Transitive: Transitive Rle.
Proof. intros ???. eapply Rle_trans. Qed.
#[global] Instance Rge_Reflexive: Reflexive Rge.
Proof. intros ?. eapply Rge_refl. Qed.
#[global] Instance Rle_Reflexive: Reflexive Rle.
Proof. intros ?. eapply Rle_refl. Qed.
#[global] Instance Rgt_Transitive: Transitive Rgt.
Proof. intros ???. eapply Rgt_trans. Qed.
#[global] Instance Rlt_Transitive: Transitive Rlt.
Proof. intros ???. eapply Rlt_trans. Qed.

#[global] Instance Rgt_decision (r1 r2 : R) : Decision (Rgt r1 r2).
Proof. apply Rgt_dec. Qed.
#[global] Instance Rge_decision (r1 r2 : R) : Decision (Rge r1 r2).
Proof. apply Rge_dec. Qed.
#[global] Instance Rlt_decision (r1 r2 : R) : Decision (Rlt r1 r2).
Proof. apply Rlt_dec. Qed.
#[global] Instance Rle_decision (r1 r2 : R) : Decision (Rle r1 r2).
Proof. apply Rle_dec. Qed.

#[global] Instance Rlt_plus_proper: Proper (Rlt ==> Rlt ==> Rlt) Rplus.
Proof.
  intros ?? Hle ?? Hle'. apply Rplus_lt_compat; auto.
Qed.
#[global] Instance Rlt_plus_proper': Proper (Rlt ==> eq ==> Rlt) Rplus.
Proof.
  intros ?? Hle ?? Hle'. subst. nra.
Qed.
#[global] Instance Rlt_plus_proper'': Proper (Rlt ==> Rle ==> Rlt) Rplus.
Proof.
  intros ?? Hle ?? Hle'. subst. nra.
Qed.

#[global] Instance Rle_plus_proper_left: Proper (Rle ==> eq ==> Rle) Rplus.
Proof. intros ?? Hle ?? Hle'. nra. Qed.
#[global] Instance Rle_plus_proper_right: Proper (eq ==> Rle ==> Rle) Rplus.
Proof. intros ?? Hle ?? Hle'. nra. Qed.
#[global] Instance Rle_plus_proper: Proper (Rle ==> Rle ==> Rle) Rplus.
Proof. intros ?? Hle ?? Hle'. nra. Qed.

Lemma Rmax_INR a b: Rmax (INR a) (INR b) = INR (max a b).
Proof.
  apply Rmax_case_strong; intros ?%INR_le; f_equal;
    [ rewrite Nat.max_l // | rewrite Nat.max_r // ].
Qed.

Global Coercion INR : nat >-> R.

Lemma Rmult_neq_0 (r1 r2 : R) :
  r1 * r2 ≠ 0 → r1 ≠ 0 ∧ r2 ≠ 0.
Proof. intros ?. split; intros ->; lra. Qed.

Lemma Rmult_neq_0_pos (r1 r2 : R) :
  r1 * r2 ≠ 0 → 0 <= r1 → 0 <= r2 → 0 < r1 ∧ 0 < r2.
Proof. intros [? ?]%Rmult_neq_0 ? ?. lra. Qed.

Lemma Rle_plus_plus (r1 r2 r3 r4 : R) :
  r1 <= r3 → r2 <= r4 → r1 + r2 <= r3 + r4.
Proof. lra. Qed.

Lemma Rle_plus_l (r1 r2 r3 : R) :
  r1 <= r2 → 0 <= r3 → r1 <= r2 + r3.
Proof. lra. Qed.

Lemma pos_sum_nn_real p q :
    0 <= p →
    0 <= q →
    0 < p + q →
    0 < p ∨ 0 < q.
  Proof.
    intros Hp Hq Hsum.
    destruct Hp as [ Hp | Hp ]; simplify_eq; auto.
    destruct Hq as [ Hq | Hq ]; simplify_eq; auto.
    lra.
  Qed.

Lemma pos_prod_nn_real p q :
    0 <= p →
    0 <= q →
    0 < p * q →
    0 < p ∧ 0 < q.
Proof.
  intros Hp Hq Hsum.
  destruct Hp as [ Hp | Hp ]; simplify_eq; split; auto; try lra.
  destruct Hq as [ Hq | Hq ]; simplify_eq ; auto; lra.
Qed.

Lemma RinvN_pos' : forall n:nat, 0 < / (INR (S n)).
Proof.
  intros n.
  assert (INR (S n) = (INR n + 1)) as ->.
  { replace 1 with (INR 1); [|done].
    rewrite -plus_INR. f_equal. lia. }
  apply RinvN_pos. 
Qed.

Ltac real_solver :=
    by repeat
         match goal with
         | |- _ <= _ <= _ => split

         (* arithmetic patterns *)
         (* <= *)
         | |- 0 <= _ * _ => apply Rmult_le_pos
         | |- ?a * ?b <= 1 => rewrite -(Rmult_1_r 1)
         | |- ?a * ?b <= ?a => rewrite -{2}(Rmult_1_r a)
         | |- ?a * ?b <= ?b => rewrite -{2}(Rmult_1_l b)

         | |- ?a * ?b <= ?a * ?c => apply Rmult_le_compat_l
         | |- ?a * ?b <= ?c * ?b => apply Rmult_le_compat_r
         | |- ?a * ?b <= ?c * ?d => apply Rmult_le_compat
         | |- ?a * ?b * ?c <= ?b => rewrite -{2}(Rmult_1_r b)

         (* < *)
         | |- 0 < _ * _ => apply Rmult_gt_0_compat
         | |- ?a * ?b < ?a * ?c => apply Rmult_lt_compat_l
         | |- ?a * ?b < ?c * ?b => apply Rmult_lt_compat_r

         (* = *)
         | H : ?r1 + ?r = ?r2 + ?r |- _ =>
             (apply Rplus_eq_reg_r in H; subst)
         | H : ?a = ?a * ?b |- _ =>
             (rewrite -{1}(Rmult_1_r a) in H; apply Rmult_eq_reg_l in H)

         (* simplifications *)
         | |- context[?a * (?b * ?c)] => rewrite -Rmult_assoc
         | |- context[_ > _] => rewrite /Rgt
         | H : context[_ > _] |- _ => rewrite /Rgt in H

         (* general solving patterns *)
         | H : _ <= _ <= _ |-  _  => destruct H
         | |- ∀ _, _ => intros
         | |- context [@bool_decide ?P ?dec] =>
             destruct_decide (@bool_decide_reflect P dec); simplify_eq
         | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
         | _ => done || lra || eauto
         end.
