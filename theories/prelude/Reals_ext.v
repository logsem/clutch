From Coq Require Import Reals Psatz.
From self.prelude Require Import base.

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
