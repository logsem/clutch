From Coq Require Import Reals Psatz.
From self.prelude Require Import base.

(* Notation "x ≤ y" := (Rle x y) (at level 70, no associativity) : R_scope. *)
(* Notation "x ≥ y" := (Rge x y) (at level 70, no associativity) : R_scope.u *)

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
