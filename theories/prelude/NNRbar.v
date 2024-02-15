(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import Reals ssreflect.
From clutch.prelude Require Export classical.

(*Require Import Rcomplements.*)

(** This file contains the definition and properties of the set
 [R] # &#8746; {+ &infin;} &#8746; {- &infin;} # denoted by [Rbar]. We have defined:
  - coercions from [R] to [Rbar] and vice versa ([Finite] gives [R0] at infinity points)
  - an order [Rbar_lt] and [Rbar_le]
  - total operations: [Rbar_opp], [Rbar_plus], [Rbar_minus], [Rbar_inv], [Rbar_min] and [Rbar_abs]
  - lemmas about the decidability of the order and properties of the operations (such as [Rbar_plus_comm] or [Rbar_plus_lt_compat])
 *)


Open Scope R_scope.


(* Operations for nonnegreals *)


Section nnreals.


Implicit Type (x y : nonnegreal).

Program Definition nnreal_plus x y : nonnegreal :=
  mknonnegreal (x + y) _.
Next Obligation.
  destruct x as [x Hx].
  destruct y as [y Hy].
  apply Rplus_le_le_0_compat; auto.
Qed.


Program Definition nnreal_mult x y : nonnegreal :=
  mknonnegreal (x * y) _.
Next Obligation.
  destruct x as [x Hx].
  destruct y as [y Hy].
  apply Rmult_le_pos; auto.
Qed.

Program Definition nnreal_minus x y (_ : (nonneg y <= nonneg x)) : nonnegreal :=
  mknonnegreal (x - y) _.
Next Obligation.
  intros x y Hxy.
  destruct x as [x Hx].
  destruct y as [y Hy].
  apply Rge_le, Rge_minus, Rle_ge; auto.
Qed.

Program Definition nnreal_inv x : nonnegreal :=
  mknonnegreal (/x) _.
Next Obligation.
  destruct x as [x Hx].
  destruct Hx as [Hlt | Heq].
  + left; apply Rinv_0_lt_compat; auto.
  + right; simpl; rewrite <- Heq; rewrite Rinv_0; auto.
Qed.

Program Definition nnreal_div x y : nonnegreal :=
  nnreal_mult x (nnreal_inv y).

Definition nnreal_zero : nonnegreal := mknonnegreal 0 (Rle_refl 0).
Definition nnreal_one : nonnegreal := mknonnegreal 1 (Rle_0_1).

Program Definition nnreal_nat (n : nat) : nonnegreal :=
  mknonnegreal (INR n) _.
Next Obligation.
  intro.
  apply pos_INR.
Qed.


Program Definition nnreal_half : nonnegreal := mknonnegreal (/2) _.
Next Obligation.
  left. apply pos_half_prf.
Qed.

Definition pos_to_nn (p : posreal) : nonnegreal := mknonnegreal p.(pos) (Rlt_le 0 p.(pos) p.(cond_pos)).

(* Uses proof irrelevance *)
Lemma nnreal_ext x y : x.(nonneg) = y.(nonneg) -> x = y.
Proof.
  destruct x as [x Hx], y as [y Hy] =>/=.
  intros ->.
  f_equal; auto.
  apply proof_irrelevance.
Qed.

Lemma nnreal_le_0 x : x <= 0 -> x = nnreal_zero.
Proof.
  destruct x as (x & Hxnn).
  simpl.
  intro Hxle.
  pose proof (Rle_antisym 0 x Hxnn Hxle) as Heq.
  rewrite /nnreal_zero.
  apply nnreal_ext; auto.
Qed.


Lemma nnreal_plus_comm (x y :nonnegreal) :
  nnreal_plus x y = nnreal_plus y x.
Proof.
  apply nnreal_ext.
  apply Rplus_comm.
Qed.

(* TODO: Make these notations work *)


End nnreals.


Declare Scope NNR_scope.
Delimit Scope NNR_scope with NNR.

Infix "+" := nnreal_plus : NNR_scope.
Infix "*" := nnreal_mult : NNR_scope.

(** * Definitions *)

Inductive NNRbar :=
  | Finite : nonnegreal -> NNRbar
  | p_infty : NNRbar.

(* TODO: Decide if we want coercions to reals
   or to nonnegreals
*)


Definition NNRbar_to_real (x : NNRbar) :=
  match x with
    | Finite x => x.(nonneg)
    | _ => 0
  end.
Coercion Finite : nonnegreal >-> NNRbar.
Coercion NNRbar_to_real : NNRbar >-> R.

(*Definition is_finite (x : NNRbar) := Finite (real x) = x.
Lemma is_finite_correct (x : Rbar) :
  is_finite x <-> exists y : R, x = Finite y.
Proof.
  rewrite /is_finite ;
  case: x => /= ; split => // H.
  by exists r.
  by case: H.
  by case: H.
Qed.
*)

(** ** Order *)

Definition NNRbar_lt (x y : NNRbar) : Prop :=
  match x,y with
    | p_infty, _  => False
    |  _, p_infty => True
    | Finite x, Finite y => Rlt x y
  end.

Definition NNRbar_le (x y : NNRbar) : Prop :=
  match x,y with
    |  _, p_infty => True
    | p_infty, _  => False
    | Finite x, Finite y => Rle x y
  end.

(** ** Operations *)
(** *** Additive operators *)

(*
Definition Rbar_opp (x : Rbar) :=
  match x with
    | Finite x => Finite (-x)
    | p_infty => m_infty
    | m_infty => p_infty
  end.
*)

Definition NNRbar_plus (x y : NNRbar) :=
  match x,y with
    | p_infty, _ | _, p_infty => p_infty
    | Finite x', Finite y' => Finite (nnreal_plus x' y')
  end.

(*
Definition Rbar_plus (x y : Rbar) :=
  match Rbar_plus' x y with Some z => z | None => Finite 0 end.
Arguments Rbar_plus !x !y /.
Definition is_Rbar_plus (x y z : Rbar) : Prop :=
  Rbar_plus' x y = Some z.
Definition ex_Rbar_plus (x y : Rbar) : Prop :=
  match Rbar_plus' x y with Some _ => True | None => False end.
Arguments ex_Rbar_plus !x !y /.

Lemma is_Rbar_plus_unique (x y z : Rbar) :
  is_Rbar_plus x y z -> Rbar_plus x y = z.
Proof.
  unfold is_Rbar_plus, ex_Rbar_plus, Rbar_plus.
  case: Rbar_plus' => // a Ha.
  by inversion Ha.
Qed.
Lemma Rbar_plus_correct (x y : Rbar) :
  ex_Rbar_plus x y -> is_Rbar_plus x y (Rbar_plus x y).
Proof.
  unfold is_Rbar_plus, ex_Rbar_plus, Rbar_plus.
  by case: Rbar_plus'.
Qed.

Definition Rbar_minus (x y : Rbar) := Rbar_plus x (Rbar_opp y).
Arguments Rbar_minus !x !y /.
Definition is_Rbar_minus (x y z : Rbar) : Prop :=
  is_Rbar_plus x (Rbar_opp y) z.
Definition ex_Rbar_minus (x y : Rbar) : Prop :=
  ex_Rbar_plus x (Rbar_opp y).
Arguments ex_Rbar_minus !x !y /.
*)

(** *** Multiplicative operators *)

Definition NNRbar_inv (x : NNRbar) : NNRbar :=
  match x with
    | Finite x => Finite (nnreal_inv x)
    | _ => Finite (nnreal_zero)
  end.


Definition NNRbar_mult' (x y : NNRbar) :=
  match x with
    | Finite x => match y with
      | Finite y => Some (Finite (nnreal_mult x y))
      | p_infty => match (Rle_dec x 0) with
        (* If x <=0, x=0 and we make 0*infty undefined *)
        | left _ => None
        | right _ => Some p_infty
      end
    end
    | p_infty => match y with
      | Finite y => match (Rle_dec y 0) with
        | left _ => None
        | right _ => Some p_infty
      end
      | p_infty => Some p_infty
    end
  end.
Definition NNRbar_mult (x y : NNRbar) :=
  match NNRbar_mult' x y with Some z => z | None => Finite nnreal_zero end.
Arguments NNRbar_mult !x !y /.


Definition is_NNRbar_mult (x y z : NNRbar) : Prop :=
  NNRbar_mult' x y = Some z.
Definition ex_NNRbar_mult (x y : NNRbar) : Prop :=
  match x with
    | Finite x => match y with
      | Finite y => True
      | p_infty => x <> nnreal_zero
    end
    | p_infty => match y with
      | Finite y => y <> nnreal_zero
      | p_infty => True
    end
  end.
Arguments ex_NNRbar_mult !x !y /.

Definition NNRbar_mult_pos (x : NNRbar) (y : posreal) :=
  match x with
    | Finite x => Finite (nnreal_mult x (pos_to_nn y))
    | _ => x
  end.

Lemma is_NNRbar_mult_unique (x y z : NNRbar) :
  is_NNRbar_mult x y z -> NNRbar_mult x y = z.
Proof.
  unfold is_NNRbar_mult.
  case: x => [x | ] ;
  case: y => [y | ] ;
  case: z => [z | ] //= H;
  inversion H => // ;
  case: Rle_dec H => // H0 ;
  case: Rle_lt_or_eq_dec => //.
Qed.
Lemma Rbar_mult_correct (x y : NNRbar) :
  ex_NNRbar_mult x y -> is_NNRbar_mult x y (NNRbar_mult x y).
Proof.
  case: x => [x | ] ;
  case: y => [y | ] //= H ;
  apply sym_not_eq in H ;
  unfold is_NNRbar_mult ; simpl ;
  case: Rle_dec => // H0 .
  (* AA: Can we make this cleaner? *)
  + destruct H; symmetry; apply nnreal_le_0; auto.
  + destruct H; symmetry; apply nnreal_le_0; auto.
Qed.

Lemma Rbar_mult_correct' (x y z : NNRbar) :
  is_NNRbar_mult x y z -> ex_NNRbar_mult x y.
Proof.
  unfold is_NNRbar_mult ;
  case: x => [x | ] ;
  case: y => [y | ] //= ;
  case: Rle_dec => //= H ; try (case: Rle_lt_or_eq_dec => //=) ; intros.
  + intro Hx; destruct H; rewrite Hx; simpl; apply Rle_refl.
  + intro Hy; destruct H; rewrite Hy; simpl; apply Rle_refl.
Qed.


Definition NNRbar_div (x y : NNRbar) : NNRbar :=
  NNRbar_mult x (NNRbar_inv y).
Arguments NNRbar_div !x !y /.
Definition is_NNRbar_div (x y z : NNRbar) : Prop :=
  is_NNRbar_mult x (NNRbar_inv y) z.
Definition ex_NNRbar_div (x y : NNRbar) : Prop :=
  ex_NNRbar_mult x (NNRbar_inv y).
Arguments ex_NNRbar_div !x !y /.

Definition NNRbar_div_pos (x : NNRbar) (y : posreal) :=
  match x with
    | Finite x => Finite (nnreal_div x (pos_to_nn y))
    | _ => x
  end.

(** * Compatibility with real numbers *)
(** For equality and order.
The compatibility of addition and multiplication is proved in Rbar_seq *)

Lemma NNRbar_finite_eq (x y : nonnegreal) :
  Finite x = Finite y <-> x = y.
Proof.
  split ; intros.
  apply nnreal_ext.
  apply Rle_antisym ; apply Rnot_lt_le ; intro.
  assert (NNRbar_lt (Finite y) (Finite x)).
  simpl ; apply H0.
  rewrite H in H1 ; simpl in H1 ; by apply Rlt_irrefl in H1.
  assert (NNRbar_lt (Finite x) (Finite y)).
  simpl ; apply H0.
  rewrite H in H1 ; simpl in H1 ; by apply Rlt_irrefl in H1.
  rewrite H ; reflexivity.
Qed.

Lemma NNRbar_finite_neq (x y : nonnegreal) :
  Finite x <> Finite y <-> x <> y.
Proof.
  split => H ; contradict H ; by apply NNRbar_finite_eq.
Qed.

(** * Properties of order *)

(** ** Relations between inequalities *)

Lemma NNRbar_lt_not_eq (x y : NNRbar) :
  NNRbar_lt x y -> x<>y.
Proof.
  destruct x ; destruct y ; simpl ; try easy.
  intros H H0.
  apply NNRbar_finite_eq in H0 ; revert H0.
  intro H1.
  apply (Rlt_not_eq _ _ H); auto.
  (* Is there a better way to do this? *)
  rewrite /nonneg /=.
  rewrite H1.
  auto.
Qed.

Lemma NNRbar_not_le_lt (x y : NNRbar) :
  ~ NNRbar_le x y -> NNRbar_lt y x.
  destruct x ; destruct y ; simpl ; intuition. by apply Rnot_le_lt.
Qed.

Lemma NNRbar_lt_not_le (x y : NNRbar) :
  NNRbar_lt y x -> ~ NNRbar_le x y.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  apply (Rlt_irrefl n0).
  now apply Rlt_le_trans with (1 := H).
Qed.

Lemma NNRbar_not_lt_le (x y : NNRbar) :
  ~ NNRbar_lt x y -> NNRbar_le y x.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  now apply Rnot_lt_le.
Qed.

Lemma NNRbar_le_not_lt (x y : NNRbar) :
  NNRbar_le y x -> ~ NNRbar_lt x y.
Proof.
  destruct x ; destruct y ; simpl ; intuition ; contradict H0.
  now apply Rle_not_lt.
Qed.

Lemma NNRbar_le_refl :
  forall x : NNRbar, NNRbar_le x x.
Proof.
intros [x| ] ; try easy.
apply Rle_refl.
Qed.

Lemma NNRbar_lt_le :
  forall x y : NNRbar,
  NNRbar_lt x y -> NNRbar_le x y.
Proof.
  intros [x| ] [y| ] ; try easy.
  apply Rlt_le.
Qed.

(** ** Decidability *)

Lemma NNRbar_total_order (x y : NNRbar) :
  {NNRbar_lt x y} + {x = y} + {NNRbar_lt y x}.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  destruct n as (n & Hn);
  destruct n0 as (n0 & Hn0).
  destruct (total_order_T n n0) as [ [ | -> ] | ]; intuition.
  left; right.
  f_equal.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma NNRbar_eq_dec (x y : NNRbar) :
  {x = y} + {x <> y}.
Proof.
  intros ; destruct (NNRbar_total_order x y) as [[H|H]|H].
  right ; revert H ; destruct x as [x| ] ; destruct y as [y| ] ; simpl ; intros H ;
  try easy.
  contradict H.
  apply NNRbar_finite_eq in H ; try apply Rle_not_lt, Req_le ; auto.
  symmetry; auto.
  rewrite H; done.
  left ; apply H.
  right ; revert H ; destruct x as [x| ] ; destruct y as [y| ] ; simpl ; intros H ;
  try easy.
  contradict H.
  apply NNRbar_finite_eq in H ; apply Rle_not_lt, Req_le ; auto.
  rewrite H; done.
Qed.

Lemma NNRbar_lt_dec (x y : NNRbar) :
  {NNRbar_lt x y} + {~NNRbar_lt x y}.
Proof.
  destruct (NNRbar_total_order x y) as [H|H] ; [ destruct H as [H|H]|].
  now left.
  right ; rewrite H ; clear H ; destruct y ; auto ; apply Rlt_irrefl ; auto.
  right ; revert H ; destruct x as [x | ] ; destruct y as [y | ] ; intros H ; auto ;
  apply Rle_not_lt, Rlt_le ; auto.
Qed.

Lemma NNRbar_lt_le_dec (x y : NNRbar) :
  {NNRbar_lt x y} + {NNRbar_le y x}.
Proof.
  destruct (NNRbar_total_order x y) as [[H|H]|H].
  now left.
  right.
  rewrite H.
  apply NNRbar_le_refl.
  right.
  now apply NNRbar_lt_le.
Qed.

Lemma NNRbar_le_dec (x y : NNRbar) :
  {NNRbar_le x y} + {~NNRbar_le x y}.
Proof.
  destruct (NNRbar_total_order x y) as [[H|H]|H].
  left.
  now apply NNRbar_lt_le.
  left.
  rewrite H.
  apply NNRbar_le_refl.
  right.
  now apply NNRbar_lt_not_le.
Qed.

Lemma NNRbar_le_lt_dec (x y : NNRbar) :
  {NNRbar_le x y} + {NNRbar_lt y x}.
Proof.
  destruct (NNRbar_total_order x y) as [[H|H]|H].
  left.
  now apply NNRbar_lt_le.
  left.
  rewrite H.
  apply NNRbar_le_refl.
  now right.
Qed.

Lemma NNRbar_le_lt_or_eq_dec (x y : NNRbar) :
  NNRbar_le x y -> { NNRbar_lt x y } + { x = y }.
Proof.
  destruct (NNRbar_total_order x y) as [[H|H]|H].
  now left.
  now right.
  intros K.
  now elim (NNRbar_le_not_lt _ _ K).
Qed.

(** ** Transitivity *)

Lemma NNRbar_lt_trans (x y z : NNRbar) :
  NNRbar_lt x y -> NNRbar_lt y z -> NNRbar_lt x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  now apply Rlt_trans with n0.
Qed.

Lemma NNRbar_lt_le_trans (x y z : NNRbar) :
  NNRbar_lt x y -> NNRbar_le y z -> NNRbar_lt x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  now apply Rlt_le_trans with n0.
Qed.

Lemma NNRbar_le_lt_trans (x y z : NNRbar) :
  NNRbar_le x y -> NNRbar_lt y z -> NNRbar_lt x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  now apply Rle_lt_trans with n0.
Qed.

Lemma NNRbar_le_trans (x y z : NNRbar) :
  NNRbar_le x y -> NNRbar_le y z -> NNRbar_le x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  now apply Rle_trans with n0.
Qed.

Lemma NNRbar_le_antisym (x y : NNRbar) :
  NNRbar_le x y -> NNRbar_le y x -> x = y.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  assert (nonneg n = nonneg n0) as H1. 1: by apply Rle_antisym.
  assert (n = n0) as ->; auto.
  apply nnreal_ext; auto.
Qed.

(** * Properties of operations *)
(** ** Additive operators *)

(*
(** *** Rbar_opp *)

Lemma Rbar_opp_involutive (x : Rbar) : (Rbar_opp (Rbar_opp x)) = x.
Proof.
  destruct x as [x| | ] ; auto ; simpl ; rewrite Ropp_involutive ; auto.
Qed.

Lemma Rbar_opp_lt (x y : Rbar) : Rbar_lt (Rbar_opp x) (Rbar_opp y) <-> Rbar_lt y x.
Proof.
  destruct x as [x | | ] ; destruct y as [y | | ] ;
  split ; auto ; intro H ; simpl ; try left.
  apply Ropp_lt_cancel ; auto.
  apply Ropp_lt_contravar ; auto.
Qed.

Lemma Rbar_opp_le (x y : Rbar) : Rbar_le (Rbar_opp x) (Rbar_opp y) <-> Rbar_le y x.
Proof.
  destruct x as [x| |] ; destruct y as [y| |] ; simpl ; intuition.
Qed.

Lemma Rbar_opp_eq (x y : Rbar) : (Rbar_opp x) = (Rbar_opp y) <-> x = y.
Proof.
  split ; intros H.
  rewrite <- (Rbar_opp_involutive x), H, Rbar_opp_involutive ; reflexivity.
  rewrite H ; reflexivity.
Qed.

Lemma Rbar_opp_real (x : Rbar) : real (Rbar_opp x) = - real x.
Proof.
  destruct x as [x | | ] ; simpl ; intuition.
Qed.
*)

(** *** NNRbar_plus *)

Lemma NNRbar_plus_comm :
  forall x y, NNRbar_plus x y = NNRbar_plus y x.
Proof.
intros [x| ] [y| ] ; try reflexivity.
apply (f_equal (fun x => (Finite x))).
rewrite /nnreal_plus /=.
apply nnreal_ext.
rewrite /nonneg /=.
apply Rplus_comm.
Qed.

(*
Lemma ex_NNRbar_plus_comm :
  forall x y,
  ex_NNRbar_plus x y -> ex_NNRbar_plus y x.
Proof.
now intros [x| |] [y| |].
Qed.

Lemma ex_NNRbar_plus_opp (x y : NNRbar) :
  ex_NNRbar_plus x y -> ex_NNRbar_plus (NNRbar_opp x) (NNRbar_opp y).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] => //.
Qed.
*)

Lemma NNRbar_plus_0_r (x : NNRbar) : NNRbar_plus x (Finite nnreal_zero) = x.
Proof.
  case: x => //= ; intuition.
  f_equal.
  rewrite /nnreal_plus.
  apply nnreal_ext.
  rewrite /nonneg /=.
  destruct n. apply Rplus_0_r.
Qed.

Lemma NNRbar_plus_0_l (x : NNRbar) : NNRbar_plus (Finite nnreal_zero) x = x.
Proof.
  case: x => //= ; intuition.
  f_equal.
  rewrite /nnreal_plus.
  apply nnreal_ext.
  rewrite /nonneg /=.
  destruct n. apply Rplus_0_l.
Qed.

(*
Lemma NNRbar_plus_comm (x y : NNRbar) : NNRbar_plus x y = NNRbar_plus y x.
Proof.
  case x ; case y ; intuition.
  simpl.
  apply f_equal, Rplus_comm.
Qed.
*)

Lemma NNRbar_plus_lt_compat (a b c d : NNRbar) :
  NNRbar_lt a b -> NNRbar_lt c d -> NNRbar_lt (NNRbar_plus a c) (NNRbar_plus b d).
Proof.
  case: a => [a |  ] // ; case: b => [b |  ] // ;
  case: c => [c |  ] // ; case: d => [d |  ] // ;
  apply Rplus_lt_compat.
Qed.

Lemma NNRbar_plus_le_compat (a b c d : NNRbar) :
  NNRbar_le a b -> NNRbar_le c d -> NNRbar_le (NNRbar_plus a c) (NNRbar_plus b d).
Proof.
  case: a => [a |  ] // ; case: b => [b |  ] // ;
  case: c => [c |  ] // ; case: d => [d |  ] //.
  apply Rplus_le_compat.
Qed.

(*
Lemma NNRbar_plus_opp (x y : NNRbar) :
  NNRbar_plus (NNRbar_opp x) (NNRbar_opp y) = NNRbar_opp (NNRbar_plus x y).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= ; apply f_equal ; ring.
Qed.
*)


(*
(** *** Rbar_minus *)

Lemma NNRbar_minus_eq_0 (x : NNRbar) : NNRbar_minus x x = 0.
Proof.
  case: x => //= x ; by apply f_equal, Rcomplements.Rminus_eq_0.
Qed.
Lemma NNRbar_opp_minus (x y : NNRbar) :
  NNRbar_opp (NNRbar_minus x y) = NNRbar_minus y x.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //=.
  by rewrite Ropp_minus_distr'.
  by rewrite Ropp_0.
  by rewrite Ropp_0.
Qed.
*)

(** ** Multiplicative *)

(** *** Rbar_inv *)

(*
Lemma NNRbar_inv_opp (x : NNRbar) :
  x <> 0 -> NNRbar_inv (NNRbar_opp x) = NNRbar_opp (NNRbar_inv x).
Proof.
  case: x => [x | | ] /= Hx.
  rewrite Ropp_inv_permute => //.
  contradict Hx.
  by rewrite Hx.
  by rewrite Ropp_0.
  by rewrite Ropp_0.
Qed.
*)

(** *** Rbar_mult *)

Lemma NNRbar_mult'_comm (x y : NNRbar) :
  NNRbar_mult' x y = NNRbar_mult' y x.
Proof.
  case: x => [x |  ] ;
  case: y => [y |  ] //=.
  f_equal.
  f_equal.
  rewrite /nnreal_mult/=.
  apply nnreal_ext.
  rewrite /nonneg/=.
  by rewrite Rmult_comm.
Qed.

(*
Lemma NNRbar_mult'_opp_r (x y : NNRbar) :
  NNRbar_mult' x (NNRbar_opp y) = match NNRbar_mult' x y with Some z => Some (NNRbar_opp z) | None => None end.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= ;
  (try case: Rle_dec => Hx //=) ;
  (try case: Rle_lt_or_eq_dec => //= Hx0).
  by rewrite Ropp_mult_distr_r_reverse.
  rewrite -Ropp_0 in Hx0.
  apply Ropp_lt_cancel in Hx0.
  case Rle_dec => Hy //=.
  now elim Rle_not_lt with (1 := Hy).
  case Rle_dec => Hy //=.
  case Rle_lt_or_eq_dec => Hy0 //=.
  elim Rlt_not_le with (1 := Hy0).
  apply Ropp_le_cancel.
  by rewrite Ropp_0.
  elim Hy.
  apply Ropp_le_cancel.
  rewrite -Hx0 Ropp_0.
  apply Rle_refl.
  case Rle_dec => Hy //=.
  case Rle_lt_or_eq_dec => Hy0 //=.
  elim Hx.
  rewrite -Hy0 Ropp_0.
  apply Rle_refl.
  elim Hx.
  rewrite -Ropp_0.
  apply Ropp_le_contravar.
  apply Rlt_le.
  now apply Rnot_le_lt.
  case Rle_dec => Hy //=.
  elim Rlt_not_le with (1 := Hx0).
  rewrite -Ropp_0.
  now apply Ropp_le_contravar.
  case Rle_dec => Hy //=.
  case Rle_lt_or_eq_dec => Hy0 //=.
  elim Rlt_not_le with (1 := Hy0).
  apply Ropp_le_cancel.
  rewrite -Hx0 Ropp_0.
  apply Rle_refl.
  elim Hy.
  apply Ropp_le_cancel.
  rewrite -Hx0 Ropp_0.
  apply Rle_refl.
  case Rle_dec => Hy //=.
  case Rle_lt_or_eq_dec => Hy0 //=.
  elim Hx.
  rewrite -Hy0 Ropp_0.
  apply Rle_refl.
  elim Hx.
  rewrite -Ropp_0.
  apply Ropp_le_contravar.
  apply Rlt_le.
  now apply Rnot_le_lt.
Qed.
*)

Lemma NNRbar_mult_comm (x y : NNRbar) :
  NNRbar_mult x y = NNRbar_mult y x.
Proof.
  unfold NNRbar_mult.
  by rewrite NNRbar_mult'_comm.
Qed.

(*
Lemma NNRbar_mult_opp_r (x y : NNRbar) :
  NNRbar_mult x (NNRbar_opp y) = (NNRbar_opp (NNRbar_mult x y)).
Proof.
  unfold NNRbar_mult.
  rewrite NNRbar_mult'_opp_r.
  case NNRbar_mult' => //=.
  apply f_equal, eq_sym, Ropp_0.
Qed.
Lemma NNRbar_mult_opp_l (x y : NNRbar) :
  NNRbar_mult (NNRbar_opp x) y = NNRbar_opp (NNRbar_mult x y).
Proof.
  rewrite ?(NNRbar_mult_comm _ y).
  by apply NNRbar_mult_opp_r.
Qed.
Lemma NNRbar_mult_opp (x y : NNRbar) :
  NNRbar_mult (NNRbar_opp x) (NNRbar_opp y) = NNRbar_mult x y.
Proof.
  by rewrite NNRbar_mult_opp_l -NNRbar_mult_opp_r NNRbar_opp_involutive.
Qed.
Lemma NNRbar_mult_0_l (x : NNRbar) : NNRbar_mult 0 x = 0.
Proof.
  case: x => [x | | ] //=.
  by rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
Qed.
Lemma NNRbar_mult_0_r (x : NNRbar) : NNRbar_mult x 0 = 0.
Proof.
  rewrite NNRbar_mult_comm ; by apply NNRbar_mult_0_l.
Qed.
*)

Lemma NNRbar_mult_eq_0 (y x : NNRbar) :
  NNRbar_mult x y = Finite (nnreal_zero) -> x = Finite (nnreal_zero) \/ y = Finite (nnreal_zero).
Proof.
  case: x => [x | ] //= ;
  case: y => [y | ] //= ;
  (try case: Rle_dec => //= H).
  + intros H.
    apply (f_equal NNRbar_to_real) in H.
    simpl in H.
    apply Rmult_integral in H.
    case H as [H1 | H2].
    ++ left.
       f_equal.
       apply nnreal_ext; auto.
    ++ right.
       f_equal.
       apply nnreal_ext; auto.
  + intro H1.
    left.
    f_equal.
    apply nnreal_le_0; auto.
  + intro H1.
    right.
    f_equal.
    apply nnreal_le_0; auto.
Qed.

Lemma ex_NNRbar_mult_sym (x y : NNRbar) :
  ex_NNRbar_mult x y -> ex_NNRbar_mult y x.
Proof.
  case: x => [x | ] ;
  case: y => [y | ] //.
Qed.

(*
Lemma ex_NNRbar_mult_opp_l (x y : NNRbar) :
  ex_NNRbar_mult x y -> ex_NNRbar_mult (NNRbar_opp x) y.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= Hx ;
  by apply Ropp_neq_0_compat.
Qed.
Lemma ex_NNRbar_mult_opp_r (x y : NNRbar) :
  ex_NNRbar_mult x y -> ex_NNRbar_mult x (NNRbar_opp y).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= Hx ;
  by apply Ropp_neq_0_compat.
Qed.
*)

Lemma is_NNRbar_mult_sym (x y z : NNRbar) :
  is_NNRbar_mult x y z -> is_NNRbar_mult y x z.
Proof.
  case: x => [x | ] ;
  case: y => [y | ] ;
  case: z => [z | ] //= ;
  unfold is_NNRbar_mult, NNRbar_mult' ;
  try (case: Rle_dec => // H) ;
  try (case: Rle_lt_or_eq_dec => // H0) ;
  try (case => <-) ; try (move => _).
  f_equal; f_equal.
  rewrite /nnreal_mult /=.
  apply nnreal_ext.
  simpl.
  by rewrite Rmult_comm.
Qed.

(*
Lemma is_NNRbar_mult_opp_l (x y z : NNRbar) :
  is_NNRbar_mult x y z -> is_NNRbar_mult (NNRbar_opp x) y (NNRbar_opp z).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] ;
  case: z => [z | | ] //= ;
  unfold is_NNRbar_mult, NNRbar_mult' ;
  try (case: Rle_dec => // H) ;
  try (case: Rle_lt_or_eq_dec => // H0) ;
  try (case => <-) ; try (move => _).
  apply (f_equal (@Some _)), f_equal ; ring.
  apply Ropp_lt_contravar in H0 ; rewrite Ropp_0 in H0 ;
  now move/Rlt_not_le: H0 ; case: Rle_dec.
  apply Rnot_le_lt, Ropp_lt_contravar in H ; rewrite Ropp_0 in H ;
  move/Rlt_le: (H) ; case: Rle_dec => // H0 _ ;
  now move/Rlt_not_eq: H ; case: Rle_lt_or_eq_dec.
  apply Rnot_le_lt, Ropp_lt_contravar in H ; rewrite Ropp_0 in H ;
  move/Rlt_le: (H) ; case: Rle_dec => // H0 _ ;
  now move/Rlt_not_eq: H ; case: Rle_lt_or_eq_dec.
  apply Ropp_lt_contravar in H0 ; rewrite Ropp_0 in H0 ;
  now move/Rlt_not_le: H0 ; case: Rle_dec.
Qed.
Lemma is_NNRbar_mult_opp_r (x y z : NNRbar) :
  is_NNRbar_mult x y z -> is_NNRbar_mult x (NNRbar_opp y) (NNRbar_opp z).
Proof.
  move/is_NNRbar_mult_sym => H.
  now apply is_NNRbar_mult_sym, is_NNRbar_mult_opp_l.
Qed.
*)

Lemma is_NNRbar_mult_p_infty_pos (x : NNRbar) :
  NNRbar_lt (Finite nnreal_zero) x -> is_NNRbar_mult p_infty x p_infty.
Proof.
  case: x => [x | ] // Hx.
  unfold is_NNRbar_mult, NNRbar_mult'.
  case: Rle_dec (Rlt_le _ _ Hx) => // Hx' _.
  destruct x as [x Hxnn].
  rewrite /NNRbar_lt in Hx.
  rewrite {1}/nonneg /= in Hx.
  rewrite /nonneg/= in Hx'.
  pose proof (Rlt_not_eq _ _ Hx).
  pose proof (Rle_antisym 0 x Hxnn Hx').
  done.
Qed.
(*
Lemma is_NNRbar_mult_p_infty_neg (x : NNRbar) :
  NNRbar_lt x 0 -> is_NNRbar_mult p_infty x m_infty.
Proof.
  case: x => [x | | ] // Hx.
  unfold is_NNRbar_mult, NNRbar_mult'.
  case: Rle_dec (Rlt_not_le _ _ Hx) => // Hx' _.
Qed.
Lemma is_NNRbar_mult_m_infty_pos (x : NNRbar) :
  NNRbar_lt 0 x -> is_NNRbar_mult m_infty x m_infty.
Proof.
  case: x => [x | | ] // Hx.
  unfold is_NNRbar_mult, NNRbar_mult'.
  case: Rle_dec (Rlt_le _ _ Hx) => // Hx' _.
  now case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hx).
Qed.
Lemma is_NNRbar_mult_m_infty_neg (x : NNRbar) :
  NNRbar_lt x 0 -> is_NNRbar_mult m_infty x p_infty.
Proof.
  case: x => [x | | ] // Hx.
  unfold is_NNRbar_mult, NNRbar_mult'.
  case: Rle_dec (Rlt_not_le _ _ Hx) => // Hx' _.
Qed.
*)

(** Rbar_div *)

Lemma is_NNRbar_div_p_infty (x : nonnegreal) :
  is_NNRbar_div (Finite x) p_infty (Finite nnreal_zero).
Proof.
  apply (f_equal (@Some _)).
  f_equal.
  rewrite /nnreal_mult/=.
  apply nnreal_ext.
  simpl.
  by rewrite Rmult_0_r.
Qed.

(*
Lemma is_NNRbar_div_m_infty (x : R) :
  is_NNRbar_div x m_infty 0.
Proof.
  apply (f_equal (@Some _)).
  by rewrite Rmult_0_r.
Qed.
*)

(** NNRbar_mult_pos *)

Lemma NNRbar_mult_pos_eq (x y : NNRbar) (z : posreal) :
  x = y <-> (NNRbar_mult_pos x z) = (NNRbar_mult_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | ] ; case: y => [y | ] ;
  split => //= H ; apply NNRbar_finite_eq in H.
  by rewrite H.
  rewrite /nnreal_mult /= in H.
  apply NNRbar_finite_eq.
  apply (f_equal nonneg) in H.
  simpl in H.
  apply nnreal_ext; simpl.
  apply (Rmult_eq_reg_r (z)) => //.
  by apply Rgt_not_eq.
Qed.

Lemma NNRbar_mult_pos_lt (x y : NNRbar) (z : posreal) :
  NNRbar_lt x y <-> NNRbar_lt (NNRbar_mult_pos x z) (NNRbar_mult_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | ] ; case: y => [y | ] ;
  split => //= H.
  apply (Rmult_lt_compat_r (z)) => //.
  apply (Rmult_lt_reg_r (z)) => //.
Qed.

Lemma NNRbar_mult_pos_le (x y : NNRbar) (z : posreal) :
  NNRbar_le x y <-> NNRbar_le (NNRbar_mult_pos x z) (NNRbar_mult_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | ] ; case: y => [y | ] ;
  split => //= H.
  apply Rmult_le_compat_r with (2 := H).
  now apply Rlt_le.
  now apply Rmult_le_reg_r with (2 := H).
Qed.

(** NNRbar_div_pos *)

Lemma NNRbar_div_pos_eq (x y : NNRbar) (z : posreal) :
  x = y <-> (NNRbar_div_pos x z) = (NNRbar_div_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | ] ; case: y => [y | ] ;
  split => //= H ; apply NNRbar_finite_eq in H.
  by rewrite H.
  f_equal.
  apply (f_equal nonneg) in H.
  simpl in H.
  apply nnreal_ext; simpl.
  apply (Rmult_eq_reg_r (/z)) => // ;
  by apply Rgt_not_eq, Rinv_0_lt_compat.
Qed.

Lemma NNRbar_div_pos_lt (x y : NNRbar) (z : posreal) :
  NNRbar_lt x y <-> NNRbar_lt (NNRbar_div_pos x z) (NNRbar_div_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | ] ; case: y => [y | ] ;
  split => //= H.
  apply (Rmult_lt_compat_r (/z)) => // ; by apply Rinv_0_lt_compat.
  apply (Rmult_lt_reg_r (/z)) => // ; by apply Rinv_0_lt_compat.
Qed.

Lemma NNRbar_div_pos_le (x y : NNRbar) (z : posreal) :
  NNRbar_le x y <-> NNRbar_le (NNRbar_div_pos x z) (NNRbar_div_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | ] ; case: y => [y | ] ;
  split => //= H.
  apply Rmult_le_compat_r with (2 := H).
  now apply Rlt_le, Rinv_0_lt_compat.
  apply Rmult_le_reg_r with (2 := H).
  now apply Rinv_0_lt_compat.
Qed.

(** * NNRbar_min *)

Definition NNRbar_min (x y : NNRbar) : NNRbar :=
  match x, y with
  | z, p_infty | p_infty, z => z
  | Finite x, Finite y =>
      match (Rle_dec x y) with
      | left _ => Finite x
      | right _ => Finite y
      end
  end.

(*
Let's skip this for now, I don't know if we need it


Lemma NNRbar_lt_locally (a b : NNRbar) (x : R) :
  NNRbar_lt a x -> NNRbar_lt x b ->
  exists delta : posreal,
    forall y, Rabs (y - x) < delta -> NNRbar_lt a y /\ NNRbar_lt y b.
Proof.
  case: a => [ a /= Ha | | _ ] //= ; (try apply Rminus_lt_0 in Ha) ;
  case: b => [ b Hb | _ | ] //= ; (try apply Rminus_lt_0 in Hb).
  assert (0 < Rmin (x - a) (b - x)).
    by apply Rmin_case.
  exists (mkposreal _ H) => y /= Hy ; split.
  apply Rplus_lt_reg_r with (-x).
  replace (a+-x) with (-(x-a)) by ring.
  apply (Rabs_lt_between (y - x)).
  apply Rlt_le_trans with (1 := Hy).
  by apply Rmin_l.
  apply Rplus_lt_reg_r with (-x).
  apply (Rabs_lt_between (y - x)).
  apply Rlt_le_trans with (1 := Hy).
  by apply Rmin_r.
  exists (mkposreal _ Ha) => y /= Hy ; split => //.
  apply Rplus_lt_reg_r with (-x).
  replace (a+-x) with (-(x-a)) by ring.
  by apply (Rabs_lt_between (y - x)).
  exists (mkposreal _ Hb) => y /= Hy ; split => //.
  apply Rplus_lt_reg_r with (-x).
  by apply (Rabs_lt_between (y - x)).
  exists (mkposreal _ Rlt_0_1) ; by split.
Qed.

Lemma NNRbar_min_comm (x y : NNRbar) : NNRbar_min x y = NNRbar_min y x.
Proof.
  case: x => [x | | ] //= ;
  case: y => [y | | ] //=.
  by rewrite Rmin_comm.
Qed.

Lemma NNRbar_min_r (x y : NNRbar) : NNRbar_le (NNRbar_min x y) y.
Proof.
  case: x => [x | | ] //= ;
  case: y => [y | | ] //=.
  by apply Rmin_r.
  by apply Rle_refl.
Qed.

Lemma NNRbar_min_l (x y : NNRbar) : NNRbar_le (NNRbar_min x y) x.
Proof.
  rewrite NNRbar_min_comm.
  by apply NNRbar_min_r.
Qed.

Lemma NNRbar_min_case (x y : NNRbar) (P : NNRbar -> Type) :
  P x -> P y -> P (NNRbar_min x y).
Proof.
  case: x => [x | | ] //= ;
  case: y => [y | | ] //=.
  by apply Rmin_case.
Qed.
Lemma NNRbar_min_case_strong (r1 r2 : NNRbar) (P : NNRbar -> Type) :
  (NNRbar_le r1 r2 -> P r1) -> (NNRbar_le r2 r1 -> P r2)
    -> P (NNRbar_min r1 r2).
Proof.
  case: r1 => [x | | ] //= ;
  case: r2 => [y | | ] //= Hx Hy ;
  (try by apply Hx) ; (try by apply Hy).
  by apply Rmin_case_strong.
Qed.

*)

(*
(** * Rbar_abs *)

Definition Rbar_abs (x : Rbar) :=
  match x with
    | Finite x => Finite (Rabs x)
    | _ => p_infty
  end.

Lemma Rbar_abs_lt_between (x y : Rbar) :
  Rbar_lt (Rbar_abs x) y <-> (Rbar_lt (Rbar_opp y) x /\ Rbar_lt x y).
Proof.
  case: x => [x | | ] ; case: y => [y | | ] /= ; try by intuition.
  by apply Rabs_lt_between.
Qed.

Lemma Rbar_abs_opp (x : Rbar) :
  Rbar_abs (Rbar_opp x) = Rbar_abs x.
Proof.
  case: x => [x | | ] //=.
  by rewrite Rabs_Ropp.
Qed.

Lemma Rbar_abs_pos (x : Rbar) :
  Rbar_le 0 x -> Rbar_abs x = x.
Proof.
  case: x => [x | | ] //= Hx.
  by apply f_equal, Rabs_pos_eq.
Qed.
Lemma Rbar_abs_neg (x : Rbar) :
  Rbar_le x 0 -> Rbar_abs x = Rbar_opp x.
Proof.
  case: x => [x | | ] //= Hx.
  rewrite -Rabs_Ropp.
  apply f_equal, Rabs_pos_eq.
  now rewrite -Ropp_0 ; apply Ropp_le_contravar.
Qed.
*)
