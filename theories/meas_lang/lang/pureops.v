(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From Coq Require Export ssrfun.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

Local Notation RR := ((R : realType) : measurableType _)%type.

Section arithmetic.
(** Arithmetic functions bug given measurale types *)

Definition neg_bool   : <<discr bool>> -> <<discr bool>> := negb.
Definition neg_int    : <<discr Z>> -> <<discr Z>>  := Z.lnot.
Definition minus_int  : <<discr Z>> -> <<discr Z>>  := Z.opp.
Definition minus_real : RR -> RR := Ropp.

Definition loc_offset : (<<discr loc>> * <<discr Z>>)%type -> <<discr loc>> := uncurry (fun x y => x +ₗ y).
Definition loc_le : (<<discr loc>> * <<discr loc>>)%type -> <<discr loc>>. Admitted.
Definition loc_lt : (<<discr loc>> * <<discr loc>>)%type -> <<discr loc>>. Admitted.


Definition plus_real : (RR * RR)%type -> RR := uncurry Rplus.
Definition sub_real  : (RR * RR)%type -> RR := uncurry Rminus.
Definition le_real   : (RR * RR)%type -> <<discr bool>>. Admitted.
Definition lt_real   : (RR * RR)%type -> <<discr bool>>. Admitted.
Definition eq_real   : (RR * RR)%type -> <<discr bool>>. Admitted.

Lemma neg_bool_meas_fun   : measurable_fun setT neg_bool. Admitted.
Lemma neg_int_meas_fun    : measurable_fun setT neg_int. Admitted.
Lemma minus_int_meas_fun  : measurable_fun setT minus_int. Admitted.
Lemma minus_real_meas_fun : measurable_fun setT minus_real. Admitted.
Lemma loc_offset_meas_fun : measurable_fun setT loc_offset. Admitted.
Lemma loc_le_meas_fun     : measurable_fun setT loc_le. Admitted.
Lemma loc_lt_meas_fun     : measurable_fun setT loc_lt. Admitted.
Lemma plus_real_meas_fun  : measurable_fun setT loc_offset. Admitted.
Lemma sub_real_meas_fun   : measurable_fun setT loc_offset. Admitted.
Lemma le_real_meas_fun    : measurable_fun setT loc_offset. Admitted.
Lemma lt_real_meas_fun    : measurable_fun setT loc_offset. Admitted.
Lemma eq_real_meas_fun    : measurable_fun setT loc_offset. Admitted.

Hint Resolve neg_bool_meas_fun   : mf_fun.
Hint Resolve neg_int_meas_fun    : mf_fun.
Hint Resolve minus_int_meas_fun  : mf_fun.
Hint Resolve minus_real_meas_fun : mf_fun.
Hint Resolve loc_offset_meas_fun : mf_fun.
Hint Resolve loc_le_meas_fun     : mf_fun.
Hint Resolve loc_lt_meas_fun     : mf_fun.
Hint Resolve plus_real_meas_fun  : mf_fun.
Hint Resolve sub_real_meas_fun   : mf_fun.
Hint Resolve le_real_meas_fun    : mf_fun.
Hint Resolve lt_real_meas_fun    : mf_fun.
Hint Resolve eq_real_meas_fun    : mf_fun.

End arithmetic.

(* un_op_eval: Normal (reducible) version *)
Definition un_op_eval (op : <<discr un_op>>) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt z) => Some $ LitV $ LitInt (Z.lnot z)
  | MinusUnOp, LitV (LitInt z) => Some $ LitV $ LitInt (- z)%Z
  | MinusUnOp, LitV (LitReal r) => Some $ LitV $ LitReal (- r)%R
  | _, _ => None
  end.

Definition un_op_eval'_cov_neg_bool : set (<<discr un_op>> * val) :=
  setX [set (NegOp : <<discr un_op>>)] (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitBool).

Definition un_op_eval'_cov_neg_int : set (<<discr un_op>> * val) :=
  setX [set NegOp] (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitInt).

Definition un_op_eval'_cov_minus_int : set (<<discr un_op>> * val) :=
  setX [set MinusUnOp] (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitInt).

Definition un_op_eval'_cov_minus_real : set (<<discr un_op>> * val) :=
  setX [set MinusUnOp] (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitReal).

Lemma un_op_eval'_cov_neg_bool_meas_set : measurable un_op_eval'_cov_neg_bool.
Proof. by ms_unfold; ms_solve. Qed.

Lemma un_op_eval'_cov_neg_int_meas_set : measurable un_op_eval'_cov_neg_int.
Proof. by ms_unfold; ms_solve. Qed.

Lemma un_op_eval'_cov_minus_int_meas_set : measurable un_op_eval'_cov_minus_int.
Proof. by ms_unfold; ms_solve. Qed.

Lemma un_op_eval'_cov_minus_real_meas_set : measurable un_op_eval'_cov_minus_real.
Proof. by ms_unfold; ms_solve. Qed.

Hint Resolve un_op_eval'_cov_neg_bool_meas_set   : mf_set.
Hint Resolve un_op_eval'_cov_neg_int_meas_set    : mf_set.
Hint Resolve un_op_eval'_cov_minus_int_meas_set  : mf_set.
Hint Resolve un_op_eval'_cov_minus_real_meas_set : mf_set.

Definition un_op_eval'_neg_bool : (<<discr un_op>> * val) -> option val :=
  Some \o LitVU \o LitBoolU \o neg_bool \o 𝜋_LitBool_b \o 𝜋_LitV_v \o snd.

Definition un_op_eval'_neg_int : (<<discr un_op>> * val) -> option val :=
  Some \o LitVU \o LitIntU \o neg_int \o 𝜋_LitInt_z \o 𝜋_LitV_v \o snd.

Definition un_op_eval'_minus_int : (<<discr un_op>> * val) -> option val :=
  Some \o LitVU \o LitIntU \o minus_int \o 𝜋_LitInt_z \o 𝜋_LitV_v \o snd.

Definition un_op_eval'_minus_real : (<<discr un_op>> * val) -> option val :=
  Some \o LitVU \o LitRealU \o minus_real \o 𝜋_LitReal_r \o 𝜋_LitV_v \o snd.

Create HintDb projection_subs.

Lemma un_op_eval'_neg_bool_meas_fun : measurable_fun un_op_eval'_cov_neg_bool un_op_eval'_neg_bool.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_snd.
  mf_cmp_tree; first by apply 𝜋_LitV_v_sub.
  mf_cmp_tree.
  mf_cmp_tree.
  mf_cmp_tree.
  mf_cmp_tree.
  { by apply Some_meas_fun. }
  { by apply LitVU_meas_fun. }
Qed.

Lemma un_op_eval'_neg_int_meas_fun : measurable_fun un_op_eval'_cov_neg_int un_op_eval'_neg_int.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_snd.
  mf_cmp_tree; first by apply 𝜋_LitV_v_sub.
  mf_cmp_tree.
  mf_cmp_tree.
  mf_cmp_tree.
  mf_cmp_tree.
  { by apply Some_meas_fun. }
  { by apply LitVU_meas_fun. }
Qed.

Lemma un_op_eval'_minus_int_meas_fun : measurable_fun un_op_eval'_cov_minus_int un_op_eval'_minus_int.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_snd.
  mf_cmp_tree; first by apply 𝜋_LitV_v_sub.
  mf_cmp_tree.
  mf_cmp_tree.
  mf_cmp_tree.
  mf_cmp_tree.
  { by apply Some_meas_fun. }
  { by apply LitVU_meas_fun. }
Qed.

Lemma un_op_eval'_minus_real_meas_fun : measurable_fun un_op_eval'_cov_minus_real un_op_eval'_minus_real.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_snd.
  mf_cmp_tree; first by apply 𝜋_LitV_v_sub.
  mf_cmp_tree.
  mf_cmp_tree; last by apply minus_real_meas_fun.
  mf_cmp_tree; last by apply LitRealU_meas_fun.
  mf_cmp_tree.
  { by apply Some_meas_fun. }
  { by apply LitVU_meas_fun. }
Qed.

(* NOTE: Only ever put composite proofs that start with mf_unfold_dom; mf_unfold_fun into mf_fun. *)
Hint Resolve un_op_eval'_neg_bool_meas_fun   : mf_fun.
Hint Resolve un_op_eval'_neg_int_meas_fun    : mf_fun.
Hint Resolve un_op_eval'_minus_int_meas_fun  : mf_fun.
Hint Resolve un_op_eval'_minus_real_meas_fun : mf_fun.


(* un_op_eval: Measurable version *)
Definition un_op_eval' : (<<discr un_op>> * val)%type -> option val :=
  if_in un_op_eval'_cov_neg_bool    un_op_eval'_neg_bool   $
  if_in un_op_eval'_cov_neg_int     un_op_eval'_neg_int    $
  if_in un_op_eval'_cov_minus_int   un_op_eval'_minus_int  $
  if_in un_op_eval'_cov_minus_real  un_op_eval'_minus_real $
  cst None.

Lemma un_op_eval'_meas_fun : measurable_fun setT un_op_eval'.
Proof.
  mf_unfold_fun.
  (* ifIn_meas_fun is wrong.

  have X := (@if_in_meas_fun _ _ _ _ setT).
  eapply X; clear X.
  { by ms_done. }
  { by ms_done. }
  { by rewrite setTI; mf_done. }
  simpl.
  Set Printing Parentheses.
*)
Admitted.


(* TODO: Make sure this is the right theorem first *)
Lemma un_op_eval_eq (op : <<discr un_op>>) (v : val) : un_op_eval op v = un_op_eval' (op, v).
Proof. Admitted.

(* Only one version of bin_op_eval_int because its uncurry is measurable *)
Definition bin_op_eval_int (op : <<discr bin_op>>) (n1 n2 : <<discr Z>>) : base_lit :=
  match op with
  | PlusOp => LitInt (n1 + n2)
  | MinusOp => LitInt (n1 - n2)
  | MultOp => LitInt (n1 * n2)
  | QuotOp => LitInt (n1 `quot` n2)
  | RemOp => LitInt (n1 `rem` n2)
  | AndOp => LitInt (Z.land n1 n2)
  | OrOp => LitInt (Z.lor n1 n2)
  | XorOp => LitInt (Z.lxor n1 n2)
  | ShiftLOp => LitInt (n1 ≪ n2)
  | ShiftROp => LitInt (n1 ≫ n2)
  | LeOp => LitBool (bool_decide (n1 ≤ n2))
  | LtOp => LitBool (bool_decide (n1 < n2))
  | EqOp => LitBool (bool_decide (n1 = n2))
  | OffsetOp => LitInt (n1 + n2) (* Treat offsets as ints *)
  end%Z.


Lemma bin_op_eval_int_measurable_fun : measurable_fun setT (uncurry (uncurry bin_op_eval_int)).
Proof. (* Product of discrete countable spaces is discrete *) Admitted.

(* Only one version of bin_op_eval_bool because its uncurry is measurable *)
Definition bin_op_eval_bool (op : <<discr bin_op>>) (b1 b2 : <<discr bool>>) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp => None
  end.

Lemma bin_op_eval_bool_measurable_fun : measurable_fun setT (uncurry (uncurry bin_op_eval_bool)).
Proof. (* Product of discrete countable spaces is discrete *) Admitted.






Definition bin_op_eval_loc (op : <<discr bin_op>>) (l1 : <<discr loc>>) (v2 : base_lit) : option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
  | LeOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 ≤ₗ l2))
  | LtOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 <ₗ l2))
  | _, _ => None
  end.


Definition bin_op_eval'_loc_cov_offset_int : set (<<discr bin_op>> * <<discr loc>> * base_lit) :=
  setX (setX [set OffsetOp] setT) bcov_LitInt.
Definition bin_op_eval'_loc_cov_le_loc : set (<<discr bin_op>> * <<discr loc>> * base_lit) :=
  setX (setX [set LeOp] setT) bcov_LitLoc.
Definition bin_op_eval'_loc_cov_lt_loc : set (<<discr bin_op>> * <<discr loc>> * base_lit) :=
  setX (setX [set LtOp] setT) bcov_LitLoc.

Lemma bin_op_eval'_loc_cov_offset_int_meas_set : measurable bin_op_eval'_loc_cov_offset_int.
Proof. ms_unfold; ms_prod; [ ms_prod |]; by ms_done. Qed.

Lemma bin_op_eval'_loc_cov_le_loc_meas_set : measurable bin_op_eval'_loc_cov_le_loc.
Proof. ms_unfold; ms_prod; [ ms_prod |]; by ms_done. Qed.

Lemma bin_op_eval'_loc_cov_lt_loc_meas_set : measurable bin_op_eval'_loc_cov_lt_loc.
Proof. ms_unfold; ms_prod; [ ms_prod |]; by ms_done. Qed.

Hint Resolve bin_op_eval'_loc_cov_offset_int_meas_set : mf_set.
Hint Resolve bin_op_eval'_loc_cov_le_loc_meas_set     : mf_set.
Hint Resolve bin_op_eval'_loc_cov_lt_loc_meas_set     : mf_set.

Definition bin_op_eval'_loc_offset_int : (<<discr bin_op>> * <<discr loc>> * base_lit) -> option base_lit :=
  Some \o LitLocU \o loc_offset \o (snd \o fst △ 𝜋_LitInt_z \o snd).

Definition bin_op_eval'_loc_le_loc : (<<discr bin_op>> * <<discr loc>> * base_lit) -> option base_lit :=
  Some \o LitLocU \o loc_le \o (snd \o fst △ 𝜋_LitLoc_l \o snd).

Program Definition bin_op_eval'_loc_lt_loc : (<<discr bin_op>> * <<discr loc>> * base_lit) -> option base_lit :=
  Some \o LitLocU \o loc_lt \o (snd \o fst △ 𝜋_LitLoc_l \o snd).

Lemma bin_op_eval'_loc_offset_int_meas_fun : measurable_fun bin_op_eval'_loc_cov_offset_int bin_op_eval'_loc_offset_int.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree.
  - mf_cmp_tree; last by eapply loc_offset_meas_fun.
    mf_cmp_tree.
    by apply Some_meas_fun.
  - mf_prod.
    + mf_cmp_fst; first by ms_solve.
      eapply (@measurable_snd_restriction _ _ <<discr bin_op>> <<discr loc>>).
      by ms_solve.
    + mf_cmp_snd; first by ms_solve.
      by mf_done.
Qed.

Lemma bin_op_eval'_loc_le_loc_meas_fun : measurable_fun bin_op_eval'_loc_cov_le_loc bin_op_eval'_loc_le_loc.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree.
  - mf_cmp_tree; last by eapply loc_le_meas_fun.
    mf_cmp_tree.
    by apply Some_meas_fun.
  - mf_prod.
    + mf_cmp_fst; first by ms_solve.
      eapply (@measurable_snd_restriction _ _ <<discr bin_op>> <<discr loc>>).
      by ms_solve.
    + mf_cmp_snd; first by ms_solve.
      by mf_done.
Qed.

Lemma bin_op_eval'_loc_lt_loc_meas_fun : measurable_fun bin_op_eval'_loc_cov_lt_loc bin_op_eval'_loc_lt_loc.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree.
  - mf_cmp_tree; last by eapply loc_lt_meas_fun.
    mf_cmp_tree.
    by apply Some_meas_fun.
  - mf_prod.
    + mf_cmp_fst; first by ms_solve.
      eapply (@measurable_snd_restriction _ _ <<discr bin_op>> <<discr loc>>).
      by ms_solve.
    + mf_cmp_snd; first by ms_solve.
      by mf_done.
Qed.

Hint Resolve bin_op_eval'_loc_offset_int_meas_fun : mf_fun.
Hint Resolve bin_op_eval'_loc_le_loc_meas_fun     : mf_fun.
Hint Resolve bin_op_eval'_loc_lt_loc_meas_fun     : mf_fun.

Definition bin_op_eval'_loc : (<<discr bin_op>> * <<discr loc>> * base_lit) -> option base_lit :=
  if_in bin_op_eval'_loc_cov_offset_int bin_op_eval'_loc_offset_int $
  if_in bin_op_eval'_loc_cov_le_loc     bin_op_eval'_loc_le_loc $
  if_in bin_op_eval'_loc_cov_lt_loc     bin_op_eval'_loc_lt_loc $
  cst None.

Lemma bin_op_eval'_loc_meas_fun : measurable_fun setT bin_op_eval'_loc. Admitted.

Hint Resolve bin_op_eval'_loc_meas_fun : mf_fun.

(* bin_op_eval_real: Normal (reducible) version *)
Definition bin_op_eval_real (op : <<discr bin_op>>) (r1 r2 : ((R : realType) : measurableType _)) : option base_lit :=
  match op with
  | PlusOp => Some $ LitReal (r1 + r2)
  | MinusOp => Some $ LitReal (r1 - r2)
  | MultOp => Some $ LitReal (r1 * r2)
  | LeOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 <= r2)%R
  | LtOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 < r2)%R
  | EqOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 = r2)%R
  | _ => None
  end%R.

Definition bin_op_eval_real'_cov_plus  : set (<<discr bin_op>> * ((R : realType) : measurableType _) * ((R : realType) : measurableType _)). Admitted.
Definition bin_op_eval_real'_cov_minus : set (<<discr bin_op>> * ((R : realType) : measurableType _) * ((R : realType) : measurableType _)). Admitted.
Definition bin_op_eval_real'_cov_mul   : set (<<discr bin_op>> * ((R : realType) : measurableType _) * ((R : realType) : measurableType _)). Admitted.
Definition bin_op_eval_real'_cov_le    : set (<<discr bin_op>> * ((R : realType) : measurableType _) * ((R : realType) : measurableType _)). Admitted.
Definition bin_op_eval_real'_cov_lt    : set (<<discr bin_op>> * ((R : realType) : measurableType _) * ((R : realType) : measurableType _)). Admitted.
Definition bin_op_eval_real'_cov_eq    : set (<<discr bin_op>> * ((R : realType) : measurableType _) * ((R : realType) : measurableType _)). Admitted.

Lemma bin_op_eval_real'_cov_plus_meas_set  : measurable bin_op_eval_real'_cov_plus. Admitted.
Lemma bin_op_eval_real'_cov_minus_meas_set : measurable bin_op_eval_real'_cov_minus. Admitted.
Lemma bin_op_eval_real'_cov_mul_meas_set   : measurable bin_op_eval_real'_cov_mul. Admitted.
Lemma bin_op_eval_real'_cov_le_meas_set    : measurable bin_op_eval_real'_cov_le. Admitted.
Lemma bin_op_eval_real'_cov_lt_meas_set    : measurable bin_op_eval_real'_cov_lt. Admitted.
Lemma bin_op_eval_real'_cov_eq_meas_set    : measurable bin_op_eval_real'_cov_eq. Admitted.

Hint Resolve bin_op_eval_real'_cov_plus_meas_set  : mf_set.
Hint Resolve bin_op_eval_real'_cov_minus_meas_set : mf_set.
Hint Resolve bin_op_eval_real'_cov_mul_meas_set   : mf_set.
Hint Resolve bin_op_eval_real'_cov_le_meas_set    : mf_set.
Hint Resolve bin_op_eval_real'_cov_lt_meas_set    : mf_set.
Hint Resolve bin_op_eval_real'_cov_eq_meas_set    : mf_set.

Definition bin_op_eval_real'_plus  : (<<discr bin_op>> * ((R : realType) : measurableType _) * ((R : realType) : measurableType _)) -> option base_lit. Admitted.
Definition bin_op_eval_real'_minus : (<<discr bin_op>> * ((R : realType) : measurableType _) * ((R : realType) : measurableType _)) -> option base_lit. Admitted.
Definition bin_op_eval_real'_mul   : (<<discr bin_op>> * ((R : realType) : measurableType _) * ((R : realType) : measurableType _)) -> option base_lit. Admitted.
Definition bin_op_eval_real'_le    : (<<discr bin_op>> * ((R : realType) : measurableType _) * ((R : realType) : measurableType _)) -> option base_lit. Admitted.
Definition bin_op_eval_real'_lt    : (<<discr bin_op>> * ((R : realType) : measurableType _) * ((R : realType) : measurableType _)) -> option base_lit. Admitted.
Definition bin_op_eval_real'_eq    : (<<discr bin_op>> * ((R : realType) : measurableType _) * ((R : realType) : measurableType _)) -> option base_lit. Admitted.

Lemma bin_op_eval_real'_plus_meas_fun  : measurable_fun bin_op_eval_real'_cov_plus  bin_op_eval_real'_plus.  Admitted.
Lemma bin_op_eval_real'_minus_meas_fun : measurable_fun bin_op_eval_real'_cov_minus bin_op_eval_real'_minus. Admitted.
Lemma bin_op_eval_real'_mul_meas_fun   : measurable_fun bin_op_eval_real'_cov_mul   bin_op_eval_real'_mul.   Admitted.
Lemma bin_op_eval_real'_le_meas_fun    : measurable_fun bin_op_eval_real'_cov_le    bin_op_eval_real'_le.    Admitted.
Lemma bin_op_eval_real'_lt_meas_fun    : measurable_fun bin_op_eval_real'_cov_lt    bin_op_eval_real'_lt.    Admitted.
Lemma bin_op_eval_real'_eq_meas_fun    : measurable_fun bin_op_eval_real'_cov_eq    bin_op_eval_real'_eq.    Admitted.

Hint Resolve bin_op_eval_real'_plus_meas_fun  : mf_fun.
Hint Resolve bin_op_eval_real'_minus_meas_fun : mf_fun.
Hint Resolve bin_op_eval_real'_mul_meas_fun   : mf_fun.
Hint Resolve bin_op_eval_real'_le_meas_fun    : mf_fun.
Hint Resolve bin_op_eval_real'_lt_meas_fun    : mf_fun.
Hint Resolve bin_op_eval_real'_eq_meas_fun    : mf_fun.

Definition bin_op_eval_real' :=
  if_in bin_op_eval_real'_cov_plus  bin_op_eval_real'_plus $
  if_in bin_op_eval_real'_cov_minus bin_op_eval_real'_minus $
  if_in bin_op_eval_real'_cov_mul   bin_op_eval_real'_mul $
  if_in bin_op_eval_real'_cov_le    bin_op_eval_real'_le $
  if_in bin_op_eval_real'_cov_lt    bin_op_eval_real'_lt $
  if_in bin_op_eval_real'_cov_eq    bin_op_eval_real'_eq $
  cst None.

Lemma bin_op_eval_real'_meas_fun : measurable_fun setT bin_op_eval_real'.
Admitted.

Hint Resolve bin_op_eval_real'_meas_fun  : mf_fun.


Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    if decide (v1 = v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1 , v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => Some $ LitV $ bin_op_eval_int op n1 n2
    | LitV (LitReal r1), LitV (LitReal r2) => LitV <$> bin_op_eval_real op r1 r2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => None
    end.


Definition bin_op_eval'_cov_eq   : set (<<discr bin_op>> * val * val)%type. Admitted.
Definition bin_op_eval'_cov_int  : set (<<discr bin_op>> * val * val)%type. Admitted.
Definition bin_op_eval'_cov_real : set (<<discr bin_op>> * val * val)%type. Admitted.
Definition bin_op_eval'_cov_bool : set (<<discr bin_op>> * val * val)%type. Admitted.
Definition bin_op_eval'_cov_locX : set (<<discr bin_op>> * val * val)%type. Admitted.

Lemma bin_op_eval'_cov_eq_meas_set   : measurable bin_op_eval'_cov_eq. Admitted.
Lemma bin_op_eval'_cov_int_meas_set  : measurable bin_op_eval'_cov_int. Admitted.
Lemma bin_op_eval'_cov_real_meas_set : measurable bin_op_eval'_cov_real. Admitted.
Lemma bin_op_eval'_cov_bool_meas_set : measurable bin_op_eval'_cov_bool. Admitted.
Lemma bin_op_eval'_cov_locX_meas_set : measurable bin_op_eval'_cov_locX. Admitted.

Hint Resolve bin_op_eval'_cov_eq_meas_set   : mf_set.
Hint Resolve bin_op_eval'_cov_int_meas_set  : mf_set.
Hint Resolve bin_op_eval'_cov_real_meas_set : mf_set.
Hint Resolve bin_op_eval'_cov_bool_meas_set : mf_set.
Hint Resolve bin_op_eval'_cov_locX_meas_set  : mf_set.

Definition bin_op_eval'_eq   : (<<discr bin_op>> * val * val)%type -> option val. Admitted.
Definition bin_op_eval'_int  : (<<discr bin_op>> * val * val)%type -> option val. Admitted.
Definition bin_op_eval'_real : (<<discr bin_op>> * val * val)%type -> option val. Admitted.
Definition bin_op_eval'_bool : (<<discr bin_op>> * val * val)%type -> option val. Admitted.
Definition bin_op_eval'_locX : (<<discr bin_op>> * val * val)%type -> option val. Admitted.

Lemma bin_op_eval'_eq_meas_fun   : measurable_fun bin_op_eval'_cov_eq   bin_op_eval'_eq. Admitted.
Lemma bin_op_eval'_int_meas_fun  : measurable_fun bin_op_eval'_cov_int  bin_op_eval'_int. Admitted.
Lemma bin_op_eval'_real_meas_fun : measurable_fun bin_op_eval'_cov_real bin_op_eval'_real. Admitted.
Lemma bin_op_eval'_bool_meas_fun : measurable_fun bin_op_eval'_cov_bool bin_op_eval'_bool. Admitted.
Lemma bin_op_eval'_locX_meas_fun : measurable_fun bin_op_eval'_cov_locX bin_op_eval'_locX. Admitted.

Hint Resolve bin_op_eval'_eq_meas_fun   : mf_fun.
Hint Resolve bin_op_eval'_int_meas_fun  : mf_fun.
Hint Resolve bin_op_eval'_real_meas_fun : mf_fun.
Hint Resolve bin_op_eval'_bool_meas_fun : mf_fun.
Hint Resolve bin_op_eval'_locX_meas_fun : mf_fun.


Definition bin_op_eval' : (<<discr bin_op>> * val * val) -> option val :=
  if_in bin_op_eval'_cov_eq   bin_op_eval'_eq $
  if_in bin_op_eval'_cov_int  bin_op_eval'_int $
  if_in bin_op_eval'_cov_real bin_op_eval'_real $
  if_in bin_op_eval'_cov_bool bin_op_eval'_bool $
  if_in bin_op_eval'_cov_locX bin_op_eval'_locX  $
  cst None.

Lemma bin_op_eval'_meas_fun : measurable_fun setT bin_op_eval'. Admitted.

Hint Resolve bin_op_eval'_meas_fun : mf_fun.







(*


(** UnOp  *)

Definition un_op_evalC (x : (<<discr un_op >> * val)%type) : val
  := match (un_op_eval x.1 x.2) with
     | Some v => v
     | None => inhabitant
     end.

Definition auxcov_unop_ok : set (<<discr un_op>> * val)%type :=
  [set x | ∃ w, un_op_eval x.1 x.2 = Some w].

Definition auxcov_unop_stuck : set (<<discr un_op>> * val)%type :=
  [set x | un_op_eval x.1 x.2 = None].

Definition aux_aux_unop_1 : set (<<discr un_op>> * val)%type :=
  setX [set NegOp] (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitBool).

Definition aux_aux_unop_2 : set (<<discr un_op>> * val)%type :=
  setX [set NegOp] (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitInt).

Definition aux_aux_unop_3 : set (<<discr un_op>> * val)%type :=
  setX [set MinusUnOp] (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitInt).

Definition aux_aux_unop_4 : set (<<discr un_op>> * val)%type :=
  setX [set MinusUnOp] (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitReal).

Lemma aux_aux_unop_1_meas : measurable aux_aux_unop_1.
Proof. apply measurableX; [by rewrite /measurable//= |]. apply 𝜋_LitV_v_meas; by eauto with measlang. Qed.

Lemma aux_aux_unop_2_meas : measurable aux_aux_unop_2.
Proof. apply measurableX; [by rewrite /measurable//= |]. apply 𝜋_LitV_v_meas; by eauto with measlang. Qed.

Lemma aux_aux_unop_3_meas : measurable aux_aux_unop_3.
Proof. apply measurableX; [by rewrite /measurable//= |]. apply 𝜋_LitV_v_meas; by eauto with measlang. Qed.

Lemma aux_aux_unop_4_meas : measurable aux_aux_unop_4.
Proof. apply measurableX; [by rewrite /measurable//= |]. apply 𝜋_LitV_v_meas; by eauto with measlang. Qed.

Lemma aux_unop : auxcov_unop_ok = aux_aux_unop_1 `|` aux_aux_unop_2 `|` aux_aux_unop_3 `|` aux_aux_unop_4.
Proof.
  rewrite /auxcov_unop_ok/aux_aux_unop_1/aux_aux_unop_2/aux_aux_unop_3/aux_aux_unop_4/setU/=.
  apply /predeqP =>[[y1 y2]] /=.
  split.
  { repeat move=> [+]; move=>?//=.
    destruct y1.
    all: move=>//=.
    all: destruct y2.
    all: move=>//=.
    all: destruct l.
    all: move=>//=?.
    1: left; left; right.
    2: left; left; left.
    3: left; right.
    4: right.
    all: split; rewrite //.
    all: rewrite /vcov_lit/bcov_LitInt/bcov_LitBool/bcov_LitReal//=.
    all: by split; eexists. }
  { move=>[[[[->[++]]|[->[++]]]|[->[++]]]|[->[++]]].
Admitted.
(*
    all: repeat move=> [+]; move=>?->.
    all: repeat move=> [+]; move=>?//=->.
    all: by eexists _; move=>//=. }
Qed.
 *)
Lemma auxcov_unop_ok_meas : measurable auxcov_unop_ok.
Proof.
  rewrite aux_unop.
  eapply @measurableU; last by apply aux_aux_unop_4_meas.
  eapply @measurableU; last by apply aux_aux_unop_3_meas.
  eapply @measurableU; last by apply aux_aux_unop_2_meas.
  by apply aux_aux_unop_1_meas.
Qed.
Hint Resolve auxcov_unop_ok_meas : measlang.

Lemma aux_unop' : auxcov_unop_stuck = ~` auxcov_unop_ok.
Proof.
  rewrite /auxcov_unop_stuck/setC/auxcov_unop_ok.
  apply /predeqP =>[[y1 y2]] /=.
  split.
  { all: rewrite/un_op_eval//=.
    all: destruct y1.
    all: move=>//=.
    all: destruct y2.
    all: move=>//=.
    all: try by move=>? [? HK]; inversion HK.
    all: destruct l.
    all: move=>//=?.
    all: by move=> [? HK]; inversion HK. }
  { all: rewrite/un_op_eval//=.
    all: destruct y1.
    all: move=>//=.
    all: destruct y2.
    all: move=>//=.
    all: destruct l.
    all: move=>//= H.
    all: exfalso; apply H.
    all: by eexists _. }
Qed.

Lemma auxcov_unop_stuck_meas : measurable auxcov_unop_stuck.
Proof. by rewrite aux_unop'; eapply @measurableC, auxcov_unop_ok_meas. Qed.
Hint Resolve auxcov_unop_stuck_meas : measlang.

Lemma un_op_evalC_meas : measurable_fun auxcov_unop_ok un_op_evalC.
Proof.
(* Cover argument *)
Admitted.
Hint Resolve un_op_evalC_meas : measlang.


(** BinOp  *)

Definition auxcov_binop_ok : set (<<discr bin_op>> * val * val)%type :=
  [set x | ∃ w, bin_op_eval x.1.1 x.1.2 x.2 = Some w].

Definition auxcov_binop_stuck : set (<<discr bin_op>> * val * val)%type :=
  [set x | bin_op_eval x.1.1 x.1.2 x.2 = None].

Definition bin_op_evalC (x : (<<discr bin_op >> * val * val)%type) : val
  := match (bin_op_eval x.1.1 x.1.2 x.2) with
     | Some v => v
     | None => inhabitant
     end.

Lemma auxcov_binop_ok_meas : measurable auxcov_binop_ok.
Proof.
Admitted.
Hint Resolve auxcov_binop_ok_meas : measlang.

Lemma auxcov_binop_stuck_meas : measurable auxcov_binop_stuck.
Proof.
Admitted.
Hint Resolve auxcov_binop_stuck_meas : measlang.

Lemma bin_op_evalC_meas : measurable_fun auxcov_binop_ok bin_op_evalC.
Proof.
Admitted.
Hint Resolve bin_op_evalC_meas : measlang.


(*


Definition is_unop :


Definition unop_matcher_cover : list (set (<<discr un_op>> * val)) :=
  [ [set x | ∃ w, un_op_eval x.1 x.2 = Some w ];
    [set x | un_op_eval x.1 x.2 = None ] ].



Definition head_stepM_unop_destructor : expr -> (<<discr un_op>> * val)%type :=
  (mProd
    𝜋_UnOp_op
    (ssrfun.comp 𝜋_Val_v 𝜋_UnOp_e)).

(* TODO: delete *)
Definition Some_get {T : Type} [_ : Inhabited T] (x : option T) : T :=
  match x with
  | Some w => w
  | None => inhabitant
  end.

Definition head_stepM_unop_matcher_ok : <<discr un_op>> * val -> giryM expr :=
  ssrfun.comp (giryM_ret R) $
  ssrfun.comp ValC $
  ssrfun.comp (@Some_get val _)
  (uncurry un_op_eval).

Definition head_stepM_unop_matcher_stuck : <<discr un_op>> * val -> giryM expr :=
  cst giryM_zero.

Definition head_stepM_unop_matcher (x : <<discr un_op>> * val) : giryM expr :=
  match (un_op_eval x.1 x.2) with
  | Some _ => head_stepM_unop_matcher_ok x
  | None => head_stepM_unop_matcher_stuck x
  end.

(*  Plan: Split the implmenetation into a projection and two construction part(s)
      Do a different construction part depending on if unop_ok

  (* [set (op, Val v) | un_op_eval op v = Some _ ]*)
  Definition unop_cover_ok : set (<<discr un_op >> * expr) :=
    setI
      (setX setT ecov_val)
      [set x | ∃ w, un_op_eval x.1 (𝜋_Val_v x.2) = Some w ].

  (* [set (op, Val v) | un_op_eval op v = Some _ ]*)
  Definition unop_cover_stuck : set (<<discr un_op >> * expr) :=
    setD
      (setX setT ecov_val)
      [set x | un_op_eval x.1 (𝜋_Val_v x.2) = None ].

  (* [set c | ∃ v op w σ,     c = (UnOp op (Val v), σ) /\ un_op_eval op v = Some w] *)
  Program Definition cover_unop_ok : set cfg :=
    setI cover_unop_ok

  (*
     [set c | ∃ v op σ,       c = (UnOp op (Val v), σ) /\ un_op_eval op v = None ].
     [set c | ∃ v1 v2 op w σ, c = (BinOp op (Val v1) (Val v2), σ) /\ bin_op_eval op v1 v2 = Some w].
     [set c | ∃ v1 v2 op σ,   c = (BinOp op (Val v1) (Val v2), σ) /\ bin_op_eval op v1 v2 = None].
   *)
    _.
   *)


  Lemma unop_matcher_cover_ok_meas :
    (default_measure_display, val_cyl.-sigma).-prod.-measurable ([set x | ∃ w : val, un_op_eval x.1 x.2 = Some w] : (set (<<discr un_op>> * val))).
  Proof. Admitted.

  Lemma unop_matcher_cover_stuck_meas :
    (default_measure_display, val_cyl.-sigma).-prod.-measurable ([set x | un_op_eval x.1 x.2 = None] : (set (<<discr un_op>> * val))).
  Proof. Admitted.

  Lemma unop_matcher_cover_measurable :
      Forall ((default_measure_display, val_cyl.-sigma).-prod.-measurable) unop_matcher_cover.
  Proof.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    + by apply unop_matcher_cover_ok_meas.
    + by apply unop_matcher_cover_stuck_meas.
  Qed.

  Lemma head_stepM_unop_matcher_restricted_measurable :
      Forall (fun S => measurable_fun S head_stepM_unop_matcher) unop_matcher_cover.
  Proof.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    + eapply (mathcomp_measurable_fun_ext _ _ head_stepM_unop_matcher_ok head_stepM_unop_matcher).
      - rewrite /head_stepM_unop_matcher_ok.
        apply measurable_compT; try by eauto with measlang.
        { by apply unop_matcher_cover_ok_meas. }
        { apply measurable_compT; try by eauto with measlang.
          - admit. (*  by apply unop_matcher_cover_ok_meas.  *) }
        admit.
      - move=> [e?]//=.
        move=> [?+].
        rewrite /head_stepM_unop_matcher//=.
        by move=>->//=.
    + eapply (mathcomp_measurable_fun_ext _ _ head_stepM_unop_matcher_stuck head_stepM_unop_matcher).
      - by eapply measurable_cst.
      - move=> [e?]//=.
        rewrite /head_stepM_unop_matcher//=.
        by move=>->//=.
  Admitted.

  Lemma head_stepM_matcher_meas : measurable_fun setT head_stepM_unop_matcher.
  Proof.
    apply (@measurable_by_cover_list _ _ _ _ head_stepM_unop_matcher unop_matcher_cover).
    - by apply unop_matcher_cover_measurable.
    - rewrite /unop_matcher_cover//=.
      apply /predeqP =>y /=.
      split.
      + by move=>?.
      + move=>_.
        remember (un_op_eval y.1 y.2) as X.
        rewrite -HeqX; clear HeqX.
        destruct X; simpl.
        * left; by eexists.
        * by right; left.
    - suffices HFdep : (Forall (λ l, elem_of_list l unop_matcher_cover ->
                     measurable_fun  l (head_stepM_unop_matcher \_ l)) unop_matcher_cover).
      { apply Forall_forall.
        intros x Hx.
        by apply (iffLR (Forall_forall _ _) HFdep x Hx Hx).
      }
      eapply (Forall_impl _ _ _ head_stepM_unop_matcher_restricted_measurable).
      intros S H HS.
      eapply @mathcomp_restriction_is_measurable in H; last first.
     { eapply @Forall_forall; last by eapply HS.
        by apply unop_matcher_cover_measurable. }
      eapply @mathcomp_restriction_setT.
      by eapply H.
  Qed.

  Definition head_stepM_unop_destructor_domain : set expr :=
    setI ecov_unop $
    preimage 𝜋_UnOpU $
    setX setT ecov_val.

  Lemma head_stepM_unop_destructor_domain_meas : measurable head_stepM_unop_destructor_domain.
  Proof.
    apply 𝜋_UnOpU_meas; try by eauto with measlang.
    apply measurableX ; by eauto with measlang.
  Qed.

  Lemma head_stepM_destructor_meas :
    measurable_fun head_stepM_unop_destructor_domain head_stepM_unop_destructor.
  Proof.
    apply measurable_fun_prod'_expr; first by apply head_stepM_unop_destructor_domain_meas.
    rewrite /head_stepM_unop_destructor_domain.
    rewrite <-(setIid ecov_unop).
    rewrite <-setIA.
    apply measurable_fun_setI1; try by eauto with measlang.
    { apply 𝜋_UnOpU_meas; try by eauto with measlang.
      apply measurableX ; by eauto with measlang. }
    rewrite /head_stepM_unop_destructor_domain.
    eapply measurable_comp.
    3: { by eapply 𝜋_Val_v_meas. }
    + by eauto with measlang.
    + rewrite /subset//=.
      move=>?[++].
      move=>?[[+[++]]+].
      move=>??->[++].
      move=>_[++]//=.
      move=>?//=.
      move=>-><-//=.
      rewrite /ecov_val//=.
      by eexists.
    rewrite <-(setIid ecov_unop).
    rewrite <-setIA.
    apply measurable_fun_setI1; try by eauto with measlang.
    apply 𝜋_UnOpU_meas; try by eauto with measlang.
    apply measurableX ; by eauto with measlang.
  Qed.
*)
*)
