(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From Coq Require Export ssrfun.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import measure lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state cfg.

Require Import mathcomp.reals_stdlib.Rstruct.
Require Import mathcomp.reals.reals.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

Local Notation RR := ((R : realType) : measurableType _)%type.

Section arithmetic.
(** Arithmetic functions bug given measurale types *)

Definition neg_bool   : <<discr bool>> -> <<discr bool>> := negb.
Definition neg_int    : <<discr Z>> -> <<discr Z>>  := Z.lnot.
Definition minus_int  : <<discr Z>> -> <<discr Z>>  := Z.opp.
Definition minus_real : RR -> RR := Ropp.

Definition loc_offset : (<<discr loc>> * <<discr Z>>)%type -> <<discr loc>> := uncurry loc_add.
Definition loc_le : (<<discr loc>> * <<discr loc>>)%type -> <<discr bool>> := asbool \o uncurry locations.loc_le.
Definition loc_lt : (<<discr loc>> * <<discr loc>>)%type -> <<discr bool>> := asbool \o uncurry locations.loc_lt.

Definition plus_real : (RR * RR)%type -> RR := uncurry Rplus.
Definition sub_real  : (RR * RR)%type -> RR := uncurry Rminus.
Definition mul_real  : (RR * RR)%type -> RR := uncurry Rmult.

Definition le_real : (RR * RR)%type -> <<discr bool>> := asbool \o uncurry Rle.
Definition lt_real : (RR * RR)%type -> <<discr bool>> := asbool \o uncurry Rlt.
Definition eq_real : (RR * RR)%type -> <<discr bool>> := asbool \o uncurry eq.

(* FIXME: Change these definitions to whatever is already proven for R
   The discrete ones should follow from generalized uncurry lemmas (since they're discr + countable)
   Search measurable_fun realType "lt". *)

Lemma neg_bool_meas_fun   : measurable_fun setT neg_bool.
Proof.
  by apply: measurable_neg.
Qed.
Lemma neg_int_meas_fun    : measurable_fun setT neg_int.
Proof. apply: discr_meas_fun. Qed. 
Lemma minus_int_meas_fun  : measurable_fun setT minus_int.
Proof. apply: discr_meas_fun. Qed. 
Lemma minus_real_meas_fun : measurable_fun setT minus_real.
Proof.
  apply oppr_measurable.
Qed. 
Lemma loc_offset_meas_fun : measurable_fun setT loc_offset. 
Proof. rewrite /loc_offset/=.
       apply: uncurry_loc_measurable.
       intros. apply: discr_meas_fun.
Qed.
Lemma loc_le_meas_fun     : measurable_fun setT loc_le.
Proof.
  replace (loc_le) with (uncurry (λ x y, loc_car x <=? loc_car y))%Z; last first.
  { 
  rewrite /loc_le/=.
  rewrite /locations.loc_le.
  extensionality x. destruct x. simpl. symmetry.
  apply: asbool_equiv_eqP; last done.
  apply Z.leb_spec0.
  }
  apply: uncurry_loc_measurable.
  intros. apply discr_meas_fun.
Qed.
Lemma loc_lt_meas_fun     : measurable_fun setT loc_lt.
Proof.  
  replace (loc_lt) with (uncurry (λ x y, loc_car x <? loc_car y))%Z; last first.
  { 
  rewrite /loc_lt/=.
  rewrite /locations.loc_lt.
  extensionality x. destruct x. simpl. symmetry.
  apply: asbool_equiv_eqP; last done.
  apply Z.ltb_spec0.
  }
  apply: uncurry_loc_measurable.
  intros. apply discr_meas_fun.
Qed.
Lemma plus_real_meas_fun  : measurable_fun setT plus_real.
Proof.
  rewrite /plus_real.
  assert (uncurry Rplus=GRing.add_fun fst snd)%R as ->; last by apply: measurable_funD.
  extensionality x.
  by destruct x.
Qed. 
Lemma sub_real_meas_fun   : measurable_fun setT sub_real.
Proof.
  rewrite /sub_real.
  assert (uncurry Rminus=GRing.sub_fun fst snd)%R as ->; last by apply: measurable_funB.
  extensionality x.
  by destruct x.
Qed. 
Lemma mul_real_meas_fun   : measurable_fun setT mul_real.
Proof. 
  rewrite /mul_real.
  assert (uncurry Rmult=GRing.mul_fun fst snd)%R as ->; last by apply: measurable_funM.
  extensionality x.
  by destruct x.
Qed. 
Lemma le_real_meas_fun    : measurable_fun setT le_real.
Proof.
  eassert (le_real=_)%R as ->;last by apply: (measurable_fun_ler (f:=fst) (g:=snd)).
  extensionality x.
  destruct x. rewrite /le_real/=.
  destroy_mathcomp.
  apply: asbool_equiv_eqP; first apply RlebP; done.
Qed.
Lemma lt_real_meas_fun    : measurable_fun setT lt_real.
Proof.
  eassert (lt_real=_)%R as ->;last by apply: (measurable_fun_ltr (f:=fst) (g:=snd)).
  extensionality x.
  destruct x. rewrite /lt_real/=.
  destroy_mathcomp.
  apply: asbool_equiv_eqP; first apply RltbP; done.
Qed.
Lemma eq_real_meas_fun    : measurable_fun setT eq_real.
Proof.
  eassert (eq_real=_)%R as ->;last by apply: (measurable_fun_eqr (f:=fst) (g:=snd)).
  extensionality x.
  destruct x. rewrite /eq_real/=.
  destroy_mathcomp. 
  apply: asbool_equiv_eqP; last done.
  rewrite /eq_op/=/eqr.
  case_match.
  - by apply ReflectT.
  - by apply ReflectF.
Qed.
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
  apply: if_in_meas_fun; ms_solve.
  { rewrite setIT. apply un_op_eval'_neg_bool_meas_fun. }
  apply: if_in_meas_fun; ms_solve.
  { rewrite setIT.
    rewrite setIidl.
    - apply un_op_eval'_neg_int_meas_fun.
    - rewrite /un_op_eval'_cov_neg_int/un_op_eval'_cov_neg_bool. intros []; simpl.
      intros [?[[][]]][?[[][]]]; subst; simpl in *; subst; simpl in *; done.
  }
  apply: if_in_meas_fun; ms_solve.
  { rewrite setIT.
    rewrite setIidl; first apply un_op_eval'_minus_int_meas_fun.
    rewrite /un_op_eval'_cov_minus_int/un_op_eval'_cov_neg_int/un_op_eval'_cov_neg_bool. intros []; simpl.
    intros [?[[][]]]; split; intros [?[[][]]]; subst; simpl in *; subst; done.
  }
  apply: if_in_meas_fun; ms_solve.
  { rewrite setIT.
    rewrite setIidl; first apply un_op_eval'_minus_real_meas_fun.
    rewrite /un_op_eval'_cov_minus_real/un_op_eval'_cov_minus_int/un_op_eval'_cov_neg_int/un_op_eval'_cov_neg_bool. intros []; simpl.
    intros [?[[][]]]; repeat split; intros [?[[][]]]; subst; simpl in *; subst; done.
  }
Qed.

Lemma un_op_eval_eq (op : <<discr un_op>>) (v : val) : un_op_eval op v = un_op_eval' (op, v).
Proof.
  rewrite /un_op_eval/un_op_eval'.
  repeat apply if_in_split; try (intros [?[[][]]]; simpl in *; subst; simpl in *; by subst).
  simpl. intros H1 H2 H3 H4.
  repeat case_match; try done; exfalso; subst.
  - apply H3. rewrite /un_op_eval'_cov_neg_int. naive_solver.
  - apply H4. rewrite /un_op_eval'_cov_neg_bool. naive_solver.
  - apply H2. rewrite /un_op_eval'_cov_minus_int. naive_solver.
  - apply H1. rewrite /un_op_eval'_cov_minus_real. naive_solver.
Qed. 

Definition un_op_eval''_ok : set (<<discr un_op>> * val * state)%type :=
  (un_op_eval'_cov_neg_bool `|` un_op_eval'_cov_neg_int `|` un_op_eval'_cov_minus_int `|` un_op_eval'_cov_minus_real) `*` setT.

Lemma un_op_eval''_ok_meas_set : measurable un_op_eval''_ok.
Proof. rewrite /un_op_eval''_ok.
       apply measurableX; last done.
       assert ((setU (setU (setU un_op_eval'_cov_neg_bool un_op_eval'_cov_neg_int) un_op_eval'_cov_minus_int)
                  un_op_eval'_cov_minus_real) =\bigcup_(i in
                   ([set
                       un_op_eval'_cov_neg_bool    ;
                     un_op_eval'_cov_neg_int   ;
                     un_op_eval'_cov_minus_int;
                 un_op_eval'_cov_minus_real ])) i
              ) as ->.
       { rewrite eqEsubset; split; intros ?; simpl.
         - intros [[[|]|]|]; (eexists _; last done); naive_solver.
         - intros [? [[[|]|]|] ?]; naive_solver.
       }
       apply: fin_bigcup_measurable; first apply cardinality.finite_set4.
       intros ? [[[|]|]|]; simpl in *; subst; ms_solve.
Qed.

Hint Resolve un_op_eval''_ok_meas_set : mf_set.

Definition un_op_eval'' : (<<discr un_op>> * val * state)%type -> giryM cfg :=
  if_in un_op_eval''_ok (gRet \o (ValU \o of_option un_op_eval' \o fst △ snd)) (cst gZero).


Lemma un_op_eval''_meas_fun : measurable_fun setT un_op_eval''.
Proof.
  rewrite /un_op_eval''.
  apply: if_in_meas_fun; ms_solve.
  mf_cmp_tree; first apply: gRet_meas_fun.
  mf_prod; last apply: measurable_snd_restriction; ms_solve.
  rewrite /un_op_eval''_ok.
  eapply @measurable_comp; last apply: measurable_fst_restriction; last ms_solve; last first.
  - eapply @measurable_comp; last first.
    + apply: of_option_meas_fun.
      apply un_op_eval'_meas_fun.
    + apply ValU_meas_fun.
    + done.
    + done.
  - intros ?; simpl.
    intros [[[]][[[[[H|H]|H]|H]]]]; simpl in *; subst; rewrite /option_cov_Some/=/un_op_eval'.
    + eexists _. by rewrite ifIn_eq_left.
    + eexists _. rewrite ifIn_eq_right; first by rewrite ifIn_eq_left.
      intros H'. destruct H as [?[[][]]]. destruct H' as [?[[][]]].
       repeat (subst; simpl in * ). simplify_eq.
    + eexists _. rewrite ifIn_eq_right; first rewrite ifIn_eq_right; first by rewrite ifIn_eq_left.
      all: intros H'; destruct H as [?[[][]]]; destruct H' as [?[[][]]];
        repeat (subst; simpl in * ); simplify_eq.
    + eexists _. rewrite ifIn_eq_right;
        first rewrite ifIn_eq_right; first rewrite ifIn_eq_right; first by rewrite ifIn_eq_left.
      all: intros H'; destruct H as [?[[][]]]; destruct H' as [?[[][]]];
        repeat (subst; simpl in * ); simplify_eq.
  - simpl. 
    rewrite /un_op_eval'.
    replace (preimage _ _) with (setU un_op_eval'_cov_neg_bool
                                   (setU un_op_eval'_cov_neg_int
                                         (setU un_op_eval'_cov_minus_int un_op_eval'_cov_minus_real)
                                )).
    { repeat apply: measurableU; ms_solve. }
    rewrite eqEsubset. split; intros []; simpl.
    + intros [H'|[H'|[H'|H']]].
      * rewrite ifIn_eq_left; last done.
        destruct H' as [?[[][]]]; repeat (subst; simpl in * ).
        rewrite /option_cov_Some/=. naive_solver.
      * rewrite ifIn_eq_right; first rewrite ifIn_eq_left; try done;
          destruct H' as [?[[][]]]; repeat (subst; simpl in * ).
        -- rewrite /option_cov_Some/=. naive_solver.
        -- intros [?[[][]]]; repeat (subst; simpl in * ). simplify_eq.
      * rewrite ifIn_eq_right; first rewrite ifIn_eq_right; first rewrite ifIn_eq_left; try done;
          destruct H' as [?[[][]]]; repeat (subst; simpl in * ).
        -- rewrite /option_cov_Some; naive_solver.
        -- intros [?[[][]]]; repeat (subst; simpl in * ). simplify_eq.
        -- intros [?[[][]]]; repeat (subst; simpl in * ). simplify_eq.
      * rewrite ifIn_eq_right; first rewrite ifIn_eq_right; first rewrite ifIn_eq_right; first rewrite ifIn_eq_left; try done;
          destruct H' as [?[[][]]]; repeat (subst; simpl in * ).
        -- rewrite /option_cov_Some; naive_solver.
        -- intros [?[[][]]]; repeat (subst; simpl in * ). simplify_eq.
        -- intros [?[[][]]]; repeat (subst; simpl in * ). simplify_eq.
        -- intros [?[[][]]]; repeat (subst; simpl in * ). simplify_eq.
    + rewrite /option_cov_Some/=. elim. intros x.
      repeat apply if_in_split; try done; intros; naive_solver.
Qed. 
Hint Resolve un_op_eval''_meas_fun : mf_fun.

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


Lemma bin_op_eval_int_measurable_fun : measurable_fun setT (uncurry
                                                              (λ x, uncurry (bin_op_eval_int x))).
Proof.
  simpl.
  apply : uncurry_measurable; last apply bin_op_enum_surj.
  intros. apply: uncurry_measurable; last first.
  { instantiate (1:= λ x, match decode_nat x with | None => 0%Z | Some z => z end).
    intros x. Local Opaque decode_nat. simpl. exists (encode_nat x).
    by rewrite decode_encode_nat.
  }
  intros. apply: discr_meas_fun.
Qed. 

(* Only one version of bin_op_eval_bool because its uncurry is measurable *)
Definition bin_op_eval_bool (op : <<discr bin_op>>) (b1 b2 : <<discr bool>>) : option val :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitV $ LitBool (b1 && b2))
  | OrOp => Some (LitV $LitBool (b1 || b2))
  | XorOp => Some (LitV $LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitV $LitBool (bool_decide (b1 = b2)))
  | OffsetOp => None
  end.

Lemma bin_op_eval_bool_measurable_fun : measurable_fun setT (uncurry (λ x, uncurry (bin_op_eval_bool x))).
Proof.
  simpl.
  apply : uncurry_measurable; last apply bin_op_enum_surj.
  intros. apply: uncurry_measurable; last first.
  { instantiate (1:= λ x, match decode_nat x with | None => true | Some z => z end).
    intros x. Local Opaque decode_nat. simpl. exists (encode_nat x).
    by rewrite decode_encode_nat.
  }
  intros. apply: discr_meas_fun.
Qed. 

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

Definition bin_op_eval'_loc_offset_int : (<<discr bin_op>> * <<discr loc>> * base_lit) -> option val :=
  Some \o LitVU \o LitLocU \o loc_offset \o (snd \o fst △ 𝜋_LitInt_z \o snd).

Definition bin_op_eval'_loc_le_loc : (<<discr bin_op>> * <<discr loc>> * base_lit) -> option val :=
  Some \o LitVU \o LitBoolU \o loc_le \o (snd \o fst △ 𝜋_LitLoc_l \o snd).

Definition bin_op_eval'_loc_lt_loc : (<<discr bin_op>> * <<discr loc>> * base_lit) -> option val :=
  Some \o LitVU \o LitBoolU \o loc_lt \o (snd \o fst △ 𝜋_LitLoc_l \o snd).

Lemma bin_op_eval'_loc_offset_int_meas_fun : measurable_fun bin_op_eval'_loc_cov_offset_int bin_op_eval'_loc_offset_int.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree.
  - mf_cmp_tree; last by eapply loc_offset_meas_fun.
    repeat mf_cmp_tree.
    + by apply Some_meas_fun.
    + apply LitVU_meas_fun.
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
    repeat mf_cmp_tree.
    + by apply Some_meas_fun.
    + apply LitVU_meas_fun.
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
    repeat mf_cmp_tree.
    + by apply Some_meas_fun.
    + apply LitVU_meas_fun.
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

Definition bin_op_eval'_loc : (<<discr bin_op>> * <<discr loc>> * base_lit) -> option val :=
  if_in bin_op_eval'_loc_cov_offset_int bin_op_eval'_loc_offset_int $
  if_in bin_op_eval'_loc_cov_le_loc     bin_op_eval'_loc_le_loc $
  if_in bin_op_eval'_loc_cov_lt_loc     bin_op_eval'_loc_lt_loc $
  cst None.

Lemma bin_op_eval'_loc_meas_fun : measurable_fun setT bin_op_eval'_loc.
Proof.
  rewrite /bin_op_eval'_loc.
  simpl.
  apply: if_in_meas_fun; try ms_solve.
  { rewrite setIT. mf_done. }
  rewrite setIT.
  apply: if_in_meas_fun; try ms_solve.
  { rewrite setIidl; first mf_done.
    intros []. intros [?[]][?[]]; simpl in *; subst. simplify_eq.
  }
  apply: if_in_meas_fun; try ms_solve.
  rewrite setIidl; first mf_done.
  intros [[]]. intros [[][]]; simpl in *. split; intros [[][]]; simpl in *; subst; simplify_eq.
Qed. 

Hint Resolve bin_op_eval'_loc_meas_fun : mf_fun.

(* bin_op_eval_real: Normal (reducible) version *)
Definition bin_op_eval_real (op : <<discr bin_op>>) (r1 r2 : RR) : option base_lit :=
  match op with
  | PlusOp => Some $ LitReal (r1 + r2)
  | MinusOp => Some $ LitReal (r1 - r2)
  | MultOp => Some $ LitReal (r1 * r2)
  | LeOp => Some $ LitBool $ bool_decide (dec:=make_decision _) (r1 <= r2)%R
  | LtOp => Some $ LitBool $ bool_decide (dec:=make_decision _) (r1 < r2)%R
  (* | EqOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 = r2)%R *)
  | _ => None
  end%R.

Program Definition bin_op_eval_real'_cov_plus : set (<<discr bin_op>> * RR * RR)%type :=
  ([set (PlusOp : <<discr bin_op>>)] `*` setT `*` setT).

Definition bin_op_eval_real'_cov_minus : set (<<discr bin_op>> * RR * RR)%type :=
  ([set (MinusOp : <<discr bin_op>>)] `*` setT `*` setT).

Definition bin_op_eval_real'_cov_mul : set (<<discr bin_op>> * RR * RR)%type :=
  ([set (MultOp : <<discr bin_op>>)] `*` setT `*` setT).

Definition bin_op_eval_real'_cov_le : set (<<discr bin_op>> * RR * RR)%type :=
  ([set (LeOp : <<discr bin_op>>)] `*` setT `*` setT).

Definition bin_op_eval_real'_cov_lt : set (<<discr bin_op>> * RR * RR)%type :=
  ([set (LtOp : <<discr bin_op>>)] `*` setT `*` setT).

(* Definition bin_op_eval_real'_cov_eq : set (<<discr bin_op>> * RR * RR)%type := *)
(*   ([set (EqOp : <<discr bin_op>>)] `*` setT `*` setT). *)

Lemma bin_op_eval_real'_cov_plus_meas_set  : measurable bin_op_eval_real'_cov_plus.
Proof. by ms_unfold; ms_solve. Qed.

Lemma bin_op_eval_real'_cov_minus_meas_set : measurable bin_op_eval_real'_cov_minus.
Proof. by ms_unfold; ms_solve. Qed.

Lemma bin_op_eval_real'_cov_mul_meas_set : measurable bin_op_eval_real'_cov_mul.
Proof. by ms_unfold; ms_solve. Qed.

Lemma bin_op_eval_real'_cov_le_meas_set : measurable bin_op_eval_real'_cov_le.
Proof. by ms_unfold; ms_solve. Qed.

Lemma bin_op_eval_real'_cov_lt_meas_set : measurable bin_op_eval_real'_cov_lt.
Proof. by ms_unfold; ms_solve. Qed.

(* Lemma bin_op_eval_real'_cov_eq_meas_set : measurable bin_op_eval_real'_cov_eq. *)
(* Proof. by ms_unfold; ms_solve. Qed. *)

Hint Resolve bin_op_eval_real'_cov_plus_meas_set  : mf_set.
Hint Resolve bin_op_eval_real'_cov_minus_meas_set : mf_set.
Hint Resolve bin_op_eval_real'_cov_mul_meas_set   : mf_set.
Hint Resolve bin_op_eval_real'_cov_le_meas_set    : mf_set.
Hint Resolve bin_op_eval_real'_cov_lt_meas_set    : mf_set.
(* Hint Resolve bin_op_eval_real'_cov_eq_meas_set    : mf_set. *)

Definition bin_op_eval_real'_plus  : (<<discr bin_op>> * RR * RR)%type -> option val :=
  Some \o LitVU \o  LitRealU \o plus_real \o (snd \o fst △ snd).

Definition bin_op_eval_real'_minus : (<<discr bin_op>> * RR * RR)%type -> option val :=
  Some \o LitVU \o LitRealU \o sub_real \o (snd \o fst △ snd).

Definition bin_op_eval_real'_mul   : (<<discr bin_op>> * RR * RR)%type -> option val :=
  Some \o LitVU \o LitRealU \o mul_real \o (snd \o fst △ snd).

Definition bin_op_eval_real'_le    : (<<discr bin_op>> * RR * RR)%type -> option val :=
  Some \o LitVU \o LitBoolU \o le_real \o (snd \o fst △ snd).

Definition bin_op_eval_real'_lt    : (<<discr bin_op>> * RR * RR)%type -> option val :=
  Some \o LitVU \o LitBoolU \o lt_real \o (snd \o fst △ snd).

(* Definition bin_op_eval_real'_eq    : (<<discr bin_op>> * RR * RR)%type -> option base_lit := *)
(*   Some \o LitBoolU \o eq_real \o (snd \o fst △ snd). *)


Lemma bin_op_eval_real'_plus_meas_fun  : measurable_fun bin_op_eval_real'_cov_plus  bin_op_eval_real'_plus.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree.
  { mf_cmp_tree; last by apply plus_real_meas_fun.
    repeat mf_cmp_tree.
    { by apply Some_meas_fun. }
    { by apply LitVU_meas_fun. }
    { by apply LitRealU_meas_fun. }}
  { mf_prod.
    { mf_cmp_fst; first by ms_solve.
      apply @measurable_snd_restriction.
      by ms_solve. }
    { apply @measurable_snd_restriction.
      by ms_solve. }}
Qed.

Lemma bin_op_eval_real'_minus_meas_fun : measurable_fun bin_op_eval_real'_cov_minus bin_op_eval_real'_minus.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree.
  { mf_cmp_tree; last by apply sub_real_meas_fun.
    repeat mf_cmp_tree.
    { by apply Some_meas_fun. }
    { by apply LitVU_meas_fun. }
    { by apply LitRealU_meas_fun. }}
  { mf_prod.
    { mf_cmp_fst; first by ms_solve.
      apply @measurable_snd_restriction.
      by ms_solve. }
    { apply @measurable_snd_restriction.
      by ms_solve. }}
Qed.

Lemma bin_op_eval_real'_mul_meas_fun   : measurable_fun bin_op_eval_real'_cov_mul   bin_op_eval_real'_mul.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree.
  { mf_cmp_tree; last by apply mul_real_meas_fun.
    repeat mf_cmp_tree.
    { by apply Some_meas_fun. }
    { by apply LitVU_meas_fun. }
    { by apply LitRealU_meas_fun. }}
  { mf_prod.
    { mf_cmp_fst; first by ms_solve.
      apply @measurable_snd_restriction.
      by ms_solve. }
    { apply @measurable_snd_restriction.
      by ms_solve. }}
Qed.

Lemma bin_op_eval_real'_le_meas_fun    : measurable_fun bin_op_eval_real'_cov_le    bin_op_eval_real'_le.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree.
  { mf_cmp_tree; last by apply le_real_meas_fun.
    repeat mf_cmp_tree.
    - by apply Some_meas_fun.
    - by apply LitVU_meas_fun. 
  }
  { mf_prod.
    { mf_cmp_fst; first by ms_solve.
      apply @measurable_snd_restriction.
      by ms_solve. }
    { apply @measurable_snd_restriction.
      by ms_solve. }}
Qed.

Lemma bin_op_eval_real'_lt_meas_fun    : measurable_fun bin_op_eval_real'_cov_lt    bin_op_eval_real'_lt.
Proof.
  mf_unfold_dom; mf_unfold_fun.
  mf_cmp_tree.
  { mf_cmp_tree; last by apply lt_real_meas_fun.
    repeat mf_cmp_tree.
    - by apply Some_meas_fun.
    - by apply LitVU_meas_fun. 
  }
  { mf_prod.
    { mf_cmp_fst; first by ms_solve.
      apply @measurable_snd_restriction.
      by ms_solve. }
    { apply @measurable_snd_restriction.
      by ms_solve. }}
Qed.

(* Lemma bin_op_eval_real'_eq_meas_fun    : measurable_fun bin_op_eval_real'_cov_eq    bin_op_eval_real'_eq. *)
(* Proof. *)
(*   mf_unfold_dom; mf_unfold_fun. *)
(*   mf_cmp_tree. *)
(*   { mf_cmp_tree; last by apply eq_real_meas_fun. *)
(*     mf_cmp_tree. *)
(*     by apply Some_meas_fun. } *)
(*   { mf_prod. *)
(*     { mf_cmp_fst; first by ms_solve. *)
(*       apply @measurable_snd_restriction. *)
(*       by ms_solve. } *)
(*     { apply @measurable_snd_restriction. *)
(*       by ms_solve. }} *)
(* Qed. *)

Hint Resolve bin_op_eval_real'_plus_meas_fun  : mf_fun.
Hint Resolve bin_op_eval_real'_minus_meas_fun : mf_fun.
Hint Resolve bin_op_eval_real'_mul_meas_fun   : mf_fun.
Hint Resolve bin_op_eval_real'_le_meas_fun    : mf_fun.
Hint Resolve bin_op_eval_real'_lt_meas_fun    : mf_fun.
(* Hint Resolve bin_op_eval_real'_eq_meas_fun    : mf_fun. *)

Definition bin_op_eval_real' :=
  if_in bin_op_eval_real'_cov_plus  bin_op_eval_real'_plus $
  if_in bin_op_eval_real'_cov_minus bin_op_eval_real'_minus $
  if_in bin_op_eval_real'_cov_mul   bin_op_eval_real'_mul $
  if_in bin_op_eval_real'_cov_le    bin_op_eval_real'_le $
  if_in bin_op_eval_real'_cov_lt    bin_op_eval_real'_lt $
  (* if_in bin_op_eval_real'_cov_eq    bin_op_eval_real'_eq $ *)
  cst None.

Lemma bin_op_eval_real'_meas_fun : measurable_fun setT bin_op_eval_real'.
Proof.
  rewrite /bin_op_eval_real'.
  simpl.
  repeat (apply: if_in_meas_fun; try ms_solve;
   first (rewrite setIidl; first mf_done;
          intros [[]]; intros [[][]]; repeat split; intros[[][]]; simpl in *; subst; simplify_eq)).
Qed. 

Hint Resolve bin_op_eval_real'_meas_fun  : mf_fun.


Definition lit_is_unboxed (l: base_lit) : Prop :=
  match l with
  (** Disallow comparing (erased) prophecies with (erased) prophecies, by
  considering them boxed. *)
  (* | LitProphecy _ | LitPoison => False *)
  | LitInt _ | LitBool _  | LitLoc _ | LitLbl _ | LitUnit | LitReal _ => True
  end.
Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => lit_is_unboxed l
  | InjLV (LitV l) => lit_is_unboxed l
  | InjRV (LitV l) => lit_is_unboxed l
  | _ => False
  end.
Global Instance lit_is_unboxed_dec l : Decision (lit_is_unboxed l).
Proof. destruct l; simpl; exact (decide _). Defined.
Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Proof. destruct v as [ | | | [] | [] ]; simpl; exact (decide _). Defined.


Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if bool_decide (op = EqOp) then
    if (bool_decide (vals_compare_safe v1 v2)) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else None
  else
    match v1 , v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => Some $ LitV $ bin_op_eval_int op n1 n2
    | LitV (LitReal r1), LitV (LitReal r2) => LitV <$> bin_op_eval_real op r1 r2
    | LitV (LitBool b1), LitV (LitBool b2) => bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => None
    end.



Definition base_lit_diag := [set x: (base_lit * base_lit)| ∃ y, x =(y,y)].
Lemma base_lit_diag_meas_set : measurable base_lit_diag.
Proof.
  assert (base_lit_diag =
          ((bcov_LitInt `*` bcov_LitInt) `&` preimage (𝜋_LitInt_z \o fst△𝜋_LitInt_z \o snd)[set x| ∃ y, x =(y,y)] ) `|`
          ((bcov_LitBool `*` bcov_LitBool) `&` preimage (𝜋_LitBool_b \o fst△𝜋_LitBool_b \o snd)[set x| ∃ y, x =(y,y)] ) `|`
          ((bcov_LitUnit `*` bcov_LitUnit)) `|`
          ((bcov_LitLoc `*` bcov_LitLoc) `&` preimage (𝜋_LitLoc_l \o fst△𝜋_LitLoc_l \o snd)[set x| ∃ y, x =(y,y)] ) `|`
          ((bcov_LitLbl `*` bcov_LitLbl) `&` preimage (𝜋_LitLbl_l \o fst△𝜋_LitLbl_l \o snd)[set x| ∃ y, x =(y,y)] ) `|`
          ((bcov_LitReal `*` bcov_LitReal) `&` preimage (eq_real\o (𝜋_LitReal_r \o fst△𝜋_LitReal_r \o snd)) ([set true]) ) 
         ) as ->.
  { rewrite eqEsubset; split; intros []; simpl; rewrite /base_lit_diag/=.
    - intros [x ?]. destruct!/=.
      destruct x; simpl; [naive_solver..|].
      right. repeat split; [naive_solver..|].
      rewrite /eq_real/=. 
      apply: asbool_equiv_eqP; last done.
      by apply ReflectT.
    - intros. destruct!/=; [naive_solver..|].
      unfold eq_real in *.
      simpl in *.
      assert (asbool True = true) as Hrewrite.
      { apply: asbool_equiv_eqP; last done. by apply ReflectT. }
      rewrite -Hrewrite in H1.
      apply asbool_eq_equiv in H1.
      eexists _. f_equal. f_equal. naive_solver.
  }
  repeat apply: measurable_setU.
  - apply: apply_measurable_fun.
    { mf_prod; apply: measurable_comp; last first.
      - apply measurable_snd_restriction. ms_solve.
      - mf_done.
      - intros ?. simpl. intros. destruct!/=. naive_solver.
      - ms_solve.
      - apply measurable_fst_restriction. ms_solve.
      - mf_done.
      - intros ?. simpl. intros. destruct!/=. naive_solver.
      - ms_solve.
    }
    { ms_solve. }
    assert ([set x | ∃ y : <<discr Z>>, x = (y, y)] = \bigcup_i ([set (match decode_nat i with
                                                                       | Some x => (x, x)
                                                                       | None => (0,0)%Z
                                                                                     end
           )] ) )as ->.
    { rewrite eqEsubset; split; intros ?; simpl; intros [x ]; destruct!/=.
      - exists (encode_nat x); first done. by rewrite decode_encode_nat.
      - case_match; destruct!/=; naive_solver.
    }
    apply: bigcup_measurable.    
    intros. case_match;
      rewrite measurable_prod_measurableType/=; apply:sub_sigma_algebra; simpl; eexists (set1 _); try done. eexists (set1 _); try done.
    rewrite eqEsubset; split; intros ?; simpl; intros; destruct!/=; naive_solver.
  - apply: apply_measurable_fun.
    { mf_prod; apply: measurable_comp; last first.
      - apply measurable_snd_restriction. ms_solve.
      - mf_done.
      - intros ?. simpl. intros. destruct!/=. naive_solver.
      - ms_solve.
      - apply measurable_fst_restriction. ms_solve.
      - mf_done.
      - intros ?. simpl. intros. destruct!/=. naive_solver.
      - ms_solve.
    }
    { ms_solve. }
    assert ([set x | ∃ y : <<discr bool>>, x = (y, y)] = \bigcup_i ([set (match decode_nat i with
                                                                       | Some x => (x, x)
                                                                       | None => (inhabitant, inhabitant)
                                                                                     end
           )] ) )as ->.
    { rewrite eqEsubset; split; intros ?; simpl; intros [x ]; destruct!/=.
      - exists (encode_nat x); first done. by rewrite decode_encode_nat.
      - case_match; destruct!/=; naive_solver.
    }
    apply: bigcup_measurable.
    intros. case_match;
      rewrite measurable_prod_measurableType/=; apply:sub_sigma_algebra; simpl; eexists (set1 _); try done; eexists (set1 _); try done;
    rewrite eqEsubset; split; intros ?; simpl; intros; destruct!/=; naive_solver.
  - ms_solve.
  - apply: apply_measurable_fun.
    { mf_prod; apply: measurable_comp; last first.
      - apply measurable_snd_restriction. ms_solve.
      - mf_done.
      - intros ?. simpl. intros. destruct!/=. naive_solver.
      - ms_solve.
      - apply measurable_fst_restriction. ms_solve.
      - mf_done.
      - intros ?. simpl. intros. destruct!/=. naive_solver.
      - ms_solve.
    }
    { ms_solve. }
    assert ([set x | ∃ y, x = (y, y)] = \bigcup_i ([set (match decode_nat i with
                                                                       | Some x => (x, x)
                                                                       | None => (inhabitant, inhabitant)
                                                                                     end
           )] ) )as ->.
    { rewrite eqEsubset; split; intros ?; simpl; intros [x ]; destruct!/=.
      - exists (encode_nat x); first done. by rewrite decode_encode_nat.
      - case_match; destruct!/=; naive_solver.
    }
    apply: bigcup_measurable.
    intros. case_match;
      rewrite measurable_prod_measurableType/=; apply:sub_sigma_algebra; simpl; eexists (set1 _); try done; eexists (set1 _); try done;
    rewrite eqEsubset; split; intros ?; simpl; intros; destruct!/=; naive_solver.
  - apply: apply_measurable_fun.
    { mf_prod; apply: measurable_comp; last first.
      - apply measurable_snd_restriction. ms_solve.
      - mf_done.
      - intros ?. simpl. intros. destruct!/=. naive_solver.
      - ms_solve.
      - apply measurable_fst_restriction. ms_solve.
      - mf_done.
      - intros ?. simpl. intros. destruct!/=. naive_solver.
      - ms_solve.
    }
    { ms_solve. }
    assert ([set x | ∃ y, x = (y, y)] = \bigcup_i ([set (match decode_nat i with
                                                                       | Some x => (x, x)
                                                                       | None => (inhabitant, inhabitant)
                                                                                     end
           )] ) )as ->.
    { rewrite eqEsubset; split; intros ?; simpl; intros [x ]; destruct!/=.
      - exists (encode_nat x); first done. by rewrite decode_encode_nat.
      - case_match; destruct!/=; naive_solver.
    }
    apply: bigcup_measurable.
    intros. case_match;
      rewrite measurable_prod_measurableType/=; apply:sub_sigma_algebra; simpl; eexists (set1 _); try done; eexists (set1 _); try done;
    rewrite eqEsubset; split; intros ?; simpl; intros; destruct!/=; naive_solver.
  - apply: apply_measurable_fun.
    { mf_prod; apply: measurable_comp.
      3: apply: eq_real_meas_fun.
      - ms_solve.
      - by intros.
      - mf_prod; apply: measurable_comp; last first.
        + apply measurable_snd_restriction. ms_solve.
        + mf_done.
        + intros ?. simpl. intros. destruct!/=. naive_solver.
        + ms_solve.
        + apply measurable_fst_restriction. ms_solve.
        + mf_done.
        + intros ?. simpl. intros. destruct!/=. naive_solver.
        + ms_solve.
    }
    { ms_solve. }
    ms_solve.
    Unshelve.
    all: apply: inhabitant.
Qed. 
Hint Resolve base_lit_diag_meas_set   : mf_set.

Definition safe_val_diag := image base_lit_diag (LitVU \o fst △ LitVU \o snd) `|`
                              image base_lit_diag (InjLVU \o LitVU \o fst △ InjLVU \o LitVU \o snd) `|`

                              image base_lit_diag (InjRVU \o LitVU \o fst △ InjRVU \o LitVU \o snd).
Lemma safe_val_diag_meas_set : measurable safe_val_diag.
Proof.
  repeat apply: measurable_setU.
  - assert (image base_lit_diag (LitVU \o fst △ LitVU \o snd) =
            (vcov_lit `*` vcov_lit) `&` preimage (𝜋_LitV_v \o fst △ 𝜋_LitV_v \o snd) base_lit_diag 
           ) as ->.
    { rewrite eqEsubset; split; intros []; simpl; intros; destruct!/=; naive_solver. }
    apply: apply_measurable_fun; ms_solve.
    mf_prod; apply: measurable_comp; last first.
    + apply measurable_snd_restriction. ms_solve.
    + mf_done.
    + intros ?. simpl. intros. destruct!/=. naive_solver.
    + ms_solve.
    + apply measurable_fst_restriction. ms_solve.
    + mf_done.
    + intros ?. simpl. intros. destruct!/=. naive_solver.
    + ms_solve.
  - assert (image base_lit_diag (InjLVU \o LitVU \o fst △ InjLVU \o LitVU \o snd) =
             (vcov_injlv `*` vcov_injlv)`&` preimage (𝜋_InjLV_v  \o fst △ 𝜋_InjLV_v  \o snd)
              ((vcov_lit `*` vcov_lit) `&` preimage (𝜋_LitV_v \o fst △ 𝜋_LitV_v \o snd) base_lit_diag )) as ->.
    { rewrite eqEsubset; split; intros []; simpl; intros; destruct!/=; naive_solver. }
    apply: apply_measurable_fun; ms_solve; mf_prod; apply: measurable_comp; try apply: measurable_fst_restriction; try apply:  measurable_snd_restriction; last first; try mf_done; ms_solve; intros ?; simpl; intros; destruct!/=; naive_solver.
  - assert (image base_lit_diag (InjRVU \o LitVU \o fst △ InjRVU \o LitVU \o snd) =
             (vcov_injrv `*` vcov_injrv)`&` preimage (𝜋_InjRV_v  \o fst △ 𝜋_InjRV_v  \o snd)
              ((vcov_lit `*` vcov_lit) `&` preimage (𝜋_LitV_v \o fst △ 𝜋_LitV_v \o snd) base_lit_diag )) as ->.
    { rewrite eqEsubset; split; intros []; simpl; intros; destruct!/=; naive_solver. }
    apply: apply_measurable_fun; ms_solve; mf_prod; apply: measurable_comp; try apply: measurable_fst_restriction; try apply:  measurable_snd_restriction; last first; try mf_done; ms_solve; intros ?; simpl; intros; destruct!/=; naive_solver.
Qed. 
Hint Resolve safe_val_diag_meas_set   : mf_set.

Definition safe_val:= image setT LitVU `|` image setT (InjLVU \o LitVU)
                         `|` image setT (InjRVU \o LitVU).
Lemma safe_val_meas_set: measurable safe_val.
Proof.
  repeat apply: measurable_setU.
  - ms_solve.
  - assert (image setT (InjLVC \o LitVC) =
            val_ST (InjLV (LitV (LitInt setT))) `|`
            val_ST (InjLV (LitV (LitBool setT))) `|`
            val_ST (InjLV (LitV (LitUnit))) `|`
            val_ST (InjLV (LitV (LitLoc setT))) `|`
            val_ST (InjLV (LitV (LitLbl setT))) `|`
            val_ST (InjLV (LitV (LitReal setT)))
           ) as ->.
    { rewrite eqEsubset; split; intros ?; simpl; intros; destruct!/=; [|naive_solver..].
      destruct x; naive_solver. }
    repeat apply: measurable_setU.
    + apply sub_sigma_algebra.
      rewrite /val_cyl/=.
      eexists (InjLV (LitV (LitInt setT))); last done.
      rewrite /val_ML/base_lit_ML. ms_solve. 
    + apply sub_sigma_algebra.
      rewrite /val_cyl/=.
      eexists (InjLV (LitV (LitBool setT))); last done.
      rewrite /val_ML/base_lit_ML. ms_solve. 
    + apply sub_sigma_algebra.
      rewrite /val_cyl/=.
      eexists (InjLV (LitV (LitUnit))); last done.
      rewrite /val_ML/base_lit_ML. ms_solve. 
    + apply sub_sigma_algebra.
      rewrite /val_cyl/=.
      eexists (InjLV (LitV (LitLoc setT))); last done.
      rewrite /val_ML/base_lit_ML. ms_solve. 
    + apply sub_sigma_algebra.
      rewrite /val_cyl/=.
      eexists (InjLV (LitV (LitLbl setT))); last done.
      rewrite /val_ML/base_lit_ML. ms_solve. 
    + apply sub_sigma_algebra.
      rewrite /val_cyl/=.
      eexists (InjLV (LitV (LitReal setT))); last done.
      rewrite /val_ML/base_lit_ML. ms_solve.
  - assert (image setT (InjRVC \o LitVC) =
            val_ST (InjRV (LitV (LitInt setT))) `|`
            val_ST (InjRV (LitV (LitBool setT))) `|`
            val_ST (InjRV (LitV (LitUnit))) `|`
            val_ST (InjRV (LitV (LitLoc setT))) `|`
            val_ST (InjRV (LitV (LitLbl setT))) `|`
            val_ST (InjRV (LitV (LitReal setT)))
           ) as ->.
    { rewrite eqEsubset; split; intros ?; simpl; intros; destruct!/=; [|naive_solver..].
      destruct x; naive_solver. }
    repeat apply: measurable_setU.
    + apply sub_sigma_algebra.
      rewrite /val_cyl/=.
      eexists (InjRV (LitV (LitInt setT))); last done.
      rewrite /val_ML/base_lit_ML. ms_solve. 
    + apply sub_sigma_algebra.
      rewrite /val_cyl/=.
      eexists (InjRV (LitV (LitBool setT))); last done.
      rewrite /val_ML/base_lit_ML. ms_solve. 
    + apply sub_sigma_algebra.
      rewrite /val_cyl/=.
      eexists (InjRV (LitV (LitUnit))); last done.
      rewrite /val_ML/base_lit_ML. ms_solve. 
    + apply sub_sigma_algebra.
      rewrite /val_cyl/=.
      eexists (InjRV (LitV (LitLoc setT))); last done.
      rewrite /val_ML/base_lit_ML. ms_solve. 
    + apply sub_sigma_algebra.
      rewrite /val_cyl/=.
      eexists (InjRV (LitV (LitLbl setT))); last done.
      rewrite /val_ML/base_lit_ML. ms_solve. 
    + apply sub_sigma_algebra.
      rewrite /val_cyl/=.
      eexists (InjRV (LitV (LitReal setT))); last done.
      rewrite /val_ML/base_lit_ML. ms_solve.
Qed. 

Hint Resolve safe_val_meas_set   : mf_set.

Definition safe_val_pair := (setT `*` safe_val) `|` (safe_val `*` setT).
Lemma safe_val_pair_meas_set : measurable safe_val_pair.
Proof.
  apply: measurable_setU; ms_solve.
Qed.
Hint Resolve safe_val_pair_meas_set   : mf_set.



Definition bin_op_eval'_cov_eq :=
  (image safe_val_pair (λ '(x1,x2), ((EqOp:<<discr bin_op>>, x1), x2))).
Lemma bin_op_eval'_cov_eq_meas_set : measurable bin_op_eval'_cov_eq.
Proof. 
  assert (bin_op_eval'_cov_eq=
          (([set EqOp:<<discr bin_op>>] `*` setT) `*` setT) `&`
            preimage (fst \o fst △ (snd \o fst△snd)) (setT `*` safe_val_pair)) as ->.
  { rewrite eqEsubset; split; simpl; intros [[]]; rewrite /bin_op_eval'_cov_eq/safe_val_pair/safe_val;  simpl in *.
    - intros. destruct!/=; simpl in *; simplify_eq; naive_solver.
    - intros. destruct!/=; eexists (_,_); try done; simpl; naive_solver. }
  apply: apply_measurable_fun; ms_solve.
  repeat mf_prod.
  - mf_cmp_tree; apply: measurable_fst_restriction; ms_solve.
  - mf_cmp_tree; [apply: measurable_snd_restriction| apply: measurable_fst_restriction]; ms_solve.
  - apply: measurable_snd_restriction; ms_solve.
Qed. 
Hint Resolve bin_op_eval'_cov_eq_meas_set   : mf_set.
  
Definition bin_op_eval'_cov_eq_same := (image safe_val_diag (λ '(x1,x2), ((EqOp:<<discr bin_op>>, x1), x2))).
Lemma bin_op_eval'_cov_eq_same_meas_set : measurable bin_op_eval'_cov_eq_same.
  assert (bin_op_eval'_cov_eq_same=
          (([set EqOp:<<discr bin_op>>] `*` setT) `*` setT) `&`
            preimage (fst \o fst △ (snd \o fst△snd)) (setT `*` safe_val_diag)) as ->.
  { rewrite eqEsubset; split; simpl; intros [[]]; rewrite /bin_op_eval'_cov_eq_same /safe_val_diag/=.
    - intros [[][[|]|]]; simplify_eq; naive_solver.
    - intros [[[]][?[[|]|]]]; simplify_eq; naive_solver.
  }
  apply: apply_measurable_fun; ms_solve.
  repeat mf_prod.
  - mf_cmp_tree; apply: measurable_fst_restriction; ms_solve.
  - mf_cmp_tree; [apply: measurable_snd_restriction| apply: measurable_fst_restriction]; ms_solve.
  - apply: measurable_snd_restriction; ms_solve.
Qed. 
Hint Resolve bin_op_eval'_cov_eq_same_meas_set   : mf_set.




Definition bin_op_eval'_cov_int  : set (<<discr bin_op>> * val * val)%type :=
  (((setC [set EqOp]) `*` (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitInt)) `*` (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitInt)).
Definition bin_op_eval'_cov_real : set (<<discr bin_op>> * val * val)%type :=
  (([set PlusOp; MinusOp; MultOp; LeOp; LtOp] `*` (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitReal)) `*` (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitReal)).
Definition bin_op_eval'_cov_bool : set (<<discr bin_op>> * val * val)%type:=
  (([set AndOp; OrOp; XorOp] `*` (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitBool)) `*`
  (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitBool)).
Definition bin_op_eval'_cov_locX : set (<<discr bin_op>> * val * val)%type:=
  (([set OffsetOp] `*` (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitLoc)) `*`
     (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitInt)) `|`
    (([set LeOp; LtOp] `*` (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitLoc)) `*`
     (setI vcov_lit $ preimage 𝜋_LitV_v $ bcov_LitLoc))
.

Lemma bin_op_eval'_cov_int_meas_set  : measurable bin_op_eval'_cov_int.
Proof.
  rewrite /bin_op_eval'_cov_int.
  ms_solve.
Qed. 
Lemma bin_op_eval'_cov_real_meas_set : measurable bin_op_eval'_cov_real.
Proof.
  rewrite /bin_op_eval'_cov_real.
  ms_solve.
Qed. 
Lemma bin_op_eval'_cov_bool_meas_set : measurable bin_op_eval'_cov_bool.
Proof.
  rewrite /bin_op_eval'_cov_bool.
  ms_solve.
Qed.  
Lemma bin_op_eval'_cov_locX_meas_set : measurable bin_op_eval'_cov_locX. 
Proof.
  rewrite /bin_op_eval'_cov_locX.
  apply: measurable_setU; ms_solve.
Qed. 

Hint Resolve bin_op_eval'_cov_int_meas_set  : mf_set.
Hint Resolve bin_op_eval'_cov_real_meas_set : mf_set.
Hint Resolve bin_op_eval'_cov_bool_meas_set : mf_set.
Hint Resolve bin_op_eval'_cov_locX_meas_set  : mf_set.


Definition bin_op_eval'_eq   : (<<discr bin_op>> * val * val)%type -> option val :=
    (if_in bin_op_eval'_cov_eq_same
       (cst ((Some $ LitV $ LitBool $ true):option val))
       (cst ((Some $ LitV $ LitBool $ false):option val))).

(* Definition bin_op_eval'_eq   : (<<discr bin_op>> * val * val)%type -> option val := *)
(*   if_in (bin_op_eval'_eq_safe_cov `&` bin_op_eval'_eq_cov') *)
(*     (cst ((Some $ LitV $ LitBool $ true):option val)) $ *)
(*     if_in (bin_op_eval'_eq_safe_cov `&` setC bin_op_eval'_eq_cov') *)
(*     (cst ((Some $ LitV $ LitBool $ false):option val)) $ *)
(*     cst None.  *)

Definition bin_op_eval'_int  : (<<discr bin_op>> * val * val)%type -> option val :=
  Some \o LitVU \o (uncurry  (λ x, uncurry (bin_op_eval_int x))) \o (fst \o fst△ (𝜋_LitInt_z \o 𝜋_LitV_v  \o snd \o fst△𝜋_LitInt_z \o 𝜋_LitV_v \o snd)).
Definition bin_op_eval'_real : (<<discr bin_op>> * val * val)%type -> option val :=
  bin_op_eval_real' \o ((fst \o fst △ 𝜋_LitReal_r \o 𝜋_LitV_v \o snd \o fst) △ 𝜋_LitReal_r \o 𝜋_LitV_v \o snd).
Definition bin_op_eval'_bool : (<<discr bin_op>> * val * val)%type -> option val :=
  (uncurry (λ x, uncurry (bin_op_eval_bool x))) \o (fst \o fst△ (𝜋_LitBool_b \o 𝜋_LitV_v  \o snd \o fst△𝜋_LitBool_b \o 𝜋_LitV_v \o snd)).
Definition bin_op_eval'_locX : (<<discr bin_op>> * val * val)%type -> option val :=
  bin_op_eval'_loc \o  ((fst \o fst △ 𝜋_LitLoc_l \o 𝜋_LitV_v \o snd \o fst) △  𝜋_LitV_v \o snd).





Lemma bin_op_eval'_eq_meas_fun   : measurable_fun bin_op_eval'_cov_eq   bin_op_eval'_eq.
Proof.
  rewrite /bin_op_eval'_eq.
  apply: if_in_meas_fun.
  - ms_solve. 
  - ms_solve.
  - apply: measurable_cst.
  - apply: measurable_cst.
Qed. 
Lemma bin_op_eval'_int_meas_fun  : measurable_fun bin_op_eval'_cov_int  bin_op_eval'_int.
Proof.
  rewrite /bin_op_eval'_int.
  mf_cmp_tree.
  { repeat mf_cmp_tree; last apply: bin_op_eval_int_measurable_fun.
    - apply Some_meas_fun.
    - apply LitVU_meas_fun.
  }
  repeat mf_prod.
  - mf_cmp_tree; apply: measurable_fst_restriction; ms_solve.
  - rewrite /bin_op_eval'_cov_int.
    apply: (measurable_comp (F:=[set~ EqOp :<<discr bin_op>>] `*` (vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitInt))); last apply: measurable_fst_restriction; last ms_solve; last first.
    { apply: (measurable_comp (F:=(vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitInt))); last apply: measurable_snd_restriction; [| |apply:measurable_comp
                                                                                                                       |].
      4: apply 𝜋_LitV_v_sub.
      all: ms_solve.
      - intros ?; simpl. intros. destruct!/=. naive_solver.
      - apply 𝜋_LitInt_z_meas.
      - rewrite <- (setIid vcov_lit), <- (setIA vcov_lit);
                                 apply: measurable_fun_setI1;
                                 try (by ms_done || by ms_solve || by mf_done).
    }
    + intros ?. simpl. intros. destruct!/=. naive_solver. 
    + ms_solve.
  - rewrite /bin_op_eval'_cov_int.
    apply: (measurable_comp (F:=(vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitInt))); last apply: measurable_snd_restriction; [| |apply:measurable_comp
                                                                                                                     |].
    4: apply 𝜋_LitV_v_sub.
    all: ms_solve.
    +  intros ?; simpl. intros. destruct!/=. naive_solver.
    +  apply 𝜋_LitInt_z_meas.
    +  rewrite <- (setIid vcov_lit), <- (setIA vcov_lit);
                                 apply: measurable_fun_setI1;
                                 try (by ms_done || by ms_solve || by mf_done).
Qed. 
Lemma bin_op_eval'_real_meas_fun : measurable_fun bin_op_eval'_cov_real bin_op_eval'_real.
Proof.
  rewrite /bin_op_eval'_real.
  mf_cmp_tree; first apply bin_op_eval_real'_meas_fun.
  repeat mf_prod.
  { mf_cmp_tree; apply: measurable_fst_restriction; ms_solve. }
  - rewrite /bin_op_eval'_cov_real.
    apply: (measurable_comp (F:=setT`*`(vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitReal))); last first.
    { apply: measurable_fst_restriction; ms_solve. }
    { apply: (measurable_comp (F:=(vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitReal))); last apply: measurable_snd_restriction.
      - ms_solve.
      - intros ?; simpl. intros. destruct!/=. naive_solver.
      - mf_cmp_tree; last mf_done.
        intros ?. simpl. intros. destruct!/=. naive_solver.
      - ms_solve.
    }
    + intros ?; simpl. intros. destruct!/=; naive_solver.
    + ms_solve.
  - rewrite /bin_op_eval'_cov_real.
    apply: (measurable_comp (F:=(vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitReal))); last apply: measurable_snd_restriction.
      + ms_solve.
      + intros ?; simpl. intros. destruct!/=; naive_solver.
      + mf_cmp_tree; last mf_done.
        intros ?. simpl. intros. destruct!/=; naive_solver.
      + ms_solve.
Qed. 
Lemma bin_op_eval'_bool_meas_fun : measurable_fun bin_op_eval'_cov_bool bin_op_eval'_bool.
Proof.
  rewrite /bin_op_eval'_bool.
  mf_cmp_tree; first apply: bin_op_eval_bool_measurable_fun.
  repeat mf_prod.
  { mf_cmp_tree; apply: measurable_fst_restriction; ms_solve. }
  all: rewrite /bin_op_eval'_cov_bool.
  - apply: (measurable_comp (F:=setT`*`(vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitBool))); last first.
    { apply: measurable_fst_restriction; ms_solve. }
    { apply: (measurable_comp (F:=(vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitBool))); last apply: measurable_snd_restriction.
      - ms_solve.
      - intros ?; simpl. intros. destruct!/=. naive_solver.
      - mf_cmp_tree; last mf_done.
        intros ?. simpl. intros. destruct!/=. naive_solver.
      - ms_solve.
    }
    + intros ?; simpl. intros. destruct!/=; naive_solver.
    + ms_solve.
  - apply: (measurable_comp (F:=(vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitBool))); last apply: measurable_snd_restriction.
      + ms_solve.
      + intros ?; simpl. intros. destruct!/=; naive_solver.
      + mf_cmp_tree; last mf_done.
        intros ?. simpl. intros. destruct!/=; naive_solver.
      + ms_solve.
Qed.
Lemma bin_op_eval'_locX_meas_fun : measurable_fun bin_op_eval'_cov_locX bin_op_eval'_locX.
Proof.
  rewrite /bin_op_eval'_locX.
  mf_cmp_tree; first apply: bin_op_eval'_loc_meas_fun.
  repeat mf_prod.
  { mf_cmp_tree; apply: measurable_fst_restriction; ms_solve. }
  all: rewrite /bin_op_eval'_cov_locX.
  - apply: (measurable_comp (F:=setT`*`(vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitLoc))); last first.
    { apply: measurable_fst_restriction; ms_solve. }
    { apply: (measurable_comp (F:=(vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitLoc))); last apply: measurable_snd_restriction.
      - ms_solve.
      - intros ?; simpl. intros. destruct!/=. naive_solver.
      - mf_cmp_tree; last mf_done.
        intros ?. simpl. intros. destruct!/=. naive_solver.
      - ms_solve.
    }
    + intros ?; simpl. intros. destruct!/=; naive_solver.
    + ms_solve.
  - apply: (measurable_comp (F:=(vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitInt) `|` (vcov_lit `&` 𝜋_LitV_v @^-1` bcov_LitLoc))); last apply: measurable_snd_restriction.
      + apply: measurableU;  ms_solve.
      + intros ?; simpl. intros. destruct!/=; naive_solver.
      + apply: measurable_funS; last apply 𝜋_LitV_v_meas; ms_solve. 
        intros ?. simpl. intros. destruct!/=; naive_solver.
      + ms_solve.
Qed.

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


Lemma bin_op_eval'_meas_fun : measurable_fun setT bin_op_eval'.
Proof.
  rewrite /bin_op_eval'.
  apply: if_in_meas_fun; ms_solve.
  { rewrite setIT. mf_done. }
  rewrite setIT. 
  apply: if_in_meas_fun; ms_solve.
  { rewrite setIidl; first mf_done.
    intros ?. intros [][]. simpl in *. destruct!/=.
  }
  apply: if_in_meas_fun; ms_solve.
  { rewrite setIidl; first mf_done.
    intros ?; intros []; split; intros []; simpl in *; destruct!/=.
  }
  apply: if_in_meas_fun; ms_solve.
  { rewrite setIidl; first mf_done.
    intros ?; intros []; repeat split; intros []; simpl in *; destruct!/=.
  }
  apply: if_in_meas_fun; ms_solve.
  rewrite setIidl; first mf_done.
  intros ?; intros []; repeat split; intros []; simpl in *; destruct!/=.
Qed. 

Hint Resolve bin_op_eval'_meas_fun : mf_fun.

Definition bin_op_eval''_ok : set (<<discr bin_op>> * val * val * state)%type :=
  (bin_op_eval'_cov_eq  `|` bin_op_eval'_cov_int `|` bin_op_eval'_cov_real `|` bin_op_eval'_cov_bool `|` bin_op_eval'_cov_locX) `*` setT.

Lemma bin_op_eval''_ok_meas_set :  measurable bin_op_eval''_ok.
  rewrite /bin_op_eval''_ok.
  apply measurableX; last done.
  repeat apply: measurable_setU; ms_solve.
Qed. 

Hint Resolve bin_op_eval''_ok_meas_set  : mf_set.

Definition bin_op_eval'' : (<<discr bin_op>> * val * val * state)%type -> giryM cfg :=
  gRet \o (ValU \o of_option bin_op_eval' \o fst △ snd).

Lemma bin_op_eval''_meas_fun : measurable_fun bin_op_eval''_ok bin_op_eval''.
Proof.
  rewrite /bin_op_eval''_ok/bin_op_eval''.
  mf_cmp_tree.
  { apply measurable_funTS. apply: gRet_meas_fun. }
  mf_prod; last apply: measurable_snd_restriction; ms_solve.
  apply: measurable_comp; last apply: measurable_fst_restriction; last ms_solve; last first.
  2:{ instantiate (1:= (bin_op_eval'_cov_eq `|` bin_op_eval'_cov_int `|` bin_op_eval'_cov_real
                          `|` bin_op_eval'_cov_bool `|` bin_op_eval'_cov_locX)).
      intros ?. simpl. intros [[[[]] ] [[[[[|]|]|]|] ]]; subst; simpl; naive_solver.
  }
  2:{ repeat apply: measurableU; ms_solve. }
  apply: measurable_comp; [| | apply ValU_meas_fun|]; try done.
  assert ((bin_op_eval'_cov_eq `|` bin_op_eval'_cov_int `|` bin_op_eval'_cov_real `|` bin_op_eval'_cov_bool
             `|` bin_op_eval'_cov_locX) = bin_op_eval' @^-1` option_cov_Some) as ->; last apply of_option_meas_fun, bin_op_eval'_meas_fun.
  rewrite /bin_op_eval'.
  rewrite eqEsubset; split; intros [[]]; simpl.
  - rewrite !Logic.or_assoc.
    assert (∀ P Q, P \/ Q <-> P \/ (¬ P /\ Q)) as Hrewrite.
    { split; last naive_solver.
      pose proof lem P as [|]; naive_solver.
    }
    rewrite Hrewrite; elim.
    { intros ?. setoid_rewrite ifIn_eq_left; last done.
      apply: if_in_split; rewrite /option_cov_Some/=; naive_solver.
    }
    elim. intros H1.
    rewrite Hrewrite. elim.
    { intros ?. setoid_rewrite ifIn_eq_right; last done.
      setoid_rewrite ifIn_eq_left; last done.
      rewrite /bin_op_eval'_int/option_cov_Some/=. naive_solver.
    }
    elim. intros H2.
    rewrite Hrewrite. elim.
    { intros H. do 2 (setoid_rewrite ifIn_eq_right; last done).
      setoid_rewrite ifIn_eq_left; last done.
      rewrite /bin_op_eval'_real/bin_op_eval_real'/option_cov_Some/=.
      rewrite /bin_op_eval_real'_plus/bin_op_eval_real'_minus/bin_op_eval_real'_mul/bin_op_eval_real'_le/bin_op_eval_real'_lt.
      repeat eapply if_in_split; simpl; [naive_solver..|].
      destruct H. 
      intros K1 K2 K3 K4 K5. exfalso.
      rewrite /bin_op_eval'_cov_real in H. destruct!/=.
      - apply K5. rewrite /bin_op_eval_real'_cov_plus. naive_solver.
      - apply K4. rewrite /bin_op_eval_real'_cov_minus. naive_solver.
      - apply K3. rewrite /bin_op_eval_real'_cov_mul. naive_solver.
      - apply K2. rewrite /bin_op_eval_real'_cov_le. naive_solver.
      - apply K1. rewrite /bin_op_eval_real'_cov_lt. naive_solver.   
    }
    elim. intros H3.
    rewrite Hrewrite. elim.
    { intros H. do 3 (setoid_rewrite ifIn_eq_right; last done).
      setoid_rewrite ifIn_eq_left; last done.
      rewrite /bin_op_eval'_bool/option_cov_Some/=.
      rewrite /bin_op_eval_bool.
      destruct H. destruct!/=; naive_solver.
    }
    elim.
    intros H4.
    intros H. do 4 (setoid_rewrite ifIn_eq_right; last done).
    setoid_rewrite ifIn_eq_left; last done.
    rewrite /bin_op_eval'_locX/=.
    rewrite /bin_op_eval'_loc.
    rewrite /bin_op_eval'_loc_offset_int/bin_op_eval'_loc_le_loc/bin_op_eval'_loc_lt_loc/option_cov_Some/=.
    repeat eapply if_in_split; simpl; [naive_solver..|].
    intros K1 K2 K3. exfalso.
    rewrite /bin_op_eval'_cov_locX in H.
    destruct!/=.
    + apply K3. rewrite /bin_op_eval'_loc_cov_offset_int. naive_solver. 
    + apply K2. rewrite /bin_op_eval'_loc_cov_le_loc. naive_solver.
    + apply K1. rewrite /bin_op_eval'_loc_cov_lt_loc. naive_solver.
  - do 5 (eapply if_in_split; first naive_solver).
    rewrite /option_cov_Some. naive_solver.
Qed.
Hint Resolve bin_op_eval''_meas_fun : mf_fun.

Definition bin_op_eval''' : (<<discr bin_op>> * val * val * state)%type -> giryM cfg := if_in bin_op_eval''_ok bin_op_eval'' (cst gZero).

Definition bin_op_eval'''_meas_fun : measurable_fun setT bin_op_eval'''.
Proof.
  rewrite /bin_op_eval'''.
  apply: if_in_meas_fun; ms_solve.
  rewrite setIT.
  apply bin_op_eval''_meas_fun.
Qed. 

Hint Resolve bin_op_eval'''_meas_fun : mf_fun.
