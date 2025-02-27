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


Section arithmetic.
(** Arithmetic functions bug given measurale types *)

Definition neg_bool   : <<discr bool>> -> <<discr bool>> := negb.
Definition neg_int    : <<discr Z>> -> <<discr Z>> := Z.lnot.
Definition minus_int  : <<discr Z>> -> <<discr Z>> := Z.opp.
Definition minus_real : R -> R := Ropp.

(* TODO: measurable_fun for each of these *)

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

(** TODO: Define these sets in a way that works with the automation *)
Definition un_op_eval'_cov_neg_bool    : set (<<discr un_op>> * val). Admitted.
Definition un_op_eval'_cov_neg_int     : set (<<discr un_op>> * val). Admitted.
Definition un_op_eval'_cov_minus_int   : set (<<discr un_op>> * val). Admitted.
Definition un_op_eval'_cov_minus_real  : set (<<discr un_op>> * val). Admitted.

Lemma un_op_eval'_cov_neg_bool_meas_set : measurable un_op_eval'_cov_neg_bool.
Proof. Admitted.

Lemma un_op_eval'_cov_neg_int_meas_set : measurable un_op_eval'_cov_neg_int.
Proof. Admitted.

Lemma un_op_eval'_cov_minus_int_meas_set : measurable un_op_eval'_cov_minus_int.
Proof. Admitted.

Lemma un_op_eval'_cov_minus_real_meas_set : measurable un_op_eval'_cov_minus_real.
Proof. Admitted.

Hint Resolve un_op_eval'_cov_neg_bool_meas_set : measlang.
Hint Resolve un_op_eval'_cov_neg_int_meas_set : measlang.
Hint Resolve un_op_eval'_cov_minus_int_meas_set : measlang.
Hint Resolve un_op_eval'_cov_minus_real_meas_set : measlang.

Ltac ml_done := by eauto with measlang.



Definition un_op_eval'_neg_bool : (<<discr un_op>> * val) -> option val :=
  Some \o LitV \o LitBool \o neg_bool \o 𝜋_LitBool_b \o 𝜋_LitV_v \o snd.

Definition un_op_eval'_neg_int : (<<discr un_op>> * val) -> option val :=
  Some \o LitV \o LitInt \o neg_int \o 𝜋_LitInt_z \o 𝜋_LitV_v \o snd.

Definition un_op_eval'_minus_int : (<<discr un_op>> * val) -> option val :=
  Some \o LitV \o LitInt \o minus_int \o 𝜋_LitInt_z \o 𝜋_LitV_v \o snd.

Definition un_op_eval'_minus_real : (<<discr un_op>> * val) -> option val :=
  Some \o LitV \o LitReal \o minus_real \o 𝜋_LitReal_r \o 𝜋_LitV_v \o snd.

Ltac mf_Some := fail.



(* un_op_eval: Measurable version *)
Definition un_op_eval' : (<<discr un_op>> * val)%type -> option val :=
  if_in un_op_eval'_cov_neg_bool    un_op_eval'_neg_bool   $
  if_in un_op_eval'_cov_neg_int     un_op_eval'_neg_int    $
  if_in un_op_eval'_cov_minus_int   un_op_eval'_minus_int  $
  if_in un_op_eval'_cov_minus_real  un_op_eval'_minus_real $
  cst None.

(* TODO: Make sure this is the right theorem first *)
Lemma un_op_eval_eq (op : <<discr un_op>>) (v : val) : un_op_eval op v = un_op_eval' (op, v).
Proof. Admitted.








(* bin_op_eval_int: Normal (reducible) version *)
Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : base_lit :=
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


(* bin_op_eval_bool: Normal (reducible) version *)
Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
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

(* bin_op_eval_loc: Normal (reducible) version *)
Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
  | LeOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 ≤ₗ l2))
  | LtOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 <ₗ l2))
  | _, _ => None
  end.

(* bin_op_eval_real: Normal (reducible) version *)
Definition bin_op_eval_real (op : bin_op) (r1 r2 : R) : option base_lit :=
  match op with
  | PlusOp => Some $ LitReal (r1 + r2)
  | MinusOp => Some $ LitReal (r1 - r2)
  | MultOp => Some $ LitReal (r1 * r2)
  | LeOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 <= r2)%R
  | LtOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 < r2)%R
  | EqOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 = r2)%R
  | _ => None
  end%R.



(*
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
