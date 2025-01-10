(* TODO cleanup imports *)
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export laws extras.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state.

Local Open Scope classical_set_scope.

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
