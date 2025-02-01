From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Reals.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From clutch.bi Require Import weakestpre.
From mathcomp.analysis Require Import reals measure ereal Rstruct.
From clutch.prob.monad Require Export laws.

Notation giryM := (giryM (R := R)).

Section language_mixin.
  Local Open Scope classical_set_scope.

  (** Measurable types for the language *)
  Context {d_expr d_val d_state : measure_display}.
  Context {expr : measurableType d_expr}.
  Context {val : measurableType d_val}.
  Context {state : measurableType d_state}.

  (** Measurable val/expr coercions *)
  Context (of_val : val → expr).
  Context (of_val_meas : measurable_fun setT of_val).
  Context (to_val : expr → option val).
  Context (to_val_meas : measurable_fun setT to_val).

  (** Measurable step *)
  Context (prim_step : (expr * state)%type -> (giryM (expr * state)%type)).
  Context (prim_step_meas : measurable_fun setT prim_step).

  Record MeasLanguageMixin := {
    (** val/expr coercions are partial inverses *)
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;

    (** If (e, σ) can step to a legal cfg, e is not a value *)
    mixin_val_stuck e σ : (¬ is_zero (prim_step (e, σ))) → to_val e = None;

    (** If (e, σ) can step to a legal cfg, its mass is 1 *)
    mixin_prim_step_mass e σ : (¬ is_zero (prim_step (e, σ))) -> is_prob (prim_step (e, σ))  ;
  }.
End language_mixin.

Structure meas_language := MeasLanguage {
  d_expr : measure_display;
  d_val : measure_display;
  d_state : measure_display;
  expr : measurableType d_expr;
  val : measurableType d_val;
  state : measurableType d_state;
  of_val : val → expr;
  of_val_meas : measurable_fun setT of_val;
  to_val : expr → option val;
  to_val_meas : measurable_fun setT to_val;
  prim_step : (expr * state)%type -> (giryM (expr * state)%type);
  prim_step_meas : measurable_fun setT prim_step;
  language_mixin : MeasLanguageMixin of_val to_val prim_step
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments MeasLanguage {_ _ _ _ _ _ _ _ _ } _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments prim_step {_}.

Canonical Structure stateO Λ := leibnizO (state Λ).
Canonical Structure valO Λ := leibnizO (val Λ).
Canonical Structure exprO Λ := leibnizO (expr Λ).

Definition cfg (Λ : meas_language) := (expr Λ * state Λ)%type.

Program Definition fill_lift {Λ} (K : (expr Λ) -> (expr Λ)) : (expr Λ * state Λ) → (expr Λ * state Λ) :=
  mProd (ssrfun.comp K fst) snd.

Local Lemma fill_lift_measurable {Λ} (K : (expr Λ) -> (expr Λ)) (HK : measurable_fun setT K) :
  @measurable_fun _ _ (expr Λ * state Λ)%type (expr Λ * state Λ)%type setT (fill_lift K).
Proof. Admitted.
(*
  apply measurable_fun_prod.
  { simpl.
    have -> : (λ x : expr Λ * state Λ, K x.1) = m_cmp K fst.
    { apply functional_extensionality.
      intro x.
      by rewrite m_cmp_eval/=. }
    eapply measurable_mapP. }
  { eapply measurable_mapP. }
Qed.
*)

(*
HB.instance Definition _ {Λ} (K : measurable_map (expr Λ) (expr Λ)) :=
  isMeasurableMap.Build _ _ (expr Λ * state Λ)%type (expr Λ * state Λ)%type (fill_lift K) (fill_lift_measurable K).
*)

Global Instance inj_fill_lift {Λ : meas_language} (K : (expr Λ -> expr Λ)) :
  Inj (=) (=) K →
  Inj (=) (=) (fill_lift K).
Proof. by intros ? [] [] [=->%(inj _) ->]. Qed.

Class MeasLanguageCtx {Λ : meas_language} (K : (expr Λ) -> (expr Λ)) (HK : measurable_fun setT K) := {
  fill_not_val e :
    to_val e = None → to_val (K e) = None;
  fill_inj : Inj (=) (=) K;
  fill_dmap e1 σ1 :
    to_val e1 = None →
    prim_step ((K e1), σ1) = giryM_map (fill_lift_measurable K HK) (prim_step (e1, σ1))
}.

#[global] Existing Instance fill_inj.

Inductive atomicity := StronglyAtomic | WeaklyAtomic.

Section language.
  Context {Λ : meas_language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.


  (* From the mixin *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. apply language_mixin. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. apply language_mixin. Qed.
  Lemma val_stuck e σ : (¬ is_zero (prim_step (e, σ))) → to_val e = None.
  Proof. apply language_mixin. Qed.
  Lemma prim_step_mass e σ : (¬ is_zero (prim_step (e, σ))) -> is_prob (prim_step (e, σ)).
  Proof. apply language_mixin. Qed.

  (*
  Class Atomic (a : atomicity) (e : expr Λ) : Prop :=
    atomic σ e' σ' :
      prim_step e σ (e', σ') > 0 →
      if a is WeaklyAtomic then irreducible (e', σ') else is_Some (to_val e').
   *)

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  (*
  Lemma strongly_atomic_atomic e a :
    Atomic StronglyAtomic e → Atomic a e.
  Proof.
    unfold Atomic. destruct a; eauto.
    intros ?????. eapply is_final_irreducible.
    rewrite /is_final /to_final /=. eauto.
  Qed.
  *)

  Lemma fill_step e σ `{!MeasLanguageCtx K HK} :
    (¬ is_zero (prim_step (e, σ))) ->
    (¬ is_zero (prim_step (K e, σ))).
  Proof.
    intros Hs.
    rewrite fill_dmap; [| by eapply val_stuck].
  Admitted.
  (*
    pose HI := @inj_map_inj_eq  _ _ _ _ _ (fill_lift K) _.
    move=> HZ.
    apply Hs; clear Hs.
    move: HI.
    move /(_ _ _ (prim_step (e, σ)) giryM_zero).
    unfold is_zero.
    move ->; try done.
    rewrite giryM_map_zero.
    apply HZ.
  Qed.
   *)

  (*
  Lemma fill_step_inv e1' σ1 e2 σ2 `{!LanguageCtx K} :
    to_val e1' = None → prim_step (K e1') σ1 (e2, σ2) > 0 →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 (e2', σ2) > 0.
  Proof.
    intros Hv. rewrite fill_dmap //.
    intros ([e1 σ1'] & [=]%dret_pos & Hstep)%dbind_pos.
    subst. eauto.
  Qed.

  Lemma fill_step_prob e1 σ1 e2 σ2 `{!LanguageCtx K} :
    to_val e1 = None →
    prim_step e1 σ1 (e2, σ2) = prim_step (K e1) σ1 (K e2, σ2).
  Proof.
    intros Hv. rewrite fill_dmap //.
    by erewrite (dmap_elem_eq _ (e2, σ2) _ (λ '(e0, σ0), (K e0, σ0))).
  Qed.

  Lemma reducible_fill `{!@LanguageCtx Λ K} e σ :
    reducible (e, σ) → reducible (K e, σ).
  Proof.
    unfold reducible in *. intros [[] ?]. eexists; by apply fill_step.
  Qed.
  Lemma reducible_fill_inv `{!@LanguageCtx Λ K} e σ :
    to_val e = None → reducible (K e, σ) → reducible (e, σ).
  Proof.
    intros ? [[e1 σ1] Hstep]; unfold reducible.
    rewrite /step /= in Hstep.
    rewrite fill_dmap // in Hstep.
    apply dmap_pos in Hstep as ([e1' σ2] & ? & Hstep).
    eauto.
  Qed.
  Lemma state_step_reducible e σ σ' α :
    state_step σ α σ' > 0 → reducible (e, σ) ↔ reducible (e, σ').
  Proof. apply state_step_not_stuck. Qed.
  Lemma state_step_iterM_reducible e σ σ' α n:
    iterM n (λ σ, state_step σ α) σ σ'> 0 → reducible (e, σ) ↔ reducible (e, σ').
  Proof.
    revert σ σ'.
    induction n.
    - intros σ σ'. rewrite iterM_O. by intros ->%dret_pos.
    - intros σ σ'. rewrite iterM_Sn. rewrite dbind_pos. elim.
      intros x [??]. pose proof state_step_reducible. naive_solver.
  Qed.

  Lemma irreducible_fill `{!@LanguageCtx Λ K} e σ :
    to_val e = None → irreducible (e, σ) → irreducible (K e, σ).
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv. Qed.
  Lemma irreducible_fill_inv `{!@LanguageCtx Λ K} e σ :
    irreducible (K e, σ) → irreducible (e, σ).
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.

  Lemma not_stuck_fill_inv K `{!@LanguageCtx Λ K} e σ :
    not_stuck (K e, σ) → not_stuck (e, σ).
  Proof.
    rewrite /not_stuck /is_final /to_final /= -!not_eq_None_Some.
    intros [?|?].
    - auto using fill_not_val.
    - destruct (decide (to_val e = None)); eauto using reducible_fill_inv.
  Qed.

  Lemma stuck_fill `{!@LanguageCtx Λ K} e σ :
    stuck (e, σ) → stuck (K e, σ).
  Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed.

  Record pure_step (e1 e2 : expr Λ)  := {
    pure_step_safe σ1 : reducible (e1, σ1);
    pure_step_det σ : prim_step e1 σ (e2, σ) = 1;
  }.

  Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) :=
    pure_exec : φ → relations.nsteps pure_step n e1 e2.

  Lemma pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 :
    pure_step e1 e2 → pure_step (K e1) (K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible in *. intros σ1.
      destruct (Hred σ1) as [[]].
      eexists. by eapply fill_step.
    - intros σ.
      rewrite -fill_step_prob //.
      eapply (to_final_None_1 (_, σ)).
      by eapply reducible_not_final.
  Qed.

  Lemma pure_step_nsteps_ctx K `{!@LanguageCtx Λ K} n e1 e2 :
    relations.nsteps pure_step n e1 e2 →
    relations.nsteps pure_step n (K e1) (K e2).
  Proof. eauto using nsteps_congruence, pure_step_ctx. Qed.

  Lemma rtc_pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 :
    rtc pure_step e1 e2 → rtc pure_step (K e1) (K e2).
  Proof. eauto using rtc_congruence, pure_step_ctx. Qed.

  (* We do not make this an instance because it is awfully general. *)
  Lemma pure_exec_ctx K `{!@LanguageCtx Λ K} φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (K e1) (K e2).
  Proof. rewrite /PureExec; eauto using pure_step_nsteps_ctx. Qed.

  Lemma PureExec_reducible σ1 φ n e1 e2 :
    φ → PureExec φ (S n) e1 e2 → reducible (e1, σ1).
  Proof. move => Hφ /(_ Hφ). inversion_clear 1. apply H. Qed.

  Lemma PureExec_not_val `{Inhabited (language.state Λ)} φ n e1 e2 :
    φ → PureExec φ (S n) e1 e2 → to_val e1 = None.
  Proof.
    intros Hφ Hex.
    destruct (PureExec_reducible inhabitant _ _ _ _ Hφ Hex) => /=.
    simpl in *.
    by eapply val_stuck.
  Qed.     
  
  (* This is a family of frequent assumptions for PureExec *)
  Class IntoVal (e : expr Λ) (v : val Λ) :=
    into_val : of_val v = e.

  Class AsVal (e : expr Λ) := as_val : ∃ v, of_val v = e.
  (* There is no instance [IntoVal → AsVal] as often one can solve [AsVal] more *)
  (* efficiently since no witness has to be computed. *)
  Global Instance as_vals_of_val vs : TCForall AsVal (of_val <$> vs).
  Proof.
    apply TCForall_Forall, Forall_fmap, Forall_true=> v.
    rewrite /AsVal /=; eauto.
  Qed.

  Lemma as_val_is_Some e :
    (∃ v, of_val v = e) → is_Some (to_val e).
  Proof. intros [v <-]. rewrite to_of_val. eauto. Qed.

  Lemma fill_is_val e K `{@LanguageCtx Λ K} :
    is_Some (to_val (K e)) → is_Some (to_val e).
  Proof. rewrite -!not_eq_None_Some. eauto using fill_not_val. Qed.

  Lemma rtc_pure_step_val `{!Inhabited (state Λ)} v e :
    rtc pure_step (of_val v) e → to_val e = Some v.
  Proof.
    intros ?; rewrite <- to_of_val.
    f_equal; symmetry; eapply rtc_nf; first done.
    intros [e' [Hstep _]].
    specialize (Hstep inhabitant) as [? Hval%val_stuck].
    by rewrite to_of_val in Hval.
  Qed.
   *)
End language.

(*
Global Hint Mode PureExec + - - ! - : typeclass_instances.
*)
