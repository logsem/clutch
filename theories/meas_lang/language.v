Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz Logic.FunctionalExtensionality Reals.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From clutch.prelude Require Import base.
From clutch.bi Require Import weakestpre.
From mathcomp.analysis Require Import measure ereal.
From clutch.prob.monad Require Export giry meas_markov.
From clutch.meas_lang Require Import prelude.

Require Import mathcomp.reals_stdlib.Rstruct.
Require Import mathcomp.reals.reals.
Set Warnings "hiding-delimiting-key".

Section language_mixin.
  Local Open Scope classical_set_scope.
  Context {d_expr d_val d_state : measure_display}.
  Context {exprT valT stateT : Type}.
  Context `{SigmaAlgebra d_expr exprT}.
  Context `{SigmaAlgebra d_val valT}.
  Context `{SigmaAlgebra d_state stateT}.

  Notation val := (toPackedType d_val valT).
  Notation expr := (toPackedType d_expr exprT).
  Notation state := (toPackedType d_state stateT).

  Context (of_val : val -> expr).
  Context (to_val : expr → option val).
  Context (prim_step : (toPackedType (measure_prod_display (d_expr, d_state)) (exprT * stateT)%type) ->
                       ((giryM (toPackedType (measure_prod_display (d_expr, d_state)) (exprT * stateT)%type)))).

  Record MeasLanguageMixin := {
    mixin_of_val_meas : measurable_fun setT of_val;
    mixin_to_val_meas : measurable_fun setT to_val;
    mixin_prim_step_meas : measurable_fun setT prim_step;

    mixin_expr_meas_points : forall (e : expr), measurable [set e];
    mixin_val_meas_points : forall (v : val), measurable [set v];
    mixin_state_meas_points : forall (s : state), measurable [set s];

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
  exprT : Type;
  valT : Type;
  stateT : Type;
  expr_SigmaAlgebra : SigmaAlgebra d_expr exprT;
  val_SigmaAlgebra : SigmaAlgebra d_val valT;
  state_SigmaAlgebra : SigmaAlgebra d_state stateT;
  of_val : (toPackedType d_val valT) → (toPackedType d_expr exprT);
  to_val : (toPackedType d_expr exprT) → option (toPackedType d_val valT);
  prim_step : (toPackedType _ (exprT * stateT)%type) -> giryM (toPackedType _ (exprT * stateT)%type);
  language_mixin : MeasLanguageMixin of_val to_val prim_step
}.

Bind Scope expr_scope with exprT.
Bind Scope val_scope with valT.

Global Arguments MeasLanguage {_ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments prim_step {_}.


#[global] Existing Instance expr_SigmaAlgebra.
#[global] Existing Instance val_SigmaAlgebra.
#[global] Existing Instance state_SigmaAlgebra.

Canonical Structure stateO (Λ : meas_language) := leibnizO (stateT Λ).
Canonical Structure valO (Λ : meas_language) := leibnizO (valT Λ).
Canonical Structure exprO (Λ : meas_language):= leibnizO (exprT Λ).

(*
Notation valO Λ := (MeasO val).
Notation exprO Λ := (MeasO expr).
Notation stateO Λ := (MeasO state).

Canonical Structure stateO Λ := leibnizO (state Λ).
Canonical Structure valO Λ := leibnizO (val Λ).
Canonical Structure exprO Λ := leibnizO (expr Λ).
*)

Notation val Λ := (toPackedType (d_val Λ) (valT Λ)).
Notation expr Λ := (toPackedType (d_expr Λ) (exprT Λ)).
Notation state Λ := (toPackedType (d_state Λ) (stateT Λ)).

Definition cfg (Λ : meas_language) := (expr Λ * state Λ)%type.

Definition fill_lift {Λ} (K : (expr Λ) -> (expr Λ)) : (expr Λ * state Λ) → (expr Λ * state Λ) :=
  mProd (ssrfun.comp K fst) snd.

Lemma fill_lift_measurable {Λ} (K : (expr Λ) -> (expr Λ)) (HK : measurable_fun setT K) :
  @measurable_fun _ _ (expr Λ * state Λ)%type (expr Λ * state Λ)%type setT (fill_lift K).
Proof.
  mcrunch_prod.
  { mcrunch_comp. }
  { eauto with measlang. }
Qed.

Global Instance inj_fill_lift {Λ : meas_language} (K : (expr Λ -> expr Λ)) :
  Inj (=) (=) K →
  Inj (=) (=) (fill_lift K).
Proof. by intros ? [] [] [=->%(inj _) ->]. Qed.

Class MeasLanguageCtx {Λ : meas_language} (K : (expr Λ) -> (expr Λ))  := {
  K_measurable : measurable_fun setT K;
  fill_not_val e :
    to_val e = None → to_val (K e) = None;
  fill_inj : Inj (=) (=) K;
  fill_dmap e1 σ1 :
    to_val e1 = None →
    prim_step ((K e1), σ1) ≡μ gMap (fill_lift_measurable K K_measurable) (prim_step (e1, σ1))
}.

#[global] Existing Instance fill_inj.

Inductive atomicity := StronglyAtomic | WeaklyAtomic.

Definition meas_lang_markov_mixin (Λ : meas_language) :
  MeasMarkovMixin (@prim_step Λ) (ssrfun.comp to_val fst).
Proof.
  constructor.
  { by apply language_mixin. }
  { eapply measurable_comp.
    { by eapply @measurableT. }
    { done. }
    { by apply language_mixin. }
    { simpl. by eapply @measurable_fst. }
  }
  intros [e σ]; simpl.
  pose proof (lem (is_zero (prim_step (e, σ)))) as [|H]; first done.
  pose proof (mixin_val_stuck _ _ _ (language_mixin Λ) _ _ H) as ->.
  rewrite /is_Some.
  naive_solver.
Qed.

Canonical Structure meas_lang_markov (Λ : meas_language) := MeasMarkov _ _ _ _ (meas_lang_markov_mixin Λ).


Section language.
  Context {Λ : meas_language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.


  (* From the mixin *)
  Lemma of_val_meas : measurable_fun setT (@of_val Λ).
  Proof. apply language_mixin. Qed.
  Lemma to_val_meas : measurable_fun setT (@to_val Λ).
  Proof. apply language_mixin. Qed.
  Lemma prim_step_meas : measurable_fun setT (@prim_step Λ).
  Proof. apply language_mixin. Qed.
  Lemma expr_meas_points : forall (e : expr Λ), measurable [set e].
  Proof. apply language_mixin. Qed.
  Lemma val_meas_points : forall (e : val Λ), measurable [set e].
  Proof. apply language_mixin. Qed.
  Lemma state_meas_points : forall (e : state Λ), measurable [set e].
  Proof. apply language_mixin. Qed.
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. apply language_mixin. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. apply language_mixin. Qed.
  Lemma val_stuck e σ : (¬ is_zero (prim_step (e, σ))) → to_val e = None.
  Proof. apply language_mixin. Qed.
  Lemma prim_step_mass e σ : (¬ is_zero (prim_step (e, σ))) -> is_prob (prim_step (e, σ)).
  Proof. apply language_mixin. Qed.


  Local Open Scope classical_set_scope.
  Lemma irreducible_meas_set : measurable (irreducible : set (expr Λ * state Λ)%type).
  Proof.
    unfold irreducible.
    have H1 : giry_display.-measurable is_zero.
    { intros m T.
      unfold is_zero.
      by eapply eq_gZero_measurable. }
    have X := (@step_meas (meas_lang_markov Λ) _ is_zero).
    have X1 := X _ (H1 _ _).
    rewrite setTI in X1.
    by apply X1.
  Qed.

  Definition to_val_is_val : set (expr Λ * state Λ) := (preimage to_val option_cov_Some) `*` setT.

  Lemma to_val_is_val_meas_set : measurable to_val_is_val.
  Proof.
    unfold to_val_is_val.
    apply measurableX; last by eapply @measurableT.
    rewrite <- (setTI (preimage _ _)).
    apply to_val_meas.
    { by eapply @measurableT. }
    { by apply option_cov_Some_meas_set. }
  Qed.

  (* NOTE: This is fairly different to the Clutch version *)
  Class Atomic (a : atomicity) (e : expr Λ) : Prop :=
    atomic σ :
      if a is WeaklyAtomic
        then has_support_in (prim_step (e, σ)) irreducible
        else has_support_in (prim_step (e, σ)) to_val_is_val.

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  
  Lemma strongly_atomic_atomic e a :
    Atomic StronglyAtomic e → Atomic a e.
  Proof.
    unfold Atomic. destruct a; eauto.
    intros H ?.
    eapply has_support_in_subset; last apply H.
    - apply to_val_is_val_meas_set.
    - apply irreducible_meas_set.
    - rewrite /subset/to_val_is_val/irreducible.
      intros [e' σ']. simpl.
      intros [H1 _].
      destruct (lem (is_zero (prim_step (e', σ')))) as [|H']; first done.
      apply val_stuck in H'.
      rewrite H' in H1.
      rewrite /option_cov_Some in H1. simpl in H1.
      naive_solver.
  Qed.

  Lemma fill_step e σ `{!MeasLanguageCtx K} :
    (¬ is_zero (prim_step (e, σ))) ->
    (¬ is_zero (prim_step (K e, σ))).
  Proof.
    (* FIXME: is this true? *)
    intros Hs.
    rewrite fill_dmap; [| by eapply val_stuck].
    intro Hs'. apply Hs.
    rewrite /is_zero in Hs'.
    rewrite -gMap'_gMap in Hs'.
    eapply gMap'_is_zero; last done. apply fill_lift_measurable.
    apply K_measurable.
  Qed.

  (*
  Lemma fill_step_inv e1' σ1 e2 σ2 `{!LanguageCtx K} :
    to_val e1' = None → prim_step (K e1') σ1 (e2, σ2) > 0 →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 (e2', σ2) > 0.
  Proof.
    intros Hv. rewrite fill_dmap //.
    intros ([e1 σ1'] & [=]%dret_pos & Hstep)%dbind_pos.
    subst. eauto.
  Qed.

  (** The following lemma is redundant, see fill_dmap *)
  Lemma fill_step_prob e1 σ1 e2 σ2 `{!LanguageCtx K} :
    to_val e1 = None →
    prim_step e1 σ1 (e2, σ2) = prim_step (K e1) σ1 (K e2, σ2).
  Proof.
    intros Hv. rewrite fill_dmap //.
    by erewrite (dmap_elem_eq _ (e2, σ2) _ (λ '(e0, σ0), (K e0, σ0))).
  Qed.
   *)
  
  Lemma reducible_fill `{!@MeasLanguageCtx Λ K} e σ :
    reducible (e, σ) → reducible (K e, σ).
  Proof.
    unfold reducible in *. intros H1 H2. apply H1. simpl in *.
    erewrite fill_dmap in H2; last first.
    { by eapply val_stuck. }
    rewrite -gMap'_gMap in H2.
    eapply gMap'_is_zero; last done.
    apply fill_lift_measurable; apply K_measurable.
  Qed.

  Lemma reducible_fill_inv `{!@MeasLanguageCtx Λ K} e σ :
    to_val e = None → reducible (K e, σ) → reducible (e, σ).
  Proof.
    rewrite /reducible. simpl.
    intros H'.
    erewrite fill_dmap; last done.
    intros H1 H2. apply H1.
    rewrite /is_zero in H2.
    rewrite H2.
    by rewrite gZero_map.
    (* TODO: make measure_eq work with rewrite *)
  Qed.
  
  (*
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
*)

  Lemma irreducible_fill `{!@MeasLanguageCtx Λ K} e σ :
    to_val e = None → irreducible (e, σ) → irreducible (K e, σ).
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv. Qed.
  Lemma irreducible_fill_inv `{!@MeasLanguageCtx Λ K} e σ :
    irreducible (K e, σ) → irreducible (e, σ).
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.

  Lemma not_stuck_fill_inv K `{!@MeasLanguageCtx Λ K} e σ :
    not_stuck (K e, σ) → not_stuck (e, σ).
  Proof.
    rewrite /not_stuck /is_final /to_final /= -!not_eq_None_Some.
    intros [?|?].
    - auto using fill_not_val.
    - destruct (decide (to_val e = None)); eauto using reducible_fill_inv.
  Qed.

  Lemma stuck_fill `{!@MeasLanguageCtx Λ K} e σ :
    stuck (e, σ) → stuck (K e, σ).
  Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed.


  Record pure_step (e1 e2 : expr Λ)  := {
    pure_step_safe σ1 : ¬ (is_zero (prim_step (e1, σ1)));
    pure_step_det σ : is_det (e2, σ) (prim_step (e1, σ));
  }.

  Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) :=
    pure_exec : φ → relations.nsteps pure_step n e1 e2.

  Lemma pure_step_ctx K `{!@MeasLanguageCtx Λ K} e1 e2 :
    pure_step e1 e2 → pure_step (K e1) (K e2).
  Proof.
    intros [Hred Hstep]. split.
    { intros σ1.
      eapply (fill_step _); first by apply H.
      by apply Hred. }
    { intros σ.
      rewrite fill_dmap; last by eapply (val_stuck _ σ).
      pose proof Hstep σ as Hdet.
      eapply (is_det_gMap (f:=fill_lift K)) in Hdet.
      - by rewrite gMap'_gMap{1}/fill_lift/= in Hdet.
      - apply fill_lift_measurable. apply K_measurable.
    }
  Qed.

  Lemma pure_step_nsteps_ctx K `{!@MeasLanguageCtx Λ K} n e1 e2 :
    relations.nsteps pure_step n e1 e2 →
    relations.nsteps pure_step n (K e1) (K e2).
  Proof.
    intro H'.
    eapply (nsteps_congruence _ _ _ _ _ _ H' ).
    Unshelve.
    intros x y.
    by apply (pure_step_ctx _).
  Qed.

  Lemma rtc_pure_step_ctx K `{!@MeasLanguageCtx Λ K} e1 e2 :
    rtc pure_step e1 e2 → rtc pure_step (K e1) (K e2).
  Proof.
    intro H'.
    eapply (rtc_congruence _ _ _ _ _ H').
    Unshelve.
    intros x y.
    by apply (pure_step_ctx _).
  Qed.

  (* We do not make this an instance because it is awfully general. *)
  Lemma pure_exec_ctx K `{!@MeasLanguageCtx Λ K} φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (K e1) (K e2).
  Proof.
    rewrite /PureExec.
    intros H' p.
    apply (pure_step_nsteps_ctx _).
    by apply (H' p).
  Qed.

  
  Lemma PureExec_reducible σ1 φ n e1 e2 :
    φ → PureExec φ (S n) e1 e2 → reducible (e1, σ1).
  Proof. move => Hφ /(_ Hφ). inversion_clear 1. apply H. Qed.

  Lemma PureExec_not_val `{Inhabited (language.state Λ)} φ n e1 e2 :
    φ → PureExec φ (S n) e1 e2 → to_val e1 = None.
  Proof.
    intros Hφ Hex.
    pose proof (PureExec_reducible inhabitant _ _ _ _ Hφ Hex) as K.
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

  Lemma fill_is_val e K `{@MeasLanguageCtx Λ K} :
    is_Some (to_val (K e)) → is_Some (to_val e).
  Proof. rewrite -!not_eq_None_Some. eauto using fill_not_val. Qed.

  Lemma rtc_pure_step_val `{!Inhabited (state Λ)} v e :
    rtc pure_step (of_val v) e → to_val e = Some v.
  Proof.
    intros ?; rewrite <- to_of_val.
    f_equal; symmetry; eapply rtc_nf; first done.
    intros [e' [ Hstep ? ]].
    have K := to_of_val v.
    rewrite (val_stuck _ _ (Hstep inhabitant)) in K.
    by inversion K.
  Qed.

End language.


Global Hint Mode PureExec + - - ! - : typeclass_instances.
