From Coq Require Import Reals Psatz.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From iris.bi Require Export weakestpre.
From self.prelude Require Import classical.
From self.prob Require Import distribution.

Section language_mixin.
  Context {expr val state state_idx : Type}.
  Context `{Countable expr, Countable state}.

  Context (of_val : val → expr).
  Context (to_val : expr → option val).

  Context (prim_step  : expr → state → distr (expr * state)).
  Context (state_step : state → state_idx → distr state).

  Record LanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e σ ρ : prim_step e σ ρ > 0 → to_val e = None;
  }.
End language_mixin.

Structure language := Language {
  expr : Type;
  val : Type;
  state : Type;
  state_idx : Type;

  expr_eqdec : EqDecision expr;
  state_eqdec : EqDecision state;
  expr_countable : Countable expr;
  state_countable : Countable state;

  of_val : val → expr;
  to_val : expr → option val;
  prim_step : expr → state → distr (expr * state);
  state_step : state → state_idx → distr state;

  language_mixin : LanguageMixin of_val to_val prim_step
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments Language {_ _ _ _ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments state_step {_}.
Global Arguments prim_step {_} _ _.

#[global] Existing Instance expr_eqdec.
#[global] Existing Instance state_eqdec.
#[global] Existing Instance expr_countable.
#[global] Existing Instance state_countable.

Canonical Structure stateO Λ := leibnizO (state Λ).
Canonical Structure valO Λ := leibnizO (val Λ).
Canonical Structure exprO Λ := leibnizO (expr Λ).

Definition cfg (Λ : language) := (expr Λ * state Λ)%type.

Class LanguageCtx {Λ : language} (K : expr Λ → expr Λ) := {
  fill_not_val e :
    to_val e = None → to_val (K e) = None;
  fill_inj : Inj (=) (=) K;
  fill_step e1 σ1 e2 σ2 :
    prim_step e1 σ1 (e2, σ2) > 0 →
    prim_step (K e1) σ1 (K e2, σ2) > 0;
  fill_step_inv e1' σ1 e2 σ2 :
    to_val e1' = None → prim_step (K e1') σ1 (e2, σ2) > 0 →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 (e2', σ2) > 0;
  fill_step_prob e1 σ1 e2 σ2 :
    to_val e1 = None →
    prim_step e1 σ1 (e2, σ2) = prim_step (K e1) σ1 (K e2, σ2);
}.

#[global] Existing Instance fill_inj.

Inductive atomicity := StronglyAtomic | WeaklyAtomic.

Definition stuckness_to_atomicity (s : stuckness) : atomicity :=
  if s is MaybeStuck then StronglyAtomic else WeaklyAtomic.

Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.

  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. apply language_mixin. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. apply language_mixin. Qed.
  Lemma val_stuck e σ ρ : prim_step e σ ρ > 0 → to_val e = None.
  Proof. apply language_mixin. Qed.

  Definition reducible (e : expr Λ) (σ : state Λ) :=
    ∃ ρ, prim_step e σ ρ > 0.
  Definition irreducible (e : expr Λ) (σ : state Λ) :=
    ∀ ρ, prim_step e σ ρ = 0.
  Definition stuck (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ irreducible e σ.
  Definition not_stuck (e : expr Λ) (σ : state Λ) :=
    is_Some (to_val e) ∨ reducible e σ.

  Class Atomic (a : atomicity) (e : expr Λ) : Prop :=
    atomic σ e' σ' :
      prim_step e σ (e', σ') > 0 →
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  Inductive step (ρ1 : cfg Λ) (ρ2 : cfg Λ) : Prop :=
  | step_atomic e1 σ1 :
    ρ1 = (e1, σ1) →
    prim_step e1 σ1 ρ2 > 0 →
    step ρ1 ρ2
  | step_state e α σ1 σ2 :
    ρ1 = (e, σ1) →
    ρ2 = (e, σ2) →
    state_step σ1 α σ2 > 0 →
    step ρ1 ρ2.
  Local Hint Constructors step : core.

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.
  Lemma not_reducible e σ : ¬reducible e σ ↔ irreducible e σ.
  Proof.
    unfold reducible, irreducible. split.
    - move=> /not_exists_forall_not Hneg ρ.
      specialize (Hneg ρ). apply Rnot_gt_ge in Hneg.
      pose proof (pmf_pos (prim_step e σ) ρ). lra.
    - intros Hall [ρ ?]. specialize (Hall ρ). lra.
  Qed.
  Lemma reducible_not_val e σ : reducible e σ → to_val e = None.
  Proof. intros ([] & ?). eauto using val_stuck. Qed.
  Lemma val_irreducible e σ : is_Some (to_val e) → irreducible e σ.
  Proof.
    intros [??] ?.
    destruct (pmf_pos (prim_step e σ) ρ) as [Hs%val_stuck|]; [|done].
    simplify_eq.
  Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.
  Lemma not_not_stuck e σ : ¬not_stuck e σ ↔ stuck e σ.
  Proof.
    rewrite /stuck /not_stuck -not_eq_None_Some -not_reducible.
    destruct (decide (to_val e = None)); naive_solver.
  Qed.

  Lemma strongly_atomic_atomic e a :
    Atomic StronglyAtomic e → Atomic a e.
  Proof. unfold Atomic. destruct a; eauto using val_irreducible. Qed.

  Lemma reducible_fill `{!@LanguageCtx Λ K} e σ :
    reducible e σ → reducible (K e) σ.
  Proof. unfold reducible in *. intros [[] ?]. naive_solver eauto using fill_step. Qed.
  Lemma reducible_fill_inv `{!@LanguageCtx Λ K} e σ :
    to_val e = None → reducible (K e) σ → reducible e σ.
  Proof.
    intros ? [[] Hstep]; unfold reducible.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto.
  Qed.
  Lemma irreducible_fill `{!@LanguageCtx Λ K} e σ :
    to_val e = None → irreducible e σ → irreducible (K e) σ.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv. Qed.
  Lemma irreducible_fill_inv `{!@LanguageCtx Λ K} e σ :
    irreducible (K e) σ → irreducible e σ.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.

  Lemma not_stuck_fill_inv K `{!@LanguageCtx Λ K} e σ :
    not_stuck (K e) σ → not_stuck e σ.
  Proof.
    rewrite /not_stuck -!not_eq_None_Some. intros [?|?].
    - auto using fill_not_val.
    - destruct (decide (to_val e = None)); eauto using reducible_fill_inv.
  Qed.

  Lemma fill_step_prob' K `{!@LanguageCtx Λ K} e1 e2 σ1 σ2  :
    prim_step e1 σ1 (e2, σ2) > 0 →
    prim_step e1 σ1 (e2, σ2) = prim_step (K e1) σ1 (K e2, σ2).
  Proof. intros ?%val_stuck. by apply fill_step_prob. Qed.

  Lemma stuck_fill `{!@LanguageCtx Λ K} e σ :
    stuck e σ → stuck (K e) σ.
  Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed.

  Record pure_step (e1 e2 : expr Λ)  := {
    pure_step_safe σ1 : reducible e1 σ1;
    pure_step_det σ1 e2' σ2 :
      prim_step e1 σ1 (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2
  }.

  Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) :=
    pure_exec : φ → relations.nsteps pure_step n e1 e2.

  Lemma pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 :
    pure_step e1 e2 →
    pure_step (K e1) (K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible in *. intros σ1.
      destruct (Hred σ1) as [[]].
      eexists. by eapply fill_step.
    - intros σ1 e2' σ2 Hpstep.
      destruct (fill_step_inv e1 σ1 e2' σ2) as (e2'' & -> & ?); [|exact Hpstep|].
      + destruct (Hred σ1) as (? & ?); eauto using val_stuck.
      + edestruct (Hstep σ1 e2'' σ2) as ( -> & ->); auto.
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

  Lemma prim_step_not_stuck e σ e' σ' :
    prim_step e σ (e', σ') > 0 → not_stuck e σ.
  Proof. rewrite /not_stuck /reducible. eauto 10. Qed.

  Lemma rtc_pure_step_val `{!Inhabited (state Λ)} v e :
    rtc pure_step (of_val v) e → to_val e = Some v.
  Proof.
    intros ?; rewrite <- to_of_val.
    f_equal; symmetry; eapply rtc_nf; first done.
    intros [e' [Hstep _]].
    specialize (Hstep inhabitant) as [? Hval%val_stuck].
    by rewrite to_of_val in Hval.
  Qed.
End language.

Global Hint Mode PureExec + - - ! - : typeclass_instances.

Global Arguments step_atomic {Λ ρ1 ρ2}.
Global Arguments step_state {Λ ρ1 ρ2}.

Inductive action (Λ : language) :=
  (* prim_step *)
  | PRIM
  (* state_step *)
  | STATE (α : state_idx Λ).

Global Arguments PRIM {Λ}.
Global Arguments STATE {Λ} _.

Definition scheduler_fn (Λ : language) := cfg Λ → option (action Λ).
Definition scheduler (Λ : language) := list (scheduler_fn Λ).

Section distribution.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types α : state_idx Λ.
  Implicit Types ξ : scheduler Λ.

  Definition exec_fn_pmf '(e, σ) (f : scheduler_fn Λ) ρ : R :=
    match f (e, σ) with
    | Some PRIM => prim_step e σ ρ
    | Some (STATE α) => strength_l e (state_step σ α) ρ
    | _ => 0
    end.
  Program Definition exec_fn (ρ : cfg Λ) (f : scheduler_fn Λ) : distr (cfg Λ) :=
    MkDistr (exec_fn_pmf ρ f) _ _ _.
  Next Obligation. intros [] f ρ. rewrite /exec_fn_pmf. destruct (f _) as [[]|]; [done|done|done]. Qed.
  Next Obligation.
    intros [e σ] f. rewrite /exec_fn_pmf.
    destruct (f _) as [[]|]; [done|done|]. apply ex_seriesC_0.
  Qed.
  Next Obligation.
    intros [e σ] f. rewrite /exec_fn_pmf.
    destruct (f _) as [[]|]; [done|done|]. rewrite SeriesC_0 //; lra.
  Qed.

  Lemma exec_fn_pmf_unfold f ρ ρ' :
    exec_fn ρ f ρ' =
      match f ρ with
      | Some PRIM => prim_step ρ.1 ρ.2 ρ'
      | Some (STATE α) => strength_l ρ.1 (state_step ρ.2 α) ρ'
      | _ => 0
      end.
  Proof.
    destruct ρ as [e σ].
    rewrite /exec_fn {1}/pmf /= /exec_fn_pmf /=.
    by destruct (f _) as [[]|].
  Qed.


  Lemma exec_fn_unfold f ρ :
    exec_fn ρ f =
      match f ρ with
      | Some PRIM => prim_step ρ.1 ρ.2
      | Some (STATE α) => strength_l ρ.1 (state_step ρ.2 α)
      | _ => dzero
      end.
  Proof.
    apply distr_ext=>?. rewrite exec_fn_pmf_unfold. by repeat case_match.
  Qed.

  (* TODO: move *)
  Definition foldlM {A B} `{Countable B} (f : B → A → distr B) (b : B) (xs : list A) : distr B :=
    foldr (λ a m b, f b a ≫= m) dret xs b.

  Definition exec (ξ : scheduler Λ) (ρ : cfg Λ) : distr (cfg Λ) :=
    foldlM exec_fn ρ ξ.

  Lemma exec_nil ρ :
    exec [] ρ = dret ρ.
  Proof. done. Qed.

  Lemma exec_cons ρ f ξ :
    exec (f :: ξ) ρ = ρ'' ← exec_fn ρ f; exec ξ ρ''.
  Proof. done. Qed.

End distribution.

Global Arguments exec_fn {_} _ _ : simpl never.
Global Arguments exec {_} _ _ : simpl never.
