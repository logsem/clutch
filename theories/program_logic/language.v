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
  fill_dbind e1 σ1 :
    to_val e1 = None →
    prim_step (K e1) σ1 = dbind (λ '(e2, σ2), dret (K e2, σ2)) (prim_step e1 σ1)
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

  Lemma fill_step e1 σ1 e2 σ2 `{!LanguageCtx K} :
    prim_step e1 σ1 (e2, σ2) > 0 →
    prim_step (K e1) σ1 (K e2, σ2) > 0.
  Proof.
    intros Hs.
    rewrite fill_dbind; [|by eapply val_stuck].
    apply dbind_pos_support. eexists (_,_). split; [|done].
    rewrite dret_1 //. lra.
  Qed.

  Lemma fill_step_inv e1' σ1 e2 σ2 `{!LanguageCtx K} :
    to_val e1' = None → prim_step (K e1') σ1 (e2, σ2) > 0 →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 (e2', σ2) > 0.
  Proof.
    intros Hv. rewrite fill_dbind //.
    intros ([e1 σ1'] & [=]%dret_pos & Hstep)%dbind_pos_support.
    subst. eauto.
  Qed.

  Local Definition fill_lift K `{!LanguageCtx K} : (expr Λ * state Λ) → (expr Λ * state Λ) :=
    λ '(e, σ), (K e, σ).

  Instance inj_fill `{!LanguageCtx K} : Inj eq eq (fill_lift K).
  Proof. intros [] [] [=<-%(inj _) ->]=>//. Qed.

  Lemma fill_step_prob e1 σ1 e2 σ2 `{!LanguageCtx K} :
    to_val e1 = None →
    prim_step e1 σ1 (e2, σ2) = prim_step (K e1) σ1 (K e2, σ2).
  Proof.
    intros Hv. rewrite fill_dbind //.
    rewrite -dbind_dret_pmf_map.
    apply dbind_pmf_ext; eauto.
    eauto. by intros [] [].
  Qed.

  Lemma reducible_fill `{!@LanguageCtx Λ K} e σ :
    reducible e σ → reducible (K e) σ.
  Proof.
    unfold reducible in *. intros [[] ?]. eexists; by apply fill_step.
  Qed.
  Lemma reducible_fill_inv `{!@LanguageCtx Λ K} e σ :
    to_val e = None → reducible (K e) σ → reducible e σ.
  Proof.
    intros ? [[e1 σ1] Hstep]; unfold reducible.
    rewrite fill_dbind // in Hstep.
    apply dbind_pos_support in Hstep as ([e1' σ2] & [=]%dret_pos & Hstep).
    eauto.
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

  Lemma stuck_fill `{!@LanguageCtx Λ K} e σ :
    stuck e σ → stuck (K e) σ.
  Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed.

  Record pure_step (e1 e2 : expr Λ)  := {
    pure_step_safe σ1 : reducible e1 σ1;
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
      rewrite -fill_step_prob //; eauto using (reducible_not_val _ σ).
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

  Lemma fill_is_val e K `{@LanguageCtx Λ K} :
    is_Some (to_val (K e)) → is_Some (to_val e).
  Proof. rewrite -!not_eq_None_Some. eauto using fill_not_val. Qed.

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
