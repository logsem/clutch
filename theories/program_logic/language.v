From Coq Require Import Reals Psatz.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From iris.bi Require Export weakestpre.
From self.prob Require Import distribution.

Section language_mixin.
  Context {expr val state action : Type}.
  Context `{Countable expr, Countable state}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (prim_step : expr → state → action → distr (expr * state)).

  Record LanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e σ α ρ : prim_step e σ α ρ > 0 → to_val e = None;
  }.
End language_mixin.

Structure language := Language {
  expr : Type;
  val : Type;
  state : Type;
  action : Type;

  expr_eqdec : EqDecision expr;
  state_eqdec : EqDecision state;
  expr_countable : Countable expr;
  state_countable : Countable state;

  of_val : val → expr;
  to_val : expr → option val;
  prim_step : expr → state → action → distr (expr * state);
  language_mixin : LanguageMixin of_val to_val prim_step
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments Language {_ _ _ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments prim_step {_} _ _ _.

#[global] Existing Instance expr_eqdec.
#[global] Existing Instance state_eqdec.
#[global] Existing Instance expr_countable.
#[global] Existing Instance state_countable.

Canonical Structure stateO Λ := leibnizO (state Λ).
Canonical Structure valO Λ := leibnizO (val Λ).
Canonical Structure exprO Λ := leibnizO (expr Λ).

Definition cfg (Λ : language) := (expr Λ * state Λ)%type.

Definition scheduler_fn (Λ : language) := (cfg Λ) → option (action Λ).
Definition scheduler (Λ : language) := list (scheduler_fn Λ).

Class LanguageCtx {Λ : language} (K : expr Λ → expr Λ) := {
  fill_not_val e :
    to_val e = None → to_val (K e) = None;
  fill_step e1 σ1 α e2 σ2 :
    prim_step e1 σ1 α (e2, σ2) > 0 →
    prim_step (K e1) σ1 α (K e2, σ2) > 0;
  fill_step_inv e1' σ1 α e2 σ2 :
    to_val e1' = None → prim_step (K e1') σ1 α (e2, σ2) > 0 →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 α (e2', σ2) > 0;
  fill_step_prob e1 σ1 α e2 σ2 :
    to_val e1 = None →
    prim_step e1 σ1 α (e2, σ2) = prim_step (K e1) σ1 α (K e2, σ2);
  }.

Inductive atomicity := StronglyAtomic | WeaklyAtomic.

Definition stuckness_to_atomicity (s : stuckness) : atomicity :=
  if s is MaybeStuck then StronglyAtomic else WeaklyAtomic.

Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types α : action Λ.
  Implicit Types ξ : scheduler Λ.

  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. apply language_mixin. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. apply language_mixin. Qed.
  Lemma val_stuck e σ α ρ : prim_step e σ α ρ > 0 → to_val e = None.
  Proof. apply language_mixin. Qed.

  Definition reducible (e : expr Λ) (σ : state Λ) (α : action Λ) :=
    ∃ ρ, prim_step e σ α ρ > 0.
  Definition irreducible (e : expr Λ) (σ : state Λ) (α : action Λ) :=
    ∀ ρ, prim_step e σ α ρ = 0.
  Definition stuck (e : expr Λ) (σ : state Λ) (α : action Λ) :=
    to_val e = None ∧ irreducible e σ α.
  Definition not_stuck (e : expr Λ) (σ : state Λ) (α : action Λ):=
    is_Some (to_val e) ∨ reducible e σ α.

  Class Atomic (a : atomicity) (e : expr Λ) : Prop :=
    atomic σ e' α σ' :
      prim_step e σ α (e', σ') > 0 →
      if a is WeaklyAtomic then irreducible e' σ' α else is_Some (to_val e').

  Inductive step (ρ1 : cfg Λ) (α : action Λ) (ρ2 : cfg Λ) : Prop :=
  | step_atomic e1 σ1 :
    ρ1 = (e1, σ1) →
    prim_step e1 σ1 α ρ2 > 0 →
    step ρ1 α ρ2.
  Local Hint Constructors step : core.

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.
  Lemma not_reducible e σ α : ¬reducible e σ α ↔ irreducible e σ α.
  Proof.
    unfold reducible, irreducible. split.
    - intros Hnot ρ.
      assert (¬ prim_step e σ α ρ > 0) as H%Rnot_gt_ge; eauto.
      pose proof (pmf_pos (prim_step e σ α) ρ). lra.
    - intros Hall [ρ ?]. specialize (Hall ρ). lra.
  Qed.
  Lemma reducible_not_val e σ α : reducible e σ α → to_val e = None.
  Proof. intros ([] & ?). eauto using val_stuck. Qed.
  Lemma val_irreducible e σ α : is_Some (to_val e) → irreducible e σ α.
  Proof.
    intros [??] ?.
    destruct (Rge_dec (prim_step e σ α ρ) 0) as [Hge|]; last first.
    { pose proof (pmf_pos (prim_step e σ α) ρ). lra. }
    destruct Hge as [Hgt%val_stuck|]; [|done].
    simplify_eq.
  Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.
  Lemma not_not_stuck e σ α : ¬not_stuck e σ α ↔ stuck e σ α.
  Proof.
    rewrite /stuck /not_stuck -not_eq_None_Some -not_reducible.
    destruct (decide (to_val e = None)); naive_solver.
  Qed.

  Lemma strongly_atomic_atomic e a :
    Atomic StronglyAtomic e → Atomic a e.
  Proof. unfold Atomic. destruct a; eauto using val_irreducible. Qed.

  Lemma reducible_fill `{!@LanguageCtx Λ K} e σ α :
    reducible e σ α → reducible (K e) σ α.
  Proof. unfold reducible in *. intros [[] ?]. naive_solver eauto using fill_step. Qed.
  Lemma reducible_fill_inv `{!@LanguageCtx Λ K} e σ α :
    to_val e = None → reducible (K e) σ α → reducible e σ α.
  Proof.
    intros ? [[] Hstep]; unfold reducible.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto.
  Qed.
  Lemma irreducible_fill `{!@LanguageCtx Λ K} e σ α :
    to_val e = None → irreducible e σ α → irreducible (K e) σ α.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv. Qed.
  Lemma irreducible_fill_inv `{!@LanguageCtx Λ K} e σ α :
    irreducible (K e) σ α → irreducible e σ α.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.

  Lemma not_stuck_fill_inv K `{!@LanguageCtx Λ K} e σ α :
    not_stuck (K e) σ α → not_stuck e σ α.
  Proof.
    rewrite /not_stuck -!not_eq_None_Some. intros [?|?].
    - auto using fill_not_val.
    - destruct (decide (to_val e = None)); eauto using reducible_fill_inv.
  Qed.

  Lemma stuck_fill `{!@LanguageCtx Λ K} e σ α :
    stuck e σ α → stuck (K e) σ α.
  Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed.

  Record pure_step (e1 e2 : expr Λ) (α : action Λ) := {
      (* TODO: should [pure_step] require no probabilistic choices? *)
    pure_step_safe σ1 : reducible e1 σ1 α;
    pure_step_det σ1 e2' σ2 :
      prim_step e1 σ1 α (e2', σ2) > 0 → σ2 = σ1 ∧ e2' = e2
  }.

  (* Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) := *)
  (*   pure_exec : φ → relations.nsteps pure_step n e1 e2. *)

  Lemma pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 α :
    pure_step e1 e2 α →
    pure_step (K e1) (K e2) α.
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible in *. intros σ1.
      destruct (Hred σ1) as [[]].
      eexists. by eapply fill_step.
    - intros σ1 e2' σ2 Hpstep.
      destruct (fill_step_inv e1 σ1 α e2' σ2) as (e2'' & -> & ?); [|exact Hpstep|].
      + destruct (Hred σ1) as (? & ?); eauto using val_stuck.
      + edestruct (Hstep σ1 e2'' σ2) as ( -> & ->); auto.
  Qed.

  (* Lemma pure_step_nsteps_ctx K `{!@LanguageCtx Λ K} n e1 e2 : *)
  (*   relations.nsteps pure_step n e1 e2 → *)
  (*   relations.nsteps pure_step n (K e1) (K e2). *)
  (* Proof. eauto using nsteps_congruence, pure_step_ctx. Qed. *)

  (* Lemma rtc_pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 : *)
  (*   rtc pure_step e1 e2 → rtc pure_step (K e1) (K e2). *)
  (* Proof. eauto using rtc_congruence, pure_step_ctx. Qed. *)

  (* (* We do not make this an instance because it is awfully general. *) *)
  (* Lemma pure_exec_ctx K `{!@LanguageCtx Λ K} φ n e1 e2 : *)
  (*   PureExec φ n e1 e2 → *)
  (*   PureExec φ n (K e1) (K e2). *)
  (* Proof. rewrite /PureExec; eauto using pure_step_nsteps_ctx. Qed. *)

  (* (* This is a family of frequent assumptions for PureExec *) *)
  (* Class IntoVal (e : expr Λ) (v : val Λ) := *)
  (*   into_val : of_val v = e. *)

  (* Class AsVal (e : expr Λ) := as_val : ∃ v, of_val v = e. *)
  (* (* There is no instance [IntoVal → AsVal] as often one can solve [AsVal] more *)
  (* efficiently since no witness has to be computed. *) *)
  (* Global Instance as_vals_of_val vs : TCForall AsVal (of_val <$> vs). *)
  (* Proof. *)
  (*   apply TCForall_Forall, Forall_fmap, Forall_true=> v. *)
  (*   rewrite /AsVal /=; eauto. *)
  (* Qed. *)

  Lemma as_val_is_Some e :
    (∃ v, of_val v = e) → is_Some (to_val e).
  Proof. intros [v <-]. rewrite to_of_val. eauto. Qed.

  Lemma prim_step_not_stuck e σ e' σ' α :
    prim_step e σ α (e', σ') > 0 → not_stuck e σ α.
  Proof. rewrite /not_stuck /reducible. eauto 10. Qed.

  (* Lemma rtc_pure_step_val `{!Inhabited (state Λ)} v e : *)
  (*   rtc pure_step (of_val v) e → to_val e = Some v. *)
  (* Proof. *)
  (*   intros ?; rewrite <- to_of_val. *)
  (*   f_equal; symmetry; eapply rtc_nf; first done. *)
  (*   intros [e' [Hstep _]]. *)
  (*   destruct (Hstep inhabitant) as (?&?&?&Hval%val_stuck). *)
  (*   by rewrite to_of_val in Hval. *)
  (* Qed. *)

  Definition kernel_fn_pmf (f : scheduler_fn Λ) (ρ ρ' : cfg Λ) : R :=
    if f ρ is Some α then prim_step ρ.1 ρ.2 α ρ' else 0.

  Program Definition kernel_fn (f : scheduler_fn Λ) (ρ : cfg Λ) : distr (cfg Λ) :=
    MkDistr (kernel_fn_pmf f ρ) _ _ _.
  Next Obligation. intros f ρ a. rewrite /kernel_fn_pmf. destruct (f ρ); [done|lra]. Qed.
  Next Obligation. intros f ρ. rewrite /kernel_fn_pmf. destruct (f ρ); [done|]. eapply ex_seriesC_0. Qed.
  Next Obligation. intros f ρ. rewrite /kernel_fn_pmf. destruct (f ρ); [done|]. rewrite SeriesC_0 //. lra. Qed.

  Arguments kernel_fn _ _ : simpl never.
  Arguments dret _ : simpl never.

  Fixpoint kernel_scheduler_pmf (ξ : scheduler Λ) (ρ ρ' : cfg Λ) : R :=
    match ξ with
    | f :: ξ' => SeriesC (λ ρ'', kernel_fn f ρ ρ'' * kernel_scheduler_pmf ξ' ρ'' ρ')
    | [] => dret ρ ρ'
    end.

  #[local] Lemma kernel_scheduler_pmf_range ξ ρ ρ' :
    0 <= kernel_scheduler_pmf ξ ρ ρ' <= 1.
  Proof.
    revert ρ ρ'. induction ξ as [|f ξ IH]; intros ρ ρ'; cbn.
    { split; [done|]. eapply pmf_le_1. }
    split.
    - eapply SeriesC_ge_0.
      { intros ρ''. apply Rmult_le_pos; [done|]. apply IH. }
      eapply (ex_seriesC_le _ (kernel_fn f ρ)); [|done].
      intros ρ''. specialize (IH ρ'' ρ') as [? ?].
      split; [apply Rmult_le_pos; auto|].
      rewrite -{2}(Rmult_1_r (kernel_fn _ _ _)).
      by apply Rmult_le_compat_l.
    - transitivity (SeriesC (kernel_fn f ρ)); [|eapply pmf_SeriesC].
      eapply SeriesC_le; [|done].
      intros ρ''. specialize (IH ρ'' ρ') as [? ?].
      split; [apply Rmult_le_pos; auto|].
      rewrite -{2}(Rmult_1_r (kernel_fn _ _ _)).
      by apply Rmult_le_compat_l.
  Qed.

  #[local] Lemma kernel_scheduler_pmf_series ξ ρ :
    ex_seriesC (kernel_scheduler_pmf ξ ρ) ∧ SeriesC (kernel_scheduler_pmf ξ ρ) <= 1.
  Proof.
    revert ρ. induction ξ as [|f ξ IH]; intros ρ; cbn; [done|].
    split.
    - eapply (ex_seriesC_double_swap_impl (λ '(a, b), _)).
      eapply (ex_seriesC_ext (λ b, kernel_fn f ρ b * SeriesC _)).
      { intros a. rewrite SeriesC_scal_l //. }
      eapply (ex_seriesC_le _ (λ b , kernel_fn f ρ b * 1)); [|by apply ex_seriesC_scal_r].
      intros a. split.
      + apply Rmult_le_pos; [done|]. eapply SeriesC_ge_0.
        { apply kernel_scheduler_pmf_range. }
        apply IH.
      + apply Rmult_le_compat_l; [done|]. apply IH.
    - rewrite (SeriesC_double_swap (λ '(a, b), _)).
      rewrite -(SeriesC_ext (λ b, kernel_fn f ρ b * SeriesC (kernel_scheduler_pmf ξ b))); last first.
      { intros a. rewrite SeriesC_scal_l //. }
      transitivity (SeriesC (kernel_fn f ρ)); [|done].
      eapply SeriesC_le; [|done].
      intros ρ'. split.
      + apply Rmult_le_pos; [done|].
        apply SeriesC_ge_0.
        { apply kernel_scheduler_pmf_range. }
        apply IH.
      + rewrite -{2}(Rmult_1_r (kernel_fn _ _ _)).
        apply Rmult_le_compat_l; [done|]. apply IH.
  Qed.

  Program Definition kernel_scheduler (ξ : scheduler Λ) (ρ : cfg Λ) : distr (cfg Λ) :=
    (MkDistr (kernel_scheduler_pmf ξ ρ) _ _ _).
  Next Obligation. apply kernel_scheduler_pmf_range. Qed.
  Next Obligation. apply kernel_scheduler_pmf_series. Qed.
  Next Obligation. apply kernel_scheduler_pmf_series. Qed.

End language.

Global Arguments step_atomic {Λ ρ1 α ρ2}.
