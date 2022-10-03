(** An axiomatization of evaluation-context based languages, including a proof
    that this gives rise to a "language" in our sense. *)
From Coq Require Import Reals Psatz ClassicalEpsilon.
From stdpp Require Import decidable countable.
From iris.prelude Require Export prelude.
From self.prelude Require Import classical.
From self.program_logic Require Import language.
From self.prob Require Import distribution.

(** TAKE CARE: When you define an [ectxLanguage] canonical structure for your
    language, you need to also define a corresponding [language] canonical
    structure. Use the coercion [LanguageOfEctx] as defined in the bottom of this
    file for doing that. *)

Section ectx_language_mixin.
  Context {expr val ectx state : Type}.
  Context `{Countable expr, Countable state}.

  Context (of_val : val → expr).
  Context (to_val : expr → option val).

  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).
  Context (reshape : expr → ectx * expr).

  Context (head_step  : expr → state → distr (expr * state)).
  Context (state_step : state → distr state).

  Record EctxLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_head_stuck e1 σ1 ρ :
      head_step e1 σ1 ρ > 0 → to_val e1 = None;

    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    mixin_fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e);

    mixin_fill_reshape K e e' : reshape e = (K, e') → fill K e' = e;

    (** Given a head redex [e1_redex] somewhere in a term, and another
        decomposition of the same term into [fill K' e1'] such that [e1'] is
        not a value, then the head redex context is [e1']'s context [K']
        filled with another context [K''].  In particular, this implies [e1 =
        fill K'' e1_redex] by [fill_inj], i.e., [e1]' contains the head redex.

        This implies there can be only one head redex, see
        [head_redex_unique]. *)
    mixin_step_by_val K' K_redex e1' e1_redex σ1 ρ :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      head_step e1_redex σ1 ρ > 0 →
      ∃ K'', K_redex = comp_ectx K' K'';

  (** If [fill K e] takes a head step, then either [e] is a value or [K] is
      the empty evaluation context. In other words, if [e] is not a value
      wrapping it in a context does not add new head redex positions. *)
    mixin_head_ctx_step_val K e σ1 ρ :
      head_step (fill K e) σ1 ρ > 0 → is_Some (to_val e) ∨ K = empty_ectx;

  }.
End ectx_language_mixin.

Structure ectxLanguage := EctxLanguage {
  expr : Type;
  val : Type;
  ectx : Type;
  state : Type;

  expr_eqdec : EqDecision expr;
  state_eqdec : EqDecision state;
  ectx_eqdec : EqDecision ectx;
  expr_countable : Countable expr;
  state_countable : Countable state;

  of_val : val → expr;
  to_val : expr → option val;

  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  reshape : expr → ectx * expr;

  head_step : expr → state → distr (expr * state);
  state_step : state → distr state;

  ectx_language_mixin :
    EctxLanguageMixin of_val to_val empty_ectx comp_ectx fill reshape head_step
}.

#[global] Existing Instance expr_eqdec.
#[global] Existing Instance state_eqdec.
#[global] Existing Instance ectx_eqdec.
#[global] Existing Instance expr_countable.
#[global] Existing Instance state_countable.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments EctxLanguage {_ _ _ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments empty_ectx {_}.
Global Arguments comp_ectx {_} _ _.
Global Arguments reshape {_} _.
Global Arguments fill {_} _ _.
Global Arguments head_step {_} _ _.
Global Arguments state_step {_} _.

(* From an ectx_language, we can construct a language. *)
Section ectx_language.
  Context {Λ : ectxLanguage}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.

  (* Only project stuff out of the mixin that is not also in language *)
  Lemma val_head_stuck e1 σ1 e2 σ2 : head_step e1 σ1 (e2, σ2) > 0 → to_val e1 = None.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply ectx_language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_reshape K e e' : reshape e = (K, e') → fill K e' = e.
  Proof. apply ectx_language_mixin. Qed.
  Lemma step_by_val K' K_redex e1' e1_redex σ1 ρ :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      head_step e1_redex σ1 ρ > 0 →
      ∃ K'', K_redex = comp_ectx K' K''.
  Proof. apply ectx_language_mixin. Qed.
  Lemma head_ctx_step_val K e σ1 ρ :
    head_step (fill K e) σ1 ρ > 0 → is_Some (to_val e) ∨ K = empty_ectx.
  Proof. apply ectx_language_mixin. Qed.

  Definition head_reducible (e : expr Λ) (σ : state Λ) :=
    ∃ ρ, head_step e σ ρ > 0.
  Definition head_irreducible (e : expr Λ) (σ : state Λ) :=
    ∀ ρ, head_step e σ ρ = 0.
  Definition head_stuck (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ head_irreducible e σ.

  (* All non-value redexes are at the root. In other words, all sub-redexes are
     values. *)
  Definition sub_redexes_are_values (e : expr Λ) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Definition prim_step (e1 : expr Λ) (σ1 : state Λ) : distr (expr Λ * state Λ) :=
    let '(K, e1') := reshape e1 in
    dbind (λ '(e2', σ2), dret (fill K e2', σ2)) (head_step e1' σ1) .

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Definition ectx_lang_mixin : LanguageMixin (@of_val Λ) to_val prim_step.
  Proof.
    split.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    - intros e1 σ1 [e2 σ2] =>/=. rewrite /prim_step.
      destruct (reshape e1) as [K e1'] eqn:Heq.
      intros [[e2' σ2'] [_ Hs]]%dbind_pos_support.
      apply val_head_stuck in Hs.
      apply fill_reshape in Heq as <-.
      by eapply fill_not_val.
  Qed.

  Canonical Structure ectx_lang : language := Language (state_step := state_step) ectx_lang_mixin.

  Definition head_atomic (a : atomicity) (e : expr Λ) : Prop :=
    ∀ σ e' σ',
      head_step e σ (e', σ') > 0 →
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  (** * Some lemmas about this language *)
  Lemma not_head_reducible e σ : ¬head_reducible e σ ↔ head_irreducible e σ.
  Proof.
    unfold head_reducible, head_irreducible. split.
    - intros Hnot ρ.
      assert (¬ head_step e σ ρ > 0) as H%Rnot_gt_ge; eauto.
      pose proof (pmf_pos (head_step e σ) ρ). lra.
    - intros Hall [ρ ?]. specialize (Hall ρ). lra.
  Qed.

  (** The decomposition into head redex and context is unique.

      In all sensible instances, [comp_ectx K' empty_ectx] will be the same as
      [K'], so the conclusion is [K = K' ∧ e = e'], but we do not require a law
      to actually prove that so we cannot use that fact here. *)
  Lemma head_redex_unique K K' e e' σ :
    fill K e = fill K' e' →
    head_reducible e σ →
    head_reducible e' σ →
    K = comp_ectx K' empty_ectx ∧ e = e'.
  Proof.
    intros Heq [[e2 σ2] Hred] [[e2' σ2'] Hred'].
    edestruct (step_by_val K' K e' e) as [K'' HK];
      [by eauto using val_head_stuck..|].
    subst K. move: Heq. rewrite -fill_comp. intros <-%(inj (fill _)).
    destruct (head_ctx_step_val _ _ _ _ Hred') as [[]%not_eq_None_Some|HK''].
    { by eapply val_head_stuck. }
    subst K''. rewrite fill_empty. done.
  Qed.

  Lemma head_step_not_stuck e σ ρ : head_step e σ ρ > 0 → not_stuck e σ.
  Proof.
    rewrite /not_stuck /reducible /=. intros Hs. right.
    eexists ρ. rewrite /prim_step.
    destruct (reshape e) as [K e1'] eqn:Heq.
    rewrite -(fill_reshape _ _ _ Heq) in Hs.
    destruct (head_ctx_step_val _ _ _ _ Hs) as [Hval | ->].
    Admitted.
  (* Qed. *)

  (* TODO HERE *)

  Lemma fill_prim_step K e1 σ1 e2 σ2 :
    to_val e1 = None →
    prim_step e1 σ1 (e2, σ2) = prim_step (fill K e1) σ1 (fill K e2, σ2).
  Proof.

    intros Hs.

    destruct 1 as [K' e1' e2' -> ->].
    rewrite !fill_comp. by econstructor.
  Qed.
  Lemma fill_reducible K e σ : reducible e σ → reducible (fill K e) σ.
  Proof.
    intros (κ&e'&σ'&efs&?). exists κ, (fill K e'), σ', efs.
    by apply fill_prim_step.
  Qed.
  Lemma fill_reducible_no_obs K e σ : reducible_no_obs e σ → reducible_no_obs (fill K e) σ.
  Proof.
    intros (e'&σ'&efs&?). exists (fill K e'), σ', efs.
    by apply fill_prim_step.
  Qed.
  Lemma head_prim_reducible e σ : head_reducible e σ → reducible e σ.
  Proof. intros (κ&e'&σ'&efs&?). eexists κ, e', σ', efs. by apply head_prim_step. Qed.
  Lemma head_prim_fill_reducible e K σ :
    head_reducible e σ → reducible (fill K e) σ.
  Proof. intro. by apply fill_reducible, head_prim_reducible. Qed.
  Lemma head_prim_reducible_no_obs e σ : head_reducible_no_obs e σ → reducible_no_obs e σ.
  Proof. intros (e'&σ'&efs&?). eexists e', σ', efs. by apply head_prim_step. Qed.
  Lemma head_prim_irreducible e σ : irreducible e σ → head_irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.
  Lemma head_prim_fill_reducible_no_obs e K σ :
    head_reducible_no_obs e σ → reducible_no_obs (fill K e) σ.
  Proof. intro. by apply fill_reducible_no_obs, head_prim_reducible_no_obs. Qed.

  Lemma prim_head_reducible e σ :
    reducible e σ → sub_redexes_are_values e → head_reducible e σ.
  Proof.
    intros (κ&e'&σ'&efs&[K e1' e2' -> -> Hstep]) ?.
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty /head_reducible; eauto.
  Qed.
  Lemma prim_head_irreducible e σ :
    head_irreducible e σ → sub_redexes_are_values e → irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
  Qed.

  Lemma head_stuck_stuck e σ :
    head_stuck e σ → sub_redexes_are_values e → stuck e σ.
  Proof.
    intros [] ?. split; first done.
    by apply prim_head_irreducible.
  Qed.

  Lemma ectx_language_atomic a e :
    head_atomic a e → sub_redexes_are_values e → Atomic a e.
  Proof.
    intros Hatomic_step Hatomic_fill σ κ e' σ' efs [K e1' e2' -> -> Hstep].
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty. eapply Hatomic_step. by rewrite fill_empty.
  Qed.

  Lemma head_reducible_prim_step_ctx K e1 σ1 κ e2 σ2 efs :
    head_reducible e1 σ1 →
    prim_step (fill K e1) σ1 κ e2 σ2 efs →
    ∃ e2', e2 = fill K e2' ∧ head_step e1 σ1 κ e2' σ2 efs.
  Proof.
    intros (κ'&e2''&σ2''&efs''&HhstepK) [K' e1' e2' HKe1 -> Hstep].
    edestruct (step_by_val K) as [K'' ?];
      eauto using val_head_stuck; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp; split; first done.
    apply head_ctx_step_val in HhstepK as [[v ?]|?]; simplify_eq.
    { apply val_head_stuck in Hstep; simplify_eq. }
    by rewrite !fill_empty.
  Qed.

  Lemma head_reducible_prim_step e1 σ1 κ e2 σ2 efs :
    head_reducible e1 σ1 →
    prim_step e1 σ1 κ e2 σ2 efs →
    head_step e1 σ1 κ e2 σ2 efs.
  Proof.
    intros.
    edestruct (head_reducible_prim_step_ctx empty_ectx) as (?&?&?);
      rewrite ?fill_empty; eauto.
    by simplify_eq; rewrite fill_empty.
  Qed.

  (* Every evaluation context is a context. *)
  Global Instance ectx_lang_ctx K : LanguageCtx (fill K).
  Proof.
    split; simpl.
    - eauto using fill_not_val.
    - intros ?????? [K' e1' e2' Heq1 Heq2 Hstep].
      by exists (comp_ectx K K') e1' e2'; rewrite ?Heq1 ?Heq2 ?fill_comp.
    - intros e1 σ1 κ e2 σ2 efs Hnval [K'' e1'' e2'' Heq1 -> Hstep].
      destruct (step_by_val K K'' e1 e1'' σ1 κ e2'' σ2 efs) as [K' ->]; eauto.
      rewrite -fill_comp in Heq1; apply (inj (fill _)) in Heq1.
      exists (fill K' e2''); rewrite -fill_comp; split; auto.
      econstructor; eauto.
  Qed.

  Record pure_head_step (e1 e2 : expr Λ) := {
    pure_head_step_safe σ1 : head_reducible_no_obs e1 σ1;
    pure_head_step_det σ1 κ e2' σ2 efs :
      head_step e1 σ1 κ e2' σ2 efs → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs = []
  }.

  Lemma pure_head_step_pure_step e1 e2 : pure_head_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros σ. destruct (Hp1 σ) as (e2' & σ2 & efs & ?).
      eexists e2', σ2, efs. by apply head_prim_step.
    - intros σ1 κ e2' σ2 efs ?%head_reducible_prim_step; eauto using head_reducible_no_obs_reducible.
  Qed.

  (** This is not an instance because HeapLang's [wp_pure] tactic already takes
      care of handling the evaluation context.  So the instance is redundant.
      If you are defining your own language and your [wp_pure] works
      differently, you might want to specialize this lemma to your language and
      register that as an instance. *)
  Lemma pure_exec_fill K φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (fill K e1) (fill K e2).
  Proof. apply: pure_exec_ctx. Qed.
End ectx_language.

Global Arguments ectx_lang : clear implicits.
Global Arguments Ectx_step {Λ e1 σ1 κ e2 σ2 efs}.
Coercion ectx_lang : ectxLanguage >-> language.

(* This definition makes sure that the fields of the [language] record do not
refer to the projections of the [ectxLanguage] record but to the actual fields
of the [ectxLanguage] record. This is crucial for canonical structure search to
work.

Note that this trick no longer works when we switch to canonical projections
because then the pattern match [let '...] will be desugared into projections. *)
Definition LanguageOfEctx (Λ : ectxLanguage) : language :=
  let '@EctxLanguage E V C St K of_val to_val empty comp fill head mix := Λ in
  @Language E V St K of_val to_val _
    (@ectx_lang_mixin (@EctxLanguage E V C St K of_val to_val empty comp fill head mix)).

Global Arguments LanguageOfEctx : simpl never.
