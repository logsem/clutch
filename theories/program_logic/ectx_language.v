 (** An axiomatization of evaluation-context based languages, including a proof
    that this gives rise to a "language" in our sense. *)
From Coq Require Import Reals Psatz.
From iris.prelude Require Export prelude.
From clutch.program_logic Require Import language.
From clutch.prob Require Import distribution.

Section ectx_language_mixin.
  Context {expr val ectx state state_idx : Type}.
  Context `{Countable expr, Countable val, Countable state, Countable state_idx}.

  Context (of_val : val → expr).
  Context (to_val : expr → option val).

  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).
  Context (decomp : expr → ectx * expr).

  Context (head_step  : expr → state → distr (expr * state)).
  Context (state_step : state → state_idx → distr state).
  Context (get_active : state → list state_idx).

  Record EctxLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_head_stuck e1 σ1 ρ : head_step e1 σ1 ρ > 0 → to_val e1 = None;
    mixin_state_step_head_not_stuck e σ σ' α :
      state_step σ α σ' > 0 → (∃ ρ, head_step e σ ρ > 0) ↔ (∃ ρ', head_step e σ' ρ' > 0);
    mixin_state_step_mass σ α :
      α ∈ get_active σ → SeriesC (state_step σ α) = 1;
    mixin_head_step_mass e σ :
      (∃ ρ, head_step e σ ρ > 0) → SeriesC (head_step e σ) = 1;

    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    mixin_fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e);

    (** [decomp] decomposes an expression into an evaluation context and its head redex  *)
    mixin_decomp_fill K e e' :
      decomp e = (K, e') → fill K e' = e;
    mixin_decomp_val_empty K e e' :
      decomp e = (K, e') → is_Some (to_val e') → K = empty_ectx;
    mixin_decomp_fill_comp e e' K K' :
      to_val e = None → decomp e = (K', e') → decomp (fill K e) = (comp_ectx K K', e');

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
  state_idx : Type;

  expr_eqdec : EqDecision expr;
  val_eqdec : EqDecision val;
  state_eqdec : EqDecision state;
  state_idx_eqdec : EqDecision state_idx;
  expr_countable : Countable expr;
  val_countable : Countable val;
  state_countable : Countable state;
  state_idx_countable : Countable state_idx;

  of_val : val → expr;
  to_val : expr → option val;

  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  decomp : expr → ectx * expr;

  head_step : expr → state → distr (expr * state);
  state_step : state → state_idx → distr state;
  get_active : state → list state_idx;

  ectx_language_mixin :
    EctxLanguageMixin of_val to_val empty_ectx comp_ectx fill decomp
      head_step state_step get_active
}.

#[global] Existing Instance expr_eqdec.
#[global] Existing Instance val_eqdec.
#[global] Existing Instance state_eqdec.
#[global] Existing Instance state_idx_eqdec.
#[global] Existing Instance expr_countable.
#[global] Existing Instance val_countable.
#[global] Existing Instance state_countable.
#[global] Existing Instance state_idx_countable.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments EctxLanguage {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments empty_ectx {_}.
Global Arguments comp_ectx {_} _ _.
Global Arguments decomp {_} _.
Global Arguments fill {_} _ _.
Global Arguments head_step {_} _ _.
Global Arguments state_step {_} _.
Global Arguments get_active {_} _.

(* From an ectx_language, we can construct a language. *)
Section ectx_language.
  Context {Λ : ectxLanguage}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.

  (* Only project stuff out of the mixin that is not also in language *)
  Lemma val_head_stuck e1 σ1 ρ : head_step e1 σ1 ρ > 0 → to_val e1 = None.
  Proof. apply ectx_language_mixin. Qed.
  Lemma state_step_head_not_stuck e σ σ' α :
    state_step σ α σ' > 0 → (∃ ρ, head_step e σ ρ > 0) ↔ (∃ ρ', head_step e σ' ρ' > 0).
  Proof. apply ectx_language_mixin. Qed.
  Lemma head_step_mass e σ :
    (∃ ρ, head_step e σ ρ > 0) → SeriesC (head_step e σ) = 1.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply ectx_language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof. apply ectx_language_mixin. Qed.
  Lemma decomp_fill K e e' : decomp e = (K, e') → fill K e' = e.
  Proof. apply ectx_language_mixin. Qed.
  Lemma decomp_val_empty K e e' :
    decomp e = (K, e') → is_Some (to_val e') → K = empty_ectx.
  Proof. apply ectx_language_mixin. Qed.
  Lemma decomp_fill_comp K K' e e' :
    to_val e = None → decomp e = (K', e') → decomp (fill K e) = (comp_ectx K K', e').
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

  Definition fill_lift (K : ectx Λ) : (expr Λ * state Λ) → (expr Λ * state Λ) :=
    λ '(e, σ), (fill K e, σ).

  Lemma fill_lift_comp (K1 K2 : ectx Λ) :
    fill_lift (comp_ectx K1 K2) = fill_lift K1 ∘ fill_lift K2.
  Proof.
    extensionality ρ. destruct ρ.
    rewrite /fill_lift -fill_comp //=.
  Qed.

  Lemma fill_lift_empty :
    fill_lift empty_ectx = (λ ρ, ρ).
  Proof.
    extensionality ρ. destruct ρ.
    rewrite /fill_lift fill_empty //.
  Qed.

  Instance inj_fill (K : ectx Λ) : Inj eq eq (fill_lift K).
  Proof. intros [] [] [=<-%(inj _) ->]=>//. Qed.

  Definition prim_step (e1 : expr Λ) (σ1 : state Λ) : distr (expr Λ * state Λ) :=
    let '(K, e1') := decomp e1 in
    dmap (fill_lift K) (head_step e1' σ1).

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Definition ectx_lang_mixin : LanguageMixin (@of_val Λ) to_val prim_step state_step get_active.
  Proof.
    split.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    - intros e1 σ1 [e2 σ2] =>/=. rewrite /prim_step.
      destruct (decomp e1) as [K e1'] eqn:Heq.
      intros [[e2' σ2'] [_ Hs]]%dmap_pos.
      rewrite -(decomp_fill _ _ _ Heq).
      eapply fill_not_val.
      by eapply val_head_stuck.
    - intros e1 σ1 σ1' α. rewrite /prim_step.
      destruct (decomp e1) as [K e1'] eqn:Heq.
      intros Hs. split.
      + intros [[e2 σ2] [[e2' σ2'] [_ Hh]]%dmap_pos].
        assert (∃ ρ, head_step e1' σ1' ρ > 0) as [[e2'' σ2''] Hs'].
        { erewrite <-state_step_head_not_stuck; [|done]. eauto. }
        eexists (fill K e2'', σ2'').
        eapply dmap_pos.
        eexists (_, _). eauto.
      + intros [[e2 σ2] [[e2' σ2'] [_ Hh]]%dmap_pos].
        assert (∃ ρ, head_step e1' σ1 ρ > 0) as [[e2'' σ2''] Hs'].
        { erewrite state_step_head_not_stuck; [|done]. eauto. }
        eexists (fill K e2'', σ2'').
        eapply dmap_pos.
        eexists (_, _); eauto.
    - apply ectx_language_mixin.
    - intros e σ [[e' σ'] Hs]. revert Hs. rewrite /prim_step.
      destruct (decomp e) as [K e1'] eqn:Heq.
      intros [[e2' σ2'] [? Hs]]%dmap_pos.
      assert (SeriesC (head_step e1' σ) = 1) as Hsum; [eauto using head_step_mass|].
      rewrite dmap_mass //.
  Qed.

  Canonical Structure ectx_lang : language := Language (get_active := get_active) ectx_lang_mixin.

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

  Lemma fill_prim_step_dbind K e1 σ1 :
    to_val e1 = None →
    prim_step (fill K e1) σ1 = dmap (fill_lift K) (prim_step e1 σ1).
  Proof.
    intros Hval. rewrite /prim_step.
    destruct (decomp e1) as [K1 e1'] eqn:Heq.
    destruct (decomp (fill _ e1)) as [K1' e1''] eqn:Heq'.
    apply (decomp_fill_comp K) in Heq; [|done].
    rewrite Heq in Heq'; simplify_eq.
    rewrite dmap_comp.
    apply dmap_eq; [|done].
    intros [] ? =>/=.
    f_equal. rewrite -fill_comp //.
  Qed.

  Lemma fill_prim_step K e1 σ1 e2 σ2 :
    to_val e1 = None →
    prim_step e1 σ1 (e2, σ2) = prim_step (fill K e1) σ1 (fill K e2, σ2).
  Proof.
    intros Hval. rewrite /prim_step.
    destruct (decomp e1) as [K1 e1'] eqn:Heq.
    destruct (decomp (fill _ e1)) as [K1' e1''] eqn:Heq'.
    apply (decomp_fill_comp K) in Heq; [|done].
    rewrite Heq in Heq'; simplify_eq.
    rewrite fill_lift_comp -/fill_lift.
    rewrite -dmap_comp.
    replace (fill K e2, σ2) with (fill_lift K (e2, σ2)); [|done].
    rewrite (dmap_elem_eq (dmap _ _) (e2, σ2)) //.
  Qed.

  Lemma head_prim_step_pmf_eq e1 σ1 ρ :
    head_reducible e1 σ1 →
    prim_step e1 σ1 ρ = head_step e1 σ1 ρ.
  Proof.
    intros Hred.
    rewrite /= /prim_step.
    destruct (decomp e1) as [K e1'] eqn:Heq.
    edestruct (decomp_fill _ _ _ Heq).
    destruct Hred as [ρ' Hs].
    destruct (head_ctx_step_val _ _ _ _ Hs) as [| ->].
    - assert (K = empty_ectx) as -> by eauto using decomp_val_empty.
      rewrite fill_lift_empty fill_empty dmap_id //=.
    - rewrite fill_lift_empty fill_empty dmap_id //=.
  Qed.

  Lemma head_prim_step_eq e1 σ1 :
    head_reducible e1 σ1 →
    prim_step e1 σ1 = head_step e1 σ1.
  Proof. intros ?. apply distr_ext=>?. by eapply head_prim_step_pmf_eq. Qed.

  Lemma head_prim_step e1 σ1 ρ :
    head_step e1 σ1 ρ > 0 → prim_step e1 σ1 ρ > 0.
  Proof. intros ?. erewrite head_prim_step_eq; [done|]. eexists; eauto. Qed.

  Lemma prim_step_iff e1 e2 σ1 σ2 :
    prim_step e1 σ1 (e2, σ2) > 0 ↔
    ∃ K e1' e2',
      fill K e1' = e1 ∧
      fill K e2' = e2 ∧
      head_step e1' σ1 (e2', σ2) > 0.
  Proof.
    split.
    - rewrite /= /prim_step. intros Hs.
      destruct (decomp e1) as [K e1'] eqn:Heq.
      edestruct (decomp_fill _ _ _ Heq).
      eapply dmap_pos in Hs as [[] [[=] ?]].
      simplify_eq. do 3 eexists; eauto.
    - intros (K & e1' & e2' & Hfill1 & Hfill2 & Hs). simplify_eq.
      rewrite -fill_prim_step //; [by apply head_prim_step|].
      by eapply val_head_stuck.
  Qed.

  Lemma head_step_not_stuck e σ ρ : head_step e σ ρ > 0 → not_stuck e σ.
  Proof.
    rewrite /not_stuck /reducible /=. intros Hs. right.
    eexists ρ. by apply head_prim_step.
  Qed.

  Lemma fill_reducible K e σ : reducible e σ → reducible (fill K e) σ.
  Proof.
    rewrite /reducible /=. intros [[e2 σ2] (K' & e1' & e2' & <- & <- & Hs)%prim_step_iff].
    exists (fill (comp_ectx K K') e2', σ2).
    eapply prim_step_iff. do 3 eexists. rewrite !fill_comp //.
  Qed.
  Lemma head_prim_reducible e σ : head_reducible e σ → reducible e σ.
  Proof. intros [ρ Hstep]. exists ρ. by apply head_prim_step. Qed.
  Lemma head_prim_fill_reducible e K σ :
    head_reducible e σ → reducible (fill K e) σ.
  Proof. intro. by apply fill_reducible, head_prim_reducible. Qed.
  Lemma state_step_head_reducible e σ σ' α :
    state_step σ α σ' > 0 → head_reducible e σ ↔ head_reducible e σ'.
  Proof. eapply state_step_head_not_stuck. Qed.

  Lemma head_prim_irreducible e σ : irreducible e σ → head_irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.

  Lemma prim_head_reducible e σ :
    reducible e σ → sub_redexes_are_values e → head_reducible e σ.
  Proof.
    rewrite /reducible.
    intros [[e2 σ2] (K & e1' & e2' & <- & <- & Hs)%prim_step_iff] Hsub.
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    simplify_eq. rewrite fill_empty. eexists; eauto.
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
    intros Hatomic Hsub σ e' σ' (K & e1' & e2' & <- & <- & Hs)%prim_step_iff.
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty in Hatomic.
    eapply Hatomic. rewrite fill_empty. eauto.
  Qed.

  Lemma head_reducible_prim_step_ctx K e1 σ1 e2 σ2:
    head_reducible e1 σ1 →
    prim_step (fill K e1) σ1 (e2, σ2) > 0 →
    ∃ e2', e2 = fill K e2' ∧ head_step e1 σ1 (e2', σ2) > 0.
  Proof.
    intros [[e2'' σ2''] HhstepK] (K' & e1' & e2' & HKe1 & HKe2 & Hs)%prim_step_iff.
    symmetry in HKe1.
    edestruct (step_by_val K) as [K'' HK]; eauto using val_head_stuck; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp. split; [done|].
    destruct (head_ctx_step_val _ _ _ _ HhstepK) as [[]%not_eq_None_Some|HK''].
    { by eapply val_head_stuck. }
    subst. rewrite !fill_empty //.
  Qed.

  Lemma head_reducible_prim_step e1 σ1 ρ :
    head_reducible e1 σ1 →
    prim_step e1 σ1 ρ > 0 → head_step e1 σ1 ρ > 0.
  Proof.
    intros. destruct ρ.
    edestruct (head_reducible_prim_step_ctx empty_ectx) as (?&?&?);
      rewrite ?fill_empty; eauto.
    by simplify_eq; rewrite fill_empty.
  Qed.

  Lemma not_head_reducible_dzero e σ :
    head_irreducible e σ → head_step e σ = dzero.
  Proof.
    rewrite /reducible.
    intros Hred%not_head_reducible. apply dzero_ext=> ρ.
    destruct (Req_dec (head_step e σ ρ) 0); [done|].
    exfalso. apply Hred.
    exists ρ.
    pose proof (pmf_le_1 (head_step e σ) ρ).
    pose proof (pmf_pos (head_step e σ) ρ).
    lra.
  Qed.

  (* Every evaluation context is a context. *)
  Global Instance ectx_lang_ctx K : LanguageCtx (fill K).
  Proof.
    split; simpl.
    - eauto using fill_not_val.
    - apply _.
    - apply fill_prim_step_dbind.
  Qed.

  Record pure_head_step (e1 e2 : expr Λ) := {
    pure_head_step_safe σ1 : head_reducible e1 σ1;
    pure_head_step_det σ1 : head_step e1 σ1 (e2, σ1) = 1;
  }.

  Lemma pure_head_step_pure_step e1 e2 : pure_head_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros σ. destruct (Hp1 σ) as ([e2' σ2] & ?).
      eexists (e2', σ2). by apply head_prim_step.
    - intros σ1. rewrite /= head_prim_step_eq //.
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
Coercion ectx_lang : ectxLanguage >-> language.

(* This definition makes sure that the fields of the [language] record do not
refer to the projections of the [ectxLanguage] record but to the actual fields
of the [ectxLanguage] record. This is crucial for canonical structure search to
work.

Note that this trick no longer works when we switch to canonical projections
because then the pattern match [let '...] will be desugared into projections. *)
Definition LanguageOfEctx (Λ : ectxLanguage) : language :=
  let '@EctxLanguage E V C St StI _ _ _ _ _ _ _ _ of_val to_val empty comp fill decomp head state act mix := Λ in
  @Language E V St StI _ _ _ _ _ _ _ _ of_val to_val _ state act
    (@ectx_lang_mixin (@EctxLanguage E V C St StI _ _ _ _ _ _ _ _ of_val to_val empty comp fill decomp head state act mix )).

Global Arguments LanguageOfEctx : simpl never.
