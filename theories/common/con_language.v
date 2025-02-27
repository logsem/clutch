From Coq Require Import Reals Psatz.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From coneris.bi Require Export weakestpre.
From coneris.prob Require Import distribution mdp.

Section con_language_mixin.
  Context {expr val state state_idx : Type}.
  Context `{Countable expr, Countable val, Countable state, Countable state_idx}.

  Context (of_val : val → expr).
  Context (to_val : expr → option val).

  Context (prim_step  : expr → state → distr (expr * state * list expr)).
  Context (state_step : state → state_idx → distr state).
  (* For [prob_lang] this will just be [λ σ, elements (dom σ.(tapes))] - it'll
     be nicer with just a set but there's no set-big_op for disjunction in Iris
     at the moment, so lets stick to a list for now *)
  Context (get_active : state → list state_idx).

  Record ConLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e σ ρ : prim_step e σ ρ > 0 → to_val e = None;
    (** [state_step] preserves reducibility *)
    mixin_state_step_not_stuck e σ σ' α :
      state_step σ α σ' > 0 → (∃ ρ, prim_step e σ ρ > 0) ↔ (∃ ρ', prim_step e σ' ρ' > 0);
    (** The mass of active [state_step]s is 1 *)
    mixin_state_step_mass σ α :
      α ∈ get_active σ → SeriesC (state_step σ α) = 1;
    (** The mass of reducible [prim_step]s is 1 *)
    mixin_prim_step_mass e σ :
      (∃ ρ, prim_step e σ ρ > 0) → SeriesC (prim_step e σ) = 1;
  }.
End con_language_mixin.


Structure conLanguage := ConLanguage {
  expr : Type;
  val : Type;
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
  prim_step : expr → state → distr (expr * state * list expr);
  state_step : state → state_idx → distr state;
  get_active : state → list state_idx;

  con_language_mixin : ConLanguageMixin of_val to_val prim_step state_step get_active
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments ConLanguage {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ } _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments state_step {_}.
Global Arguments prim_step {_} _ _.
Global Arguments get_active {_} _.

#[global] Existing Instance expr_eqdec.
#[global] Existing Instance val_eqdec.
#[global] Existing Instance state_eqdec.
#[global] Existing Instance expr_countable.
#[global] Existing Instance val_countable.
#[global] Existing Instance state_countable.
#[global] Existing Instance state_idx_countable.

Canonical Structure stateO Λ := leibnizO (state Λ).
Canonical Structure valO Λ := leibnizO (val Λ).
Canonical Structure exprO Λ := leibnizO (expr Λ).

Definition cfg (Λ : conLanguage) := (list (expr Λ) * state Λ)%type.
Definition partial_cfg (Λ : conLanguage) := (expr Λ * state Λ) % type.

Definition fill_lift {Λ} (K : expr Λ → expr Λ) : (partial_cfg Λ) → (partial_cfg Λ) :=
  λ '(e, σ), (K e, σ).

Global Instance inj_fill_lift {Λ : conLanguage} (K : expr Λ → expr Λ) :
  Inj (=) (=) K →
  Inj (=) (=) (fill_lift K).
Proof. by intros ? [] [] [=->%(inj _) ->]. Qed.

Definition fill_lift' {Λ} (K : expr Λ → expr Λ)
  : (expr Λ * state Λ * list (expr Λ)) → (expr Λ * state Λ * list (expr Λ)):=
  (λ '(e, σ, efs), (fill_lift K (e, σ), efs)).

Global Instance inj_fill_lift' {Λ : conLanguage} (K : expr Λ → expr Λ) :
  Inj (=) (=) K →
  Inj (=) (=) (fill_lift' K).
Proof. intros ? [[]] [[]] ?. by simplify_eq.
Qed.

Class ConLanguageCtx {Λ : conLanguage} (K : expr Λ → expr Λ) := {
  fill_not_val e :
    to_val e = None → to_val (K e) = None;
  fill_inj : Inj (=) (=) K;
  fill_dmap e1 σ1:
    to_val e1 = None →
    prim_step (K e1) σ1 = dmap (fill_lift' K) (prim_step e1 σ1)
}.

#[global] Existing Instance fill_inj.

Inductive atomicity := StronglyAtomic | WeaklyAtomic.

Section con_language.
  Context {Λ : conLanguage}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.

  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. apply con_language_mixin. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. apply con_language_mixin. Qed.
  Lemma val_stuck e σ ρ : prim_step e σ ρ > 0 → to_val e = None.
  Proof. apply con_language_mixin. Qed.
  Lemma state_step_not_stuck e σ σ' α :
    state_step σ α σ' > 0 → (∃ ρ, prim_step e σ ρ > 0) ↔ (∃ ρ', prim_step e σ' ρ' > 0).
  Proof. apply con_language_mixin. Qed.
  Lemma state_step_mass σ α : α ∈ get_active σ → SeriesC (state_step σ α) = 1.
  Proof. apply con_language_mixin. Qed.
  Lemma prim_step_mass e σ :
    (∃ ρ, prim_step e σ ρ > 0) → SeriesC (prim_step e σ) = 1.
  Proof. apply con_language_mixin. Qed.

  Definition reducible e σ :=
    ∃ ρ, prim_step e σ ρ > 0.
  Definition irreducible e σ :=
    ∀ ρ, prim_step e σ ρ = 0.
  Definition stuck e σ := (to_val e) = None ∧ irreducible e σ.
  Definition not_stuck e σ :=
    is_Some (to_val e) \/ reducible e σ.
  
  Lemma not_reducible e σ  : ¬ reducible e σ ↔ irreducible e σ.
  Proof.
    unfold reducible, irreducible. split.
    - move=> /not_exists_forall_not Hneg ρ.
      specialize (Hneg ρ). apply Rnot_gt_ge in Hneg.
      pose proof (pmf_pos (prim_step e σ) ρ). lra.
    - intros Hall [ρ ?]. specialize (Hall ρ). lra.
  Qed.
  
  Lemma not_not_stuck e σ : ¬ not_stuck e σ ↔ stuck e σ.
  Proof.
    rewrite /stuck /not_stuck -not_reducible.
    destruct (to_val e); first naive_solver.
    split; first naive_solver.
    intros [][[]|]; naive_solver.
  Qed.
  
  Class Atomic (a : atomicity) (e : expr Λ) : Prop :=
    atomic σ e' σ' efs:
      prim_step e σ (e', σ', efs) > 0 →
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Lemma strongly_atomic_atomic e a :
    Atomic StronglyAtomic e → Atomic a e.
  Proof.
    unfold Atomic. destruct a; eauto.
    intros ????? H' [[]].
    epose proof pmf_pos (prim_step e' σ') _ as [K|]; last done.
    apply Rlt_gt, val_stuck in K.
    apply H in H'. rewrite K in H'.
    destruct H'. done.
  Qed.

  Lemma fill_step e1 σ1 e2 σ2 efs `{!ConLanguageCtx K} :
    prim_step e1 σ1 (e2, σ2, efs) > 0 →
    prim_step (K e1) σ1 (K e2, σ2, efs) > 0.
  Proof.
    intros Hs.
    rewrite fill_dmap; [|by eapply val_stuck].
    apply dbind_pos. eexists (_,_). split; [|done].
    rewrite dret_1_1 //. lra.
  Qed.

  Lemma fill_step_inv e1' σ1 e2 σ2 efs `{!ConLanguageCtx K} :
    to_val e1' = None → prim_step (K e1') σ1 (e2, σ2, efs) > 0 →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 (e2', σ2, efs) > 0.
  Proof.
    intros Hv. rewrite fill_dmap //.
    intros ([[e1 σ1']?] & [=]%dret_pos & Hstep)%dbind_pos.
    subst. eauto.
  Qed.

  Lemma fill_step_prob e1 σ1 e2 σ2 efs `{!ConLanguageCtx K} :
    to_val e1 = None →
    prim_step e1 σ1 (e2, σ2, efs) = prim_step (K e1) σ1 (K e2, σ2, efs).
  Proof.
    intros Hv. rewrite fill_dmap //.
    by erewrite (dmap_elem_eq _ _ _ _).
  Qed.

  Lemma reducible_fill `{!@ConLanguageCtx Λ K} e σ :
    reducible e σ → reducible (K e) σ.
  Proof.
    unfold reducible in *. intros [[[]]]. eexists _; by apply fill_step.
  Qed.
  Lemma reducible_fill_inv `{!@ConLanguageCtx Λ K} e σ :
    to_val e = None → reducible (K e) σ → reducible e σ.
  Proof.
    intros H0 ([[]]&Hstep); unfold reducible.
    pose proof fill_step_inv _ _  _ _ _ H0 Hstep as [? [-> ?]].
    naive_solver.
  Qed.
  Lemma state_step_reducible e σ σ' α :
    state_step σ α σ' > 0 → reducible e σ ↔ reducible e σ'.
  Proof. apply state_step_not_stuck. Qed.
  Lemma state_step_iterM_reducible e σ σ' α n:
    iterM n (λ σ, state_step σ α) σ σ'> 0 → reducible e σ ↔ reducible e σ'.
  Proof.
    revert σ σ'.
    induction n.
    - intros σ σ'. rewrite iterM_O. by intros ->%dret_pos.
    - intros σ σ'. rewrite iterM_Sn. rewrite dbind_pos. elim.
      intros x [??]. pose proof state_step_reducible. naive_solver.
  Qed.

  Lemma irreducible_fill `{!@ConLanguageCtx Λ K} e σ :
    to_val e = None → irreducible e σ → irreducible (K e) σ.
  Proof. rewrite /irreducible.
         intros H0 H1[[]] .
         epose proof pmf_pos (prim_step (K e) σ) _ as [T|]; last done.
         apply Rlt_gt in T.
         epose proof fill_step_inv _ _ _ _ _ H0 T as [? [-> H2]].
         rewrite H1 in H2. lra.
  Qed. 
  Lemma irreducible_fill_inv `{!@ConLanguageCtx Λ K} e σ :
    irreducible (K e) σ → irreducible e σ.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.

  Lemma not_stuck_fill_inv K `{!@ConLanguageCtx Λ K} e σ :
    not_stuck (K e) σ → not_stuck e σ.
  Proof.
    rewrite /not_stuck /= -!not_eq_None_Some.
    intros [?|?].
    - auto using fill_not_val.
    - destruct (decide (to_val e = None)); eauto using reducible_fill_inv.
  Qed.

  Lemma stuck_fill `{!@ConLanguageCtx Λ K} e σ :
    stuck e σ → stuck (K e) σ.
  Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed.

  Record pure_step (e1 e2 : expr Λ)  := {
    pure_step_safe σ1 : reducible e1 σ1;
    pure_step_det σ : prim_step e1 σ (e2, σ, []) = 1;
  }.

  Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) :=
    pure_exec : φ → relations.nsteps pure_step n e1 e2.

  Lemma pure_step_ctx K `{!@ConLanguageCtx Λ K} e1 e2 :
    pure_step e1 e2 → pure_step (K e1) (K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible in *. intros σ1.
      destruct (Hred σ1) as [[[]]].
      eexists. by eapply fill_step.
    - intros σ.
      rewrite -fill_step_prob //.
      eapply val_stuck. erewrite Hstep. lra.
      Unshelve.
      done.
  Qed.

  Lemma pure_step_nsteps_ctx K `{!@ConLanguageCtx Λ K} n e1 e2 :
    relations.nsteps pure_step n e1 e2 →
    relations.nsteps pure_step n (K e1) (K e2).
  Proof. eauto using nsteps_congruence, pure_step_ctx. Qed.

  Lemma rtc_pure_step_ctx K `{!@ConLanguageCtx Λ K} e1 e2 :
    rtc pure_step e1 e2 → rtc pure_step (K e1) (K e2).
  Proof. eauto using rtc_congruence, pure_step_ctx. Qed.

  (* We do not make this an instance because it is awfully general. *)
  Lemma pure_exec_ctx K `{!@ConLanguageCtx Λ K} φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (K e1) (K e2).
  Proof. rewrite /PureExec; eauto using pure_step_nsteps_ctx. Qed.

  Lemma PureExec_reducible σ1 φ n e1 e2 :
    φ → PureExec φ (S n) e1 e2 → reducible e1 σ1.
  Proof. move => Hφ /(_ Hφ). inversion_clear 1. apply H. Qed.

  Lemma PureExec_not_val `{Inhabited (con_language.state Λ)} φ n e1 e2 :
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

  Lemma fill_is_val e K `{@ConLanguageCtx Λ K} :
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
End con_language.

(* con_language is a mdp *)
Definition con_lang_mdp_step (Λ : conLanguage) (n: nat) (ρ : cfg Λ) : distr (cfg Λ) :=
  let '(expr_lis, σ) := ρ in
  match mbind to_val (expr_lis!!0%nat) with
  | Some _ => dzero
  | None => match expr_lis!!n with
           | None => (* thread id exceed num of thread, so we stutter *)
               dret (expr_lis, σ)
           | Some expr =>
               match to_val expr with 
               | Some _ => (* expr is a val, so we stutter *) dret (expr_lis, σ)
               | None => dmap (λ '(expr', σ', efs), ((<[n:=expr']> expr_lis) ++ efs, σ')) (prim_step expr σ)
               end
           end
  end.

Definition con_lang_mdp_to_final (Λ : conLanguage) (ρ : cfg Λ) : option (val Λ):=
  let '(expr_lis, σ) := ρ in
  match expr_lis !! 0%nat with
  | Some expr => to_val expr
  | None => None 
  end.

Definition con_lang_mdp_mixin (Λ : conLanguage) :
  MdpMixin (con_lang_mdp_step Λ) (con_lang_mdp_to_final Λ).
Proof.
  constructor.
  intros []. simpl.
  case_match; last by intros [].
  intros [? H1] ? .
  intros. case_match eqn: H0; first done.
  exfalso.
  apply of_to_val in H1. subst. simpl in H0.
  rewrite to_of_val in H0. done.
Qed.

Canonical Structure con_lang_mdp (Λ : conLanguage):mdp := Mdp _ _ (con_lang_mdp_mixin Λ).


Global Hint Mode PureExec + - - ! - : typeclass_instances.
