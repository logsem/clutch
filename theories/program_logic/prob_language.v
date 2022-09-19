From Coq Require Import Reals Psatz.
From stdpp Require Import gmap.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From iris.bi Require Export weakestpre.
From proba.prob Require Import distribution.

Section language_mixin.
  Context {expr val state action : Type}.
  Context `{Countable expr, Countable state}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).

  (** TODO: We need to add either a bottom element or require a sub-probability measure
      that is not required to sum to 1 *)
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

Definition scheduler_fn (Λ : language) := gmap (cfg Λ) (action Λ).
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
  Lemma val_stuck e σ α e' σ' : prim_step e σ α (e', σ') > 0 → to_val e = None.
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

  Definition kernel_conf (f : scheduler_fn Λ) (ρ ρ' : cfg Λ) : R :=
    if f !! ρ is Some α then prim_step ρ.1 ρ.2 α ρ' else 0.

  Program Definition kernel_conf_distr (f : scheduler_fn Λ) (ρ : cfg Λ) : distr (cfg Λ) :=
    MkDistr (kernel_conf f ρ) _ _.
  Next Obligation.
    intros. rewrite /kernel_conf. destruct (f !! ρ); [done|nra].
  Qed.
  Next Obligation.
    intros f ρ. rewrite /kernel_conf. destruct (f !! ρ); [done|].

    (* of course doesn't hold because it doesn't sum to one :-) *)
    Admitted.



  Inductive step (ρ1 : cfg Λ) (α : action Λ) (ρ2 : cfg Λ) : Prop :=
  | step_atomic e1 σ1 :
    ρ1 = (e1, σ1) →
    prim_step e1 σ1 α ρ2 > 0 →
    step ρ1 α ρ2.
  Local Hint Constructors step : core.

  (* Inductive nsteps : nat → cfg Λ → scheduler Λ → distr (cfg Λ) → Prop := *)
  (* | nsteps_refl ρ : *)
  (*   nsteps 0 ρ [] (dret ρ) *)
  (* | nsteps_l n f ξ ρ1 ρ2 α d d2 d3 : *)
  (*   f !! ρ1 = Some α → *)
  (*   step ρ1 α d2 → *)
  (*   nsteps n ρ2 ξ d3 → *)
  (*   (d = ρ2 ← d2; d3) → *)

  (*   (* nsteps n ρ2 ξ ρ3 → *) *)
  (*   nsteps (S n) ρ1 (f :: ξ) d  . *)
  (* Local Hint Constructors nsteps : core. *)

  (* Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v. *)
  (* Proof. intros <-. by rewrite to_of_val. Qed. *)
  (* Lemma not_reducible e σ : ¬reducible e σ ↔ irreducible e σ. *)
  (* Proof. unfold reducible, irreducible. naive_solver. Qed. *)
  (* Lemma reducible_not_val e σ : reducible e σ → to_val e = None. *)
  (* Proof. intros (?&?&?&?&?); eauto using val_stuck. Qed. *)
  (* Lemma reducible_no_obs_reducible e σ : reducible_no_obs e σ → reducible e σ. *)
  (* Proof. intros (?&?&?&?); eexists; eauto. Qed. *)
  (* Lemma val_irreducible e σ : is_Some (to_val e) → irreducible e σ. *)
  (* Proof. intros [??] ???? ?%val_stuck. by destruct (to_val e). Qed. *)
  (* Global Instance of_val_inj : Inj (=) (=) (@of_val Λ). *)
  (* Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed. *)
  (* Lemma not_not_stuck e σ : ¬not_stuck e σ ↔ stuck e σ. *)
  (* Proof. *)
  (*   rewrite /stuck /not_stuck -not_eq_None_Some -not_reducible. *)
  (*   destruct (decide (to_val e = None)); naive_solver. *)
  (* Qed. *)

  (* Lemma strongly_atomic_atomic e a : *)
  (*   Atomic StronglyAtomic e → Atomic a e. *)
  (* Proof. unfold Atomic. destruct a; eauto using val_irreducible. Qed. *)

  (* Lemma reducible_fill `{!@LanguageCtx Λ K} e σ : *)
  (*   reducible e σ → reducible (K e) σ. *)
  (* Proof. unfold reducible in *. naive_solver eauto using fill_step. Qed. *)
  (* Lemma reducible_fill_inv `{!@LanguageCtx Λ K} e σ : *)
  (*   to_val e = None → reducible (K e) σ → reducible e σ. *)
  (* Proof. *)
  (*   intros ? (e'&σ'&k&efs&Hstep); unfold reducible. *)
  (*   apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto. *)
  (* Qed. *)
  (* Lemma reducible_no_obs_fill `{!@LanguageCtx Λ K} e σ : *)
  (*   reducible_no_obs e σ → reducible_no_obs (K e) σ. *)
  (* Proof. unfold reducible_no_obs in *. naive_solver eauto using fill_step. Qed. *)
  (* Lemma reducible_no_obs_fill_inv `{!@LanguageCtx Λ K} e σ : *)
  (*   to_val e = None → reducible_no_obs (K e) σ → reducible_no_obs e σ. *)
  (* Proof. *)
  (*   intros ? (e'&σ'&efs&Hstep); unfold reducible_no_obs. *)
  (*   apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto. *)
  (* Qed. *)
  (* Lemma irreducible_fill `{!@LanguageCtx Λ K} e σ : *)
  (*   to_val e = None → irreducible e σ → irreducible (K e) σ. *)
  (* Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv. Qed. *)
  (* Lemma irreducible_fill_inv `{!@LanguageCtx Λ K} e σ : *)
  (*   irreducible (K e) σ → irreducible e σ. *)
  (* Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed. *)

  (* Lemma not_stuck_fill_inv K `{!@LanguageCtx Λ K} e σ : *)
  (*   not_stuck (K e) σ → not_stuck e σ. *)
  (* Proof. *)
  (*   rewrite /not_stuck -!not_eq_None_Some. intros [?|?]. *)
  (*   - auto using fill_not_val. *)
  (*   - destruct (decide (to_val e = None)); eauto using reducible_fill_inv. *)
  (* Qed. *)

  (* Lemma stuck_fill `{!@LanguageCtx Λ K} e σ : *)
  (*   stuck e σ → stuck (K e) σ. *)
  (* Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed. *)

  (* Lemma step_Permutation (t1 t1' t2 : list (expr Λ)) κ σ1 σ2 : *)
  (*   t1 ≡ₚ t1' → step (t1,σ1) κ (t2,σ2) → ∃ t2', t2 ≡ₚ t2' ∧ step (t1',σ1) κ (t2',σ2). *)
  (* Proof. *)
  (*   intros Ht [e1 σ1' e2 σ2' efs tl tr ?? Hstep]; simplify_eq/=. *)
  (*   move: Ht; rewrite -Permutation_middle (symmetry_iff (≡ₚ)). *)
  (*   intros (tl'&tr'&->&Ht)%Permutation_cons_inv_r. *)
  (*   exists (tl' ++ e2 :: tr' ++ efs); split; [|by econstructor]. *)
  (*   by rewrite -!Permutation_middle !assoc_L Ht. *)
  (* Qed. *)

  (* Lemma step_insert i t2 σ2 e κ e' σ3 efs : *)
  (*   t2 !! i = Some e → *)
  (*   prim_step e σ2 κ e' σ3 efs → *)
  (*   step (t2, σ2) κ (<[i:=e']>t2 ++ efs, σ3). *)
  (* Proof. *)
  (*   intros. *)
  (*   edestruct (elem_of_list_split_length t2) as (t21&t22&?&?); *)
  (*     first (by eauto using elem_of_list_lookup_2); simplify_eq. *)
  (*   econstructor; eauto. *)
  (*   by rewrite insert_app_r_alt // Nat.sub_diag /= -assoc_L. *)
  (* Qed. *)

  (* Lemma erased_step_Permutation (t1 t1' t2 : list (expr Λ)) σ1 σ2 : *)
  (*   t1 ≡ₚ t1' → erased_step (t1,σ1) (t2,σ2) → ∃ t2', t2 ≡ₚ t2' ∧ erased_step (t1',σ1) (t2',σ2). *)
  (* Proof. *)
  (*   intros Heq [? Hs]. pose proof (step_Permutation _ _ _ _ _ _ Heq Hs). firstorder. *)
  (*    (* FIXME: [naive_solver] should be able to handle this *) *)
  (* Qed. *)

  (* Record pure_step (e1 e2 : expr Λ) := { *)
  (*   pure_step_safe σ1 : reducible_no_obs e1 σ1; *)
  (*   pure_step_det σ1 κ e2' σ2 efs : *)
  (*     prim_step e1 σ1 κ e2' σ2 efs → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs = [] *)
  (* }. *)

  (* Notation pure_steps_tp := (Forall2 (rtc pure_step)). *)

  (* (* TODO: Exclude the case of [n=0], either here, or in [wp_pure] to avoid it *)
  (* succeeding when it did not actually do anything. *) *)
  (* Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) := *)
  (*   pure_exec : φ → relations.nsteps pure_step n e1 e2. *)

  (* Lemma pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 : *)
  (*   pure_step e1 e2 → *)
  (*   pure_step (K e1) (K e2). *)
  (* Proof. *)
  (*   intros [Hred Hstep]. split. *)
  (*   - unfold reducible_no_obs in *. naive_solver eauto using fill_step. *)
  (*   - intros σ1 κ e2' σ2 efs Hpstep. *)
  (*     destruct (fill_step_inv e1 σ1 κ e2' σ2 efs) as (e2'' & -> & ?); [|exact Hpstep|]. *)
  (*     + destruct (Hred σ1) as (? & ? & ? & ?); eauto using val_stuck. *)
  (*     + edestruct (Hstep σ1 κ e2'' σ2 efs) as (? & -> & -> & ->); auto. *)
  (* Qed. *)

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

  (* Lemma as_val_is_Some e : *)
  (*   (∃ v, of_val v = e) → is_Some (to_val e). *)
  (* Proof. intros [v <-]. rewrite to_of_val. eauto. Qed. *)

  (* Lemma prim_step_not_stuck e σ κ e' σ' efs : *)
  (*   prim_step e σ κ e' σ' efs → not_stuck e σ. *)
  (* Proof. rewrite /not_stuck /reducible. eauto 10. Qed. *)

  (* Lemma rtc_pure_step_val `{!Inhabited (state Λ)} v e : *)
  (*   rtc pure_step (of_val v) e → to_val e = Some v. *)
  (* Proof. *)
  (*   intros ?; rewrite <- to_of_val. *)
  (*   f_equal; symmetry; eapply rtc_nf; first done. *)
  (*   intros [e' [Hstep _]]. *)
  (*   destruct (Hstep inhabitant) as (?&?&?&Hval%val_stuck). *)
  (*   by rewrite to_of_val in Hval. *)
  (* Qed. *)

  (* (** Let thread pools [t1] and [t3] be such that each thread in [t1] makes *)
  (*  (zero or more) pure steps to the corresponding thread in [t3]. Furthermore, *)
  (*  let [t2] be a thread pool such that [t1] under state [σ1] makes a (single) *)
  (*  step to thread pool [t2] and state [σ2]. In this situation, either the step *)
  (*  from [t1] to [t2] corresponds to one of the pure steps between [t1] and [t3], *)
  (*  or, there is an [i] such that [i]th thread does not participate in the *)
  (*  pure steps between [t1] and [t3] and [t2] corresponds to taking a step in *)
  (*  the [i]th thread starting from [t1]. *) *)
  (* Lemma erased_step_pure_step_tp t1 σ1 t2 σ2 t3 : *)
  (*   erased_step (t1, σ1) (t2, σ2) → *)
  (*   pure_steps_tp t1 t3 → *)
  (*   (σ1 = σ2 ∧ pure_steps_tp t2 t3) ∨ *)
  (*   (∃ i e efs e' κ, *)
  (*     t1 !! i = Some e ∧ t3 !! i = Some e ∧ *)
  (*     t2 = <[i:=e']>t1 ++ efs ∧ *)
  (*     prim_step e σ1 κ e' σ2 efs). *)
  (* Proof. *)
  (*   intros [κ [e σ e' σ' efs t11 t12 ?? Hstep]] Hps; simplify_eq/=. *)
  (*   apply Forall2_app_inv_l in Hps *)
  (*     as (t31&?&Hpsteps&(e''&t32&Hps&?&->)%Forall2_cons_inv_l&->). *)
  (*   destruct Hps as [e|e1 e2 e3 [_ Hprs]]. *)
  (*   - right. *)
  (*     exists (length t11), e, efs, e', κ; split_and!; last done. *)
  (*     + by rewrite lookup_app_r // Nat.sub_diag. *)
  (*     + apply Forall2_length in Hpsteps. *)
  (*       by rewrite lookup_app_r Hpsteps // Nat.sub_diag. *)
  (*     + by rewrite insert_app_r_alt // Nat.sub_diag /= -assoc_L. *)
  (*   - edestruct Hprs as (?&?&?&?); first done; simplify_eq. *)
  (*     left; split; first done. *)
  (*     rewrite right_id_L. *)
  (*     eauto using Forall2_app. *)
  (* Qed. *)

End language.

(* Global Arguments step_atomic {Λ ρ1 κ ρ2}. *)

(* Notation pure_steps_tp := (Forall2 (rtc pure_step)). *)
