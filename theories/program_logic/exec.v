From Coq Require Import Reals Psatz.
From stdpp Require Import gmap.
From self.prelude Require Import classical.
From self.prob Require Export distribution couplings.
From self.program_logic Require Export language.

Inductive action (Λ : language) :=
  (* prim_step *)
  | PRIM
  (* state_step *)
  | STATE (α : state_idx Λ).

Global Arguments PRIM {Λ}.
Global Arguments STATE {Λ} _.

(* TODO: come up with better naming; "scheduler" and "scheduling function" is
   not the most well-fitting names *)

Definition scheduler_fn (Λ : language) := gmap (cfg Λ) (action Λ).

Class SchedulerFnWf {Λ} (f : scheduler_fn Λ) := {
  (* The definition of [exec_fn] doesn't explicitly consider whether the
     expression is a value or not. If [f] schedules a [prim_step] when the
     expression [e] is a value, the measure will be zero; when plugging [e] into
     a context [K], the [prim_step] measure on [K e] might not be zero
     anymore. This breaks lemmas like [exec_ctx_lift_pmf] that are cruical for
     proving the [wp_bind] rule. *)

  (* For now, the well-formedness condition requires that the scheduler does not
     schedule anything when the program has reached a value. Conceptually it
     should be fine to schedule state steps, however, and this requirement could
     be relaxed slightly. *)
  scheduler_fn_val e σ : is_Some (to_val e) → f !! (e, σ) = None;
}.

Global Arguments scheduler_fn_val {_} _ _.

Local Open Scope R.

Section exec_fn.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types ρ : cfg Λ.
  Implicit Types α : state_idx Λ.
  Implicit Types f : scheduler_fn Λ.

  Definition exec_fn_pmf '(e, σ) f : cfg Λ → R :=
    match f !! (e, σ) with
    | Some PRIM => prim_step e σ
    | Some (STATE α) => strength_l e (state_step σ α)
    | None => dzero
    end.

  Program Definition exec_fn ρ f : distr (cfg Λ) :=
    MkDistr (exec_fn_pmf ρ f) _ _ _.
  Solve Obligations with rewrite /exec_fn_pmf; intros [] ?; repeat case_match; done.

  Lemma exec_fn_pmf_unfold f ρ ρ' :
    exec_fn ρ f ρ' =
      match f !! ρ with
      | Some PRIM => prim_step ρ.1 ρ.2 ρ'
      | Some (STATE α) => strength_l ρ.1 (state_step ρ.2 α) ρ'
      | _ => 0%R
      end.
  Proof.
    destruct ρ as [e σ].
    rewrite /exec_fn {1}/pmf /= /exec_fn_pmf /=.
    by destruct (f !! _) as [[]|].
  Qed.

  Lemma exec_fn_unfold f ρ :
    exec_fn ρ f =
      match f !! ρ with
      | Some PRIM => prim_step ρ.1 ρ.2
      | Some (STATE α) => strength_l ρ.1 (state_step ρ.2 α)
      | _ => dzero
      end.
  Proof.
    apply distr_ext=>?. rewrite exec_fn_pmf_unfold. by repeat case_match.
  Qed.
End exec_fn.

Global Arguments exec_fn {_} _ _ : simpl never.

Definition scheduler (Λ : language) := list (scheduler_fn Λ).

(* A "non-blocking" scheduler will always schedule a [prim_step] at the end but
   possibly add some [state_step]s beforehand.

   In a sequential language, it should morally be fine to do multiple
   [prim_step]s at once but we stick to exactly one [prim_step] for now as it
   allows us to build on our usual intuition about atomicity and invariants in
   the program logic. *)
Inductive non_blocking {Λ} : scheduler Λ → cfg Λ → Prop :=
| nonblock_prim f ρ :
  f !! ρ = Some PRIM →
  non_blocking [f] ρ
| nonblock_state f ξ ρ α e σ :
  f !! ρ = Some (STATE α) →
  ρ = (e, σ) →
  (∀ σ', state_step σ α σ' > 0 → non_blocking ξ (e, σ')) →
  non_blocking (f :: ξ) ρ.

Notation SchedulerFnsWf ξ := (TCForall SchedulerFnWf ξ).

Class SchedulerWf {Λ} (ξ : scheduler Λ) (ρ : cfg Λ) := {
  (* all the scheduling functions are individually well-formed *)
  scheduler_fns_wf : SchedulerFnsWf ξ;
  (* the scheduler must be non-blocking w.r.t. [ρ]; this is important for the
     extracted trace scheduler in the adequacy theorem of the program logic to
     be non-blocking as well. *)
  scheduler_non_blocking : non_blocking ξ ρ;
}.

Global Instance SchedulerFnsWfToFnWf {Λ} (f : scheduler_fn Λ) (ξ : scheduler Λ) :
  SchedulerFnsWf (f :: ξ) → SchedulerFnWf f.
Proof. by inversion 1. Qed.

(* We add this as a lemma as an instance makes typeclass resolution diverge *)
Lemma scheduler_fns_wf_tail {Λ} (f : scheduler_fn Λ) (ξ : scheduler Λ) :
  SchedulerFnsWf (f :: ξ) → SchedulerFnsWf ξ.
Proof. by inversion 1. Qed.

Global Instance SchedulerWfToFnWf {Λ} (ξ : scheduler Λ) (ρ : cfg Λ) :
  SchedulerWf ξ ρ → SchedulerFnsWf ξ.
Proof. by inversion 1. Qed.

Section exec.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types f : scheduler_fn Λ.
  Implicit Types ξ : scheduler Λ.

  Definition exec ξ ρ : distr (cfg Λ) := foldlM exec_fn ρ ξ.

  Lemma exec_nil ρ :
    exec [] ρ = dret ρ.
  Proof. done. Qed.

  Lemma exec_cons ρ f ξ :
    exec (f :: ξ) ρ = dbind (λ ρ'', exec ξ ρ'') (exec_fn ρ f).
  Proof. done. Qed.

  Lemma exec_prim_step e1 e2 σ1 σ2 ξ `{Hwf : !SchedulerWf ξ (e1, σ1)} :
    exec ξ (e1, σ1) (e2, σ2) > 0 → ∃ σ, prim_step e1 σ (e2, σ2) > 0.
  Proof.
    revert σ1 Hwf. induction ξ as [|f ξ IH].
    { intros ? [? Hnb]. inversion Hnb. }
    intros σ1 [Hfns Hnb]. rewrite exec_cons exec_fn_unfold.
    inversion Hnb; simplify_map_eq.
    - intros [? [->%dret_pos ?]]%dbind_pos_support. eauto.
    - intros [? [? (?&?&?)%dmap_pos]]%dbind_pos_support.
      simplify_eq.
      eapply IH; [|done].
      econstructor; [|eauto].
      by eapply scheduler_fns_wf_tail.
   Qed.
End exec.

Global Arguments exec {_} _ _ : simpl never.

(** * [LanguageCtx] lifting of a scheduler  *)
Section ctx_lifting.
  Context {Λ : language}.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types ρ : cfg Λ.
  Implicit Types α : state_idx Λ.
  Implicit Types f : scheduler_fn Λ.
  Implicit Types ξ : scheduler Λ.
  Implicit Types K : expr Λ → expr Λ.

  Definition fill_lift K : cfg Λ → cfg Λ := (λ '(e, σ), (K e, σ)).

  Global Instance fill_lift_inj K `{!LanguageCtx K} : Inj (=) (=) (fill_lift K).
  Proof. rewrite /fill_lift. by intros [] [] [= <-%fill_inj <-]. Qed.

  (* Maps the domain of the scheduling function from expressions of the shape
     [e] to [K e] *)
  Definition sch_fn_ctx_lift K f : scheduler_fn Λ := kmap (fill_lift K) f.

  Definition sch_ctx_lift K ξ : scheduler Λ := sch_fn_ctx_lift K <$> ξ.

  Lemma sch_fn_ctx_lift_lookup K `{!LanguageCtx K} f e σ:
    sch_fn_ctx_lift K f !! (K e, σ) = f !! (e, σ).
  Proof. rewrite /sch_fn_ctx_lift -(lookup_kmap (fill_lift _) _ (e , _)) //. Qed.

  Lemma sch_ctx_lift_cons K `{!LanguageCtx K} f ξ :
    sch_ctx_lift K (f :: ξ) = sch_fn_ctx_lift K f :: sch_ctx_lift K ξ.
  Proof. done. Qed.

  Global Instance sch_fn_ctx_lift_wf f K `{!LanguageCtx K} :
    SchedulerFnWf f → SchedulerFnWf (sch_fn_ctx_lift K f).
  Proof.
    intros Hwf. constructor.
    intros e σ Hval.
    rewrite /sch_fn_ctx_lift.
    rewrite lookup_kmap_None.
    intros [e' σ'] [=]; simplify_eq.
    eapply scheduler_fn_val; [done|].
    by eapply fill_is_val.
  Qed.

  Lemma sch_ctx_lift_fns ξ K `{!LanguageCtx K} :
    TCForall SchedulerFnWf ξ → TCForall SchedulerFnWf (sch_ctx_lift K ξ).
  Proof.
    induction ξ; [done|].
    inversion 1; simplify_eq.
    rewrite sch_ctx_lift_cons.
    eapply TCForall_cons; [apply _|eauto].
  Qed.

  Lemma sch_ctx_lift_nonblocking ξ K `{!LanguageCtx K} e σ :
    non_blocking ξ (e, σ) → non_blocking (sch_ctx_lift K ξ) (K e, σ).
  Proof.
    revert σ. induction ξ.
    { inversion 1. }
    intros σ. inversion 1; simplify_eq.
    - eapply nonblock_prim. rewrite sch_fn_ctx_lift_lookup //.
    - rewrite sch_ctx_lift_cons. eapply nonblock_state; [|done|eauto].
      rewrite sch_fn_ctx_lift_lookup //.
  Qed.

  Global Instance sch_ctx_lift_wf ξ K `{!LanguageCtx K} e σ :
    SchedulerWf ξ (e, σ) → SchedulerWf (sch_ctx_lift K ξ) (K e, σ).
  Proof.
    inversion 1.
    constructor; [by apply sch_ctx_lift_fns|by apply sch_ctx_lift_nonblocking].
  Qed.

  Lemma exec_ctx_lift_pmf_pos K `{!LanguageCtx K} e1 σ1 e2 σ2 ξ `{Hwf : !SchedulerFnsWf ξ } :
    exec (sch_ctx_lift K ξ) (K e1, σ1) (e2, σ2) > 0 → ∃ e2', e2 = K e2'.
  Proof.
    revert e1 σ1 e2 σ2.
    induction ξ as [|f ξ IH].
    - intros ????. rewrite exec_nil. intros [=]%dret_pos. eauto.
    - intros ????.
      inversion Hwf; simplify_eq.
      rewrite sch_ctx_lift_cons exec_cons.
      rewrite exec_fn_unfold sch_fn_ctx_lift_lookup /=.
      destruct (f !! _) as [[]|] eqn:Heq.
      + intros [[e3 σ3] [Hexec Hs]]%dbind_pos_support.
        destruct (to_val e1) as [v|] eqn:Heq'.
        { rewrite scheduler_fn_val in Heq; [simplify_eq|eauto]. }
        eapply fill_step_inv in Hs as [e3' [? ?]]; [|done].
        simplify_eq. by eapply IH.
      + intros [[e3 σ3] [Hexec [σ [? ?]]%dmap_pos]]%dbind_pos_support.
        simplify_eq. by eapply IH.
      + rewrite dbind_dzero_pmf. lra.
  Qed.

  Lemma exec_ctx_lift_pmf K `{!LanguageCtx K} ξ `{Hwf : !SchedulerFnsWf ξ} e1 σ1 e2 σ2 :
    exec (sch_ctx_lift K ξ) (K e1, σ1) (K e2, σ2) = exec ξ (e1, σ1) (e2, σ2) .
  Proof.
    revert e1 σ1.
    induction ξ as [|f ξ IH]; intros.
    { rewrite 2!exec_nil. apply (dret_pmf_map (fill_lift _) (e1, _) (e2, _)). }
    rewrite sch_ctx_lift_cons 2!exec_cons 2!exec_fn_unfold.
    rewrite sch_fn_ctx_lift_lookup.
    destruct (to_val e1) as [v|] eqn:Heq.
    { erewrite 2!(scheduler_fn_val f); try (apply _ || eauto).
      rewrite 2!dbind_dzero //. }
    destruct (f !! _) as [[] |]=>/=.
    - inversion Hwf; simplify_eq.
      rewrite /pmf /= /dbind_pmf.
      rewrite (SeriesC_rearrange_covering (fill_lift K)) /=; last first.
      { eapply ex_seriesC_ext.
        - intros ρ. rewrite Rabs_right //.
          by apply Rle_ge, Rmult_le_pos.
        - eapply pmf_ex_seriesC_mult_fn. eauto. }
      { intros [] [Hs ?]%Rmult_neq_0_pos; [|done|done].
        eapply fill_step_inv in Hs as (?&?&?); [|done]; subst. by eexists (_,_). }
      { by intros ??? ?%(inj _). }
      apply SeriesC_ext; intros [e2' σ]=>/=.
      rewrite IH -fill_step_prob //.
    - inversion Hwf; simplify_eq.
      rewrite /pmf /= /dbind_pmf /strength_l.
      rewrite (SeriesC_rearrange_covering (fill_lift K)) /=; last first.
      { eapply ex_seriesC_ext.
        - intros ρ. rewrite Rabs_right //.
          by apply Rle_ge, Rmult_le_pos.
        - eapply pmf_ex_seriesC_mult_fn. eauto. }
      { intros [] [Hs ?]%Rmult_neq_0_pos; [|done|done].
        eapply dmap_pos in Hs as (σ' & ? & ?); simplify_eq.
        by eexists (_,_). }
      { by intros ??? ?%(inj _). }
      apply SeriesC_ext; intros [e σ]=>/=.
      destruct (decide (e = e1)); [subst|].
      + rewrite 2!dbind_dret_pmf_map IH. lra.
      + rewrite /dmap {1 3}/pmf /= /dbind_pmf.
        setoid_rewrite dret_0; [|intros ?; simplify_eq..].
        rewrite SeriesC_0; [lra|]. intros; lra.
    - rewrite 2!dbind_dzero //.
  Qed.

  Lemma exec_ctx_lift_fill K `{!LanguageCtx K} e1 σ1 ξ `{!SchedulerFnsWf ξ}:
    exec (sch_ctx_lift K ξ) (K e1, σ1) = dmap (fill_lift K) (exec ξ (e1, σ1)).
  Proof.
    apply dmap_rearrange; [apply _| |].
    - intros [e2 σ2] [? ?]%exec_ctx_lift_pmf_pos; [|done|done].
      eexists (_,_). by simplify_eq.
    - intros []. by apply exec_ctx_lift_pmf.
  Qed.

  Lemma Rcoupl_exec_ctx_lift K `{!LanguageCtx K} e1 σ1 ρ R ξ ξ' `{!SchedulerFnsWf ξ}:
    Rcoupl (exec ξ (e1, σ1)) (exec ξ' ρ) R →
    Rcoupl (exec (sch_ctx_lift K ξ) (K e1, σ1)) (exec ξ' ρ)
      (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R (e2', σ2) ρ').
  Proof.
    intros Hcpl.
    rewrite exec_ctx_lift_fill //.
    rewrite -(dret_id_right (exec ξ' ρ)).
    rewrite /dmap.
    eapply Rcoupl_bind; [|done].
    intros [e2' σ2] ρ' HR =>/=.
    apply Rcoupl_ret; eauto.
  Qed.

End ctx_lifting.
