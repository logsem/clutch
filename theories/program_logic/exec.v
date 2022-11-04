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

  Lemma exec_singleton f ρ :
    exec [f] ρ = exec_fn ρ f.
  Proof. rewrite /= dret_id_right //. Qed.

  Lemma exec_snoc ξ f ρ :
    exec (ξ ++ [f]) ρ = dbind (λ ρ'', exec_fn ρ'' f) (exec ξ ρ).
  Proof.
    revert ρ. induction ξ; intros ρ.
    { rewrite exec_singleton exec_nil /= dret_id_left //. }
    rewrite -app_comm_cons !exec_cons.
    rewrite -dbind_assoc.
    eapply distr_ext=>ρ''.
    eapply dbind_pmf_ext; [|done|done].
    intros ρ1 ρ2. rewrite IHξ //.
  Qed.


  Lemma exec_app_pmf ξ1 ξ2 ρ ρ' :
    exec (ξ1 ++ ξ2) ρ ρ' = dbind (exec ξ2) (exec ξ1 ρ) ρ'.
  Proof.
    revert ρ ρ'. induction ξ1; intros ρ ρ'; simpl.
    { rewrite exec_nil dret_id_left_pmf //. }
    rewrite 2!exec_cons /=. rewrite -dbind_assoc.
    apply dbind_pmf_ext; auto.
  Qed.

  Lemma exec_app ξ1 ξ2 ρ :
    exec (ξ1 ++ ξ2) ρ = dbind (exec ξ2) (exec ξ1 ρ).
  Proof. apply distr_ext, exec_app_pmf. Qed.

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

(** * [PRIM] scheduler   *)
Section prim_scheduler.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types f : scheduler_fn Λ.
  Implicit Types ξ : scheduler Λ.
  Implicit Types K : expr Λ → expr Λ.

  Definition prim_step_sch_fn ρ : scheduler_fn Λ := {[ ρ := PRIM ]}.
  Definition prim_step_sch ρ : scheduler Λ := [prim_step_sch_fn ρ].

  Global Instance prim_step_sch_wf e σ :
    TCEq (to_val e) None → SchedulerWf (prim_step_sch (e, σ)) (e, σ).
  Proof.
    rewrite /prim_step_sch /prim_step_sch_fn. intros ?%TCEq_eq.
    constructor.
    - do 2 constructor. intros e' σ' [v Hv].
      rewrite lookup_singleton_None. intros [=]; simplify_eq.
    - apply nonblock_prim. rewrite lookup_singleton_Some //.
  Qed.

  Lemma exec_fn_prim_step_sch_fn_pmf e σ ρ :
    exec_fn (e, σ) (prim_step_sch_fn (e, σ)) ρ = prim_step e σ ρ.
  Proof. rewrite /prim_step_sch_fn exec_fn_pmf_unfold lookup_singleton //. Qed.

  Lemma exec_fn_prim_step_sch_fn_pmf_ne ρ ρ1 ρ2  :
    ρ1 ≠ ρ2 → exec_fn ρ1 (prim_step_sch_fn ρ2) ρ = 0.
  Proof. intros ?. rewrite /prim_step_sch_fn exec_fn_pmf_unfold lookup_singleton_ne //. Qed.

  Lemma exec_prim_step_sch_pmf e1 e2 σ1 σ2 :
    exec (prim_step_sch (e1, σ1)) (e1, σ1) (e2, σ2) = prim_step e1 σ1 (e2, σ2).
  Proof. rewrite /prim_step_sch exec_singleton exec_fn_prim_step_sch_fn_pmf //. Qed.

  Lemma exec_prim_step_sch e σ :
    exec (prim_step_sch (e, σ)) (e, σ) = prim_step e σ.
  Proof. eapply distr_ext. intros []. apply exec_prim_step_sch_pmf. Qed.

  Lemma exec_det_step ξ ρ e1 e2 σ1 σ2 :
    prim_step e1 σ1 (e2, σ2) = 1 →
    exec (ξ ++ prim_step_sch (e1, σ1)) ρ (e2, σ2) = exec ξ ρ (e1, σ1).
  Proof.
    intros Hdet.
    rewrite exec_snoc.
    rewrite {1}/pmf /= /dbind_pmf /=.
    erewrite (SeriesC_ext _
                (λ a, if bool_decide (a = (e1, σ1))
                      then exec ξ ρ (e1, σ1) *
                           exec_fn (e1, σ1) (prim_step_sch_fn (e1, σ1)) (e2, σ2)
                      else 0)); last first.
    { intros [e0 σ0]. case_bool_decide as Heq; [by inversion Heq|].
      rewrite exec_fn_prim_step_sch_fn_pmf_ne //. lra. }
    rewrite SeriesC_singleton.
    rewrite exec_fn_prim_step_sch_fn_pmf Hdet. lra.
  Qed.

  Lemma exec_det_step_ctx ξ ρ e1 e2 σ1 σ2 K `{!LanguageCtx K} :
    prim_step e1 σ1 (e2, σ2) = 1 →
    exec (ξ ++ prim_step_sch (K e1, σ1)) ρ (K e2, σ2) = exec ξ ρ (K e1, σ1).
  Proof.
    intros. eapply exec_det_step.
    rewrite -fill_step_prob //. eapply (val_stuck _ σ1 (e2, σ2)). lra.
  Qed.

  Lemma exec_PureExec_ctx K `{!LanguageCtx K} (P : Prop) n ξ ρ e e' σ :
    P →
    PureExec P n e e' →
    ∃ ξ', exec (ξ ++ ξ') ρ (K e', σ) = exec ξ ρ (K e, σ).
  Proof.
    move=> HP /(_ HP).
    (* We do induction in [n] as [nsteps] is defined in the "wrong" direction *)
    revert e e'. induction n=> e e'.
    { inversion 1; subst. exists []. rewrite app_nil_r //. }
    intros (e'' & Hsteps & Hpstep)%nsteps_inv_r.
    edestruct (IHn _ _ Hsteps) as [ξ' Hexec].
    exists (ξ' ++ prim_step_sch (K e'', σ)).
    rewrite app_assoc exec_det_step_ctx //. eapply Hpstep.
  Qed.

  (* TODO [SG]: The 3 lemmas below are currently not used (but I proved them
     before realising it was not the thing I needed...) *)
  (* Lemma exec_pure_step ξ ρ e e' σ : *)
  (*   pure_step e e' → *)
  (*   exec (prim_step_sch (e, σ) ++ ξ) (e, σ) ρ = exec ξ (e', σ) ρ. *)
  (* Proof. *)
  (*   intros [Hsafe Hdet]. *)
  (*   rewrite exec_cons. *)
  (*   rewrite {1}/pmf /= /dbind_pmf /=. *)
  (*   erewrite (SeriesC_ext _ *)
  (*               (λ a, if bool_decide (a = (e', σ)) *)
  (*                     then exec_fn (e, σ) (prim_step_sch_fn (e, σ)) (e', σ) * exec ξ (e', σ) ρ *)
  (*                     else 0)); last first. *)
  (*   { intros [e0 σ0]. case_bool_decide as Heq; [by inversion Heq|]. *)
  (*     rewrite exec_fn_prim_step_sch_fn_pmf //. *)
  (*     destruct (decide (prim_step e σ (e0, σ0) > 0)) as [Hp | Hp]. *)
  (*     - by destruct (pmf_1_supp_eq _ _ _ (Hdet σ) Hp). *)
  (*     - apply pmf_eq_0_not_gt_0 in Hp as ->. lra. } *)
  (*   rewrite SeriesC_singleton. *)
  (*   rewrite exec_fn_prim_step_sch_fn_pmf Hdet. lra. *)
  (* Qed. *)

  (* Lemma exec_pure_step_ctx ξ ρ e e' σ K `{!LanguageCtx K} : *)
  (*   pure_step e e' → *)
  (*   exec (prim_step_sch (K e, σ) ++ ξ) (K e, σ) ρ = exec ξ (K e', σ) ρ. *)
  (* Proof. intros ?%(pure_step_ctx K). by eapply exec_pure_step. Qed. *)

  (* Lemma exec_PureExec_ctx K `{!LanguageCtx K} (P : Prop) n ξ ρ e e' σ  : *)
  (*   P → *)
  (*   PureExec P n e e' → *)
  (*   ∃ ξ', exec (ξ' ++ ξ) (K e, σ) ρ = exec ξ (K e', σ) ρ. *)
  (* Proof. *)
  (*   intros HP. induction 1; [| |done]. *)
  (*   { exists []. rewrite app_nil_l //. } *)
  (*   destruct IHp as [ξ' Hexec]. *)
  (*   exists (prim_step_sch (K x, σ) ++ ξ'). *)
  (*   rewrite -app_assoc. *)
  (*   by erewrite exec_pure_step_ctx. *)
  (* Qed. *)

End prim_scheduler.

(** * [STATE(α)] scheduler  *)
Section state_step_sch.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types f : scheduler_fn Λ.
  Implicit Types ξ : scheduler Λ.

  Definition state_step_sch_fn ρ α : scheduler_fn Λ := {[ρ := STATE α]}.
  Definition state_step_sch ρ α : scheduler Λ := [state_step_sch_fn ρ α].

  Lemma exec_fn_state_step_sch_fn_pmf e σ σ' α :
    exec_fn (e, σ) (state_step_sch_fn (e, σ) α) (e, σ') = state_step σ α σ'.
  Proof.
    rewrite /prim_step_sch_fn exec_fn_pmf_unfold /= lookup_singleton //.
    rewrite /strength_l.
    erewrite dmap_eq; [done|apply _|done].
  Qed.

  Lemma exec_fn_state_step_sch_fn_pmf_ne e e' σ σ' α :
    e ≠ e' → exec_fn (e, σ) (state_step_sch_fn (e, σ) α) (e', σ') = 0.
  Proof.
    intros ?.
    rewrite /state_step_sch_fn exec_fn_pmf_unfold lookup_singleton //=.
    rewrite dmap_ne //. by intros [? [? [=]]].
  Qed.

  Lemma exec_state_step_sch_pmf e σ σ' α :
    exec (state_step_sch (e, σ) α) (e, σ) (e, σ') = state_step σ α σ'.
  Proof. rewrite /state_step_sch exec_singleton exec_fn_state_step_sch_fn_pmf //. Qed.

  Lemma exec_state_step_sch_pmf_ne e e' σ σ' α :
    e ≠ e' → exec (state_step_sch (e, σ) α) (e, σ) (e', σ') = 0.
  Proof. intros ?. rewrite /state_step_sch exec_singleton exec_fn_state_step_sch_fn_pmf_ne //. Qed.

  Lemma exec_state_step_sch e σ α :
    exec (state_step_sch (e, σ) α) (e, σ) = strength_l e (state_step σ α).
  Proof.
    eapply distr_ext. intros [e0 σ0].
    destruct (decide (e = e0)); subst.
    - rewrite exec_state_step_sch_pmf.
      rewrite /strength_l. erewrite dmap_eq; [done|apply _|done].
    - rewrite exec_state_step_sch_pmf_ne //.
      rewrite /strength_l dmap_ne //. by intros [? [? [=]]].
  Qed.

End state_step_sch.

(** * [STATE(α); PRIM] scheduler  *)
Section state_prim_sch.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types f : scheduler_fn Λ.
  Implicit Types ξ : scheduler Λ.

  Definition state_prim_step_sch ρ α : scheduler Λ := state_step_sch ρ α ++ prim_step_sch ρ.
End state_prim_sch.

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

Global Hint Extern 0 (TCEq (to_val ?e) _) =>
       match goal with | H : to_val e = _ |- _ => rewrite H; constructor end : core.
