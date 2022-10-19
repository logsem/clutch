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


Definition scheduler_fn (Λ : language) := gmap (cfg Λ) (action Λ).

Class SchedulerFnWf {Λ} (f : scheduler_fn Λ) := {
  scheduler_fn_val e σ : is_Some (to_val e) → f !! (e, σ) = None;
}.

Global Arguments scheduler_fn_val {_} _ &.

Definition scheduler (Λ : language) := list (scheduler_fn Λ).

Notation SchedulerWf ξ := (TCForall SchedulerFnWf ξ).

Global Instance SchedulerWfToFnWf {Λ} (f : scheduler_fn Λ) (ξ : scheduler Λ) :
  SchedulerWf (f :: ξ) → SchedulerFnWf f.
Proof. by inversion 1. Qed.

Local Open Scope R.

Section distribution.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types α : state_idx Λ.
  Implicit Types ξ : scheduler Λ.

  Definition exec_fn_pmf '(e, σ) (f : scheduler_fn Λ) ρ : R :=
    match f !! (e, σ) with
    | Some PRIM => prim_step e σ ρ
    | Some (STATE α) => strength_l e (state_step σ α) ρ
    | None => 0%R
    end.
  Program Definition exec_fn (ρ : cfg Λ) (f : scheduler_fn Λ) : distr (cfg Λ) :=
    MkDistr (exec_fn_pmf ρ f) _ _ _.
  Next Obligation. intros [] f ρ. rewrite /exec_fn_pmf. destruct (f !! _) as [[]|]; [done|done|done]. Qed.
  Next Obligation.
    intros [e σ] f. rewrite /exec_fn_pmf.
    destruct (f !! _) as [[]|]; [done|done|]. apply ex_seriesC_0.
  Qed.
  Next Obligation.
    intros [e σ] f. rewrite /exec_fn_pmf.
    destruct (f !! _) as [[]|]; [done|done|]. rewrite SeriesC_0 //; lra.
  Qed.

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

  Definition exec (ξ : scheduler Λ) (ρ : cfg Λ) : distr (cfg Λ) :=
    foldlM exec_fn ρ ξ.

  Lemma exec_nil ρ :
    exec [] ρ = dret ρ.
  Proof. done. Qed.

  Lemma exec_cons ρ f ξ :
    exec (f :: ξ) ρ = dbind (λ ρ'', exec ξ ρ'') (exec_fn ρ f).
  Proof. done. Qed.
End distribution.

Global Arguments exec_fn {_} _ _ : simpl never.
Global Arguments exec {_} _ _ : simpl never.

(** * [LanguageCtx] lifting of schedulers  *)
Section ctx_lifting.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types α : state_idx Λ.
  Implicit Types ξ : scheduler Λ.
  Implicit Types f : scheduler_fn Λ.

  Definition fill_lift K : cfg Λ → cfg Λ := (λ '(e, σ), (K e, σ)).

  #[global] Instance fill_lift_inj K `{!LanguageCtx K} : Inj (=) (=) (fill_lift K).
  Proof. rewrite /fill_lift. by intros [] [] [= <-%fill_inj <-]. Qed.

  Definition sch_fn_ctx_lift (K : expr Λ → expr Λ) (f : scheduler_fn Λ) : scheduler_fn Λ :=
    kmap (fill_lift K) f.

  Definition sch_ctx_lift (K : expr Λ → expr Λ) (ξ : scheduler Λ) : scheduler Λ :=
    sch_fn_ctx_lift K <$> ξ.

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

  Global Instance sch_ctx_lift_wf ξ K `{!LanguageCtx K} :
    SchedulerWf ξ → SchedulerWf (sch_ctx_lift K ξ).
  Proof.
    induction ξ; [done|].
    inversion 1; simplify_eq.
    rewrite sch_ctx_lift_cons.
    apply TCForall_cons; [apply _|eauto].
  Qed.

  (* TODO: move and prove *)
  Lemma SeriesC_rearrange_covering `{Countable A} (f : A → A) `{Inj A A (=) (=) f} (g : A → R) :
    (∀ a, (∀ a', a ≠ f a') → g a = 0%R) →
    SeriesC g = SeriesC (λ a, g (f a)).
  Proof. Admitted.

  Lemma exec_ctx_lift_pmf K `{!LanguageCtx K} ξ `{Hwf : !SchedulerWf ξ} e1 σ1 e2 σ2 :
    exec (sch_ctx_lift K ξ) (K e1, σ1) (K e2, σ2) = (exec ξ (e1, σ1)) (e2, σ2) .
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
      { intros [e3 σ3] Hdom.
        destruct (decide (prim_step (K e1) σ1 (e3, σ3) > 0)) as [Hs|]; last first.
        { rewrite Rmult_eq_0_compat_r //. by apply pmf_eq_0_not_gt_0. }
        apply fill_step_inv in Hs as (e3' & -> & H); [|done].
        exfalso; by eapply (Hdom (_, _)). }
      apply SeriesC_ext; intros [e2' σ].
      rewrite IH -fill_step_prob //.
    - inversion Hwf; simplify_eq.
      rewrite /pmf /= /dbind_pmf /strength_l.
      rewrite (SeriesC_rearrange_covering (fill_lift K)) /=; last first.
      { intros [e3 σ3] Hdom.
        destruct (decide (dmap (λ σ, (K e1, σ)) (state_step σ1 α) (e3, σ3) > 0)) as [H'|]; last first.
        { rewrite Rmult_eq_0_compat_r //. by apply pmf_eq_0_not_gt_0. }
        apply dmap_pos in H' as [σ [? ?]]. simplify_eq.
        exfalso. by eapply (Hdom (_,_)). }
      apply SeriesC_ext; intros [e σ].
      destruct (decide (e = e1)); [subst|].
      + rewrite 2!dbind_dret_pmf_map IH. lra.
      + rewrite /dmap {1 3}/pmf /= /dbind_pmf.
        setoid_rewrite dret_0; [|intros ?; simplify_eq..].
        rewrite SeriesC_0; [lra|]. intros; lra.
    - rewrite 2!dbind_dzero //.
  Qed.

  Lemma exec_ctx_lift_pmf_pos K `{!LanguageCtx K} e1 σ1 e2 σ2 ξ `{Hwf : !SchedulerWf ξ} :
    exec (sch_ctx_lift K ξ) (K e1, σ1) (e2, σ2) > 0 → ∃ e2', e2 = K e2'.
  Proof.
    revert e1 σ1 e2 σ2.
    induction ξ as [|f ξ IH].
    - intros e1 σ1 e2 σ2. rewrite exec_nil. intros [=]%dret_pos. eauto.
    - intros e1 σ1 e2 σ2.
      inversion Hwf; simplify_eq.
      rewrite sch_ctx_lift_cons exec_cons.
      rewrite exec_fn_unfold sch_fn_ctx_lift_lookup /=.
      destruct (f !! _) as [[]|] eqn:Heq.
      + intros [[e3 σ3] [Hexec Hs]]%dbind_pos_support.
        destruct (to_val e1) as [v|] eqn:Heq'.
        { rewrite scheduler_fn_val in Heq; [simplify_eq|eauto].  }
        eapply fill_step_inv in Hs as [e3' [? ?]]; [|done].
        simplify_eq. by eapply IH.
      + intros [[e3 σ3] [Hexec [σ [? ?]]%dmap_pos]]%dbind_pos_support.
        simplify_eq. by eapply IH.
      + rewrite dbind_dzero_pmf. lra.
  Qed.

  Lemma exec_ctx_lift_fill K `{!LanguageCtx K} e1 σ1 ξ `{!SchedulerWf ξ}:
    exec (sch_ctx_lift K ξ) (K e1, σ1) = dmap (fill_lift K) (exec ξ (e1, σ1)).
  Proof.
    apply dmap_rearrange; [apply _| |].
    - intros [e2 σ2] [? ?]%exec_ctx_lift_pmf_pos; [|done|done].
      eexists (_,_). by simplify_eq.
    - intros []. by apply exec_ctx_lift_pmf.
  Qed.

  Lemma Rcoupl_exec_ctx_lift K `{!LanguageCtx K} e1 σ1 ρ R ξ ξ' `{!SchedulerWf ξ}:
    to_val e1 = None →
    Rcoupl (exec ξ (e1, σ1)) (exec ξ' ρ) R →
    Rcoupl (exec (sch_ctx_lift K ξ) (K e1, σ1)) (exec ξ' ρ) (λ '(e2, σ2) ρ', ∃ e2', e2 = K e2' ∧ R (e2', σ2) ρ').
  Proof.
    intros Hv Hcpl.
    rewrite exec_ctx_lift_fill //.
    rewrite -(dret_id_right (exec ξ' ρ)).
    rewrite /dmap.
    eapply Rcoupl_bind; [|done].
    intros [e2' σ2] ρ' HR =>/=.
    apply Rcoupl_ret; eauto.
  Qed.

End ctx_lifting.
