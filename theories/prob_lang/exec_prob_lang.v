From Coq Require Import Reals Psatz.
From stdpp Require Import fin_maps.
From self.prelude Require Import stdpp_ext.
From self.program_logic Require Export exec.
From self.prob_lang Require Export lang.

Local Open Scope R.

Definition valid_double_state_step '(σ1, σ1') (α α' : loc) '(σ2, σ2') : Prop :=
    (* heaps are the same *)
    σ2.(heap) = σ1.(heap) ∧
    σ2'.(heap) = σ1'.(heap) ∧
   (* but we add the same bit to the [α] and [α'] tapes *)
    ∃ b, σ2.(tapes) = <[α := σ1.(tapes) !!! α ++ [b]]>σ1.(tapes) ∧
         σ2'.(tapes) = <[α' := σ1'.(tapes) !!! α' ++ [b]]>σ1'.(tapes).

Global Instance valid_double_state_step_dec σs α α' σs' :
  Decision (valid_double_state_step σs α α' σs').
Proof. destruct σs, σs'. apply _. Qed.

Definition double_state_step_pmf (σs1 : state * state) (α α' : loc) (σs2 : state * state) : R :=
  if bool_decide (valid_double_state_step σs1 α α' σs2) then 0.5 else 0.

Program Definition double_state_step (σs1 : state * state) (α α' : loc) : distr (state * state) :=
  MkDistr (double_state_step_pmf σs1 α α') _ _ _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Definition double_step (ρs : cfg * cfg) (α1 α2 : loc) : distr (cfg * cfg) :=
  let '((e1, σ1), (e2, σ2)) := ρs in
  dmap (λ '(σ1', σ2'),  ((e1, σ1'), (e2, σ2'))) (double_state_step (σ1, σ2) α1 α2).

Lemma Rcoupl_state_step σ1 σ2 α1 α2 :
  Rcoupl
    (state_step σ1 α1)
    (state_step σ2 α2)
    (λ σ1' σ2', valid_double_state_step (σ1, σ2) α1 α2 (σ1', σ2')).
Proof.
  exists (double_state_step (σ1, σ2) α1 α2). split.
  - split.
    + eapply distr_ext. intros σ.
      rewrite lmarg_pmf /pmf /= /double_state_step_pmf /state_step_pmf.
      case_bool_decide as Heq.
      * destruct Heq as (? & b & H).
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton
                     (state_upd_tapes <[α2 := σ2.(tapes) !!! α2 ++ [b]]> σ2))|].
        intros σ'; simpl.
        symmetry; case_bool_decide as Heq; simplify_eq.
        { rewrite bool_decide_eq_true_2 //; eauto. }
        rewrite bool_decide_eq_false_2 //.
        intros (?&?&?&Htapes &?).
        destruct σ, σ', σ1, σ2; simplify_map_eq.
        apply insert_inv in Htapes. simplify_map_eq.
      * apply SeriesC_0. intros σ'.
        rewrite bool_decide_eq_false_2 //.
        intros (?&?&?&?&?). apply Heq. split_and!; eauto.
    + eapply distr_ext. intros σ.
      rewrite rmarg_pmf /pmf /= /double_state_step_pmf /state_step_pmf.
      case_bool_decide as Heq.
      * destruct Heq as (? & b & H).
        erewrite SeriesC_ext;
          [eapply (SeriesC_singleton
                     (state_upd_tapes <[α1 := σ1.(tapes) !!! α1 ++ [b]]> σ1))|].
        intros σ'; simpl.
        symmetry; case_bool_decide as Heq; simplify_eq.
        { rewrite bool_decide_eq_true_2 //; eauto. }
        rewrite bool_decide_eq_false_2 //.
        intros (?&?&?&?& Htapes).
        destruct σ, σ', σ1, σ2; simplify_map_eq.
        apply insert_inv in Htapes. simplify_map_eq.
      * apply SeriesC_0. intros σ'.
        rewrite bool_decide_eq_false_2 //.
        intros (?&?&?&?&?). apply Heq. split_and!; eauto.
  - intros [ρ1 ρ2]. rewrite /pmf /= /double_state_step_pmf.
    case_bool_decide; eauto. lra.
Qed.

Lemma state_step_sch_coupl e1 e2 α1 α2 σ1 σ2 :
  Rcoupl
    (exec (state_step_sch (e1, σ1) α1) (e1, σ1))
    (exec (state_step_sch (e2, σ2) α2) (e2, σ2))
    (λ '(e1', σ1') '(e2', σ2'),
      e1' = e1 ∧ e2' = e2 ∧ valid_double_state_step (σ1, σ2) α1 α2 (σ1', σ2')).
Proof.
  intros. rewrite 2!exec_state_step_sch.
  apply Rcoupl_strength_l, Rcoupl_state_step.
Qed.

Definition prim_step_sch_sample '(e, σ) α : scheduler_fn prob_lang :=
  {[ (e, (state_upd_tapes <[α := σ.(tapes) !!! α ++ [true]]> σ)) := PRIM;
     (e, (state_upd_tapes <[α := σ.(tapes) !!! α ++ [false]]> σ)) := PRIM ]}.

Definition state_prim_step_sch ρ α : scheduler prob_lang :=
  state_step_sch ρ α ++ [prim_step_sch_sample ρ α].

Lemma state_step_pos σ α σ' :
  state_step σ α σ' > 0 →
  σ' = state_upd_tapes <[α := σ.(tapes) !!! α ++ [true]]> σ ∨
  σ' = state_upd_tapes <[α := σ.(tapes) !!! α ++ [false]]> σ.
Proof.
  rewrite /pmf /= state_step_pmf_eq.
  do 2 (case_bool_decide; eauto). lra.
Qed.

Lemma state_prim_step_sch_wf e σ α :
  TCEq (to_val e) None →
  SchedulerWf (state_prim_step_sch (e, σ) α) (e, σ).
Proof.
  intros Hv. constructor.
  - repeat constructor.
    + simpl. intros ?? [? Hv']. rewrite /state_step_sch_fn lookup_singleton_ne //.
      intros [=<- <-]. by rewrite Hv in Hv'.
    + simpl. intros ?? [? Hv'].
      rewrite /prim_step_sch_sample ?lookup_insert_ne; [done| |];
        intros [=<- <-]; by rewrite Hv in Hv'.
  - eapply nonblock_state; [rewrite lookup_singleton //|done|]; simpl.
    intros σ' [-> | ->]%state_step_pos; eapply nonblock_prim.
    + rewrite lookup_insert //.
    + rewrite lookup_insert_ne ?lookup_insert //.
      intros [= Hσ%insert_inv]. simplify_map_eq.
Qed.

Lemma state_prim_state_coupl α1 α2 e1 e1' e2 σ1 σ2 :
  pure_step e1 e1' →
  Rcoupl
    (exec (state_prim_step_sch (e1, σ1) α1) (e1, σ1))
    (exec (state_step_sch (e2, σ2) α2) (e2, σ2))
    (λ '(e', σ1') '(e2', σ2'),
      e' = e1' ∧ e2' = e2 ∧ valid_double_state_step (σ1, σ2) α1 α2 (σ1', σ2')) .
Proof.
  intros Hpstep.
  rewrite -(dret_id_right (exec (state_step_sch _ _) _)).
  rewrite exec_cons.
  eapply Rcoupl_bind; last first.
  { rewrite -exec_singleton. apply state_step_sch_coupl. }
  intros [? σ1'] [? σ2'] (?&?&?&?& b &?&?); simplify_eq.
  exists (dprod (exec [prim_step_sch_sample (e1, σ1) α1] (e1, σ1')) (dret (e2, σ2'))).
  split.
  { split; rewrite ?lmarg_dprod ?rmarg_dprod //. }
  intros [[] []] [Hexec [=]%dret_pos]%dprod_pos; simplify_eq/=.
  move: Hexec.
  rewrite exec_singleton exec_fn_pmf_unfold.
  destruct b.
  - assert (σ1' = state_upd_tapes <[α1:=tapes σ1 !!! α1 ++ [true]]> σ1) as <-.
    { destruct σ1'. by simplify_map_eq. }
    rewrite lookup_insert /=.
    intros Hs.
    eapply pmf_1_supp_eq in Hs; [|apply Hpstep].
    simplify_eq.
    split_and!; eauto.
  - assert (σ1' = state_upd_tapes <[α1:=tapes σ1 !!! α1 ++ [false]]> σ1) as <-.
    { destruct σ1'. by simplify_map_eq. }
    rewrite lookup_insert_ne /=; last first.
    { intros [=]. destruct σ1', σ1. simplify_map_eq.
      eapply map_eq_iff in H0.
      erewrite 2!(lookup_insert _ α1) in H0.
      simplify_option_eq. }
    rewrite lookup_insert /=.
    intros Hs.
    eapply pmf_1_supp_eq in Hs; [|apply Hpstep].
    simplify_eq.
    split_and!; eauto.
Qed.

Lemma Rcoupl_exec_det_prefix_r ξ ξ1 ξ2 (ρ ρ1 ρ2 : cfg) (S : cfg → cfg → Prop) :
  exec ξ1 ρ1 ρ2 = 1 →
  Rcoupl (exec ξ ρ) (exec ξ2 ρ2) S →
  Rcoupl (exec ξ ρ) (exec (ξ1 ++ ξ2) ρ1) S.
Proof.
  intros Hdet%pmf_1_eq_dret Hcpl.
  replace ξ with ([] ++ ξ); [|done].
  rewrite 2!exec_app.
  eapply (Rcoupl_bind _ _ _ _ (λ ρ' ρ'', ρ' = ρ ∧ ρ'' = ρ2)); last first.
  { rewrite exec_nil Hdet. by eapply Rcoupl_ret. }
  intros ?? [-> ->]. done.
Qed.
