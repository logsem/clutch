(* TODO move into metatheory.v ? *)

From Coq Require Export Reals Psatz.
From clutch.meas_lang Require Import lang ectx_language.
From clutch.prob.monad Require Import giry meas_markov.

Local Open Scope classical_set_scope.

(*
Lemma exec_det_step_ctx K `{!MeasLanguageCtx K} n ρ e1 e2 σ1 σ2 :
  is_det ((e2, σ2) : _ * _) (prim_step (e1, σ1))  →
  pexec n ρ (K e1, σ1) = 1%R →
  pexec (S n) ρ (K e2, σ2) = 1%R.
Proof.
  intros. eapply pexec_det_step; [|done].
  rewrite -fill_step_prob //.
  eapply (val_stuck _ σ1 (e2, σ2)).
  rewrite H. lra.
Qed.

Lemma exec_PureExec_ctx K `{!LanguageCtx K} (P : Prop) m n ρ (e e' : expr) σ :
  P →
  PureExec P n e e' →
  pexec m ρ (K e, σ) = 1 →
  pexec (m + n) ρ (K e', σ) = 1.
Proof.
  move=> HP /(_ HP).
  destruct ρ as [e0 σ0].
  revert e e' m. induction n=> e e' m.
  { rewrite -plus_n_O. by inversion 1. }
  intros (e'' & Hsteps & Hpstep)%nsteps_inv_r Hdet.
  specialize (IHn _ _ m Hsteps Hdet).
  rewrite -plus_n_Sm.
  eapply exec_det_step_ctx; [done| |done].
  apply Hpstep.
Qed.

Lemma stepN_det_step_ctx K `{!LanguageCtx K} n ρ (e1 e2 : expr) σ1 σ2 :
  prim_step e1 σ1 (e2, σ2) = 1%R →
  stepN n ρ (K e1, σ1) = 1%R →
  stepN (S n) ρ (K e2, σ2) = 1%R.
Proof.
  intros.
  rewrite -Nat.add_1_r.
  erewrite (stepN_det_trans n 1); [done|done|].
  rewrite stepN_Sn /=.
  rewrite dret_id_right.
  rewrite -fill_step_prob //.
  eapply (val_stuck _ σ1 (e2, σ2)).
  rewrite H. lra.
Qed.

Lemma stepN_PureExec_ctx K `{!LanguageCtx K} (P : Prop) m n ρ (e e' : expr) σ :
  P →
  PureExec P n e e' →
  stepN m ρ (K e, σ) = 1 →
  stepN (m + n) ρ (K e', σ) = 1.
Proof.
  move=> HP /(_ HP).
  destruct ρ as [e0 σ0].
  revert e e' m. induction n=> e e' m.
  { rewrite -plus_n_O. by inversion 1. }
  intros (e'' & Hsteps & Hpstep)%nsteps_inv_r Hdet.
  specialize (IHn _ _ m Hsteps Hdet).
  rewrite -plus_n_Sm.
  eapply stepN_det_step_ctx; [done| |done].
  apply Hpstep.
Qed.
*)
