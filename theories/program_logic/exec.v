From Coq Require Import Reals Psatz.
From Coquelicot Require Import Rcomplements Rbar Series Lim_seq Hierarchy.
From stdpp Require Import relations fin_maps functions.
From self.prelude Require Import classical.
From self.program_logic Require Export language.
From self.prob Require Export distribution couplings.

(** Distribution for [n]-step partial evaluation *)
Section exec.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.

  Definition exec (n : nat) ρ : distr (cfg Λ) := iterM n (λ '(e, σ), prim_step e σ) ρ.

  Lemma exec_O ρ : exec 0 ρ = dret ρ.
  Proof. done. Qed.

  Lemma exec_Sn e σ n : exec (S n) (e, σ) = prim_step e σ ≫= exec n.
  Proof. done. Qed.

  Lemma exec_plus e σ n m : exec (n + m) (e, σ) = exec n (e, σ) ≫= exec m.
  Proof. rewrite /exec iterM_plus //.  Qed.

  Lemma exec_1 : exec 1 = λ '(e, σ), prim_step e σ.
  Proof.
    extensionality ρ; destruct ρ as [e σ].
    rewrite exec_Sn /exec /= dret_id_right //.
  Qed.

  Lemma exec_Sn_r e σ n : exec (S n) (e, σ) = exec n (e, σ) ≫= (λ '(e, σ), prim_step e σ).
  Proof.
    assert (S n = n + 1)%nat as -> by lia.
    rewrite exec_plus exec_1 //.
  Qed.

  Lemma exec_det_step n ρ e1 e2 σ1 σ2 :
    prim_step e1 σ1 (e2, σ2) = 1 →
    exec n ρ (e1, σ1) = 1 →
    exec (S n) ρ (e2, σ2) = 1.
  Proof.
    destruct ρ as [e0 σ0].
    rewrite exec_Sn_r.
    intros ? ->%pmf_1_eq_dret.
    rewrite dret_id_left //.
  Qed.

  Lemma exec_det_step_ctx K `{!LanguageCtx K} n ρ e1 e2 σ1 σ2 :
    prim_step e1 σ1 (e2, σ2) = 1 →
    exec n ρ (K e1, σ1) = 1 →
    exec (S n) ρ (K e2, σ2) = 1.
  Proof.
    intros. eapply exec_det_step; [|done].
    rewrite -fill_step_prob //.
    eapply (val_stuck _ σ1 (e2, σ2)). lra.
  Qed.

  Lemma exec_PureExec_ctx K `{!LanguageCtx K} (P : Prop) m n ρ e e' σ :
    P →
    PureExec P n e e' →
    exec m ρ (K e, σ) = 1 →
    exec (m + n) ρ (K e', σ) = 1.
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

End exec.

Global Arguments exec {_} _ _ : simpl never.

(** Distribution for evaluation ending in a value in less than [n]-step *)
Section prim_exec.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.

  Fixpoint prim_exec (ρ : cfg Λ) (n : nat) {struct n} : distr (cfg Λ) :=
    match to_val ρ.1, n with
      | Some v, _ => dret ρ
      | None, 0 => dzero
      | None, S n => dbind (λ ρ', prim_exec ρ' n) (prim_step ρ.1 ρ.2)
    end.

  Lemma prim_exec_rw (ρ : cfg Λ) (n : nat) :
    prim_exec ρ n =
      match to_val ρ.1, n with
      | Some v, _ => dret ρ
      | None, 0 => dzero
      | None, S n => dbind (λ ρ', prim_exec ρ' n) (prim_step ρ.1 ρ.2)
      end.
  Proof. by destruct n. Qed.

  Lemma prim_exec_is_val e σ n :
    is_Some (to_val e) → prim_exec (e, σ) n = dret (e, σ).
  Proof. destruct n; simpl; by intros [? ->]. Qed.

  Definition prim_step_or_val (ρ : cfg Λ) : distr (cfg Λ) :=
    match to_val ρ.1 with
      | Some v => dret ρ
      | None => prim_step ρ.1 ρ.2
    end.

  Lemma prim_exec_Sn (ρ : cfg Λ) (n: nat) :
    prim_exec ρ (S n) = dbind (λ ρ', prim_exec ρ' n) (prim_step_or_val ρ).
  Proof.
    rewrite /prim_step_or_val /=. destruct ρ as [e σ]. simpl.
    destruct (to_val e) eqn:Hv=>/=; [|done].
    rewrite dret_id_left prim_exec_is_val //.
  Qed.

End prim_exec.

(** Limit of [prim_exec]  *)
Section prim_exec_lim.
  Context {Λ : language}.
  Implicit Types ρ : cfg Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.

  Program Definition lim_prim_exec (ρ : cfg Λ) : distr (cfg Λ):= MkDistr (λ ρ', Lim_seq (λ n, prim_exec ρ n ρ')) _ _ _.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.


End prim_exec_lim.
