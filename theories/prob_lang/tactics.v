From Coq Require Import Reals Psatz.
From stdpp Require Import fin_maps.
From clutch.prob Require Import distribution.
From clutch.program_logic Require Import ectx_language.
From clutch.prob_lang Require Import lang.
From iris.prelude Require Import options.
Import prob_lang.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
  match e with
  | _ => tac K e
  | App ?e (Val ?v) => go (AppLCtx v :: K) e
  | App ?e1 ?e2 => go (AppRCtx e1 :: K) e2
  | UnOp ?op ?e => go (UnOpCtx op :: K) e
  | BinOp ?op ?e (Val ?v) => go (BinOpLCtx op v :: K) e
  | BinOp ?op ?e1 ?e2 => go (BinOpRCtx op e1 :: K) e2
  | If ?e0 ?e1 ?e2 => go (IfCtx e1 e2 :: K) e0
  | Pair ?e (Val ?v) => go (PairLCtx v :: K) e
  | Pair ?e1 ?e2 => go (PairRCtx e1 :: K) e2
  | Fst ?e => go (FstCtx :: K) e
  | Snd ?e => go (SndCtx :: K) e
  | InjL ?e => go (InjLCtx :: K) e
  | InjR ?e => go (InjRCtx :: K) e
  | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0
  | Alloc ?e => go (AllocCtx :: K) e
  | Load ?e => go (LoadCtx :: K) e
  | Store ?e (Val ?v) => go (StoreLCtx v :: K) e
  | Store ?e1 ?e2 => go (StoreRCtx e1 :: K) e2
  | AllocTape ?e => go (AllocTapeCtx :: K) e
  | Rand ?e (Val ?v) => go (RandLCtx v :: K) e
  | Rand ?e1 ?e2 => go (RandRCtx e1 :: K) e2
  end in go (@nil ectx_item) e.

Local Open Scope R.

Lemma head_step_support_eq e1 e2 σ1 σ2 r :
  r > 0 → head_step e1 σ1 (e2, σ2) = r → head_step_rel e1 σ1 e2 σ2.
Proof. intros ? <-. by eapply head_step_support_equiv_rel. Qed.

Lemma head_step_support_eq_1 e1 e2 σ1 σ2 :
  head_step e1 σ1 (e2, σ2) = 1 → head_step_rel e1 σ1 e2 σ2.
Proof. eapply head_step_support_eq; lra. Qed.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
    [head_step]. The tactic will discharge head-reductions starting from values,
    and simplifies hypothesis related to conversions from and to values, and
    finite map operations. This tactic is slightly ad-hoc and tuned for proving
    our lifting lemmas. *)

Global Hint Extern 0 (head_reducible _ _) =>
         eexists (_, _); eapply head_step_support_equiv_rel : head_step.
Global Hint Extern 1 (head_step _ _ _ > 0) =>
         eapply head_step_support_equiv_rel; econstructor : head_step.

Ltac solve_step :=
  simpl;
  match goal with
  | |- (prim_step _ _).(pmf) _ = 1%R  =>
      rewrite head_prim_step_eq /=;
        [simplify_map_eq; solve_distr|eauto with head_step]
  | |- (head_step _ _).(pmf) _ = 1%R  => simplify_map_eq; solve_distr
  | |- (head_step _ _).(pmf) _ > 0%R  => eauto with head_step
  end.
