From Stdlib Require Import Reals Psatz.
From stdpp Require Import fin_maps.
From iris.proofmode Require Import environments proofmode.
From clutch.prob Require Import distribution.
From clutch.common Require Import ectx_language.
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
  | AllocN ?e (Val ?v) => go (AllocNLCtx v :: K) e
  | AllocN ?e1 ?e2 => go (AllocNRCtx e1 :: K) e2
  | Load ?e => go (LoadCtx :: K) e
  | Store ?e (Val ?v) => go (StoreLCtx v :: K) e
  | Store ?e1 ?e2 => go (StoreRCtx e1 :: K) e2
  | AllocTape ?e => go (AllocTapeCtx :: K) e
  | AllocTapeLaplace ?e1 (Val ?v2) (Val ?v3) => go (AllocTapeLaplaceNumCtx v2 v3 :: K) e1
  | AllocTapeLaplace ?e1 ?e2 (Val ?v3) => go (AllocTapeLaplaceDenCtx e1 v3 :: K) e2
  | AllocTapeLaplace ?e1 ?e2 ?e3 => go (AllocTapeLaplaceMeanCtx e1 e2 :: K) e3
  | Rand ?e (Val ?v) => go (RandLCtx v :: K) e
  | Rand ?e1 ?e2 => go (RandRCtx e1 :: K) e2
  | Laplace ?e1 (Val ?v2) (Val ?v3) (Val ?v4) => go (LaplaceNumCtx v2 v3 v4 :: K) e1
  | Laplace ?e1 ?e2 (Val ?v3) (Val ?v4) => go (LaplaceDenCtx e1 v3 v4 :: K) e2
  | Laplace ?e1 ?e2 ?e3 (Val ?v4) => go (LaplaceMeanCtx e1 e2 v4 :: K) e3
  | Laplace ?e1 ?e2 ?e3 ?e4 => go (LaplaceTapeCtx e1 e2 e3 :: K) e4
  | Tick ?e => go (TickCtx :: K) e
  end in go (@nil ectx_item) e.

Local Open Scope R.

Lemma head_step_support_eq e1 e2 σ1 σ2 r :
  r > 0 → head_step e1 σ1 (e2, σ2) = r → head_step_rel e1 σ1 e2 σ2.
Proof. intros ? <-. by eapply head_step_support_equiv_rel. Qed.

Lemma head_step_support_eq_1 e1 e2 σ1 σ2 :
  head_step e1 σ1 (e2, σ2) = 1 → head_step_rel e1 σ1 e2 σ2.
Proof. eapply head_step_support_eq; lra. Qed.

Lemma head_reducible_laplace (num den mean num' den' mean' : Z) α σ1 xs :
  tapes_laplace σ1 !! α = Some (Tape_Laplace num' den' mean' xs) →
  head_reducible (Laplace (Val $ LitV $ LitInt num) (Val $ LitV $ LitInt den) (Val $ LitV $ LitInt mean) (Val $ LitV $ LitLbl α)) σ1.
Proof.
  intros hh.
  destruct (tapes_laplace σ1 !! α) eqn:hα.
  2: done.
  destruct (decide (num = num' ∧ den = den' ∧ mean = mean')), xs ; eexists ; eapply head_step_support_equiv_rel.
  - eapply LaplaceTapeEmptyS. all: intuition simplify_eq ; try done.
  - eapply LaplaceTapeConsS. all: intuition simplify_eq ; try done.
  - eapply LaplaceTapeOtherS. 2: apply n. all: intuition simplify_eq ; try done.
  - eapply LaplaceTapeOtherS. 2: apply n. all: intuition simplify_eq ; try done.
Qed.

Global Hint Extern 1
  (head_step_rel (Laplace (Val (LitV _)) (Val (LitV _)) (Val (LitV _)) (Val (LitV LitUnit))) _ _ _) =>
         (eapply (LaplaceNoTapeS _ _ _ _ _) ; inv_distr ; intuition simplify_eq ; eauto)
 : head_step.


(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
    [head_step]. The tactic will discharge head-reductions starting from values,
    and simplifies hypothesis related to conversions from and to values, and
    finite map operations. This tactic is slightly ad-hoc and tuned for proving
    our lifting lemmas. *)

Global Hint Extern 0 (head_reducible (Laplace _ _ _ _) _) =>
         eapply head_reducible_laplace : head_step.

Global Hint Extern 0 (head_reducible _ _) =>
         eexists (_, _); eapply head_step_support_equiv_rel : head_step.
Global Hint Extern 1 (head_step _ _ _ > 0) =>
         eapply head_step_support_equiv_rel; econstructor : head_step.

Global Hint Extern 2 (head_reducible _ _) =>
         by eauto with head_step : typeclass_instances.

Ltac solve_step :=
  simpl;
  match goal with
  | |- (prim_step _ _).(pmf) _ = 1%R  =>
      rewrite head_prim_step_eq /= ;
        simplify_map_eq ; solve_distr
  | |- (head_step _ _).(pmf) _ = 1%R  => simplify_map_eq; solve_distr
  | |- (head_step _ _).(pmf) _ > 0%R  => eauto with head_step
  end.

Ltac solve_red :=
  match goal with
  | |- (environments.envs_entails _ ( ⌜ _ ⌝ ∗ _)) =>
      iSplitR ; [ by (iPureIntro ; solve_red) | ]
  | |- (environments.envs_entails _ ( _ ∗ ⌜ _ ⌝)) =>
      iSplitL ; [ by (iPureIntro ; solve_red) | ]
  | |- reducible ((fill _ _), _) =>
      apply reducible_fill ; solve_red
  | |- reducible _ =>
      apply head_prim_reducible ; solve_red
  | |- (head_reducible _ _) =>
      by eauto with head_step
  end.
