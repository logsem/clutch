(** Minimal tactic support for gen_prob_lang: the [head_step] hint database and
    [solve_red], ported from [prob_lang/tactics.v] (the generic, non-Laplace
    parts). [inv_head_step] is already provided by [lang.v]. *)
From Stdlib Require Import Reals Psatz.
From clutch.common Require Import ectx_language.
From clutch.prob Require Import distribution.
From clutch.gen_prob_lang Require Import lang.
From iris.proofmode Require Import environments proofmode.
From iris.prelude Require Import options.

#[local] Open Scope R.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds.  Ported from
[prob_lang/tactics.v] with the heap-deref context renamed to [Deref] and the generic
[Sample]/[AllocSampleTape] contexts replacing the rand/laplace ones. *)
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
  | Deref ?e => go (DerefCtx :: K) e
  | Store ?e (Val ?v) => go (StoreLCtx v :: K) e
  | Store ?e1 ?e2 => go (StoreRCtx e1 :: K) e2
  | Sample ?i ?e1 (Val ?v2) => go (SampleParamsCtx i v2 :: K) e1
  | Sample ?i ?e1 ?e2 => go (SampleTapeCtx i e1 :: K) e2
  | AllocSampleTape ?i ?e1 => go (AllocSampleTapeCtx i :: K) e1
  | Tick ?e => go (TickCtx :: K) e
  end in go (@nil ectx_item) e.

(* Re-export the head_step_rel constructors into the [head_step] db (the in-file
   hint was section-local), and the generic reducibility bridges. *)
Global Hint Constructors head_step_rel : head_step.

Global Hint Extern 0 (head_reducible _ _) =>
  eexists (_, _); eapply head_step_support_equiv_rel : head_step.
Global Hint Extern 1 (head_step _ _ _ > 0) =>
  eapply head_step_support_equiv_rel; econstructor : head_step.
Global Hint Extern 2 (head_reducible _ _) =>
  by eauto with head_step : typeclass_instances.

(* [inv_head_step]/[solve_distr] are defined inside [lang.v]'s [Section semantics]
   for the metatheory proofs, but do not survive section close + [Export]; re-export
   them here (the bodies are S-independent). *)
Ltac inv_head_step :=
  repeat
    match goal with
    | H : context [@bool_decide ?P ?dec] |- _ =>
        try (rewrite bool_decide_eq_true_2 in H; [|done]);
        try (rewrite bool_decide_eq_false_2 in H; [|done]);
        destruct_decide (@bool_decide_reflect P dec); simplify_eq
    | _ => progress simplify_map_eq; simpl in *; inv_distr; repeat case_match; inv_distr
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : is_Some (_ !! _) |- _ => destruct H
    end.

Ltac solve_distr :=
  repeat
    match goal with
    | |- (dret _).(pmf) _ > 0 => rewrite dret_1_1 //; lra
    | |- (dret ?x).(pmf) ?x = 1 => by apply dret_1_1
    | |- (dbind _ _).(pmf) _ > 0 => apply dbind_pos; eexists; split
    | |- (dmap _ _).(pmf) _ > 0 =>
        apply dmap_pos; eexists; (split; [done|]); try done
    | |- (dunifP _).(pmf) _ > 0 => apply dunifP_pos
    | |- (dunifv _ _).(pmf) _ > 0 => apply dunifv_pos
    | |- (d_proj_Some _).(pmf) _ > 0 => rewrite d_proj_Some_pos
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
