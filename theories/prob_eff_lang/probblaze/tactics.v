From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import  na_invariants.
From iris.algebra Require Import agree excl auth frac excl_auth.
From iris.algebra.lib Require Import dfrac_agree.
From clutch Require Import stdpp_ext.
From clutch.prob_eff_lang.probblaze Require Import logic primitive_laws proofmode
  spec_rules spec_ra 
  class_instances.

Module Export Tactics.

Tactic Notation "foldkont" ident(k) open_constr(kctx) :=
    match goal with
    | |- context[KontV ?kont] =>
        unify kont kctx ; set (k := KontV kont)
    end.

  Tactic Notation "foldkont" ident(k) := foldkont k _.

  Tactic Notation "foldkont" := let k := fresh "kont" in foldkont k.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
  match e with
  | _ => tac K e
  | App ?e (Val ?v) => go (K ++ [AppLCtx v]) e
  | App ?e1 ?e2 => go (K ++ [AppRCtx e1]) e2
  | UnOp ?op ?e => go (K ++ [UnOpCtx op]) e
  | BinOp ?op ?e (Val ?v) => go (K ++ [BinOpLCtx op v]) e
  | BinOp ?op ?e1 ?e2 => go (K ++ [BinOpRCtx op e1]) e2
  | If ?e0 ?e1 ?e2 => go (K ++ [IfCtx e1 e2]) e0
  | Pair ?e (Val ?v) => go (K ++ [PairLCtx v]) e
  | Pair ?e1 ?e2 => go (K ++ [PairRCtx e1]) e2
  | Fst ?e => go (K ++ [FstCtx]) e
  | Snd ?e => go (K ++ [SndCtx]) e
  | InjL ?e => go (K ++ [InjLCtx]) e
  | InjR ?e => go (K ++ [InjRCtx]) e
  | Case ?e0 ?e1 ?e2 => go (K ++ [CaseCtx e1 e2]) e0
  | AllocN ?e (Val ?v) => go (K ++ [AllocNLCtx v]) e
  | AllocN ?e1 ?e2 => go (K ++ [AllocNRCtx e1]) e2
  | Load ?e => go (K ++ [LoadCtx]) e
  | Store ?e (Val ?v) => go (K ++ [StoreLCtx v]) e
  | Store ?e1 ?e2 => go (K ++ [StoreRCtx e1]) e2
  | AllocTape ?e => go (K ++ [AllocTapeCtx]) e
  | Rand ?e (Val ?v) => go (K ++ [RandLCtx v]) e
  | Rand ?e1 ?e2 => go (K ++ [RandRCtx e1]) e2
  end in go (@nil syntax.frame) e.

  
End Tactics.
