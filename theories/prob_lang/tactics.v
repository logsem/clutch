From Coq Require Import Reals Psatz.
From stdpp Require Import fin_maps.
From self.prob Require Import distribution.
From self.prob_lang Require Export lang.
From iris.prelude Require Import options.
Import prob_lang.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
(* Ltac reshape_expr e tac := *)
(*   (* Note that the current context is spread into a list of fully-constructed *)
(*      items [K], and a list of pairs of values [vs] (prophecy identifier and *)
(*      resolution value) that is only non-empty if a [ResolveLCtx] item (maybe *)
(*      having several levels) is in the process of being constructed. Note that *)
(*      a fully-constructed item is inserted into [K] by calling [add_item], and *)
(*      that is only the case when a non-[ResolveLCtx] item is built. When [vs] *)
(*      is non-empty, [add_item] also wraps the item under several [ResolveLCtx] *)
(*      constructors: one for each pair in [vs]. *) *)
(*   let rec go K vs e := *)
(*     match e with *)
(*     | _                               => lazymatch vs with [] => tac K e | _ => fail end *)
(*     | App ?e (Val ?v)                 => add_item (AppLCtx v) vs K e *)
(*     | App ?e1 ?e2                     => add_item (AppRCtx e1) vs K e2 *)
(*     | UnOp ?op ?e                     => add_item (UnOpCtx op) vs K e *)
(*     | BinOp ?op ?e (Val ?v)           => add_item (BinOpLCtx op v) vs K e *)
(*     | BinOp ?op ?e1 ?e2               => add_item (BinOpRCtx op e1) vs K e2 *)
(*     | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) vs K e0 *)
(*     | Pair ?e (Val ?v)                => add_item (PairLCtx v) vs K e *)
(*     | Pair ?e1 ?e2                    => add_item (PairRCtx e1) vs K e2 *)
(*     | Fst ?e                          => add_item FstCtx vs K e *)
(*     | Snd ?e                          => add_item SndCtx vs K e *)
(*     | InjL ?e                         => add_item InjLCtx vs K e *)
(*     | InjR ?e                         => add_item InjRCtx vs K e *)
(*     | Case ?e0 ?e1 ?e2                => add_item (CaseCtx e1 e2) vs K e0 *)
(*     | AllocN ?e (Val ?v)              => add_item (AllocNLCtx v) vs K e *)
(*     | AllocN ?e1 ?e2                  => add_item (AllocNRCtx e1) vs K e2 *)
(*     | Free ?e                         => add_item FreeCtx vs K e *)
(*     | Load ?e                         => add_item LoadCtx vs K e *)
(*     | Store ?e (Val ?v)               => add_item (StoreLCtx v) vs K e *)
(*     | Store ?e1 ?e2                   => add_item (StoreRCtx e1) vs K e2 *)
(*     | Xchg ?e (Val ?v)                => add_item (XchgLCtx v) vs K e *)
(*     | Xchg ?e1 ?e2                    => add_item (XchgRCtx e1) vs K e2 *)
(*     | CmpXchg ?e0 (Val ?v1) (Val ?v2) => add_item (CmpXchgLCtx v1 v2) vs K e0 *)
(*     | CmpXchg ?e0 ?e1 (Val ?v2)       => add_item (CmpXchgMCtx e0 v2) vs K e1 *)
(*     | CmpXchg ?e0 ?e1 ?e2             => add_item (CmpXchgRCtx e0 e1) vs K e2 *)
(*     | FAA ?e (Val ?v)                 => add_item (FaaLCtx v) vs K e *)
(*     | FAA ?e1 ?e2                     => add_item (FaaRCtx e1) vs K e2 *)
(*     | Resolve ?ex (Val ?v1) (Val ?v2) => go K ((v1,v2) :: vs) ex *)
(*     | Resolve ?ex ?e1 (Val ?v2)       => add_item (ResolveMCtx ex v2) vs K e1 *)
(*     | Resolve ?ex ?e1 ?e2             => add_item (ResolveRCtx ex e1) vs K e2 *)
(*     end *)
(*   with add_item Ki vs K e := *)
(*     lazymatch vs with *)
(*     | []               => go (Ki :: K) (@nil (val * val)) e *)
(*     | (?v1,?v2) :: ?vs => add_item (ResolveLCtx Ki v1 v2) vs K e *)
(*     end *)
(*   in *)
(*   go (@nil ectx_item) (@nil (val * val)) e. *)

Local Open Scope R.

(* TODO: upstream some of these to stdpp *)
Tactic Notation "case_match" "in" ident(H) "eqn" ":" ident(Hd) :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x eqn:Hd
  end.

Tactic Notation "case_match" "in" ident(H) :=
  let Hf := fresh in case_match in H eqn:Hf.

Tactic Notation "case_bool_decide" "in" ident(H) "as" ident(Hd) :=
  match goal with
  | H : context [@bool_decide ?P ?dec] |- _ =>
    destruct_decide (@bool_decide_reflect P dec) as Hd
  end.
Tactic Notation "case_bool_decide" "in" ident(H) :=
  let Hfr := fresh in case_bool_decide in H as Hf.

Tactic Notation "case_bool_decide_and_destruct" "in" ident(H) :=
  let Hf := fresh in
  case_bool_decide in H as Hf;
  destruct_and? Hf;
  simplify_eq.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat
    match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : @pmf _ _ _ (head_step ?e _) _ > 0  |- _ =>
        try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
        rewrite /pmf /= in H;
        repeat (case_bool_decide_and_destruct in H || case_match in H);
        (lra || done)
    end.

Create HintDb head_step.
Global Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : head_step.
Global Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : head_step.
