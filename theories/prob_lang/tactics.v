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
  match type of H with
  | context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  | _ => fail "expected hypothesis to include a 'match'"
  end.

Tactic Notation "case_match" "in" ident(H) :=
  let Hf := fresh in case_match in H eqn:Hf.

Tactic Notation "case_bool_decide" "in" ident(H) "as" ident(Hd) :=
  match type of H with
  | context [@bool_decide ?P ?dec] =>
      destruct_decide (@bool_decide_reflect P dec) as Hd
  | _ => fail "expected hypothesis to include a 'bool_decide _'"
  end.
Tactic Notation "case_bool_decide" "in" ident(H) :=
  let Hfr := fresh in case_bool_decide in H as Hf.

Tactic Notation "case_bool_decide_and_destruct" "in" ident(H) :=
  let Hf := fresh in
  case_bool_decide in H as Hf;
  destruct_and? Hf;
  simplify_eq.

(** A relational definition of the support of [head_step] to make it possible to
    do inversion and prove reducibility easier c.f. lemma below *)
Inductive head_step_rel : expr → state → expr → state → Prop :=
| RecS f x e σ :
  head_step_rel (Rec f x e) σ (Val $ RecV f x e) σ
| PairS v1 v2 σ :
  head_step_rel (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ
| InjLS v σ :
  head_step_rel (InjL $ Val v) σ (Val $ InjLV v) σ
| InjRS v σ :
  head_step_rel (InjR $ Val v) σ (Val $ InjRV v) σ
| BetaS f x e1 v2 e' σ :
  e' = subst' x v2 (subst' f (RecV f x e1) e1) →
  head_step_rel (App (Val $ RecV f x e1) (Val v2)) σ e' σ
| UnOpS op v v' σ :
  un_op_eval op v = Some v' →
  head_step_rel (UnOp op (Val v)) σ (Val v') σ
| BinOpS op v1 v2 v' σ :
  bin_op_eval op v1 v2 = Some v' →
  head_step_rel (BinOp op (Val v1) (Val v2)) σ (Val v') σ
| IfTrueS e1 e2 σ :
  head_step_rel (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ
| IfFalseS e1 e2 σ :
  head_step_rel (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ
| FstS v1 v2 σ :
  head_step_rel (Fst (Val $ PairV v1 v2)) σ (Val v1) σ
| SndS v1 v2 σ :
  head_step_rel (Snd (Val $ PairV v1 v2)) σ (Val v2) σ
| CaseLS v e1 e2 σ :
  head_step_rel (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ
| CaseRS v e1 e2 σ :
  head_step_rel (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ
| AllocS v σ l :
  l = fresh_loc σ.(heap) →
  head_step_rel (Alloc (Val v)) σ
    (Val $ LitV $ LitLoc l) (state_upd_heap <[l:=v]> σ)
| LoadS l v σ :
  σ.(heap) !! l = Some v →
  head_step_rel (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ
| StoreS l v w σ :
  σ.(heap) !! l = Some v →
  head_step_rel (Store (Val $ LitV $ LitLoc l) (Val w)) σ
    (Val $ LitV LitUnit) (state_upd_heap <[l:=w]> σ)
| AllocTapeS σ l :
  l = fresh_loc σ.(tapes) →
  head_step_rel AllocTape σ
    (Val $ LitV $ LitLbl l) (state_upd_tapes <[l:=[]]> σ)
| FlipS l b bs σ :
  σ.(tapes) !! l = Some (b :: bs) →
  head_step_rel (Flip (Val (LitV (LitLbl l)))) σ (Val $ LitV $ LitBool b) (state_upd_tapes <[l:=bs]> σ)
| FlipEmptyS l b σ :
  σ.(tapes) !! l = Some [] →
  head_step_rel (Flip (Val (LitV (LitLbl l)))) σ (Val $ LitV $ LitBool b) σ.

Create HintDb head_step.
Global Hint Constructors head_step_rel : head_step.

(** A computational/destructing version of [inv_head_step] - only to be used for
    the lemma below *)
Local Ltac inv_head_step' :=
  repeat
    match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : is_Some (_ !! _) |- _ => destruct H
    | H : @pmf _ _ _ (head_step ?e _) _ > 0  |- _ =>
        try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
        rewrite /pmf /= in H;
        repeat (case_bool_decide_and_destruct in H || case_match in H);
        try (lra || done)
    end.

Lemma head_step_support_equiv_rel e1 e2 σ1 σ2 :
  head_step e1 σ1 (e2, σ2) > 0 ↔ head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intros Hstep.
    destruct e1; inv_head_step'; eauto with head_step.
    + (* semi-bogus case because of a too eager [case_bool_decide] in [inv_head_step] *)
      rewrite {2}H9. by eapply FlipS.
  - inversion 1;
      rewrite /pmf /= /head_step_pmf //; simplify_map_eq;
      rewrite ?bool_decide_eq_true_2 //; try lra.
Qed.

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
Ltac inv_head_step :=
  repeat
    match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : is_Some (_ !! _) |- _ => destruct H
    | H : @pmf _ _ _ (head_step _ _) _ > 0  |- _ => apply head_step_support_equiv_rel in H
    | H : @pmf _ _ _ (head_step _ _) _ = 1  |- _ => apply head_step_support_eq_1 in H
    | H : head_step_rel ?e _ _ _ |- _ =>
        try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
        inversion H; subst; clear H
    end.

Global Hint Extern 0 (head_reducible _ _) =>
         eexists (_, _); simpl; eapply head_step_support_equiv_rel : head_step.
Global Hint Extern 1 (head_step _ _ _ > 0) =>
         eapply head_step_support_equiv_rel; econstructor : head_step.
