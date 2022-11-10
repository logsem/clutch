From Coq Require Import Reals Psatz.
From stdpp Require Export binders strings.
From stdpp Require Import gmap fin_maps.
From iris.algebra Require Export ofe.
From self.prob Require Import distribution.
From self.program_logic Require Export language ectx_language ectxi_language.
From self.prob_lang Require Export locations.
From iris.prelude Require Import options.
From self.prelude Require Import stdpp_ext.

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module prob_lang.

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc) | LitLbl (l : loc).
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp. (* Relations *)

Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  (* Heap *)
  | Alloc (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  (* Probabilistic choice *)
  | AllocTape
  | Flip (e : expr)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Definition tape := list bool.

(** The state: a [loc]-indexed heap of [val]s, and [loc]-indexed tapes of
    booleans. *)
Record state : Type := {
  heap  : gmap loc val;
  tapes : gmap loc tape
}.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance expr_eq_dec : EqDecision expr.
Proof.
  refine (
   fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
     match e1, e2 with
     | Val v, Val v' => cast_if (decide (v = v'))
     | Var x, Var x' => cast_if (decide (x = x'))
     | Rec f x e, Rec f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | App e1 e2, App e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
     | BinOp o e1 e2, BinOp o' e1' e2' =>
        cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
     | If e0 e1 e2, If e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Pair e1 e2, Pair e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Fst e, Fst e' => cast_if (decide (e = e'))
     | Snd e, Snd e' => cast_if (decide (e = e'))
     | InjL e, InjL e' => cast_if (decide (e = e'))
     | InjR e, InjR e' => cast_if (decide (e = e'))
     | Case e0 e1 e2, Case e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Alloc e, Alloc e' => cast_if (decide (e = e'))
     | Load e, Load e' => cast_if (decide (e = e'))
     | Store e1 e2, Store e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | AllocTape, AllocTape => left _
     | Flip e, Flip e' => cast_if (decide (e = e'))
     | _, _ => right _
     end
   with gov (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
     match v1, v2 with
     | LitV l, LitV l' => cast_if (decide (l = l'))
     | RecV f x e, RecV f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | PairV e1 e2, PairV e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | InjLV e, InjLV e' => cast_if (decide (e = e'))
     | InjRV e, InjRV e' => cast_if (decide (e = e'))
     | _, _ => right _
     end
   for go); try (clear go gov; abstract intuition congruence).
Defined.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.
Global Instance state_eq_dec : EqDecision state.
Proof. solve_decision. Defined.

Global Instance base_lit_countable : Countable base_lit.
Proof.
 refine (inj_countable' (λ l, match l with
  | LitInt n => inl (inl n)
  | LitBool b => inl (inr b)
  | LitUnit => inr (inl ())
  | LitLoc l => inr (inr (inr l))
  | LitLbl l => inr (inr (inl l))
  end) (λ l, match l with
  | inl (inl n) => LitInt n
  | inl (inr b) => LitBool b
  | inr (inl ()) => LitUnit
  | inr (inr (inr l)) => LitLoc l
  | inr (inr (inl l)) => LitLbl l
  end) _); by intros [].
Qed.
Global Instance un_op_finite : Countable un_op.
Proof.
 refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 end)
  (λ n, match n with 0 => NegOp | _ => MinusUnOp end) _); by intros [].
Qed.
Global Instance bin_op_countable : Countable bin_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
  | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
  | LeOp => 10 | LtOp => 11 | EqOp => 12
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | _ => EqOp
  end) _); by intros [].
Qed.
Global Instance expr_countable : Countable expr.
Proof.
 set (enc :=
   fix go e :=
     match e with
     | Val v => GenNode 0 [gov v]
     | Var x => GenLeaf (inl (inl x))
     | Rec f x e => GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | App e1 e2 => GenNode 2 [go e1; go e2]
     | UnOp op e => GenNode 3 [GenLeaf (inr (inr (inl op))); go e]
     | BinOp op e1 e2 => GenNode 4 [GenLeaf (inr (inr (inr op))); go e1; go e2]
     | If e0 e1 e2 => GenNode 5 [go e0; go e1; go e2]
     | Pair e1 e2 => GenNode 6 [go e1; go e2]
     | Fst e => GenNode 7 [go e]
     | Snd e => GenNode 8 [go e]
     | InjL e => GenNode 9 [go e]
     | InjR e => GenNode 10 [go e]
     | Case e0 e1 e2 => GenNode 11 [go e0; go e1; go e2]
     | Alloc e => GenNode 12 [go e]
     | Load e => GenNode 13 [go e]
     | Store e1 e2 => GenNode 14 [go e1; go e2]
     | AllocTape => GenNode 15 []
     | Flip e => GenNode 16 [go e]
     end
   with gov v :=
     match v with
     | LitV l => GenLeaf (inr (inl l))
     | RecV f x e =>
        GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
     | InjLV v => GenNode 2 [gov v]
     | InjRV v => GenNode 3 [gov v]
     end
   for go).
 set (dec :=
   fix go e :=
     match e with
     | GenNode 0 [v] => Val (gov v)
     | GenLeaf (inl (inl x)) => Var x
     | GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => Rec f x (go e)
     | GenNode 2 [e1; e2] => App (go e1) (go e2)
     | GenNode 3 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
     | GenNode 4 [GenLeaf (inr (inr (inr op))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 [e0; e1; e2] => If (go e0) (go e1) (go e2)
     | GenNode 6 [e1; e2] => Pair (go e1) (go e2)
     | GenNode 7 [e] => Fst (go e)
     | GenNode 8 [e] => Snd (go e)
     | GenNode 9 [e] => InjL (go e)
     | GenNode 10 [e] => InjR (go e)
     | GenNode 11 [e0; e1; e2] => Case (go e0) (go e1) (go e2)
     | GenNode 12 [e] => Alloc (go e)
     | GenNode 13 [e] => Load (go e)
     | GenNode 14 [e1; e2] => Store (go e1) (go e2)
     | GenNode 15 [] => AllocTape
     | GenNode 16 [e] => Flip (go e)
     | _ => Val $ LitV LitUnit (* dummy *)
     end
   with gov v :=
     match v with
     | GenLeaf (inr (inl l)) => LitV l
     | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => RecV f x (go e)
     | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
     | GenNode 2 [v] => InjLV (gov v)
     | GenNode 3 [v] => InjRV (gov v)
     | _ => LitV LitUnit (* dummy *)
     end
   for go).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
 - destruct e as [v| | | | | | | | | | | | | | | | | ]; simpl; f_equal;
     [exact (gov v)|done..].
 - destruct v; by f_equal.
Qed.
Global Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.
Global Program Instance state_countable : Countable state :=
  {| encode σ := encode (σ.(heap), σ.(tapes));
     decode p := '(h, t) ← decode p; mret {|heap:=h; tapes:=t|} |}.
Next Obligation. intros [h t]. rewrite decode_encode //=. Qed.

Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; tapes := inhabitant |}.
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

(** Evaluation contexts *)
Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (v2 : val)
  | PairRCtx (e1 : expr)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : expr) (e2 : expr)
  | AllocCtx
  | LoadCtx
  | StoreLCtx (v2 : val)
  | StoreRCtx (e1 : expr)
  | FlipCtx.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op v2 => BinOp op e (Val v2)
  | BinOpRCtx op e1 => BinOp op e1 e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx v2 => Pair e (Val v2)
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | AllocCtx => Alloc e
  | LoadCtx => Load e
  | StoreLCtx v2 => Store e (Val v2)
  | StoreRCtx e1 => Store e1 e
  | FlipCtx => Flip e
  end.

Definition decomp_item (e : expr) : option (ectx_item * expr) :=
  match e with
  | App (Val _) (Val _)      => None
  | App e (Val v)            => Some (AppLCtx v, e)
  | App e1 e2                => Some (AppRCtx e1, e2)
  | UnOp _ (Val _)           => None
  | UnOp op e                => Some (UnOpCtx op, e)
  | BinOp _ (Val _) (Val _)  => None
  | BinOp op e (Val v)       => Some (BinOpLCtx op v, e)
  | BinOp op e1 e2           => Some (BinOpRCtx op e1, e2)
  | If (Val _) _ _           => None
  | If e0 e1 e2              => Some (IfCtx e1 e2, e0)
  | Pair (Val _) (Val _)     => None
  | Pair e (Val v)           => Some (PairLCtx v, e)
  | Pair e1 e2               => Some (PairRCtx e1, e2)
  | Fst (Val _)              => None
  | Fst e                    => Some (FstCtx, e)
  | Snd (Val _)              => None
  | Snd e                    => Some (SndCtx, e)
  | InjL (Val _)             => None
  | InjL e                   => Some (InjLCtx, e)
  | InjR (Val _)             => None
  | InjR e                   => Some (InjRCtx, e)
  | Case (Val _) _ _         => None
  | Case e0 e1 e2            => Some (CaseCtx e1 e2, e0)
  | Alloc (Val _)            => None
  | Alloc e                  => Some (AllocCtx, e)
  | Load (Val _)             => None
  | Load e                   => Some (LoadCtx, e)
  | Store (Val _) (Val _)    => None
  | Store e (Val v)          => Some (StoreLCtx v, e)
  | Store e1 e2              => Some (StoreRCtx e1, e2)
  | Flip (Val _)             => None
  | Flip e                   => Some (FlipCtx, e)
  | _                        => None
  end.

(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
  | Alloc e => Alloc (subst x v e)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | AllocTape => AllocTape
  | Flip e => Flip (subst x v e)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => λ x, x end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : base_lit :=
  match op with
  | PlusOp => LitInt (n1 + n2)
  | MinusOp => LitInt (n1 - n2)
  | MultOp => LitInt (n1 * n2)
  | QuotOp => LitInt (n1 `quot` n2)
  | RemOp => LitInt (n1 `rem` n2)
  | AndOp => LitInt (Z.land n1 n2)
  | OrOp => LitInt (Z.lor n1 n2)
  | XorOp => LitInt (Z.lxor n1 n2)
  | ShiftLOp => LitInt (n1 ≪ n2)
  | ShiftROp => LitInt (n1 ≫ n2)
  | LeOp => LitBool (bool_decide (n1 ≤ n2))
  | LtOp => LitBool (bool_decide (n1 < n2))
  | EqOp => LitBool (bool_decide (n1 = n2))
  end%Z.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => Some $ LitV $ bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | _, _ => None
    end.

Definition state_upd_heap (f: gmap loc val → gmap loc val) (σ: state) : state :=
  {| heap := f σ.(heap); tapes := σ.(tapes) |}.
Global Arguments state_upd_heap _ !_ /.

Definition state_upd_tapes (f: gmap loc tape → gmap loc tape) (σ: state) : state :=
  {| heap := σ.(heap); tapes := f σ.(tapes) |}.
Global Arguments state_upd_tapes _ !_ /.

#[local] Open Scope R.

Definition head_step_pmf (e1 : expr) (σ1 : state) '(e2, σ2) : R :=
  match e1, e2 with
  | Rec f x e, Val (RecV f' x' e') =>
      if bool_decide (f = f' ∧ x = x' ∧ e = e' ∧ σ1 = σ2) then 1 else 0
  | Pair (Val v1) (Val v2), Val (PairV v1' v2') =>
      if bool_decide (v1 = v1' ∧ v2 = v2' ∧ σ1 = σ2) then 1 else 0
  | InjL (Val v), (Val (InjLV v')) =>
      if bool_decide (v = v' ∧ σ1 = σ2) then 1 else 0
  | InjR (Val v), (Val (InjRV v')) =>
      if bool_decide (v = v' ∧ σ1 = σ2) then 1 else 0
  | App (Val (RecV f x e1)) (Val v2), e' =>
      if bool_decide (e' = subst' x v2 (subst' f (RecV f x e1) e1) ∧ σ1 = σ2) then 1 else 0
  | UnOp op (Val v), Val v' =>
      if bool_decide (un_op_eval op v = Some v' ∧ σ1 = σ2) then 1 else 0
  | BinOp op (Val v1) (Val v2), Val v' =>
      if bool_decide (bin_op_eval op v1 v2 = Some v' ∧ σ1 = σ2) then 1 else 0
  | If (Val (LitV (LitBool true))) e1 e2, e1' =>
      if bool_decide (e1 = e1' ∧ σ1 = σ2) then 1 else 0
  | If (Val (LitV (LitBool false))) e1 e2, e2' =>
      if bool_decide (e2 = e2' ∧ σ1 = σ2) then 1 else 0
  | Fst (Val (PairV v1 v2)), Val v1' =>
      if bool_decide (v1 = v1' ∧ σ1 = σ2) then 1 else 0
  | Snd (Val (PairV v1 v2)), Val v2' =>
      if bool_decide (v2 = v2' ∧ σ1 = σ2) then 1 else 0
  | Case (Val (InjLV v)) e1 e2, App e1' (Val v') =>
      if bool_decide (v = v' ∧ e1 = e1' ∧ σ1 = σ2) then 1 else 0
  | Case (Val (InjRV v)) e1 e2, App e2' (Val v') =>
      if bool_decide (v = v' ∧ e2 = e2' ∧ σ1 = σ2) then 1 else 0
  | Alloc (Val v), Val (LitV (LitLoc l)) =>
      let ℓ := fresh_loc σ1.(heap) in
      if bool_decide (l = ℓ ∧ σ2 = state_upd_heap <[ℓ:=v]> σ1) then 1 else 0
  | Load (Val (LitV (LitLoc l))), Val v =>
      if bool_decide (σ1.(heap) !! l = Some v ∧ σ1 = σ2) then 1 else 0
  | Store (Val (LitV (LitLoc l))) (Val w), Val (LitV LitUnit) =>
      if bool_decide (is_Some (σ1.(heap) !! l) ∧ σ2 = state_upd_heap <[l:=w]> σ1) then 1 else 0
  | AllocTape, Val (LitV (LitLbl l)) =>
      let ℓ := fresh_loc σ1.(tapes) in
      if bool_decide (l = ℓ ∧ σ2 = state_upd_tapes <[ℓ:=[]]> σ1) then 1 else 0
  | Flip (Val (LitV (LitLbl l))), Val (LitV (LitBool b)) =>
      match σ1.(tapes) !! l with
      | Some (b' :: bs) => (* the tape is non-empty so we consume the first bit *)
          if bool_decide (b = b' ∧ σ2 = state_upd_tapes <[l:=bs]> σ1) then 1 else 0
      | Some [] => (* if nothing is on the tape, we do an actual probabilistic choice *)
          if bool_decide (σ1 = σ2) then 0.5 else 0
      | None => (* unallocated tape *)
          0
      end
  | _, _ => 0
  end.

(* helper tactics to make the [head_step] proofs more tractable *)
#[local] Tactic Notation "solve_ex_seriesC_0" :=
  by (eapply ex_seriesC_ext; [|apply ex_seriesC_0]; intros [[]]).

#[local] Tactic Notation "solve_ex_single" :=
  (* decompose the expression as much as possible *)
  repeat case_match; try solve_ex_seriesC_0; subst;
  (* use that its equivalent to a singleton *)
  eapply ex_seriesC_ext; [|eapply (ex_seriesC_singleton (_, _) 1)];
  (* we can now decompose more to infer which singleton it is *)
  intros []=>/=; case_bool_decide; subst;
  [| repeat (case_bool_decide || case_match); try done; destruct_and!; simplify_eq];
  (* the only case we're really intered in *)
  simplify_eq; rewrite bool_decide_eq_true_2 //.

#[local] Tactic Notation "solve_SeriesC_0" :=
  by (rewrite SeriesC_0; [lra|]; intros [[]]; repeat case_match).

#[local] Tactic Notation "solve_SeriesC_single"  :=
  repeat case_match; try solve_SeriesC_0; subst;
  erewrite SeriesC_ext; [erewrite (SeriesC_singleton (_,_) 1); lra|];
  intros []=>/=; case_bool_decide;
  subst; destruct_and?;
  [|repeat (case_bool_decide || case_match); try done; destruct_and?; simplify_eq; exfalso; auto];
  simplify_eq; rewrite bool_decide_eq_true_2 //.

Program Definition head_step (e1 : expr) (σ1 : state) : distr (expr * state) :=
  MkDistr (head_step_pmf e1 σ1) _ _ _.
Next Obligation. intros ???. rewrite /head_step_pmf. repeat case_match; lra. Qed.
Next Obligation.
  intros [] ?; rewrite /head_step_pmf.
  - solve_ex_seriesC_0.
  - solve_ex_seriesC_0.
  - solve_ex_single.
  - solve_ex_single.
  - case_match; try solve_ex_seriesC_0; subst.
    destruct (un_op_eval op v); [solve_ex_single|solve_ex_seriesC_0].
  - do 2 (case_match; try solve_ex_seriesC_0); subst.
    destruct (bin_op_eval op v v0); [solve_ex_single|solve_ex_seriesC_0].
  - do 3 (case_match; try solve_ex_seriesC_0). destruct b; solve_ex_single.
  - solve_ex_single.
  - solve_ex_single.
  - solve_ex_single.
  - solve_ex_single.
  - solve_ex_single.
  - do 2 (case_match; try solve_ex_seriesC_0); solve_ex_single.
  - solve_ex_single.
  - do 3 (case_match; try solve_ex_seriesC_0).
    destruct (heap σ1 !! l0); [solve_ex_single|solve_ex_seriesC_0].
  - do 4 (case_match; try solve_ex_seriesC_0).
    destruct (heap σ1 !! l0); [solve_ex_single|].
    eapply ex_seriesC_ext; [|apply ex_seriesC_0]; intros [[]]=>//=.
    repeat case_match; done.
  - solve_ex_single.
  - do 3 (case_match; try solve_ex_seriesC_0).
    destruct (σ1.(tapes) !! l0) as [[|b bs]|] eqn:Heq.
    + eapply ex_seriesC_ext;
        [|eapply ex_seriesC_plus;
          [eapply (ex_seriesC_singleton (Val (LitV (LitBool true)), σ1) 0.5)|
           eapply (ex_seriesC_singleton (Val (LitV (LitBool false)), σ1) 0.5)]].
      intros [? σ2]. simplify_eq. symmetry.
      do 3 (case_match; simpl; try lra).
      destruct b; repeat case_bool_decide; simplify_eq; try lra.
    + solve_ex_single.
    + eapply ex_seriesC_ext; [|apply ex_seriesC_0]; intros [[]]=>//=. by repeat case_match.
Qed.
Next Obligation.
  intros [] ?; rewrite /head_step_pmf.
  - solve_SeriesC_0.
  - solve_SeriesC_0.
  - solve_SeriesC_single.
  - solve_SeriesC_single.
  - case_match; try solve_SeriesC_0; subst.
    destruct (un_op_eval op v); [solve_SeriesC_single|solve_SeriesC_0].
  - do 2 (case_match; try solve_SeriesC_0); subst.
    destruct (bin_op_eval op v v0); [solve_SeriesC_single|solve_SeriesC_0].
  - do 3 (case_match; try solve_SeriesC_0). destruct b; solve_SeriesC_single.
  - solve_SeriesC_single.
  - solve_SeriesC_single.
  - solve_SeriesC_single.
  - solve_SeriesC_single.
  - solve_SeriesC_single.
  - do 2 (case_match; try solve_SeriesC_0); solve_SeriesC_single.
  - solve_SeriesC_single.
  - do 3 (case_match; try solve_SeriesC_0).
    destruct (heap σ1 !! l0); [solve_SeriesC_single|solve_SeriesC_0].
  - do 4 (case_match; try solve_SeriesC_0).
    destruct (heap σ1 !! l0); [|solve_SeriesC_0].
    repeat case_match; try solve_SeriesC_0; subst.
    erewrite SeriesC_ext; [erewrite (SeriesC_singleton (Val (LitV LitUnit), _) 1); lra|].
    intros []. symmetry.
    case_bool_decide; simplify_eq.
    + rewrite bool_decide_eq_true_2 //.
    + do 3 (case_match; try done).
      rewrite bool_decide_eq_false_2 //. intros ?; destruct_and!; simplify_eq.
  - solve_SeriesC_single.
  - do 3 (case_match; try solve_SeriesC_0).
    destruct (σ1.(tapes) !! l0) as [[|b bs]|] eqn:Heq.
    + erewrite SeriesC_ext.
      { erewrite SeriesC_plus;
          [|eapply (ex_seriesC_singleton (Val (LitV (LitBool true)), σ1) 0.5)
           |eapply (ex_seriesC_singleton (Val (LitV (LitBool false)), σ1) 0.5)].
        rewrite 2!SeriesC_singleton. lra. }
      intros [? σ2]. simplify_eq.
      do 3 (case_match; simpl; try lra).
      destruct b; repeat case_bool_decide; simplify_eq; try lra.
    + solve_SeriesC_single.
    + solve_SeriesC_0.
Qed.

Definition valid_state_step (σ1 : state) (α : loc) (σ2 : state) : Prop :=
  (* the heap is the same but we add a bit to the [α] tape *)
  ∃ b, σ2 = state_upd_tapes <[α := σ1.(tapes) !!! α ++ [b]]> σ1.

Local Instance valid_state_step_dec σ1 α σ2 : Decision (valid_state_step σ1 α σ2).
Proof. apply _. Qed.

Definition state_step_pmf (σ1 : state) (α : loc) (σ2 : state) : R :=
  if bool_decide (valid_state_step σ1 α σ2) then 0.5 else 0.

Lemma state_step_pmf_eq σ1 α σ2 :
  state_step_pmf σ1 α σ2 =
    (if bool_decide (σ2 = state_upd_tapes (<[α := σ1.(tapes) !!! α ++ [true]]>) σ1)
     then 0.5 else 0)
  + (if bool_decide (σ2 = state_upd_tapes (<[α := σ1.(tapes) !!! α ++ [false]]>) σ1)
     then 0.5 else 0).
Proof.
  rewrite /pmf /= /state_step_pmf /valid_state_step. case_bool_decide as Heq.
  - destruct Heq as [[] ->]; simplify_map_eq.
    + rewrite bool_decide_eq_true_2 // bool_decide_eq_false_2; [lra|].
      case. rewrite map_eq_iff => /(_ α) ?. simplify_map_eq.
    + rewrite bool_decide_eq_false_2.
      { rewrite bool_decide_eq_true_2 //. lra. }
      case. rewrite map_eq_iff => /(_ α) ?. simplify_map_eq.
  - rewrite !bool_decide_eq_false_2; [lra| |]; intros; eauto.
Qed.

Program Definition state_step (σ1 : state) (α : loc) : distr state :=
  MkDistr (state_step_pmf σ1 α) _ _ _.
Next Obligation. rewrite /state_step_pmf. intros. case_bool_decide; lra. Qed.
Next Obligation.
  intros σ1 α.
  eapply ex_seriesC_ext.
  { intros σ2. rewrite state_step_pmf_eq //. }
  eapply ex_seriesC_plus; eapply ex_seriesC_singleton.
Qed.
Next Obligation.
  intros σ1 α.
  erewrite SeriesC_ext.
  2 : { intros σ2. rewrite state_step_pmf_eq //. }
  erewrite SeriesC_plus; [|eapply ex_seriesC_singleton..].
  rewrite 2!SeriesC_singleton. lra.
Qed.

(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e σ ρ :
  head_step e σ ρ > 0 → to_val e = None.
Proof. destruct ρ, e; [|done..]. rewrite /pmf /=. lra. Qed.
Lemma head_ctx_step_val Ki e σ ρ :
  head_step (fill_item Ki e) σ ρ > 0 → is_Some (to_val e).
Proof. destruct ρ, Ki; rewrite /pmf/=; repeat case_match; try (done || lra). Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. destruct Ki2, Ki1; naive_solver eauto with f_equal. Qed.

Fixpoint height (e : expr) : nat :=
  match e with
  | Val _ => 1
  | Var _ => 1
  | Rec _ _ e => 1 + height e
  | App e1 e2 => 1 + height e1 + height e2
  | UnOp _ e => 1 + height e
  | BinOp _ e1 e2 => 1 + height e1 + height e2
  | If e0 e1 e2 => 1 + height e0 + height e1 + height e2
  | Pair e1 e2 => 1 + height e1 + height e2
  | Fst e => 1 + height e
  | Snd e => 1 + height e
  | InjL e => 1 + height e
  | InjR e => 1 + height e
  | Case e0 e1 e2 => 1 + height e0 + height e1 + height e2
  | Alloc e => 1 + height e
  | Load e => 1 + height e
  | Store e1 e2 => 1 + height e1 + height e2
  | AllocTape => 1
  | Flip e => 1 + height e
  end .

Definition expr_ord (e1 e2 : expr) : Prop := (height e1 < height e2)%nat.

Lemma expr_ord_wf' h e : (height e ≤ h)%nat → Acc expr_ord e.
Proof.
  rewrite /expr_ord. revert e; induction h.
  { destruct e; simpl; lia. }
  intros []; simpl;
    constructor; simpl; intros []; eauto with lia.
Defined.

Lemma expr_ord_wf : well_founded expr_ord.
Proof. red; intro; eapply expr_ord_wf'; eauto. Defined.

(* TODO: this proof is slow, but I do not see how to make it faster... *)
Lemma decomp_expr_ord Ki e e' : decomp_item e = Some (Ki, e') → expr_ord e' e.
Proof.
  rewrite /expr_ord /decomp_item.
  destruct e; try done;
  destruct Ki; simpl;
    repeat case_match; intros [=]; subst; lia.
Qed.

Lemma decomp_fill_item Ki e :
  to_val e = None → decomp_item (fill_item Ki e) = Some (Ki, e).
Proof. destruct Ki; simpl; by repeat case_match. Qed.

(* TODO: this proof is slow, but I do not see how to make it faster... *)
Lemma decomp_fill_item_2 e e' Ki :
  decomp_item e = Some (Ki, e') → fill_item Ki e' = e ∧ to_val e' = None.
Proof.
  destruct e; try done;
    destruct Ki; simpl;
    repeat case_match; intros [=]; subst; done.
Qed.

Lemma prob_lang_mixin :
  EctxiLanguageMixin of_val to_val fill_item decomp_item expr_ord head_step .
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val,
    decomp_fill_item, decomp_fill_item_2, expr_ord_wf, decomp_expr_ord.
Qed.
End prob_lang.

(** Language *)
Canonical Structure prob_ectxi_lang := EctxiLanguage prob_lang.state_step prob_lang.prob_lang_mixin.
Canonical Structure prob_ectx_lang := EctxLanguageOfEctxi prob_ectxi_lang.
Canonical Structure prob_lang := LanguageOfEctx prob_ectx_lang.

(* Prefer prob_lang names over ectx_language names. *)
Export prob_lang.

Definition cfg : Type := expr * state.

  
(* (** The following lemma is not provable using the axioms of [ectxi_language]. *)
(* The proof requires a case analysis over context items ([destruct i] on the *)
(* last line), which in all cases yields a non-value. To prove this lemma for *)
(* [ectxi_language] in general, we would require that a term of the form *)
(* [fill_item i e] is never a value. *) *)
(* Lemma to_val_fill_some K e v : to_val (fill K e) = Some v → K = [] ∧ e = Val v. *)
(* Proof. *)
(*   intro H. destruct K as [|Ki K]; first by apply of_to_val in H. exfalso. *)
(*   assert (to_val e ≠ None) as He. *)
(*   { intro A. by rewrite fill_not_val in H. } *)
(*   assert (∃ w, e = Val w) as [w ->]. *)
(*   { destruct e; try done; eauto. } *)
(*   assert (to_val (fill (Ki :: K) (Val w)) = None). *)
(*   { destruct Ki; simpl; apply fill_not_val; done. } *)
(*   by simplify_eq. *)
(* Qed. *)

(* Lemma prim_step_to_val_is_head_step e σ1 κs w σ2 efs : *)
(*   prim_step e σ1 κs (Val w) σ2 efs → head_step e σ1 κs (Val w) σ2 efs. *)
(* Proof. *)
(*   intro H. destruct H as [K e1 e2 H1 H2]. *)
(*   assert (to_val (fill K e2) = Some w) as H3; first by rewrite -H2. *)
(*   apply to_val_fill_some in H3 as [-> ->]. subst e. done. *)
(* Qed. *)

(* (** If [e1] makes a head step to a value under some state [σ1] then any head *)
(*  step from [e1] under any other state [σ1'] must necessarily be to a value. *) *)
(* Lemma head_step_to_val e1 σ1 κ e2 σ2 efs σ1' κ' e2' σ2' efs' : *)
(*   head_step e1 σ1 κ e2 σ2 efs → *)
(*   head_step e1 σ1' κ' e2' σ2' efs' → is_Some (to_val e2) → is_Some (to_val e2'). *)
(* Proof. destruct 1; inversion 1; naive_solver. Qed. *)
