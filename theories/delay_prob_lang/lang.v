From Stdlib Require Import Reals Psatz ClassicalEpsilon.
From stdpp Require Export binders strings.
From stdpp Require Import gmap countable fin fin_maps.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext tactics.
From iris.prelude Require Import options.
From clutch.prob Require Export distribution.
From clutch.common Require Export language ectx_language ectxi_language locations.

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module d_prob_lang.

  (** * Syntax *)
  
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp. (* Pointer offset *)

Inductive base_lit : Set :=
| LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc) | LitLbl (l : loc)
(* delayed un_op*)                                                                         
| NegOp' (x : base_lit) | MinusUnOp' (x: base_lit)
(* delayed bin_op *)     
| PlusOp' (x1 x2 : base_lit) | MinusOp' (x1 x2 : base_lit) | MultOp' (x1 x2 : base_lit)  | QuotOp' (x1 x2 : base_lit)  | RemOp' (x1 x2 : base_lit) 
| AndOp' (x1 x2 : base_lit)  | OrOp' (x1 x2 : base_lit) | XorOp' (x1 x2 : base_lit) 
| ShiftLOp' (x1 x2 : base_lit)  | ShiftROp' (x1 x2 : base_lit) 
| LeOp' (x1 x2 : base_lit)  | LtOp' (x1 x2 : base_lit)  | EqOp' (x1 x2 : base_lit)  
| OffsetOp' (x1 x2 : base_lit). 

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
  | AllocN (e1 e2 : expr) (* Array length and initial value *)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  (* Probabilistic choice *)
  (* | AllocTape (e : expr) *)
  | Rand (e : expr)
  | DRand (e : expr)
  | Laplace (e1 e2 e3: expr) 
  | DLaplace (e1 e2 e3: expr) 
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Scheme expr_mut := Induction for expr Sort Prop
    with val_mut := Induction for val Sort Prop.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Definition def_val : val := LitV LitUnit.

(** Removing vals_compare_safe for simplify computation :p *)
(* Definition val_is_unboxed (v : val) : Prop := *)
(*   match v with *)
(*   | LitV l | InjLV (LitV l) | InjRV (LitV l) => True *)
(*   | _ => False *)
(*   end. *)

(* (* Global Instance lit_is_unboxed_dec l : Decision (lit_is_unboxed l). *) *)
(* (* Proof. destruct l; simpl; exact (decide _). Defined. *) *)
(* Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v). *)
(* Proof. destruct v as [ | | | [] | [] ]; simpl; exact (decide _). Defined. *)

(* (** We just compare the word-sized representation of two values, without looking *)
(* into boxed data.  This works out fine if at least one of the to-be-compared *)
(* values is unboxed (exploiting the fact that an unboxed and a boxed value can *)
(* never be equal because these are disjoint sets). *) *)
(* Definition vals_compare_safe (vl v1 : val) : Prop := *)
(*   val_is_unboxed vl ∨ val_is_unboxed v1. *)
(* Global Arguments vals_compare_safe !_ !_ /. *)

Inductive urn :=
| urn_unif (s : gset Z)
| urn_laplace (num:nat) (den : Z) (l : Z)
.

Global Instance urn_inhabited : Inhabited urn. Proof. exact (populate (urn_unif ∅)). Qed. 
Global Instance urn_eq_dec : EqDecision urn.
Proof.
  solve_decision.
Qed.


Global Instance urn_countable : Countable urn.
Proof.
  set (enc :=
         (λ u, 
           match u with
           | urn_unif s => inl s
           | urn_laplace num den l => inr (num, den, l)
           end)).
  set (dec :=
         (λ x,
            match x with
            | inl s => urn_unif s
            | inr (num, den, l) => urn_laplace num den l
            end
         )).
  refine (inj_countable' enc dec _).
  by intros []; simpl.
Qed. 

(* Global Instance urn_lookup_total : LookupTotal loc urn (gmap loc urn). *)
(* Proof. apply map_lookup_total. Defined. *)
(* Global Instance urn_insert : Insert loc urn (gmap loc urn). *)
(* Proof. apply map_insert. Defined. *)

(** The state: a [loc]-indexed heap of [val]s, and [loc]-indexed gmap of urns. *)
Record state : Type := {
  heap  : gmap loc val;
  urns : gmap loc urn
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
     | AllocN e1 e2, AllocN e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Load e, Load e' => cast_if (decide (e = e'))
     | Store e1 e2, Store e1' e2' =>
         cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Rand e, Rand e' => cast_if (decide (e=e'))
     | DRand e, DRand e' => cast_if (decide (e=e'))
     | Laplace e0 e1 e2, Laplace e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | DLaplace e0 e1 e2, DLaplace e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
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
  set (enc :=
         fix go (bl:base_lit) :=
           match bl with
           | LitInt z => GenLeaf (inl (inl z))
           | LitBool b => GenLeaf (inl (inr b))
           | LitUnit => GenLeaf (inr (inl ()))
           | LitLoc l => GenLeaf (inr (inr (inl l)))
           | LitLbl l => GenLeaf (inr (inr (inr l)))
           | NegOp' x => GenNode 0 [go x]
           | MinusUnOp' x => GenNode 1 [go x]
           | PlusOp' x1 x2 => GenNode 2 [go x1; go x2]
           | MinusOp' x1 x2 => GenNode 3 [go x1; go x2]
           | MultOp' x1 x2 => GenNode 4 [go x1; go x2]
           | QuotOp' x1 x2 => GenNode 5 [go x1; go x2]
           | RemOp' x1 x2 => GenNode 6 [go x1; go x2]
           | AndOp' x1 x2 => GenNode 7 [go x1; go x2]
           | OrOp' x1 x2 => GenNode 8 [go x1; go x2]
           | XorOp' x1 x2 => GenNode 9 [go x1; go x2]
           | ShiftLOp' x1 x2 => GenNode 10 [go x1; go x2]
           | ShiftROp' x1 x2 => GenNode 11 [go x1; go x2]
           | LeOp' x1 x2 => GenNode 12 [go x1; go x2]
           | LtOp' x1 x2 => GenNode 13 [go x1; go x2]
           | EqOp' x1 x2 => GenNode 14 [go x1; go x2]
           | OffsetOp' x1 x2 => GenNode 15 [go x1; go x2]
           end ).
  set (dec :=
         fix go e :=
           match e with
           | GenLeaf (inl (inl z)) => LitInt z
           | GenLeaf (inl (inr b)) => LitBool b
           | GenLeaf (inr (inl ())) => LitUnit
           | GenLeaf (inr (inr (inl l))) => LitLoc l
           | GenLeaf (inr (inr (inr l))) => LitLbl l
           | GenNode 0 [x] => NegOp' (go x)
           | GenNode 1 [x] => MinusUnOp' (go x)
           | GenNode 2 [x1; x2] => PlusOp' (go x1) (go x2)
           | GenNode 3 [x1; x2] => MinusOp' (go x1) (go x2)
           | GenNode 4 [x1; x2] => MultOp' (go x1) (go x2)
           | GenNode 5 [x1; x2] => QuotOp' (go x1) (go x2)
           | GenNode 6 [x1; x2] => RemOp' (go x1) (go x2)
           | GenNode 7 [x1; x2] => AndOp' (go x1) (go x2)
           | GenNode 8 [x1; x2] => OrOp' (go x1) (go x2)
           | GenNode 9 [x1; x2] => XorOp' (go x1) (go x2)
           | GenNode 10 [x1; x2] => ShiftLOp' (go x1) (go x2)
           | GenNode 11 [x1; x2] => ShiftROp' (go x1) (go x2)
           | GenNode 12 [x1; x2] => LeOp' (go x1) (go x2)
           | GenNode 13 [x1; x2] => LtOp' (go x1) (go x2)
           | GenNode 14 [x1; x2] => EqOp' (go x1) (go x2)
           | GenNode 15 [x1; x2] => OffsetOp' (go x1) (go x2)
           | _ => LitUnit
           end
      ).
  refine (inj_countable' enc dec _).
  fix FIX 1.
  intros []; try reflexivity; simpl; by f_equal.
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
  | LeOp => 10 | LtOp => 11 | EqOp => 12 | OffsetOp => 13
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | 12 => EqOp | _ => OffsetOp
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
     | AllocN e1 e2 => GenNode 12 [go e1; go e2]
     | Load e => GenNode 13 [go e]
     | Store e1 e2 => GenNode 14 [go e1; go e2]
     | Rand e => GenNode 15 [go e]
     | DRand e => GenNode 16 [go e]
     | Laplace e0 e1 e2 => GenNode 17 [go e0; go e1; go e2]
     | DLaplace e0 e1 e2 => GenNode 18 [go e0; go e1; go e2]
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
     | GenNode 12 [e1 ; e2] => AllocN (go e1) (go e2)
     | GenNode 13 [e] => Load (go e)
     | GenNode 14 [e1; e2] => Store (go e1) (go e2)
     | GenNode 15 [e] => Rand (go e)
     | GenNode 16 [e] => DRand (go e)
     | GenNode 17 [e0; e1; e2] => Laplace (go e0) (go e1) (go e2)
     | GenNode 18 [e0; e1; e2] => DLaplace (go e0) (go e1) (go e2)
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
 - destruct e as [v| | | | | | | | | | | | | | | | | | |]; simpl; f_equal;
     [exact (gov v)|done..].
 - destruct v; by f_equal.
Qed.
Global Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.
Global Program Instance state_countable : Countable state :=
  {| encode σ := encode (σ.(heap), σ.(urns));
     decode p := '(h, u) ← decode p; mret {|heap:=h; urns:=u|} |}.
Next Obligation. intros [h t]. rewrite decode_encode //=. Qed.

Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; urns := inhabitant |}.
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
  | AllocNLCtx (v2 : val)
  | AllocNRCtx (e1 : expr)
  | LoadCtx
  | StoreLCtx (v2 : val)
  | StoreRCtx (e1 : expr)
  | RandCtx
  | DRandCtx
  | LaplaceNumCtx (v2 : val) (v3 : val)
  | LaplaceDenCtx (e1 : expr) (v3 : val)
  | LaplaceLocCtx (e1 : expr) (e2 : expr)
  | DLaplaceNumCtx (v2 : val) (v3 : val)
  | DLaplaceDenCtx (e1 : expr) (v3 : val)
  | DLaplaceLocCtx (e1 : expr) (e2 : expr)
.

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
  | AllocNLCtx v2 => AllocN e (Val v2)
  | AllocNRCtx e1 => AllocN e1 e
  | LoadCtx => Load e
  | StoreLCtx v2 => Store e (Val v2)
  | StoreRCtx e1 => Store e1 e
  | RandCtx => Rand e
  | DRandCtx => DRand e
  | LaplaceNumCtx v2 v3 => Laplace e (Val v2) (Val v3)
  | LaplaceDenCtx e1 v3 => Laplace e1 e (Val v3)
  | LaplaceLocCtx e1 e2 => Laplace e1 e2 e
  | DLaplaceNumCtx v2 v3 => DLaplace e (Val v2) (Val v3)
  | DLaplaceDenCtx e1 v3 => DLaplace e1 e (Val v3)
  | DLaplaceLocCtx e1 e2 => DLaplace e1 e2 e
  end.

Definition decomp_item (e : expr) : option (ectx_item * expr) :=
  let noval (e : expr) (ei : ectx_item) :=
    match e with Val _ => None | _ => Some (ei, e) end in
  match e with
  | App e1 e2      =>
      match e2 with
      | (Val v)    => noval e1 (AppLCtx v)
      | _          => Some (AppRCtx e1, e2)
      end
  | UnOp op e      => noval e (UnOpCtx op)
  | BinOp op e1 e2 =>
      match e2 with
      | Val v      => noval e1 (BinOpLCtx op v)
      | _          => Some (BinOpRCtx op e1, e2)
      end
  | If e0 e1 e2    => noval e0 (IfCtx e1 e2)
  | Pair e1 e2     =>
      match e2 with
      | Val v      => noval e1 (PairLCtx v)
      | _          => Some (PairRCtx e1, e2)
      end
  | Fst e          => noval e FstCtx
  | Snd e          => noval e SndCtx
  | InjL e         => noval e InjLCtx
  | InjR e         => noval e InjRCtx
  | Case e0 e1 e2  => noval e0 (CaseCtx e1 e2)
  | AllocN e1 e2        =>
      match e2 with
      | Val v      => noval e1 (AllocNLCtx v)
      | _          => Some (AllocNRCtx e1, e2)
      end

  | Load e         => noval e LoadCtx
  | Store e1 e2    =>
      match e2 with
      | Val v      => noval e1 (StoreLCtx v)
      | _          => Some (StoreRCtx e1, e2)
      end
  | Rand e => noval e RandCtx
  | DRand e => noval e DRandCtx
  | Laplace e1 e2 e3 =>
      match e3 with
      | Val v3 =>
          match e2 with
          | Val v2 => noval e1 (LaplaceNumCtx v2 v3)
          | _ => Some (LaplaceDenCtx e1 v3, e2)
          end
      | _ => Some (LaplaceLocCtx e1 e2, e3)
      end
  | DLaplace e1 e2 e3 =>
      match e3 with
      | Val v3 =>
          match e2 with
          | Val v2 => noval e1 (DLaplaceNumCtx v2 v3)
          | _ => Some (DLaplaceDenCtx e1 v3, e2)
          end
      | _ => Some (DLaplaceLocCtx e1 e2, e3)
      end
  | _              => None
  end.

(** This is needed for the commute lemma *)
Global Instance ectx_item_eq_dec : EqDecision ectx_item.
Proof. solve_decision. Defined.
Global Instance ectx_item_countable : Countable ectx_item.
Proof.
  set (enc :=
         λ Ki,
           match Ki with
           | AppLCtx v2 => GenNode 0 [GenLeaf (inl$ inl v2)]
           | AppRCtx e1 => GenNode 1 [GenLeaf (inl $ inr e1)]
           | UnOpCtx op => GenNode 2 [GenLeaf (inr $ inl op)]
           | BinOpLCtx op v2 => GenNode 3 [GenLeaf (inl$ inl v2); GenLeaf (inr $ inr op)]
           | BinOpRCtx op e1 => GenNode 4 [GenLeaf (inl $ inr e1); GenLeaf (inr $ inr op)]
           | IfCtx e1 e2 => GenNode 5 [GenLeaf (inl $ inr e1); GenLeaf (inl $ inr e2)]
           | PairLCtx v2 => GenNode 6 [GenLeaf (inl $ inl v2)]
           | PairRCtx e1 => GenNode 7 [GenLeaf (inl $ inr e1)]
           | FstCtx => GenNode 8 []
           | SndCtx => GenNode 9 []
           | InjLCtx => GenNode 10 []
           | InjRCtx => GenNode 11 []
           | CaseCtx e1 e2 => GenNode 12 [GenLeaf (inl $ inr e1); GenLeaf (inl $ inr e2)]
           | AllocNLCtx v2 => GenNode 13 [GenLeaf (inl$ inl v2)]
           | AllocNRCtx e1 => GenNode 14 [GenLeaf (inl $ inr e1)]
           | LoadCtx => GenNode 15 []
           | StoreLCtx v2 => GenNode 16 [GenLeaf (inl$ inl v2)]
           | StoreRCtx e1 => GenNode 17 [GenLeaf (inl $ inr e1)]
           | RandCtx => GenNode 18 []
           | DRandCtx => GenNode 19 []
           | LaplaceNumCtx v2 v3 => GenNode 20 [GenLeaf (inl $ inl v2); (GenLeaf (inl $ inl v3))]
           | LaplaceDenCtx e1 v3 => GenNode 21 [GenLeaf (inl $ inr e1); (GenLeaf (inl $ inl v3))]
           | LaplaceLocCtx e1 e2 => GenNode 22 [GenLeaf (inl $ inr e1); (GenLeaf (inl $ inr e2))]
           | DLaplaceNumCtx v2 v3 => GenNode 23 [GenLeaf (inl $ inl v2); (GenLeaf (inl $ inl v3))]
           | DLaplaceDenCtx e1 v3 => GenNode 24 [GenLeaf (inl $ inr e1); (GenLeaf (inl $ inl v3))]
           | DLaplaceLocCtx e1 e2 => GenNode 25 [GenLeaf (inl $ inr e1); (GenLeaf (inl $ inr e2))]
           end).
  set (dec :=
         λ e, 
           match e with
           | GenNode 0 [GenLeaf (inl (inl v2))] => AppLCtx v2 
           | GenNode 1 [GenLeaf (inl (inr e1))] => AppRCtx e1 
           | GenNode 2 [GenLeaf (inr (inl op))] => UnOpCtx op 
           | GenNode 3 [GenLeaf (inl (inl v2)); GenLeaf (inr (inr op))] => BinOpLCtx op v2
           | GenNode 4 [GenLeaf (inl (inr e1)); GenLeaf (inr (inr op))] => BinOpRCtx op e1 
           | GenNode 5 [GenLeaf (inl (inr e1)); GenLeaf (inl (inr e2))] => IfCtx e1 e2 
           | GenNode 6 [GenLeaf (inl (inl v2))] => PairLCtx v2 
           | GenNode 7 [GenLeaf (inl (inr e1))] => PairRCtx e1 
           | GenNode 8 [] => FstCtx 
           | GenNode 9 [] => SndCtx 
           | GenNode 10 [] => InjLCtx 
           | GenNode 11 [] => InjRCtx 
           | GenNode 12 [GenLeaf (inl (inr e1)); GenLeaf (inl (inr e2))] => CaseCtx e1 e2 
           | GenNode 13 [GenLeaf (inl (inl v2))] => AllocNLCtx v2 
           | GenNode 14 [GenLeaf (inl (inr e1))] => AllocNRCtx e1 
           | GenNode 15 [] => LoadCtx 
           | GenNode 16 [GenLeaf (inl (inl v2))] => StoreLCtx v2 
           | GenNode 17 [GenLeaf (inl (inr e1))] => StoreRCtx e1  
           | GenNode 18 [] => RandCtx 
           | GenNode 19 [] => DRandCtx
           | GenNode 20 [GenLeaf (inl (inl v2)); GenLeaf (inl (inl v3))] => LaplaceNumCtx v2 v3
           | GenNode 21 [GenLeaf (inl (inr e1)); GenLeaf (inl (inl v3))] => LaplaceDenCtx e1 v3
           | GenNode 22 [GenLeaf (inl (inr e1)); GenLeaf (inl (inr e2))] => LaplaceLocCtx e1 e2
           | GenNode 23 [GenLeaf (inl (inl v2)); GenLeaf (inl (inl v3))] => DLaplaceNumCtx v2 v3
           | GenNode 24 [GenLeaf (inl (inr e1)); GenLeaf (inl (inl v3))] => DLaplaceDenCtx e1 v3
           | GenNode 25 [GenLeaf (inl (inr e1)); GenLeaf (inl (inr e2))] => DLaplaceLocCtx e1 e2
           | _ => DRandCtx
           end).
  refine (inj_countable' enc dec _).
  intros []; try reflexivity; simpl; by f_equal. Defined.

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
  | AllocN e1 e2 => AllocN (subst x v e1) (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | Rand e => Rand (subst x v e)
  | DRand e => DRand (subst x v e)
  | Laplace e0 e1 e2 => Laplace (subst x v e0) (subst x v e1) (subst x v e2)
  | DLaplace e0 e1 e2 => DLaplace (subst x v e0) (subst x v e1) (subst x v e2)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => λ x, x end.

(** * typing for well formness *)
(** For the stepping relations for unop and binop, we check as follows
    - is it well typed, and has the right value? If not, dont step
    - are any of the arguments a delayed value? if yes, just combine them symbolically
    - otherwise it is normal semantics
 *)

(** Design choice: to simplify stuff with all these urn labels flying around
    You can only compare LitVs. So InjLV x = InjLV x will NOT step. 
    (To be fair in previous languages (InjLV (InjLV x)= InjLV (InjLV x)) will not
    step as well due to the compare safe constraint, so its not THAT big a deal)
 *)

(* Note that there is no BLTLbl, because that is the BLTInt type *)
Inductive base_lit_type :=
| BLTUnit : base_lit_type
| BLTInt : base_lit_type
| BLTBool : base_lit_type
| BLTLoc : base_lit_type
.

Fixpoint base_lit_type_check (bl:base_lit) :=
  match bl with
  | LitInt n => Some BLTInt
  | LitBool b => Some BLTBool
  | LitUnit => Some BLTUnit
  | LitLoc l => Some BLTLoc
  | LitLbl l => Some BLTInt
  | NegOp' x =>
      match base_lit_type_check x with
      | Some BLTBool => Some BLTBool
      | _ => None
      end
  | MinusUnOp' x =>
      match base_lit_type_check x with
      | Some BLTInt => Some BLTInt
      | _ => None
      end
  | PlusOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTInt, Some BLTInt) => Some BLTInt
      | _ => None
      end
  | MinusOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTInt, Some BLTInt) => Some BLTInt
      | _ => None
      end
  | MultOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTInt, Some BLTInt) => Some BLTInt
      | _ => None
      end
  | QuotOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTInt, Some BLTInt) => Some BLTInt
      | _ => None
      end
  | RemOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTInt, Some BLTInt) => Some BLTInt
      | _ => None
      end
  | AndOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTBool, Some BLTBool) => Some BLTBool
      | _ => None
      end
  | OrOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTBool, Some BLTBool) => Some BLTBool
      | _ => None
      end
  | XorOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTBool, Some BLTBool) => Some BLTBool
      | _ => None
      end
  | ShiftLOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTInt, Some BLTInt) => Some BLTInt
      | _ => None
      end
  | ShiftROp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTInt, Some BLTInt) => Some BLTInt
      | _ => None
      end
  | LeOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTInt, Some BLTInt) => Some BLTBool
      | _ => None
      end
  | LtOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTInt, Some BLTInt) => Some BLTBool
      | _ => None
      end
  | EqOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some t1, Some t2) => Some BLTBool
      | _ => None
      end
  | OffsetOp' x1 x2 => 
      match (base_lit_type_check x1), (base_lit_type_check x2) with
      | (Some BLTLoc), (Some BLTInt) => Some BLTLoc
      | _, _ => None
      end
  end
.

Fixpoint well_formed_expr (e:expr) :=
  match e with
  | Val v =>
      well_formed_val v
  | Var x => true
  | Rec f x e => well_formed_expr e
  | App e1 e2 => well_formed_expr e1 && well_formed_expr e2
  | UnOp op e => well_formed_expr e
  | BinOp op e1 e2 => well_formed_expr e1 && well_formed_expr e2
  | If e0 e1 e2 => well_formed_expr e0 && well_formed_expr e1 && well_formed_expr e2
  | Pair e1 e2 => well_formed_expr e1 && well_formed_expr e2
  | Fst e => well_formed_expr e
  | Snd e => well_formed_expr e
  | InjL e => well_formed_expr e
  | InjR e => well_formed_expr e
  | Case e0 e1 e2 => well_formed_expr e0 && well_formed_expr e1 && well_formed_expr e2
  | AllocN e1 e2 => well_formed_expr e1 && well_formed_expr e2
  | Load e => well_formed_expr e
  | Store e1 e2 => well_formed_expr e1 && well_formed_expr e2
  | Rand e => well_formed_expr e
  | DRand e => well_formed_expr e
  | Laplace e0 e1 e2 => well_formed_expr e0 && well_formed_expr e1 && well_formed_expr e2
  | DLaplace e0 e1 e2 => well_formed_expr e0 && well_formed_expr e1 && well_formed_expr e2
  end
with
well_formed_val (v:val) :=
  match v with
  | LitV l => match base_lit_type_check l with
             | Some _ => true
             | _ => false
             end
  | RecV f x e => well_formed_expr e
  | PairV v1 v2 => well_formed_val v1 && well_formed_val v2
  | InjLV v => well_formed_val v
  | InjRV v => well_formed_val v
  end
.

(** * semantics *)
(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  (* check whether v is a base lit  *)
  match v with
  | LitV bl =>
      match op, base_lit_type_check bl with
        (* neg *)
      | NegOp, Some BLTBool =>
          match bl with
          | LitBool b => Some $ LitV $ LitBool (negb b)
          | _ => Some $ LitV $ NegOp' bl
          end
        (* minus*)
      | MinusUnOp, Some BLTInt =>
          match bl with
          | LitInt n => Some $ LitV $ LitInt (- n)
          | _ => Some $ LitV $ MinusUnOp' bl
          end
      | _, _ => None
      end
  | _ => None
  end. 

(* Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit := *)
(*   match op with *)
(*   | PlusOp => Some $ LitInt (n1 + n2) *)
(*   | MinusOp => Some $ LitInt (n1 - n2) *)
(*   | MultOp => Some $ LitInt (n1 * n2) *)
(*   | QuotOp => Some $ LitInt (n1 `quot` n2) *)
(*   | RemOp => Some $ LitInt (n1 `rem` n2) *)
(*   | AndOp => None(* LitInt (Z.land n1 n2) *) *)
(*   | OrOp => None (* LitInt (Z.lor n1 n2) *) *)
(*   | XorOp => None (* LitInt (Z.lxor n1 n2) *) *)
(*   | ShiftLOp => Some $ LitInt (n1 ≪ n2) *)
(*   | ShiftROp => Some $ LitInt (n1 ≫ n2) *)
(*   | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2)) *)
(*   | LtOp => Some $ LitBool (bool_decide (n1 < n2)) *)
(*   | EqOp => Some $ LitBool (bool_decide (n1 = n2)) *)
(*   | OffsetOp => None (* LitInt (n1 + n2) *) (* Treat offsets as ints *) *)
(*   end%Z. *)

(* Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit := *)
(*   match op with *)
(*   | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *) *)
(*   | AndOp => Some (LitBool (b1 && b2)) *)
(*   | OrOp => Some (LitBool (b1 || b2)) *)
(*   | XorOp => Some (LitBool (xorb b1 b2)) *)
(*   | ShiftLOp | ShiftROp => None (* Shifts *) *)
(*   | LeOp | LtOp => None (* InEquality *) *)
(*   | EqOp => Some (LitBool (bool_decide (b1 = b2))) *)
(*   | OffsetOp => None *)
(*   end. *)

(* Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit := *)
(*   match op, v2 with *)
(*   | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off) *)
(*   | LeOp, LitLoc l2 => None  (* Some $ LitBool (bool_decide (l1 ≤ₗ l2)) *) *)
(*   | LtOp, LitLoc l2 => None (* Some $ LitBool (bool_decide (l1 <ₗ l2)) *) *)
(*   | _, _ => None *)
(*   end. *)

Definition bin_op_eval_bl (op:bin_op) (bl1 bl2: base_lit) :=
  match op with
  | PlusOp =>
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTInt, Some BLTInt =>
          match bl1, bl2 with
          | LitInt n1, LitInt n2 => Some $ LitInt (n1 + n2)
          | _, _ => Some $ PlusOp' bl1 bl2
          end                            
      | _, _ => None
      end
  | MinusOp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTInt, Some BLTInt =>
          match bl1, bl2 with
          | LitInt n1, LitInt n2 => Some $ LitInt (n1 - n2)
          | _, _ => Some $ MinusOp' bl1 bl2
          end                            
      | _, _ => None
      end
  | MultOp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTInt, Some BLTInt =>
          match bl1, bl2 with
          | LitInt n1, LitInt n2 => Some $ LitInt (n1 * n2)
          | _, _ => Some $ MultOp' bl1 bl2
          end                            
      | _, _ => None
      end
  | QuotOp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTInt, Some BLTInt =>
          match bl1, bl2 with
          | LitInt n1, LitInt n2 => Some $ LitInt (n1 `quot` n2)
          | _, _ => Some $ QuotOp' bl1 bl2
          end                            
      | _, _ => None
      end
  | RemOp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTInt, Some BLTInt =>
          match bl1, bl2 with
          | LitInt n1, LitInt n2 => Some $ LitInt (n1 `rem` n2)
          | _, _ => Some $ RemOp' bl1 bl2
          end                            
      | _, _ => None
      end
  | AndOp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTBool, Some BLTBool =>
          match bl1, bl2 with
          | LitBool b1, LitBool b2 => Some $ LitBool (b1 && b2)
          | _, _ => Some $ AndOp' bl1 bl2
          end                            
      | _, _ => None
      end
  | OrOp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTBool, Some BLTBool =>
          match bl1, bl2 with
          | LitBool b1, LitBool b2 => Some $ LitBool (b1 || b2)
          | _, _ => Some $ OrOp' bl1 bl2
          end                            
      | _, _ => None
      end
  | XorOp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTBool, Some BLTBool =>
          match bl1, bl2 with
          | LitBool b1, LitBool b2 => Some $ LitBool (xorb b1 b2)
          | _, _ => Some $ XorOp' bl1 bl2
          end                            
      | _, _ => None
      end
  | ShiftLOp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTInt, Some BLTInt =>
          match bl1, bl2 with
          | LitInt n1, LitInt n2 => Some $ LitInt (n1 ≪ n2)
          | _, _ => Some $ ShiftLOp' bl1 bl2
          end                            
      | _, _ => None
      end
  | ShiftROp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTInt, Some BLTInt =>
          match bl1, bl2 with
          | LitInt n1, LitInt n2 => Some $ LitInt (n1 ≫ n2)
          | _, _ => Some $ ShiftROp' bl1 bl2
          end                            
      | _, _ => None
      end
  | LeOp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTInt, Some BLTInt =>
          match bl1, bl2 with
          | LitInt n1, LitInt n2 => Some $ LitBool (bool_decide (n1 ≤ n2)%Z)
          | _, _ => Some $ LeOp' bl1 bl2
          end                            
      | _, _ => None
      end
  | LtOp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTInt, Some BLTInt =>
          match bl1, bl2 with
          | LitInt n1, LitInt n2 => Some $ LitBool (bool_decide (n1 < n2)%Z)
          | _, _ => Some $ LtOp' bl1 bl2
          end                            
      | _, _ => None
      end
  | EqOp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some x, Some y =>
          match bl1 with
          | LitInt _ | LitBool _ | LitUnit | LitLoc _ =>
            match bl2 with
            | LitInt _ | LitBool _ | LitUnit | LitLoc _ => Some $ LitBool (bool_decide (bl1 = bl2))                          
            | _ => Some $ EqOp' bl1 bl2
            end
          | _ => Some $ EqOp' bl1 bl2
          end                                     
      | _, _ => None
      end
  | OffsetOp => 
      match base_lit_type_check bl1, base_lit_type_check bl2 with
      | Some BLTLoc, Some BLTInt =>
          match bl1, bl2 with
          | LitLoc l1, LitInt n2 => Some $ LitLoc (l1 +ₗ n2)
          | _, _ => Some $ OffsetOp' bl1 bl2
          end                            
      | _, _ => None
      end
  end
.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  match v1, v2 with
  | LitV bl1, LitV bl2 =>
       x ← bin_op_eval_bl op bl1 bl2; Some $ LitV x
  | _, _ => None
  end.
  
Definition state_upd_heap (f : gmap loc val → gmap loc val) (σ : state) : state :=
  {| heap := f σ.(heap); urns := σ.(urns) |}.
Global Arguments state_upd_heap _ !_ /.

Definition state_upd_urns (f : gmap loc urn → gmap loc urn) (σ : state) : state :=
  {| heap := σ.(heap); urns := f σ.(urns) |}.
Global Arguments state_upd_urns _ !_ /.

Lemma state_upd_urns_twice σ l xs ys :
  state_upd_urns <[l:=(ys)]> (state_upd_urns <[l:=(xs)]> σ) = state_upd_urns <[l:=(ys)]> σ.
Proof. rewrite /state_upd_urns /=. f_equal. apply insert_insert. Qed.

Lemma state_upd_urns_same σ σ' l xs ys :
  state_upd_urns <[l:=(ys)]> σ = state_upd_urns <[l:=(xs)]> σ' -> xs = ys.
Proof. rewrite /state_upd_urns /=. intros K. simplify_eq.
       rewrite map_eq_iff in H.
       specialize (H l).
       rewrite !lookup_insert in H.
       by simplify_eq.
Qed.


Lemma state_upd_urns_no_change σ l ys :
  urns σ !! l = Some (ys)-> 
  state_upd_urns <[l:=(ys)]> σ = σ .
Proof.
  destruct σ as [? t]. simpl.
  intros Ht.
  f_equal.
  apply insert_id. done.
Qed.

Fixpoint heap_array (l : loc) (vs : list val) : gmap loc val :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_app l vs1 vs2 : heap_array l (vs1 ++ vs2) = (heap_array l vs1) ∪ (heap_array (l +ₗ (length vs1)) vs2) .
Proof.
  revert l.
  induction vs1; intro l.
  - simpl.
    rewrite map_empty_union loc_add_0 //.
  - rewrite -app_comm_cons /= IHvs1.
    rewrite map_union_assoc.
    do 2 f_equiv.
    rewrite Nat2Z.inj_succ /=.
    rewrite /Z.succ
      Z.add_comm
      loc_add_assoc //.
Qed.

Lemma heap_array_lookup l vs v k :
  heap_array l vs !! k = Some v ↔
  ∃ j, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ vs !! (Z.to_nat j) = Some v.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & ? & -> & ?)].
    { eexists 0. rewrite loc_add_0. naive_solver lia. }
    eexists (1 + j)%Z. rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & ? & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite loc_add_0; eauto. }
    right. split.
    { rewrite -{1}(loc_add_0 l). intros ?%(inj (loc_add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z. rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc val) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&?&->&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

Definition state_upd_heap_N (l : loc) (n : nat) (v : val) (σ : state) : state :=
  state_upd_heap (λ h, heap_array l (replicate n v) ∪ h) σ.

Lemma state_upd_heap_singleton l v σ :
  state_upd_heap_N l 1 v σ = state_upd_heap <[l:= v]> σ.
Proof.
  destruct σ as [h p]. rewrite /state_upd_heap_N /=. f_equiv.
  rewrite right_id insert_union_singleton_l. done.
Qed.

Lemma state_upd_urns_heap σ l1 l2 xs m v :
  state_upd_urns <[l2:=(xs)]> (state_upd_heap_N l1 m v σ) =
  state_upd_heap_N l1 m v (state_upd_urns <[l2:=(xs)]> σ).
Proof.
  by rewrite /state_upd_urns /state_upd_heap_N /=.
Qed.

Lemma heap_array_replicate_S_end l v n :
  heap_array l (replicate (S n) v) = heap_array l (replicate n v) ∪ {[l +ₗ n:= v]}.
Proof.
  induction n.
  - simpl.
    rewrite map_union_empty.
    rewrite map_empty_union.
    by rewrite loc_add_0.
  - rewrite replicate_S_end
     heap_array_app
     IHn /=.
    rewrite map_union_empty length_replicate //.
Qed.

Lemma heap_array_disjoint (m:gmap loc val) n v:
  dom (heap_array (fresh_loc m) (replicate n v)) ## dom m.
Proof.
  remember n as n' eqn:Heqn.
  replace (fresh_loc m) with ((fresh_loc m +ₗ (n-n'))); last first.
  { subst. rewrite Z.sub_diag. by rewrite loc_add_0. }
  assert (n'<=n)%nat as H by lia.
  clear Heqn.
  revert H.
  revert m.
  induction n' as [|? IHn']; first set_solver.
  simpl.
  intros.
  rewrite dom_union.
  rewrite disjoint_union_l.
  split.
  - rewrite dom_singleton.
    rewrite disjoint_singleton_l.
    apply fresh_loc_offset_is_fresh.
    lia.
  - rewrite loc_add_assoc.
    replace (_-_+_)%Z with (n-n')%Z by lia.
    apply IHn'. lia.
Qed. 

Lemma dom_heap_array x l lis:
  x ∈ dom (heap_array l lis) ->
  loc_le l x /\ loc_lt x (loc_add l (length lis)).
Proof.
  rewrite elem_of_dom.
  intros [? H].
  rewrite heap_array_lookup in H.
  destruct H as [? [? [? K]]].
  subst.
  rewrite -{1}(loc_add_0 l).
  split; first by apply loc_add_le_mono.
  apply Z.add_lt_mono_l.
  apply lookup_lt_Some in K. lia.
Qed. 
#[local] Open Scope R.

Section urn.
  (** Definitions for relating delayed program with nondelayed one *)
  (** Note here after the urn_subst, we completely remove all delayed unop binop operations*)
  Fixpoint urn_subst (f: gmap loc Z) (bl : base_lit) : option base_lit :=
    match bl with
    | LitInt n => Some $ LitInt n
    | LitBool b => Some $ LitBool b
    | LitUnit => Some LitUnit
    | LitLoc l => Some $ LitLoc l
    | LitLbl l => (x ← f !! l; Some $ LitInt (x))
    | NegOp' x => (i ← urn_subst f x;
                  match i with
                  | LitBool b => Some $ LitBool (negb b)
                  | _ => None end
                 )
    | MinusUnOp' x => (i ← urn_subst f x;
                      match i with
                      | LitInt n => Some $ LitInt (- n)
                      | _ => None end
                     )
    | PlusOp' x1 x2 => (i ← urn_subst f x1;
                       j ← urn_subst f x2;
                       match i, j with
                       | LitInt n1, LitInt n2 =>
                           Some $ LitInt (n1 + n2)
                       | _, _ => None
                       end
                      )
    | MinusOp' x1 x2 => (i ← urn_subst f x1;
                        j ← urn_subst f x2;
                        match i, j with
                        | LitInt n1, LitInt n2 =>
                            Some $ LitInt (n1 - n2)
                        | _, _ => None
                        end
                       )
    | MultOp' x1 x2 => (i ← urn_subst f x1;
                       j ← urn_subst f x2;
                       match i, j with
                       | LitInt n1, LitInt n2 =>
                           Some $ LitInt (n1 * n2)
                       | _, _ => None
                       end
                      )
    | QuotOp' x1 x2 => (i ← urn_subst f x1;
                       j ← urn_subst f x2;
                       match i, j with
                       | LitInt n1, LitInt n2 =>
                           Some $ LitInt (n1 `quot` n2)
                       | _, _ => None
                       end
                      )
    | RemOp' x1 x2 => (i ← urn_subst f x1;
                      j ← urn_subst f x2;
                      match i, j with
                      | LitInt n1, LitInt n2 =>
                          Some $ LitInt (n1 `rem` n2)
                      | _, _ => None
                      end
                     )
    | AndOp' x1 x2 => (i ← urn_subst f x1;
                      j ← urn_subst f x2;
                      match i, j with
                      | LitBool b1, LitBool b2 =>
                          Some $ LitBool (b1 && b2)
                      | _, _ => None
                      end
                     )
    | OrOp' x1 x2 => (i ← urn_subst f x1;
                     j ← urn_subst f x2;
                     match i, j with
                     | LitBool b1, LitBool b2 =>
                         Some $ LitBool (b1 || b2)
                     | _, _ => None
                     end
                    )
    | XorOp' x1 x2 => (i ← urn_subst f x1;
                      j ← urn_subst f x2;
                      match i, j with
                      | LitBool b1, LitBool b2 =>
                          Some $ LitBool (xorb b1 b2)
                      | _, _ => None
                      end
                     )
    | ShiftLOp' x1 x2 => (i ← urn_subst f x1;
                         j ← urn_subst f x2;
                         match i, j with
                         | LitInt n1, LitInt n2 =>
                             Some $ LitInt (n1 ≪ n2)
                         | _, _ => None
                         end
                        )
    | ShiftROp' x1 x2 => (i ← urn_subst f x1;
                         j ← urn_subst f x2;
                         match i, j with
                         | LitInt n1, LitInt n2 =>
                             Some $ LitInt (n1 ≫ n2)
                         | _, _ => None
                         end
                        )
    | LeOp' x1 x2 => (i ← urn_subst f x1;
                     j ← urn_subst f x2;
                     match i, j with
                     | LitInt n1, LitInt n2 =>
                         Some $ LitBool (bool_decide(n1 ≤ n2)%Z)
                     | _, _ => None
                     end
                    )
    | LtOp' x1 x2 => (i ← urn_subst f x1;
                     j ← urn_subst f x2;
                     match i, j with
                     | LitInt n1, LitInt n2 =>
                         Some $ LitBool (bool_decide (n1 < n2)%Z)
                     | _, _ => None
                     end
                    )
    | EqOp' x1 x2 => (i ← urn_subst f x1;
                     j ← urn_subst f x2;
                     Some $ LitBool (bool_decide (i=j))
                    )
    | OffsetOp' x1 x2 => (i ← urn_subst f x1;
                         j ← urn_subst f x2;
                         match i, j with
                         | LitLoc l1, LitInt n2 =>
                             Some $ LitLoc (l1 +ₗ n2)
                         | _, _ => None
                         end
                        )
    end.

  Definition is_valid_urn (u: urn) :=
    match u with
    | urn_unif s => s ≠ ∅
    | urn_laplace num den l => (0<IZR num/IZR den)
    end.

  Global Instance is_valid_urn_dec u : Decision (is_valid_urn u).
  Proof.
    destruct u; simpl; first solve_decision.
    apply make_decision.
  Qed. 
  
  Definition urns_support_set (m:gmap loc urn):=
    dom (filter (λ '(k, u), is_valid_urn u) m).

  Lemma elem_of_urns_support_set x m:
    x ∈ urns_support_set m <-> (∃ s, m!!x = Some s /\ is_valid_urn s).
  Proof.
    rewrite /urns_support_set.
    rewrite elem_of_dom.
    split; intros [a Ha].
    - apply map_lookup_filter_Some in Ha.
      naive_solver.
    - eexists _.
      apply map_lookup_filter_Some.
      naive_solver.
  Qed.

  Lemma urns_support_set_insert_subset m u s:
    is_valid_urn s ->
    urns_support_set m ⊆ urns_support_set (<[u:=s]> m).
  Proof.
    intros.
    rewrite /urns_support_set.
    intros x.
    repeat rewrite elem_of_filter.
    rewrite map_filter_insert_True; last done.
    rewrite dom_insert_L.
    set_solver.
  Qed. 
  
  (* Definition urns_subst_f_num (m:gmap loc urn):= *)
  (*   map_fold (λ _ u n, *)
  (*               if bool_decide (u=∅) *)
  (*               then n else size u * n *)
  (*     )%nat 1%nat m. *)

  (* Lemma urns_subst_f_num_insert m u s: *)
  (*   s≠∅-> *)
  (*   m!!u=None -> *)
  (*   urns_subst_f_num (<[u:=s]> m) = *)
  (*   (urns_subst_f_num m * size s)%nat. *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite /urns_subst_f_num. *)
  (*   rewrite map_fold_insert; last done. *)
  (*   - rewrite bool_decide_eq_false_2; last done. *)
  (*     lia. *)
  (*   - intros. *)
  (*     repeat case_bool_decide; lia. *)
  (* Qed.   *)

  Fixpoint base_lit_support_set bl : gset loc :=
    match bl with
    | LitInt n => ∅
    | LitBool b => ∅
    | LitUnit => ∅
    | LitLoc l => ∅
    | LitLbl l => {[l]}
    | NegOp' x => base_lit_support_set x
    | MinusUnOp' x => base_lit_support_set x
    | PlusOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | MinusOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | MultOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | QuotOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | RemOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | AndOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | OrOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | XorOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | ShiftLOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | ShiftROp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | LeOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | LtOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | EqOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    | OffsetOp' x1 x2 => base_lit_support_set x1 ∪ base_lit_support_set x2
    end.

  Definition urns_f_valid (m : gmap loc urn) (f:gmap loc Z) :=
    forall l, match (m!!l), (f!!l)with
         | Some u, Some _ => is_valid_urn u
         | Some u, None => ¬ is_valid_urn u
         | None, Some _ => False
         | None, None => True
         end.
  
  Lemma urns_f_valid_support m f:
    urns_f_valid m f -> urns_support_set m = dom f.
  Proof.
    rewrite /urns_f_valid.
    intros H.
    apply set_eq.
    intros l.
    rewrite elem_of_dom.
    rewrite elem_of_urns_support_set.
    split.
    - intros [?[]].
      pose proof H l.
      repeat case_match; destruct!/=; naive_solver.
    - intros [? H'].
      pose proof H l as H.
      rewrite H' in H.
      repeat case_match; naive_solver.
  Qed.

  Global Instance urns_f_valid_dec m f : Decision (urns_f_valid m f). 
  Proof.
    replace (urns_f_valid _ _) with
      (urns_support_set m = dom f /\
       map_Forall (λ l x,
            match m!!l with
            | Some u => is_valid_urn u
            | None => False
             end
         ) f); last (intros; apply propositional_extensionality).
    - apply and_dec; first solve_decision.
      apply map_Forall_dec.
      intros ??.
      repeat case_match; solve_decision.
    - rewrite /urns_f_valid. split.
      + rewrite /urns_support_set.
        intros [H1 H2].
        intros l.
        rewrite map_Forall_lookup in H2.
        pose proof H2 l as H2.
        case_match.
        * case_match; first naive_solver.
          intro.
          assert (l∈ dom f) as H4.
          { rewrite -H1.
            rewrite elem_of_dom.
            by setoid_rewrite map_lookup_filter_Some_2.
          }
          apply elem_of_dom in H4 as []. naive_solver.
        * case_match; naive_solver.
      + intros.
        split.
        * apply set_eq.
          intros l.
          rewrite elem_of_urns_support_set elem_of_dom.
          pose proof H l as H.
          repeat case_match; split; intros H'; destruct!/=; try naive_solver; by destruct H'.
        * apply map_Forall_lookup.
          intros l x.
          pose proof H l as H.
          intros H'. by rewrite H' in H.
  Qed. 

  (* We always assume (urns_f_valid m f) for this function *)

  Definition urns_f_distr_compute u z:=
    match u with
    | urn_unif s => if bool_decide (z∈s) then /size(s) else 0
    | urn_laplace num den l =>
        (match decide (0 < IZR num / IZR den) with
         | left εpos => laplace_rat num den l εpos z
         | right _ => 0 (* not possible *)
         end)   
    end.
  
  Lemma urns_f_distr_compute_pos u x : 0<=urns_f_distr_compute u x.
  Proof.
    rewrite /urns_f_distr_compute.
    case_match.
    - case_bool_decide; last done.
      rewrite -Rdiv_1_l.
      apply Rdiv_INR_ge_0.
    - by case_match.
  Qed.

  Lemma urns_f_distr_compute_le_1 x: SeriesC (urns_f_distr_compute x) <= 1.
  Proof.
    rewrite /urns_f_distr_compute.
    case_match; subst.
    - erewrite (SeriesC_ext _ (λ z, if bool_decide (z∈elements s) then /size s else 0)).
      + rewrite SeriesC_list_2.
        * rewrite length_elements_size_gset.
          destruct (length (_)) as [|n].
          -- vm_compute. lra.
          -- replace (_*_) with (S n / S n) by lra.
             rewrite Rdiv_diag; first done.
             apply not_0_INR.
             lia.
        * apply NoDup_elements.
      + intros.
        repeat case_bool_decide; set_solver.
    - case_match; last rewrite SeriesC_0; try (intros; lra); done.
  Qed. 

  Lemma ex_seriesC_urns_f_distr_compute x: ex_seriesC (urns_f_distr_compute x).
  Proof.
    rewrite /urns_f_distr_compute.
    case_match.
    - subst.
      apply (ex_seriesC_ext  (λ z, if bool_decide (z∈elements s) then /size s else 0)); last apply ex_seriesC_list.
      intros.
      repeat case_bool_decide; set_solver.
    - case_match; try done.
      apply ex_seriesC_0.
  Qed.

  Program Definition urns_f_distr_compute_distr u := MkDistr (urns_f_distr_compute u) _ _ _.
  Next Obligation.
    apply urns_f_distr_compute_pos.
  Qed.
  Next Obligation.
    apply ex_seriesC_urns_f_distr_compute.
  Qed.
  Next Obligation.
    apply urns_f_distr_compute_le_1.
  Qed.  


  Lemma urns_f_distr_compute_distr_mass u:
    is_valid_urn u ->
    SeriesC (urns_f_distr_compute u) = 1.
  Proof.
    intros H.
    rewrite /urns_f_distr_compute.
    unfold is_valid_urn in *.
    case_match.
    - erewrite (SeriesC_ext _ (λ z, if bool_decide (z ∈elements s) then /size s else 0)).
      + rewrite SeriesC_list_2; last apply NoDup_elements.
        rewrite -length_elements_size_gset.
        replace (_*_) with ((size s)/ (size s)) by lra.
        apply Rdiv_diag.
        apply not_0_INR.
        rewrite size_non_empty_iff.
        set_solver.
      + intros.
        repeat case_bool_decide; set_solver.
    - case_match eqn:Hn.
      + apply laplace_mass.
      + done.
  Qed. 

        
  Definition urns_f_distr_f1 (m: gmap loc urn):=
    (λ lo z r, r*match m!!lo with
                | None => 0 (* Not possible *)
                | Some u => urns_f_distr_compute u z
                end
    ).
  
  Definition urns_f_distr_f2 (m: gmap loc urn) (f:gmap loc Z) :=
    map_fold (urns_f_distr_f1 m) 1 f.

  Lemma urns_f_distr_f2_pos m x : 0<=urns_f_distr_f2 m x.
  Proof.
    rewrite /urns_f_distr_f2.
    induction x as [|i x m' Hx Hfirst] using map_first_key_ind; first (vm_compute; lra).
    rewrite map_fold_insert_first_key; try done.
    rewrite {1}/urns_f_distr_f1.
    case_match; last real_solver.
    apply Rmult_le_pos; first done.
    apply urns_f_distr_compute_pos.
  Qed. 
  
  Lemma urns_f_distr_f2_agree m1 m2 f :
    (∀ x, x ∈ dom f-> m1!!x = m2!!x) ->
    urns_f_distr_f2 m1 f = urns_f_distr_f2 m2 f.
  Proof.
    revert m1 m2.
    induction f as [|i x m Hx Hfirst] using map_first_key_ind; first by vm_compute.
    intros ? m2 H.
    unfold urns_f_distr_f2 in *.
    rewrite !map_fold_insert_first_key; [|done..].
    erewrite (IHf _ m2); last first.
    { intros. apply H. set_solver. }
    rewrite {1 3}/urns_f_distr_f1.
    by rewrite H; last set_solver.
  Qed. 

  Lemma urns_f_distr_f2_insert l u m f z:
    urns_f_valid (<[l:=u]> m) f ->
    f !! l = Some z ->
    is_valid_urn u -> 
    urns_f_distr_f2 (<[l:=u]> m) f = urns_f_distr_f2 m (delete l f) * urns_f_distr_compute u z.
  Proof.
    rewrite {1}/urns_f_distr_f2.
    intros H1 H2 H3.
    replace (f) with (<[l:=z]> (delete l f)) at 1; last by rewrite insert_delete.
    rewrite map_fold_insert; last by simplify_map_eq.
    - rewrite -/(urns_f_distr_f2 _ (delete _ _)).
      erewrite (urns_f_distr_f2_agree _ m); last first.
      { intros x. rewrite elem_of_dom. intros []. simplify_map_eq.
        destruct (decide (x=l)); subst; by simplify_map_eq. }
      rewrite /urns_f_distr_f1.
      by simplify_map_eq.
    - intros.
      rewrite /urns_f_distr_f1.
      lra.
  Qed.
  
  (* Lemma urns_f_distr_f_insert (m:gmap loc urn) i u: *)
  (*   m!!i=None -> *)
  (*     urns_f_distr_f (<[i:=u]> m) = *)
  (*   (λ f, match f!!i with *)
  (*         | Some z => *)
  (*             match u with *)
  (*             | urn_unif s => *)
  (*                 if bool_decide (z∈s) then *)
  (*                   urns_f_distr_f m (delete i f) / size (s) *)
  (*                 else 0 *)
  (*             | urn_laplace num den l => *)
  (*                 (match decide (0 < IZR num / IZR den) with *)
  (*                  | left εpos => urns_f_distr_f m (delete i f) * *)
  (*                                  laplace_rat num den l εpos z *)
  (*                  | right _ => 0  *)
  (*                  end) *)
  (*             end *)
                
  (*         | None => *)
  (*             if bool_decide (is_valid_urn u) *)
  (*             then 0 *)
  (*             else urns_f_distr_f m f *)
  (*         end *)
  (*   ). *)
  (* Proof. *)
  (*   intros Hnone Hfirst. *)
  (*   extensionality f. *)
  (*   rewrite {1}/urns_f_distr_f. *)
  (*   case_bool_decide as H'. *)
  (*   - rewrite map_fold_insert_first_key; try done. *)
  (*     case_match eqn: H''; subst. *)
  (*     + pose proof H' i. *)
  (*       case_match. *)
  (*       * simplify_map_eq. *)
  (*         case_bool_decide; last set_solver. *)
  (*         rewrite bool_decide_eq_true_2; last done. *)
  (*         f_equal. *)
  (*         rewrite /urns_f_distr_f. *)
  (*         rewrite bool_decide_eq_true_2; last first. *)
  (*         -- intros l. *)
  (*            case_match eqn:H2. *)
  (*            ++ apply lookup_delete_Some in H2. *)
  (*               destruct!/=. *)
  (*               pose proof H' l. *)
  (*               case_match; destruct!/=. *)
  (*               by simplify_map_eq. *)
  (*            ++ apply lookup_delete_None in H2. *)
  (*               pose proof H' l. *)
  (*               case_match; destruct!/=; by simplify_map_eq. *)
  (*         -- clear -Hnone. *)
  (*            induction m as [|i' x m Hx Hfirst] using map_first_key_ind; first by vm_compute. *)
  (*            rewrite !map_fold_insert_first_key; try done. *)
  (*            case_match. *)
  (*            ++ case_bool_decide. *)
  (*               ** f_equal. *)
  (*                  apply IHm. *)
  (*                  simplify_map_eq. *)
  (*                  apply lookup_insert_None in Hnone. naive_solver. *)
  (*               ** apply IHm. *)
  (*                  simplify_map_eq. *)
  (*                  apply lookup_insert_None in Hnone. naive_solver. *)
  (*            ++ replace (f!! _) with (delete i f !! i') at 1. *)
  (*               ** case_match; try done. *)
  (*                  case_match; try done. *)
  (*                  f_equal. *)
  (*                  apply IHm. *)
  (*                  apply lookup_insert_None in Hnone. naive_solver. *)
  (*               ** rewrite lookup_delete_ne; first done. *)
  (*                  apply lookup_insert_None in Hnone. naive_solver. *)
  (*       * simplify_map_eq. *)
  (*         rewrite bool_decide_eq_false_2; last naive_solver. *)
  (*         rewrite /urns_f_distr_f. *)
  (*         rewrite bool_decide_eq_false_2; try done. *)
  (*         rewrite bool_decide_eq_true_2; first done. *)
  (*         intros l. *)
  (*         pose proof H' l. *)
  (*         case_match. *)
  (*         -- case_match; by simplify_map_eq. *)
  (*         -- do 2 case_match; try done; by simplify_map_eq. *)
  (*     + case_match; last first. *)
  (*       * rewrite bool_decide_eq_true_2; first done. *)
  (*         admit. *)
  (*       * simpl. case_match; try done. *)
  (*         f_equal. admit.  *)
  (*   - admit. *)
  (* Admitted. *)
  
  (* Definition set_urns_f_valid (m:gmap loc urn) : gset (gmap loc nat):= *)
  (*   map_fold (λ k u l, *)
  (*               if bool_decide (u=∅) *)
  (*               then l *)
  (*               else *)
  (*                 set_bind (λ a, set_bind (λ b, {[<[k:=a]> b]}) l) u *)
  (*     ) {[∅]} m. *)
             
  (* Lemma set_urns_f_nonempty m: *)
  (*   (0< size (set_urns_f_valid m))%nat. *)
  (* Proof. *)
  (*   rewrite /set_urns_f_valid. apply (map_fold_weak_ind (λ x _, 0<size x)%nat). *)
  (*   { rewrite size_singleton. lia. } *)
  (*   intros ? x ? r ??. *)
  (*   case_bool_decide; first done. *)
  (*   rewrite /set_bind. *)
  (*   destruct (elements x) eqn:Heqn. *)
  (*   { apply elements_empty_inv in Heqn. apply leibniz_equiv in Heqn. naive_solver. } *)
  (*   simpl. *)
  (*   eapply (Nat.lt_le_trans _ (size _)); last first. *)
  (*   - apply subseteq_size. *)
  (*     apply union_subseteq_l. *)
  (*   - destruct (elements r) eqn:Heqn'. *)
  (*     { assert (size r = 0)%nat; last lia. *)
  (*       apply elements_empty_inv in Heqn'. apply leibniz_equiv in Heqn'. *)
  (*       subst. set_solver. *)
  (*     } *)
  (*     simpl.  *)
  (*     eapply (Nat.lt_le_trans _ (size _)); last first. *)
  (*     + apply subseteq_size. *)
  (*       apply union_subseteq_l. *)
  (*     + rewrite size_singleton. *)
  (*       lia. *)
  (* Qed. *)

  (* Lemma elem_of_set_urns_f_valid m f : *)
  (*     f ∈set_urns_f_valid m <-> *)
  (*       urns_f_valid m f . *)
  (* Proof. *)
  (*   symmetry. *)
  (*   rewrite /set_urns_f_valid. *)
  (*   revert f. *)
  (*   apply (map_fold_weak_ind (λ x m, forall f, urns_f_valid m f <-> f ∈ x)). *)
  (*   - intros f. rewrite elem_of_singleton. *)
  (*     split. *)
  (*     + rewrite /urns_f_valid. *)
  (*       intros. *)
  (*       apply map_eq. *)
  (*       intros i. *)
  (*       simplify_map_eq. *)
  (*       pose proof H i as H'. *)
  (*       case_match eqn:Heqn; last done. *)
  (*       destruct H' as [?[H0 ?]]. *)
  (*       simplify_map_eq. *)
  (*     + intros ->. rewrite /urns_f_valid. intros. rewrite !lookup_empty. *)
  (*       naive_solver. *)
  (*   - intros i ???? H0 f. split. *)
  (*     + intros H'. *)
  (*       case_bool_decide as H1. *)
  (*       * subst. *)
  (*         apply H0. *)
  (*         rewrite /urns_f_valid in H' *. *)
  (*         intros l. *)
  (*         pose proof H' l as H'. *)
  (*         case_match. *)
  (*         -- destruct H' as [? [K1 K2]]. *)
  (*            destruct (decide (i=l)). *)
  (*            ++ subst. *)
  (*               simplify_map_eq. set_solver. *)
  (*            ++ simplify_map_eq. *)
  (*               naive_solver. *)
  (*         -- destruct (decide (i=l)); simplify_map_eq; naive_solver. *)
  (*       * rewrite elem_of_set_bind. *)
  (*         destruct (f!!i) as [n'|] eqn :Hf. *)
  (*         -- exists n'. *)
  (*            rewrite elem_of_set_bind. *)
  (*            split; last first.  *)
  (*            ++ eexists (delete i f). *)
  (*               split; last first.  *)
  (*               ** rewrite insert_delete; [set_solver|done]. *)
  (*               ** apply H0. *)
  (*                  intros i'. *)
  (*                  destruct (decide (i=i')); simplify_map_eq; first naive_solver. *)
  (*                  pose proof H' i'. *)
  (*                  by simplify_map_eq. *)
  (*            ++ pose proof H' i as H2. *)
  (*               rewrite Hf in H2. *)
  (*               destruct!/=. by simplify_map_eq. *)
  (*         -- exfalso. *)
  (*            pose proof H' i as H2. *)
  (*            rewrite Hf in H2. *)
  (*            simplify_map_eq. naive_solver. *)
  (*     + case_bool_decide. *)
  (*       * subst. rewrite -H0. *)
  (*         rewrite /urns_f_valid. *)
  (*         intros H' l. *)
  (*         pose proof H' l as H'. *)
  (*         case_match; destruct (decide (i=l)); subst; simplify_map_eq; destruct!/=; naive_solver. *)
  (*       * rewrite elem_of_set_bind. *)
  (*         setoid_rewrite elem_of_set_bind. *)
  (*         intros [y [H4[y' [H3 H2]]]]. *)
  (*         rewrite - H0 in H3. *)
  (*         apply elem_of_singleton in H2. *)
  (*         subst.  *)
  (*         intros l. *)
  (*         pose proof H3 l as H5. *)
  (*         destruct (decide (i=l)); simplify_map_eq; naive_solver. *)
  (* Qed.  *)
  (* Global Instance urn_f_valid_dec m f: Decision (urns_f_valid m f). *)
  (* Proof. *)
  (*   replace (urns_f_valid _ _) with (f∈set_urns_f_valid m); first apply _. *)
  (*   apply propositional_extensionality. *)
  (*   by rewrite elem_of_set_urns_f_valid. *)
  (* Qed. *)

  (* Lemma urns_f_valid_exists m: *)
  (*   ∃ f, urns_f_valid m f. *)
  (* Proof. *)
  (*   setoid_rewrite <-elem_of_set_urns_f_valid. *)
  (*   apply size_pos_elem_of. *)
  (*   apply set_urns_f_nonempty. *)
  (* Qed.  *)
  
  (* Lemma size_set_urns_f m: *)
  (*   size (set_urns_f_valid m) = urns_subst_f_num m. *)
  (* Proof. *)
  (*   revert m. *)
  (*   apply map_ind; first set_solver. *)
  (*   intros i x m Hnone Hind. *)
  (*   rewrite /set_urns_f_valid/urns_subst_f_num.  *)
  (*   rewrite !map_fold_insert; try done; last first. *)
  (*   - intros. repeat case_bool_decide; try done. *)
  (*     apply set_eq. *)
  (*     intros. repeat setoid_rewrite elem_of_set_bind. *)
  (*     split; intros; destruct!/=; set_unfold; subst; eexists _; split; first done; try done; rewrite insert_commute; naive_solver. *)
  (*   - intros. repeat case_bool_decide; try done. *)
  (*     lia.  *)
  (*   - case_bool_decide as H; first done. *)
  (*     rewrite /urns_subst_f_num in Hind. *)
  (*     rewrite -Hind. *)
  (*     rewrite -/(set_urns_f_valid m). *)
  (*     rewrite (size_set_bind_const _ _ (size (set_urns_f_valid m))); first done. *)
  (*     + intros. *)
  (*       erewrite (size_set_bind_const); first by erewrite Nat.mul_1_r. *)
  (*       * intros. apply size_singleton. *)
  (*       * intros ??. *)
  (*         rewrite !elem_of_set_urns_f_valid. *)
  (*         intros H1 H2 H3. *)
  (*         set_unfold. *)
  (*         intros ? -> ?. *)
  (*         apply H3. *)
  (*         apply map_eq. *)
  (*         intros l. *)
  (*         destruct (decide (i=l)). *)
  (*         -- pose proof H1 l as H1. *)
  (*            pose proof H2 l as H2. *)
  (*            repeat case_match; by destruct!/=. *)
  (*         -- apply (f_equal (λ x, x!!l)) in H4. by simplify_map_eq. *)
  (*     + intros. *)
  (*       rewrite /set_bind. *)
  (*       set_unfold. *)
  (*       setoid_rewrite elem_of_union_list. *)
  (*       setoid_rewrite elem_of_list_fmap. *)
  (*       setoid_rewrite elem_of_elements. *)
  (*       intros. *)
  (*       destruct!/=. *)
  (*       set_unfold. *)
  (*       subst. *)
  (*       rename select (<[_:=_]> _ = _) into H'. *)
  (*       apply (f_equal (λ x,x!!i)) in H'. *)
  (*       simplify_map_eq. *)
  (* Qed. *)

  
  (* Lemma set_urns_f_valid_singleton m: *)
  (*   map_Forall (λ _ v, v= ∅ \/ size v = 1)%nat m-> *)
  (*   size (set_urns_f_valid m) = 1%nat. *)
  (* Proof. *)
  (*   rewrite size_set_urns_f. *)
  (*   revert m. *)
  (*   apply (map_ind (λ m, _ -> _)); first by rewrite /urns_subst_f_num map_fold_empty. *)
  (*   intros i x m Hnone IH H. *)
  (*   rewrite /urns_subst_f_num. *)
  (*   rewrite map_fold_insert_L; last done; last first. *)
  (*   { intros. *)
  (*     repeat case_bool_decide; lia.  *)
  (*   } *)
  (*   rewrite map_Forall_insert in H; last done. *)
  (*   destruct H as [H1 H2]. *)
  (*   destruct!/=. *)
  (*   - rewrite bool_decide_eq_true_2; naive_solver. *)
  (*   - rewrite bool_decide_eq_false_2; last (intros ->; set_solver). *)
  (*     rewrite H1. setoid_rewrite IH; [lia|done]. *)
  (* Qed. *)
  
  (** We define a distribution, where given a urn map, 
      produces a distribution of urn subst functions *)



  Definition urns_f_distr_f3 m:= (λ f, if bool_decide (urns_f_valid m f)
                                       then urns_f_distr_f2 m f else 0).

  Lemma urns_f_distr_f3_pos m x : 0<=urns_f_distr_f3 m x.
  Proof.
    rewrite /urns_f_distr_f3.
    case_bool_decide; last done.
    apply urns_f_distr_f2_pos.
  Qed.
  
  Lemma urns_f_distr_f3_insert m l u:
    (match m!!l with
     | None => True
     | Some u' => ¬ is_valid_urn u'
    end) ->
    is_valid_urn u ->
    urns_f_distr_f3 (<[l:=u]> m) =
    (λ f, match f!!l with
          | None => 0
          | Some z =>
              urns_f_distr_f3 m (delete l f) * (urns_f_distr_compute u z)
          end
    )
  .
  Proof.
    intros.
    extensionality f.
    destruct (decide (urns_f_valid (<[l:=u]> m) f)) as [Hn|Hn]; last first.
    { trans 0.
      - rewrite /urns_f_distr_f3.
        case_bool_decide; naive_solver.
      - symmetry.
        destruct (f!!l) eqn:Heqn; last done.
        apply Rmult_eq_0_compat_r.
        rewrite /urns_f_distr_f3.
        rewrite bool_decide_eq_false_2; first done.
        intros Hcontra.
        apply Hn.
        intros l'.
        pose proof Hcontra l'.
        destruct (decide (l=l')); subst; by simplify_map_eq. 
    }
    pose proof Hn l as Hn'.
    simplify_map_eq.
    case_match; last naive_solver.
    rewrite /urns_f_distr_f3.
    rewrite bool_decide_eq_true_2; last done.
    rewrite bool_decide_eq_true_2; last first. 
    { intros l'.
      pose proof Hn l'.
      destruct (decide (l=l')); subst; by simplify_map_eq. 
    }
    by apply urns_f_distr_f2_insert.
  Qed.
  
  Lemma urns_f_distr_f3_insert_no_change m l u:
    (match m!!l with
     | None => True
     | Some u' => ¬ is_valid_urn u'
    end) ->
    ¬ is_valid_urn u ->
    urns_f_distr_f3 (<[l:=u]> m) = urns_f_distr_f3 m.
  Proof.
    rewrite /urns_f_distr_f3.
    intros H1 H2.
    extensionality f.
    case_bool_decide as H0.
    * rewrite bool_decide_eq_true_2.
      -- apply urns_f_distr_f2_agree.
         apply urns_f_valid_support in H0.
         rewrite -H0.
         intros l'.
         rewrite elem_of_urns_support_set.
         intros.
         destruct!/=.
         assert (l≠l'); last by simplify_map_eq.
         intros ->.
         by simplify_map_eq.
      -- intros l'.
         pose proof H0 l'.
         destruct (decide (l'=l)); subst; try by simplify_map_eq.
         subst.
         simplify_map_eq.
         case_match; first done.
         by case_match.
    * rewrite bool_decide_eq_false_2; first done.
      intros Hcontra; apply H0.
      intros l'.
      pose proof Hcontra l'.
      destruct (decide (l'=l)); subst; try by simplify_map_eq.
      subst.
      simplify_map_eq.
      case_match; case_match; naive_solver.
  Qed. 
  
  
  Lemma ex_seriesC_urns_f_distr_f3 m: ex_seriesC (urns_f_distr_f3 m).
  Proof.
    induction m as [|i x m Hx Hfirst] using map_first_key_ind.
    - eapply (ex_seriesC_ext (λ f, if bool_decide (f=∅) then 1 else _)); last apply ex_seriesC_singleton.
      intros.
      rewrite /urns_f_distr_f3.
      case_bool_decide as H0.
      + rewrite bool_decide_eq_true_2.
        * subst.
          rewrite /urns_f_valid.
          intros.
          repeat case_match; set_solver.
        * subst. intros ?.
          repeat case_match; set_solver.
      + rewrite bool_decide_eq_false_2; first done.
        intros ?.
        apply map_choose in H0.
        destruct!/=.
        rewrite /urns_f_valid in H.
        epose proof H _ as H1.
        erewrite H0 in H1.
        case_match; set_solver.
    - destruct (decide (is_valid_urn x)) as [H|H].
      + rewrite urns_f_distr_f3_insert; last first.
        * done.
        * by rewrite Hx.
        * apply ex_seriesC_gmap_insert.
          -- intros. apply urns_f_distr_f3_pos.
          -- apply urns_f_distr_compute_pos.
          -- done.
          -- apply ex_seriesC_urns_f_distr_compute. 
      + eapply ex_seriesC_ext; last done.
        simpl.
        intros f.
        rewrite urns_f_distr_f3_insert_no_change; try done.
        by rewrite Hx.
  Qed. 
  
  Program Definition urns_f_distr m := MkDistr (urns_f_distr_f3 m) _ _ _.
  Next Obligation.
    intros m f. simpl.
    rewrite /urns_f_distr_f3.
    case_bool_decide; last done.
    rewrite /urns_f_distr_f2.
    clear.
    induction f using map_first_key_ind; first (vm_compute; lra).
    rewrite map_fold_insert_first_key; [|done..].
    rewrite {1}/urns_f_distr_f1.
    rewrite /urns_f_distr_compute.
    case_match; last lra.
    case_match; first case_match; [|real_solver..].
    rewrite -Rdiv_1_l.
    apply Rmult_le_pos; first done.
    apply Rdiv_INR_ge_0.
  Qed.
  Next Obligation.
    apply ex_seriesC_urns_f_distr_f3.
  Qed. 
  Next Obligation.
    intros m.
    induction m as [|i x m Hx Hfirst] using map_first_key_ind.
    - erewrite (SeriesC_ext _ (λ f, if bool_decide (f=∅) then 1 else _)); first by erewrite SeriesC_singleton.
      intros.
      rewrite /urns_f_distr_f3.
      symmetry. 
      case_bool_decide as H0.
      + rewrite bool_decide_eq_true_2.
        * subst.
          rewrite /urns_f_valid.
          intros.
          repeat case_match; set_solver.
        * subst. intros ?.
          repeat case_match; set_solver.
      + rewrite bool_decide_eq_false_2; first done.
        intros ?.
        apply map_choose in H0.
        destruct!/=.
        rewrite /urns_f_valid in H.
        epose proof H _ as H1.
        erewrite H0 in H1.
        case_match; set_solver.
    - destruct (decide (is_valid_urn x)) as [H|H].
      + rewrite urns_f_distr_f3_insert; last first.
        * done.
        * by rewrite Hx.
        * apply SeriesC_gmap_insert_le_1.
          -- apply urns_f_distr_f3_pos.
          -- apply urns_f_distr_compute_pos.
          -- apply ex_seriesC_urns_f_distr_f3.
          -- apply ex_seriesC_urns_f_distr_compute.
          -- done.
          -- apply urns_f_distr_compute_le_1.
      + etrans; last exact.
        right.
        apply SeriesC_ext.
        intros f.
        rewrite urns_f_distr_f3_insert_no_change; try done.
        by rewrite Hx.
  Qed.

  Lemma urns_f_distr_empty :
    urns_f_distr ∅ = dret ∅.
  Proof.
    apply distr_ext.
    intros.
    destruct (decide(a = ∅)) as [|Hn].
    { subst.
      rewrite dret_1_1; last done.
      rewrite /urns_f_distr/pmf/=.
      rewrite /urns_f_distr_f3.
      rewrite bool_decide_eq_true_2.
      - rewrite /urns_f_distr_f2.
        by vm_compute.
      - intros ?. repeat case_match; set_solver.
    }
    rewrite dret_0; last done.
    rewrite /urns_f_distr/pmf.
    rewrite /urns_f_distr_f3.
    rewrite bool_decide_eq_false_2; first done.
    apply map_choose in Hn.
    destruct Hn as [i []].
    intros Hcontra.
    pose proof Hcontra i.
    repeat case_match; set_solver.
  Qed.

  Lemma urns_f_distr_pos m f:
    urns_f_distr m f > 0 -> urns_f_valid m f.
  Proof.
    rewrite /urns_f_distr/pmf/urns_f_distr_f3.
    case_bool_decide; [done|lra].
  Qed. 

  Lemma urns_f_distr_insert m l u:
    (match m!!l with
     | None => True
     | Some u' => ¬ is_valid_urn u'
     end) ->
    is_valid_urn u ->
    urns_f_distr (<[l:=u]> m) =
    dbind
      (λ f,
         dbind (λ z, dret (<[l:=z]> f)) (urns_f_distr_compute_distr u)
      )
      (urns_f_distr m).
  Proof.
    intros H1 H2.
    apply distr_ext.
    intros a.
    rewrite {1}/urns_f_distr{1}/pmf.
    rewrite urns_f_distr_f3_insert; try done.
    destruct (a!!_) eqn:Ha.
    - rewrite {1}/dbind{1}/dbind_pmf{1 }/pmf.
      rewrite /dbind/dbind_pmf{2}/pmf.
      erewrite (SeriesC_ext _ (λ a0, if bool_decide (a0 = (delete l a)) then _ else 0)); last first.
      + intros n.
        case_bool_decide as H; first done.
        destruct (pmf_pos (urns_f_distr m) n) as [Hineq|<-]; last lra.
        apply (Rlt_gt) in Hineq.
        apply urns_f_distr_pos in Hineq as Hineq'.
        apply Rmult_eq_0_compat_l.
        apply SeriesC_0.
        intros.
        apply Rmult_eq_0_compat_l.
        rewrite dret_0; first done.
        intros ->.
        apply H.
        simplify_map_eq.
        rewrite delete_insert; first done.
        pose proof Hineq' l.
        repeat case_match; naive_solver.
      + rewrite SeriesC_singleton_dependent.
        f_equal.
        erewrite (SeriesC_ext _ (λ a0, if bool_decide (a0 = (z)) then _ else 0)); last first.
        { intros. case_bool_decide; first done.
          rewrite dret_0; first lra.
          intros H'. rewrite H' in Ha. simplify_map_eq.
        }
        rewrite SeriesC_singleton_dependent.
        rewrite /urns_f_distr_compute_distr{1}/pmf dret_1_1; first lra.
        by rewrite insert_delete.
    - symmetry.
      apply: SeriesC_0.
      intros.
      apply Rmult_eq_0_compat_l.
      apply:SeriesC_0.
      intros.
      rewrite dret_0; first lra.
      intros ->.
      simplify_map_eq.
  Qed. 

  Lemma urns_f_distr_insert_no_change m l u:
    (match m!!l with
     | None => True
     | Some u' => ¬ is_valid_urn u'
    end) ->
    ¬ is_valid_urn u ->
    urns_f_distr (<[l:=u]> m) = urns_f_distr m.
  Proof.
    intros.
    apply distr_ext.
    intros.
    rewrite /urns_f_distr/pmf.
    by rewrite urns_f_distr_f3_insert_no_change.
  Qed. 
  
  Lemma urns_f_distr_mass m:
    SeriesC (urns_f_distr m) = 1.
  Proof.
    induction m as [|i x m Hx Hfirst] using map_first_key_ind.
    { rewrite urns_f_distr_empty.
      by rewrite dret_mass.
    }
    destruct (decide (is_valid_urn x)).
    - setoid_rewrite urns_f_distr_insert; try done; last by rewrite Hx.
      rewrite dbind_mass.
      erewrite SeriesC_ext; last first.
      + intros. rewrite dbind_mass.
        erewrite SeriesC_ext; last first.
        * intros. rewrite dret_mass. by rewrite Rmult_1_r.
        * rewrite urns_f_distr_compute_distr_mass; last done.
          by rewrite Rmult_1_r.
      + done. 
    - rewrite urns_f_distr_insert_no_change; try done.
      by case_match.
  Qed.

  Lemma urns_f_distr_witness m :
    ∃ f, urns_f_distr m f > 0.
  Proof.
    apply: SeriesC_gtz_ex; first done.
    rewrite urns_f_distr_mass.
    lra.
  Qed. 

  (** Not true *)
  (* Lemma urns_f_distr_pos m f: *)
  (*   urns_f_distr m f > 0 <-> urns_f_valid m f. *)
  (* Proof. *)
  (*   rewrite /urns_f_distr/pmf/=. *)
  (*   case_bool_decide; split; try done; try lra. *)
  (*   intros. *)
  (*   pose proof set_urns_f_nonempty m. *)
  (*   apply Rdiv_pos_pos; first lra. *)
  (*   apply Rlt_gt. *)
  (*   apply lt_0_INR. lia.  *)
  (* Qed. *)

  (** Not true *)
  (* Lemma urns_f_distr_eval m f : *)
  (*   urns_f_valid m f -> urns_f_distr m f = 1/(urns_subst_f_num m). *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite /urns_f_distr/pmf. *)
  (*   rewrite size_set_urns_f. *)
  (*   by rewrite bool_decide_eq_true_2. *)
  (* Qed. *)

  (** not true *)
  (* Lemma urns_f_distr_is_pos_eval m f : *)
  (*   urns_f_distr m f > 0 -> urns_f_distr m f = 1/(urns_subst_f_num m). *)
  (* Proof. *)
  (*   rewrite urns_f_distr_pos. *)
  (*   by intros ?%urns_f_distr_eval. *)
  (* Qed.  *)
  
  Lemma urns_f_distr_eval' m f :
    ¬ urns_f_valid m f -> urns_f_distr m f = 0.
  Proof.
    intros.
    rewrite /urns_f_distr/pmf/urns_f_distr_f3.
    case_bool_decide; naive_solver.
  Qed.
  
  (** Need to be restated *)
  (* Lemma urns_f_distr_insert m lis l N: *)
  (*   NoDup lis ->  *)
  (*   l∉dom m -> *)
  (*   length lis = S N -> *)
  (*   urns_f_distr (<[l:=list_to_set lis]> m) = *)
  (*   dbind (λ f, *)
  (*            dbind (λ n, *)
  (*                     match lis!!(fin_to_nat n) with *)
  (*                     | Some y => dret (<[l:=y]> f) *)
  (*                     | None => dzero *)
  (*                     end  *)
  (*              ) (dunifP (N)) *)
  (*     ) (urns_f_distr m). *)
  (* Proof. *)
  (*   intros Hnodup Hdom Hneq. *)
  (*   apply distr_ext. *)
  (*   intros f. *)
  (*   destruct (pmf_pos (urns_f_distr (<[l:=list_to_set lis]> m)) f) as [H1|H1]; *)
  (*     destruct (pmf_pos (dbind *)
  (*                          (λ f0 : gmap loc nat, *)
  (*                             dbind *)
  (*                               (λ n, *)
  (*                                  match lis !! (fin_to_nat n) with *)
  (*                                  | Some y => dret (<[l:=y]> f0) *)
  (*                                  | None => dzero *)
  (*                                  end) (dunifP (N))) (urns_f_distr m)) f) as [H2|H2]. *)
  (*   - apply Rlt_gt in H1. *)
  (*     apply Rlt_gt in H2. *)
  (*     inv_distr. *)
  (*     case_match eqn:K1; inv_distr. *)
  (*     rewrite urns_f_distr_is_pos_eval; last done. *)
  (*     rewrite {1}/dbind{1}/dbind_pmf{1}/pmf. *)
  (*     rename select (gmap _ _) into f.  *)
  (*     rename select (fin _) into x'.  *)
  (*     erewrite (SeriesC_ext _ (λ a, if bool_decide (a = (delete l f)) then _ * _ else 0)); last first. *)
  (*     { intros f'. *)
  (*       case_bool_decide; first done. *)
  (*       apply pmf_mult_eq_0. *)
  (*       intros H'. *)
  (*       apply Rmult_eq_0_compat_l. *)
  (*       rewrite {1}/dbind{1}/dbind_pmf{1}/pmf. *)
  (*       erewrite (SeriesC_ext _ (λ a, if bool_decide (a = x') then _ * _ else 0)); last first. *)
  (*       - intros. case_bool_decide; first done. *)
  (*         apply pmf_mult_eq_0. intros H''. *)
  (*         apply Rmult_eq_0_compat_l. *)
  (*         case_match eqn:K2; last done. *)
  (*         apply dret_0. *)
  (*         intros Hcontra. *)
  (*         assert ( <[l:=n]> f !!l = <[l:=n1]> f'!!l) as Hcontra'. *)
  (*         + rewrite Hcontra; naive_solver. *)
  (*         + rewrite !lookup_insert in Hcontra'. *)
  (*           simplify_eq. *)
  (*           eapply NoDup_lookup in K1; last apply K2; naive_solver. *)
  (*       - rewrite SeriesC_singleton_dependent. *)
  (*         apply Rmult_eq_0_compat_l. *)
  (*         case_match; last done. *)
  (*         apply dret_0. *)
  (*         intros Hcontra. *)
  (*         simplify_eq. *)
  (*         apply H. *)
  (*         apply (f_equal (λ x, delete l x)) in Hcontra. *)
  (*         rewrite !delete_insert_delete in Hcontra. *)
  (*         rewrite (delete_notin f') in Hcontra; first done. *)
  (*         rewrite -not_elem_of_dom. *)
  (*         erewrite <-urns_f_valid_support; last by apply urns_f_distr_pos. *)
  (*         rewrite /urns_support_set. *)
  (*         rewrite elem_of_filter. *)
  (*         intros ?. *)
  (*         destruct!/=.  *)
  (*     } *)
  (*     rewrite SeriesC_singleton_dependent. *)
  (*     rewrite delete_notin; last first. *)
  (*     { rewrite -not_elem_of_dom. *)
  (*       erewrite <-urns_f_valid_support; last by apply urns_f_distr_pos. *)
  (*       rewrite /urns_support_set. *)
  (*       rewrite elem_of_filter. *)
  (*       intros ?. *)
  (*       destruct!/=. } *)
  (*     rewrite urns_f_distr_is_pos_eval; last done. *)
  (*     rewrite urns_subst_f_num_insert; last first. *)
  (*     { by rewrite -not_elem_of_dom. } *)
  (*     { destruct lis; set_solver. } *)
  (*     rewrite !Rdiv_1_l. *)
  (*     rewrite mult_INR. *)
  (*     rewrite Rinv_mult. *)
  (*     f_equal. *)
  (*     rewrite {1}/dbind{1}/dbind_pmf{1}/pmf. *)
  (*     erewrite (SeriesC_ext _ (λ a, if bool_decide (a = x') then _ else 0)); last first. *)
  (*     { intros. case_bool_decide; first done. *)
  (*       apply Rmult_eq_0_compat_l. *)
  (*       case_match; last done. *)
  (*       apply dret_0. *)
  (*       intros Hcontra. *)
  (*       apply H. *)
  (*       apply (f_equal (λ x, x!!l)) in Hcontra. *)
  (*       rewrite !lookup_insert in Hcontra. simplify_eq. *)
  (*       eapply NoDup_lookup in K1. *)
  (*       - by apply fin_to_nat_inj. *)
  (*       - done. *)
  (*       - done.  *)
  (*     } *)
  (*     rewrite SeriesC_singleton_dependent. *)
  (*     rewrite /dunifP/dunif{1}/pmf. *)
  (*     rewrite K1. *)
  (*     rewrite size_list_to_set; last done. *)
  (*     rewrite Hneq. *)
  (*     rewrite dret_1_1; [lra|done]. *)
  (*   - exfalso. *)
  (*     apply Rlt_gt in H1. *)
  (*     symmetry in H2. *)
  (*     assert (dbind *)
  (*        (λ f0 : gmap loc nat, *)
  (*           dbind *)
  (*             (λ n : fin (S N), *)
  (*                match lis !! (fin_to_nat n) with *)
  (*                | Some y => dret (<[l:=y]> f0) *)
  (*                | None => dzero *)
  (*                end) (dunifP N)) (urns_f_distr m) f > 0); last lra. *)
  (*     clear H2. *)
  (*     apply dbind_pos. *)
  (*     exists (delete l f). *)
  (*     apply urns_f_distr_pos in H1. *)
  (*     split; last first. *)
  (*     { apply urns_f_distr_pos. *)
  (*       rewrite /urns_f_valid in H1 *. *)
  (*       intros l'. *)
  (*       destruct (decide (l=l')). *)
  (*       - subst. *)
  (*         rewrite lookup_delete. *)
  (*         rewrite -not_elem_of_dom. naive_solver. *)
  (*       - rewrite lookup_delete_ne; last done. *)
  (*         pose proof H1 l'. *)
  (*         case_match; *)
  (*           by setoid_rewrite lookup_insert_ne in H. *)
  (*     } *)
  (*     apply dbind_pos. *)
  (*     rewrite /urns_f_valid in H1. *)
  (*     pose proof H1 l as K. *)
  (*     case_match; rewrite lookup_insert in K; destruct!/=; last first. *)
  (*     { destruct lis; set_solver. } *)
  (*     rename select (_∈_) into H2. *)
  (*     rewrite elem_of_list_to_set in H2. *)
  (*     rewrite elem_of_list_lookup in H2. *)
  (*     destruct H2 as [i H2]. *)
  (*     apply lookup_lt_Some in H2 as H3. *)
  (*     rewrite Hneq in H3. *)
  (*     exists (nat_to_fin H3). *)
  (*     rewrite fin_to_nat_to_fin. *)
  (*     rewrite H2. *)
  (*     rewrite insert_delete_insert. *)
  (*     rewrite insert_id; last done. *)
  (*     rewrite dret_1_1; last done. *)
  (*     split; first lra. *)
  (*     solve_distr. *)
  (*   - exfalso. *)
  (*     assert (urns_f_distr (<[l:=list_to_set lis]> m) f > 0); last lra. *)
  (*     clear H1. *)
  (*     apply Rlt_gt in H2. *)
  (*     inv_distr. *)
  (*     case_match; inv_distr. *)
  (*     apply urns_f_distr_pos. *)
  (*     rename select (urns_f_distr _ _ > 0) into H. *)
  (*     apply urns_f_distr_pos in H. *)
  (*     unfold urns_f_valid in H. *)
  (*     intros l'. *)
  (*     destruct (decide (l=l')). *)
  (*     + subst. rewrite !lookup_insert. *)
  (*       eexists _; split; first done. *)
  (*       rewrite elem_of_list_to_set. *)
  (*       apply elem_of_list_lookup. naive_solver. *)
  (*     + rewrite !lookup_insert_ne; try done. *)
  (*       naive_solver. *)
  (*   - by rewrite -H1 -H2. *)
  (* Qed.  *)
  
  Definition urn_subst_equal σ (bl bl':base_lit) :=
    ∀ f, urns_f_distr (urns σ) f >0 -> urn_subst f bl = Some bl'.

  Lemma urn_subst_equal_witness σ bl bl':
    urn_subst_equal σ bl bl' -> ∃ f, urns_f_distr (urns σ) f > 0 /\ urn_subst f bl = Some bl'.
  Proof.
    destruct (urns_f_distr_witness (urns σ)) as [f].
    intros H'.
    exists f.
    split; first done.
    by apply H'.
  Qed. 
  (*   rewrite /urn_subst_equal. *)
  (*   setoid_rewrite <-elem_of_set_urns_f_valid. *)
  (*   pose proof set_urns_f_nonempty (urns σ). *)
  (*   apply size_pos_elem_of in H. *)
  (*   destruct H as [f H]. *)
  (*   intros H'. pose proof H' _ H as H0. *)
  (*   naive_solver. *)
  (* Qed.  *)

  Lemma urn_subst_equal_unique σ bl bl1 bl2:
    urn_subst_equal σ bl bl1 -> urn_subst_equal σ bl bl2 -> bl1=bl2.
  Proof.
  Admitted. 
  (*   rewrite /urn_subst_equal. *)
  (*   intros H1 H2. *)
  (*   setoid_rewrite <-elem_of_set_urns_f_valid in H1. *)
  (*   setoid_rewrite <-elem_of_set_urns_f_valid in H2. *)
  (*   pose proof set_urns_f_nonempty ( (urns σ)) as H. *)
  (*   apply size_pos_elem_of in H as [x ?]. *)
  (*   epose proof H1 x H as H1. *)
  (*   epose proof H2 x H as H2. *)
  (*   rewrite H1 in H2. by simplify_eq. *)
  (* Qed. *)

  Lemma urn_subst_equal_epsilon_correct σ bl (e:∃ N : Z, urn_subst_equal σ bl (LitInt N)):
    urn_subst_equal σ bl (LitInt (epsilon e)).
  Proof.
    by pose proof epsilon_correct _ e as H.
  Qed.

  Lemma urn_subst_equal_epsilon_unique σ bl (N:Z) (e:∃ N : Z, urn_subst_equal σ bl (LitInt N)):
    urn_subst_equal σ bl (LitInt N) -> epsilon e = N.
  Proof.
    pose proof epsilon_correct _ e as H.
    intros H'.
    eapply urn_subst_equal_unique in H; last apply H'.
    by simplify_eq.
  Qed. 


  Definition is_simple_base_lit bl:=
    (match bl with
     | LitInt _ | LitBool _ |LitLoc _ | LitUnit => true
     | _ => false
     end).

  Lemma urn_subst_equal_obv σ bl:
    is_simple_base_lit bl = true -> urn_subst_equal σ bl bl.
  Proof.
    intros.
    intros ??.
    by destruct bl.
  Qed.

  Lemma urn_subst_is_simple f bl bl':
    urn_subst f bl = Some bl' -> is_simple_base_lit bl' = true.
  Proof.
    destruct bl; simpl; try (intros; by simplify_eq); repeat setoid_rewrite bind_Some; intros; destruct!/=; repeat case_match; by simplify_eq.
  Qed. 
    
  Lemma urn_subst_equal_is_simple σ bl bl':
    urn_subst_equal σ bl bl' -> is_simple_base_lit bl' = true.
  Proof.
    intros H.
    apply urn_subst_equal_witness in H.
    destruct!/=.
    by eapply urn_subst_is_simple.
  Qed.

  Lemma urn_subst_well_typed f bl bl':
    urn_subst f bl = Some bl' -> (∃ t, base_lit_type_check bl = Some t /\ base_lit_type_check bl' = Some t).
  Proof.
    revert bl'.
    induction bl as [| | | | |bl IH|bl IH |bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2]; intros bl'. 
    1,2,3,4: intros; simplify_eq; naive_solver.
    1: simpl; rewrite bind_Some; intros; destruct!/=; naive_solver.
    1, 2: simpl; setoid_rewrite bind_Some;
      intros [?[H ?]];
      apply IH in H;
      destruct!/=; case_match; simpl in *; simplify_eq;
       naive_solver.
    all: simpl; repeat setoid_rewrite bind_Some;
      intros [?[H1 [?[H2]]]];
      apply IH1 in H1; apply IH2 in H2;
      destruct!/=; repeat case_match; simpl in *; simplify_eq;
                               naive_solver.
  Qed.

  Lemma urn_subst_equal_well_typed σ bl bl':
    urn_subst_equal σ bl bl' -> (∃ t, base_lit_type_check bl = Some t /\ base_lit_type_check bl' = Some t).
  Proof.
    intros H.
    apply urn_subst_equal_witness in H.
    destruct!/=.
    by eapply urn_subst_well_typed.
  Qed. 

  Lemma urn_subst_f_support f bl bl':
    urn_subst f bl = Some bl' -> base_lit_support_set bl ⊆ dom f.
  Proof.
    revert bl'.
    induction bl; intros bl'; simpl.
    1, 2, 3, 4: set_solver.
    all: repeat setoid_rewrite bind_Some.
    { intros. destruct!/=. set_unfold; intros; rewrite elem_of_dom; naive_solver. }
    1, 2: intros; destruct!/=; naive_solver.
    all: rewrite union_subseteq; naive_solver.
  Qed.

  Lemma urn_subst_equal_support σ bl bl':
    urn_subst_equal σ bl bl' -> base_lit_support_set bl ⊆ urns_support_set (σ.(urns)).
  Proof.
    intros H.
    apply urn_subst_equal_witness in H.
    destruct H as [?[H1 H2]].
    apply urns_f_valid_support in H1.
    rewrite H1.
    by eapply urn_subst_f_support.
  Qed. 
    
  Lemma urn_subst_equal_obv_neq σ bl bl':
    (urn_subst_equal σ bl bl') -> bl≠bl' -> is_simple_base_lit bl = true ->False .
  Proof.
    intros H1 H H'. apply H. eapply urn_subst_equal_unique; last done.
    by apply urn_subst_equal_obv.
  Qed.

  Lemma urn_subst_equal_not_unique σ bl bl1 bl2:
    (urn_subst_equal σ bl bl1) -> (urn_subst_equal σ bl bl2)-> bl1≠bl2 -> False.
  Proof.
    intros H1 H2.
    eapply urn_subst_equal_unique in H1; last done.
    by subst.
  Qed.

  
  Lemma urn_subst_exists bl t f:
    base_lit_type_check bl = Some t ->
    base_lit_support_set bl ⊆ dom f ->
    ∃ bl', urn_subst f bl = Some bl' /\ base_lit_type_check bl' = Some t.
  Proof.
    revert t.
    induction bl as [| | | | |bl IH|bl IH |bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2]; intros t. 
    1, 2, 3, 4: naive_solver.
    1: { simpl; setoid_rewrite bind_Some.
         intros ? H. simplify_eq.
         set_unfold.
         setoid_rewrite elem_of_dom in H.
         epose proof H _ eq_refl as [? ->].
         naive_solver. }
    1, 2: simpl; case_match eqn:H; try case_match; intros ??; simplify_eq;
    setoid_rewrite bind_Some;
    epose proof IH _ eq_refl as [x [K1 K2]]; first done;
    apply urn_subst_is_simple in K1 as K3;
    destruct x; simplify_eq;
       by repeat (eexists _||split).
    all: simpl; rewrite union_subseteq; case_match eqn:H; try case_match; try done; try case_match eqn:H'; try case_match; intros ? [Hsubset1 Hsubset2]; simplify_eq;
      repeat setoid_rewrite bind_Some;
      epose proof IH1 _ eq_refl as [x1 [K1 K2]]; first done;
      epose proof IH2 _ eq_refl as [x2 [K3 K4]]; first done;
      apply urn_subst_is_simple in K1 as K5;
      apply urn_subst_is_simple in K3 as K6;
      destruct x1, x2; simplify_eq;
                   by repeat (eexists _||split).
  Qed. 

  (** Not true *)
  (* Global Instance urn_subst_equal_dec σ bl bl': Decision (urn_subst_equal σ bl bl'). *)
  (* Proof. *)
  (*   replace (urn_subst_equal _ _ _) with *)
  (*     (∀ f, f ∈ set_urns_f_valid ( (urns σ)) -> urn_subst f bl = Some bl'). *)
  (*   - apply _.  *)
  (*   - apply propositional_extensionality. *)
  (*     rewrite /urn_subst_equal. *)
  (*     split. *)
  (*     + intros H ??. apply H. *)
  (*       by apply elem_of_set_urns_f_valid. *)
  (*     + intros H ??. *)
  (*       apply H. *)
  (*       by apply elem_of_set_urns_f_valid. *)
  (* Qed. *)

  Lemma base_lit_type_check_None bl f:
    base_lit_type_check bl = None ->
    urn_subst f bl = None.
  Proof.
    induction bl; simpl.
    1, 2, 3, 4, 5: naive_solver.
    1, 2: intros;
       rewrite bind_None;
       destruct (urn_subst _ _) eqn:Heqn; last naive_solver;
       right;
       eexists _; split; first done;
       apply urn_subst_is_simple in Heqn as Heqn';
       apply urn_subst_well_typed in Heqn as Heqn'';
       destruct!/=;
         by repeat (case_match||simplify_eq).
    all: intros; repeat setoid_rewrite bind_None;
      destruct (urn_subst _ _) eqn:Heqn1; last naive_solver; right;
      eexists _; split; first done;
      destruct (urn_subst _ bl2) eqn:Heqn2; last naive_solver;
        right;
       eexists _; split; first done;
       apply urn_subst_is_simple in Heqn1 as Heqn1';
       apply urn_subst_is_simple in Heqn2 as Heqn2';
       apply urn_subst_well_typed in Heqn1 as Heqn1'';
        apply urn_subst_well_typed in Heqn2 as Heqn2''; destruct!/=;
      by repeat (case_match||simplify_eq).
  Qed. 
                                 

  (** urns_subst_f_to_urns not used, remove? *)
  (* Definition urns_subst_f_to_urns (f:gmap loc Z): gmap loc urn := *)
  (*   (λ x, urn_unif {[x]}) <$> f. *)

  (* Lemma urns_subst_f_to_urns_support f: urns_support_set (urns_subst_f_to_urns f) = dom f. *)
  (* Proof. *)
  (* Admitted.  *)
  (* (*   rewrite /urns_subst_f_to_urns. *) *)
  (* (*   rewrite /urns_support_set. *) *)
  (* (*   rewrite dom_fmap_L. *) *)
  (* (*   apply set_eq. *) *)
  (* (*   intros x. rewrite elem_of_filter elem_of_dom. *) *)
  (* (*   split; intros H; first naive_solver. *) *)
  (* (*   split; last done. *) *)
  (* (*   rewrite lookup_fmap. *) *)
  (* (*   destruct H. *) *)
  (* (*   by rewrite H. *) *)
  (* (* Qed. *) *)

  (* Lemma urns_subst_f_to_urns_valid f: *)
  (*   urns_f_valid (urns_subst_f_to_urns f) f. *)
  (* Proof. *)
  (* Admitted.  *)
  (* (*   rewrite /urns_f_valid. *) *)
  (* (*   rewrite /urns_subst_f_to_urns. *) *)
  (* (*   intros ?. *) *)
  (* (*   case_match eqn:H. *) *)
  (* (*   - eexists _. rewrite lookup_fmap. *) *)
  (* (*     rewrite H. simpl. split; [done|set_solver]. *) *)
  (* (*   - rewrite lookup_fmap. rewrite H. naive_solver. *) *)
  (* (* Qed.  *) *)

  (* Lemma urns_subst_f_to_urns_unique_valid f f' : *)
  (*   urns_f_valid (urns_subst_f_to_urns f) f' -> f=f'. *)
  (* Proof. *)
  (*   pose proof urns_subst_f_to_urns_valid f as Hf. *)
  (*   rewrite -!elem_of_set_urns_f_valid in Hf *. *)
  (*   assert (size (set_urns_f_valid (urns_subst_f_to_urns f)) = 1)%nat as Hsize. *)
  (*   { apply set_urns_f_valid_singleton. *)
  (*     rewrite /urns_subst_f_to_urns. *)
  (*     rewrite map_Forall_fmap. *)
  (*     intros ???. simpl. *)
  (*     right. eassert (size ({[x]}:gset _) = 1)%nat; last done. *)
  (*     apply size_singleton. *)
  (*   } *)
  (*   intros. *)
  (*   by eapply size_singleton_inv. *)
  (*   Unshelve. *)
  (*   all: try apply _. *)
  (* Qed.  *)
    
End urn.


Ltac urn_subst_contradict H:=
  exfalso; eapply urn_subst_equal_obv_neq; first apply H; try done.
Global Hint Resolve urn_subst_equal_obv : core.


Definition head_step (e1 : expr) (σ1 : state) : distr (expr * state) :=
  match e1 with
  | Rec f x e =>
      dret (Val $ RecV f x e, σ1)
  | Pair (Val v1) (Val v2) =>
      dret (Val $ PairV v1 v2, σ1)
  | InjL (Val v) =>
      dret (Val $ InjLV v, σ1)
  | InjR (Val v) =>
      dret (Val $ InjRV v, σ1)
  | App (Val (RecV f x e1)) (Val v2) =>
      dret (subst' x v2 (subst' f (RecV f x e1) e1) , σ1)
  | UnOp op (Val v) =>
      match un_op_eval op v with
        | Some w => dret (Val w, σ1)
        | _ => dzero
      end
  | BinOp op (Val v1) (Val v2) =>
      match bin_op_eval op v1 v2 with
        | Some w => dret (Val w, σ1)
        | _ => dzero
      end
  | If (Val (LitV bl)) e1 e2 =>
      if @bool_decide  (urn_subst_equal σ1 bl (LitBool true)) (make_decision _)
      then dret (e1, σ1)
      else if @bool_decide (urn_subst_equal σ1 bl (LitBool false)) (make_decision _)
           then dret (e2, σ1)
           else
             dzero
             (* dbind (λ f, *)
             (*          let σ2 := {|heap:=σ1.(heap); urns:=urns_subst_f_to_urns f |} in *)
             (*          if bool_decide (urn_subst_equal σ2 bl (LitBool true)) *)
             (*          then dret (e1, σ2) *)
             (*          else if bool_decide (urn_subst_equal σ2 bl (LitBool false)) *)
             (*               then dret (e2, σ2) *)
             (*               else dzero  *)
             (*   ) (urns_f_distr (σ1.(urns))) *)
  (* | If (Val (LitV (LitBool true))) e1 e2  => *)
  (*     dret (e1 , σ1) *)
  (* | If (Val (LitV (LitBool false))) e1 e2 => *)
  (*     dret (e2 , σ1) *)
  | Fst (Val (PairV v1 v2)) =>
      dret (Val v1, σ1)
  | Snd (Val (PairV v1 v2)) =>
      dret (Val v2, σ1)
  | Case (Val (InjLV v)) e1 e2 =>
      dret (App e1 (Val v), σ1)
  | Case (Val (InjRV v)) e1 e2 =>
      dret (App e2 (Val v), σ1)
  | AllocN (Val (LitV (LitInt N))) (Val v) =>
      let ℓ := fresh_loc σ1.(heap) in
      if bool_decide (0 < Z.to_nat N)%nat
        then dret (Val $ LitV $ LitLoc ℓ, state_upd_heap_N ℓ (Z.to_nat N) v σ1)
        else dzero
  | Load (Val (LitV (LitLoc l))) =>
      match σ1.(heap) !! l with
        | Some v => dret (Val v, σ1)
        | None => dzero
      end
  | Store (Val (LitV (LitLoc l))) (Val w) =>
      match σ1.(heap) !! l with
        | Some v => dret (Val $ LitV LitUnit, state_upd_heap <[l:=w]> σ1)
        | None => dzero
      end
  (* Uniform sampling from [0, 1 , ..., N] *)
  | Rand (Val (LitV bl)) =>
      match excluded_middle_informative (∃ (N:Z), urn_subst_equal σ1 bl (LitInt N)) with
      | left P => let N := epsilon P in
                 dmap (λ n : fin _, (Val $ LitV $ LitInt n, σ1)) (dunifP (Z.to_nat N))
      | _ => dzero
      end 
  | DRand (Val (LitV bl)) =>
      match excluded_middle_informative (∃ (N:Z), urn_subst_equal σ1 bl (LitInt N)) with
      | left P =>
          let N := epsilon P in
          let l := fresh_loc σ1.(urns) in
          let N' := Z.to_nat N in
          let s := list_to_set (Z.of_nat <$>seq 0 (N'+1)) in
          dret (Val $ LitV $ LitLbl l, state_upd_urns <[l:=(urn_unif s)]> σ1)
      | _ => dzero
      end 
  | _ => dzero
  end.

(* Definition state_step (σ1 : state) (α : loc) : distr state := *)
(*   if bool_decide (α ∈ dom σ1.(tapes)) then *)
(*     let: (N; ns) := (σ1.(tapes) !!! α) in *)
(*     dmap (λ n, state_upd_tapes (<[α := (N; ns ++ [n])]>) σ1) (dunifP N) *)
(*   else dzero. *)

(* Lemma state_step_unfold σ α N ns: *)
(*   tapes σ !! α = Some (N; ns) -> *)
(*   state_step σ α = dmap (λ n, state_upd_tapes (<[α := (N; ns ++ [n])]>) σ) (dunifP N). *)
(* Proof. *)
(*   intros H. *)
(*   rewrite /state_step. *)
(*   rewrite bool_decide_eq_true_2; last first. *)
(*   { by apply elem_of_dom. } *)
(*   by rewrite (lookup_total_correct (tapes σ) α (N; ns)); last done. *)
(* Qed. *)

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
Proof.
  destruct ρ, Ki ;
    rewrite /pmf/= ;
    repeat case_match; subst; try clear -H; try inversion H; intros ; (lra || done).
Qed.

(** A relational characterization of the support of [head_step] to make it easier to
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
| IfTrueS bl e1 e2 σ :
  urn_subst_equal σ bl (LitBool true)->
  head_step_rel (If (Val $ LitV $ bl) e1 e2) σ e1 σ
| IfFalseS bl e1 e2 σ :
  urn_subst_equal σ bl (LitBool false)->
  head_step_rel (If (Val $ LitV $ bl) e1 e2) σ e2 σ
(* | IfTrueS' bl e1 e2 σ f σ': *)
(*   ¬ urn_subst_equal σ bl (LitBool true) -> *)
(*   ¬ urn_subst_equal σ bl (LitBool false) -> *)
(*   urns_f_valid (σ.(urns)) f -> *)
(*   σ' = {|heap:=σ.(heap); urns:=urns_subst_f_to_urns f |} -> *)
(*   urn_subst_equal σ' bl (LitBool true) -> *)
(*   head_step_rel (If (Val $ LitV $ bl) e1 e2) σ e1 σ' *)
(* | IfFalseS' bl e1 e2 σ f σ': *)
(*   ¬ urn_subst_equal σ bl (LitBool true) -> *)
(*   ¬ urn_subst_equal σ bl (LitBool false) -> *)
(*   urns_f_valid (σ.(urns)) f -> *)
(*   σ' = {|heap:=σ.(heap); urns:=urns_subst_f_to_urns f |} -> *)
(*   urn_subst_equal σ' bl (LitBool false) -> *)
(*   head_step_rel (If (Val $ LitV $ bl) e1 e2) σ e2 σ' *)
(* | IfFalseS e1 e2 σ : *)
(*   head_step_rel (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ *)
| FstS v1 v2 σ :
  head_step_rel (Fst (Val $ PairV v1 v2)) σ (Val v1) σ
| SndS v1 v2 σ :
  head_step_rel (Snd (Val $ PairV v1 v2)) σ (Val v2) σ
| CaseLS v e1 e2 σ :
  head_step_rel (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ
| CaseRS v e1 e2 σ :
  head_step_rel (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ
| AllocNS z N v σ l :
  l = fresh_loc σ.(heap) →
  N = Z.to_nat z →
  (0 < N)%nat ->
  head_step_rel (AllocN (Val (LitV (LitInt z))) (Val v)) σ
    (Val $ LitV $ LitLoc l) (state_upd_heap_N l N v σ)
| LoadS l v σ :
  σ.(heap) !! l = Some v →
  head_step_rel (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ
| StoreS l v w σ :
  σ.(heap) !! l = Some v →
  head_step_rel (Store (Val $ LitV $ LitLoc l) (Val w)) σ
    (Val $ LitV LitUnit) (state_upd_heap <[l:=w]> σ)
| RandS z N bl (n : fin (S N)) σ:
  urn_subst_equal σ bl (LitInt z) ->
  N = Z.to_nat z →
  head_step_rel (Rand (Val $ LitV bl)) σ (Val $ LitV $ LitInt n) σ
| DRandS z N bl σ l s:
  urn_subst_equal σ bl (LitInt z) ->
  l = fresh_loc σ.(urns) →
  N = Z.to_nat z →
  s = list_to_set (seq 0 (N+1)) ->
  head_step_rel (DRand (Val $ LitV bl)) σ (Val $ LitV $ LitLbl l) (state_upd_urns <[l:=s]> σ).
(* | AllocTapeS z N σ l : *)
(*   l = fresh_loc σ.(tapes) → *)
(*   N = Z.to_nat z → *)
(*   head_step_rel (AllocTape (Val (LitV (LitInt z)))) σ *)
(*     (Val $ LitV $ LitLbl l) (state_upd_tapes <[l := (N; []) : tape]> σ) *)
(* | RandTapeS l z N n ns σ : *)
(*   N = Z.to_nat z → *)
(*   σ.(tapes) !! l = Some ((N; n :: ns) : tape)  → *)
(*   head_step_rel (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl l)))) σ *)
(*     (Val $ LitV $ LitInt $ n) (state_upd_tapes <[l := (N; ns) : tape]> σ) *)
(* | RandTapeEmptyS l z N (n : fin (S N)) σ : *)
(*   N = Z.to_nat z → *)
(*   σ.(tapes) !! l = Some ((N; []) : tape) → *)
(*   head_step_rel (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitInt n) σ *)
(* | RandTapeOtherS l z M N ms (n : fin (S N)) σ : *)
(*   N = Z.to_nat z → *)
(*   σ.(tapes) !! l = Some ((M; ms) : tape) → *)
(*   N ≠ M → *)
(*   head_step_rel (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitInt n) σ *)
(* | TickS σ z : *)
(*   head_step_rel (Tick $ Val $ LitV $ LitInt z) σ (Val $ LitV $ LitUnit) σ *)

Create HintDb head_step.
Global Hint Constructors head_step_rel : head_step.
(* 0%fin always has non-zero mass, so propose this choice if the reduct is
   unconstrained. *)
Global Hint Extern 1
  (head_step_rel (Rand (Val (LitV _)) ) _ _ _) =>
         eapply (RandS _ _ _ 0%fin) : head_step.
(* Global Hint Extern 1 *)
(*   (head_step_rel (Rand (Val (LitV _)) (Val (LitV (LitLbl _)))) _ _ _) => *)
(*          eapply (RandTapeEmptyS _ _ _ 0%fin) : head_step. *)
(* Global Hint Extern 1 *)
(*   (head_step_rel (Rand (Val (LitV _)) (Val (LitV (LitLbl _)))) _ _ _) => *)
(*          eapply (RandTapeOtherS _ _ _ _ _ 0%fin) : head_step. *)

(* Inductive state_step_rel : state → loc → state → Prop := *)
(* | AddTapeS α N (n : fin (S N)) ns σ : *)
(*   α ∈ dom σ.(tapes) → *)
(*   σ.(tapes) !!! α = ((N; ns) : tape) → *)
(*   state_step_rel σ α (state_upd_tapes <[α := (N; ns ++ [n]) : tape]> σ). *)

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

Lemma head_step_support_equiv_rel e1 e2 σ1 σ2 :
  head_step e1 σ1 (e2, σ2) > 0 ↔ head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intros ?. destruct e1; inv_head_step; eauto with head_step.
    (* + inv_distr. *)
    (*   eapply IfTrueS'; try done. *)
    (*   by apply urns_f_distr_pos. *)
    (* + inv_distr. *)
    (*   eapply IfFalseS'; try done. *)
    (*   by apply urns_f_distr_pos. *)
    + eapply RandS; last done.
      apply urn_subst_equal_epsilon_correct.
    + eapply DRandS; last done; try done.
      apply urn_subst_equal_epsilon_correct.
  - inversion 1; simplify_map_eq/=; repeat try case_bool_decide; simplify_eq; try done; try by solve_distr.
    + exfalso.
      assert (LitBool true ≠ LitBool false) as H' by done; (apply H'; by eapply urn_subst_equal_unique).
    (* + solve_distr; last by apply urns_f_distr_pos. *)
    (*   rewrite bool_decide_eq_true_2; last done. *)
    (*   solve_distr. *)
    (* + solve_distr; last by apply urns_f_distr_pos. *)
    (*   rewrite bool_decide_eq_false_2; last first. *)
    (*   { intros H'. by eapply (urn_subst_equal_unique _ _ (LitBool true) (LitBool false)) in H'. } *)
    (*   rewrite bool_decide_eq_true_2; last done. *)
    (*   solve_distr. *)
    + solve_distr. case_match; last (exfalso; naive_solver).
      erewrite urn_subst_equal_epsilon_unique; last done.
      solve_distr.
    + case_match; last (exfalso; naive_solver).
      erewrite urn_subst_equal_epsilon_unique; last done.
      solve_distr.
Qed.

(* Lemma state_step_support_equiv_rel σ1 α σ2 : *)
(*   state_step σ1 α σ2 > 0 ↔ state_step_rel σ1 α σ2. *)
(* Proof. *)
(*   rewrite /state_step. split. *)
(*   - case_bool_decide; [|intros; inv_distr]. *)
(*     case_match. intros ?. inv_distr. *)
(*     econstructor; eauto with lia. *)
(*   - inversion_clear 1. *)
(*     rewrite bool_decide_eq_true_2 // H1. solve_distr. *)
(* Qed. *)

(* state step technically not used, but needed to define the ectxilanguage *)
Definition state_step (σ:state) (α:loc) := dret σ.
Lemma state_step_head_step_not_stuck e σ σ' α :
  state_step σ α σ' > 0 → (∃ ρ, head_step e σ ρ > 0) ↔ (∃ ρ', head_step e σ' ρ' > 0).
Proof.
  rewrite /state_step.
  intros. by inv_distr.
Qed. 
(*   rewrite state_step_support_equiv_rel. *)
(*   inversion_clear 1. *)
(*   split; intros [[e2 σ2] Hs]. *)
(*   (* TODO: the sub goals used to be solved by [simplify_map_eq]  *) *)
(*   - destruct e; inv_head_step; try by (unshelve (eexists; solve_distr)). *)
(*     + destruct (decide (α = l1)); simplify_eq. *)
(*       * rewrite lookup_insert in H11. done. *)
(*       * rewrite lookup_insert_ne // in H11. rewrite H11 in H7. done. *)
(*     + destruct (decide (α = l1)); simplify_eq. *)
(*       * rewrite lookup_insert in H11. done. *)
(*       * rewrite lookup_insert_ne // in H11. rewrite H11 in H7. done. *)
(*     + destruct (decide (α = l1)); simplify_eq. *)
(*       * rewrite lookup_insert in H10. done. *)
(*       * rewrite lookup_insert_ne // in H10. rewrite H10 in H7. done. *)
(*   - destruct e; inv_head_step; try by (unshelve (eexists; solve_distr)). *)
(*     + destruct (decide (α = l1)); simplify_eq. *)
(*       * apply not_elem_of_dom_2 in H11. done. *)
(*       * rewrite lookup_insert_ne // in H7. rewrite H11 in H7.  done. *)
(*     + destruct (decide (α = l1)); simplify_eq. *)
(*       * rewrite lookup_insert // in H7. *)
(*         apply not_elem_of_dom_2 in H11. done. *)
(*       * rewrite lookup_insert_ne // in H7. rewrite H11 in H7. done. *)
(*     + destruct (decide (α = l1)); simplify_eq. *)
(*       * rewrite lookup_insert // in H7. *)
(*         apply not_elem_of_dom_2 in H10. done. *)
(*       * rewrite lookup_insert_ne // in H7. rewrite H10 in H7. done. *)
(* Qed. *)

Lemma state_step_mass σ α :
  α ∈ dom σ.(urns) → SeriesC (state_step σ α) = 1.
Proof.
  intros Hdom.
  rewrite /state_step.
  apply dret_mass. 
Qed.

Lemma head_step_mass e σ :
  (∃ ρ, head_step e σ ρ > 0) → SeriesC (head_step e σ) = 1.
Proof.
  intros [[] Hs%head_step_support_equiv_rel].
  inversion Hs;
    repeat (simplify_map_eq/=; solve_distr_mass || case_match; try (case_bool_decide; done) ).
  (* - rename select (_=false) into L1. clear L1.  *)
  (*   rename select (_=false) into L1. clear L1. *)
  (*   rename select (urns_f_valid _ _) into H1. *)
  (*   apply dbind_det; first apply urns_f_distr_mass.  *)
  (*   intros ? Hf. *)
  (*   case_bool_decide as H2; try solve_distr_mass. *)
  (*   case_bool_decide as H4; try solve_distr_mass. *)
  (*   exfalso. *)
  (*   rewrite urns_f_distr_pos in Hf. *)
  (*   rename select (urn_subst_equal _ _ _) into H'. *)
  (*   apply urn_subst_equal_well_typed in H' as K1. *)
  (*   destruct K1 as [?[K1 K1']]. *)
  (*   apply urn_subst_equal_well_typed in H' as K2. *)
  (*   destruct!/=. *)
  (*   apply urn_subst_equal_support in H' as K3. *)
  (*   simpl in *. *)
  (*   apply urns_f_valid_support in Hf as K4. *)
  (*   apply urns_f_valid_support in H1 as K5. *)
  (*   rewrite urns_subst_f_to_urns_support in K3. *)
  (*   rewrite -K5 K4 in K3. *)
  (*   eapply urn_subst_exists in K1; last done. *)
  (*   destruct K1 as [bl' [K1 ]]. *)
  (*   apply urn_subst_is_simple in K1 as K1'. *)
  (*   destruct bl'; simplify_eq. *)
  (*   rename select bool into b. *)
  (*   destruct b. *)
  (*   + apply H2. *)
  (*     rewrite /urn_subst_equal/=. *)
  (*     by intros ? ->%urns_subst_f_to_urns_unique_valid. *)
  (*   + apply H4. *)
  (*     rewrite /urn_subst_equal/=. *)
  (*     by intros ? ->%urns_subst_f_to_urns_unique_valid. *)
  (* - rename select (_=false) into L1. clear L1.  *)
  (*   rename select (_=false) into L1. clear L1. *)
  (*   rename select (urns_f_valid _ _) into H1. *)
  (*   apply dbind_det; first apply urns_f_distr_mass.  *)
  (*   intros ? Hf. *)
  (*   case_bool_decide as H2; try solve_distr_mass. *)
  (*   case_bool_decide as H4; try solve_distr_mass. *)
  (*   exfalso. *)
  (*   rewrite urns_f_distr_pos in Hf. *)
  (*   rename select (urn_subst_equal _ _ _) into H'. *)
  (*   apply urn_subst_equal_well_typed in H' as K1. *)
  (*   destruct K1 as [?[K1 K1']]. *)
  (*   apply urn_subst_equal_well_typed in H' as K2. *)
  (*   destruct!/=. *)
  (*   apply urn_subst_equal_support in H' as K3. *)
  (*   simpl in *. *)
  (*   apply urns_f_valid_support in Hf as K4. *)
  (*   apply urns_f_valid_support in H1 as K5. *)
  (*   rewrite urns_subst_f_to_urns_support in K3. *)
  (*   rewrite -K5 K4 in K3. *)
  (*   eapply urn_subst_exists in K1; last done. *)
  (*   destruct K1 as [bl' [K1 ]]. *)
  (*   apply urn_subst_is_simple in K1 as K1'. *)
  (*   destruct bl'; simplify_eq. *)
  (*   rename select bool into b. *)
  (*   destruct b. *)
  (*   + apply H2. *)
  (*     rewrite /urn_subst_equal/=. *)
  (*     by intros ? ->%urns_subst_f_to_urns_unique_valid. *)
  (*   + apply H4. *)
  (*     rewrite /urn_subst_equal/=. *)
  (*     by intros ? ->%urns_subst_f_to_urns_unique_valid. *)
  - exfalso; naive_solver.
  - exfalso; naive_solver.
Qed. 


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
  | AllocN e1 e2 => 1 + height e1 + height e2
  | Load e => 1 + height e
  | Store e1 e2 => 1 + height e1 + height e2
  | Rand e => 1 + height e
  | DRand e => 1 + height e
  end.

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
  destruct Ki ; repeat destruct_match ; intros [=] ; subst ; cbn ; lia.
Qed.

Lemma decomp_fill_item Ki e :
  to_val e = None → decomp_item (fill_item Ki e) = Some (Ki, e).
Proof. destruct Ki ; simpl ; by repeat destruct_match. Qed.

(* TODO: this proof is slow, but I do not see how to make it faster... *)
Lemma decomp_fill_item_2 e e' Ki :
  decomp_item e = Some (Ki, e') → fill_item Ki e' = e ∧ to_val e' = None.
Proof.
  rewrite /decomp_item ;
    destruct e ; try done ;
    destruct Ki ; cbn ; repeat destruct_match ; intros [=] ; subst ; auto.
Qed.

Definition get_active (σ : state) : list loc := elements (dom σ.(urns)).

Lemma state_step_get_active_mass σ α :
  α ∈ get_active σ → SeriesC (state_step σ α) = 1.
Proof. rewrite elem_of_elements. apply state_step_mass. Qed.

(* Lemma state_steps_mass σ αs : *)
(*   αs ⊆ get_active σ → *)
(*   SeriesC (foldlM state_step σ αs) = 1. *)
(* Proof. *)
(*   induction αs as [|α αs IH] in σ |-* ; intros Hact. *)
(*   { rewrite /= dret_mass //. } *)
(*   rewrite foldlM_cons. *)
(*   rewrite dbind_det //. *)
(*   - apply state_step_get_active_mass. set_solver. *)
(*   - intros σ' Hσ'. apply IH. *)
(*     apply state_step_support_equiv_rel in Hσ'. *)
(*     inversion Hσ'; simplify_eq. *)
(*     intros α' ?. rewrite /get_active /=. *)
(*     apply elem_of_elements, elem_of_dom. *)
(*     destruct (decide (α = α')); subst. *)
(*     + eexists. rewrite lookup_insert //. *)
(*     + rewrite lookup_insert_ne //. *)
(*       apply elem_of_dom. eapply elem_of_elements, Hact. by right. *)
(* Qed. *)

Lemma d_prob_lang_mixin :
  EctxiLanguageMixin of_val to_val fill_item decomp_item expr_ord head_step state_step get_active.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    state_step_head_step_not_stuck, state_step_get_active_mass, head_step_mass,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val,
    decomp_fill_item, decomp_fill_item_2, expr_ord_wf, decomp_expr_ord.
Qed.

End d_prob_lang.

(** Language *)
Canonical Structure d_prob_ectxi_lang := EctxiLanguage d_prob_lang.get_active d_prob_lang.d_prob_lang_mixin (def_val := d_prob_lang.def_val).
Canonical Structure d_prob_ectx_lang := EctxLanguageOfEctxi d_prob_ectxi_lang.
Canonical Structure d_prob_lang := LanguageOfEctx d_prob_ectx_lang.

(* Prefer prob_lang names over ectx_language names. *)
Export d_prob_lang.

Definition cfg : Type := expr * state.
