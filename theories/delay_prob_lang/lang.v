From Coq Require Import Reals Psatz.
From stdpp Require Export binders strings.
From stdpp Require Import gmap fin_maps countable fin.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext tactics.
From clutch.prob Require Export distribution.
From clutch.common Require Export language ectx_language ectxi_language locations.
From iris.prelude Require Import options.

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module d_prob_lang.

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


Definition urn :=  gset nat .

Global Instance urn_inhabited : Inhabited urn. Proof. apply _. Qed. 
Global Instance urn_eq_dec : EqDecision urn. Proof. apply _. Defined.
Global Instance urn_countable : EqDecision urn. Proof. apply _. Qed.

Global Instance urn_lookup_total : LookupTotal loc urn (gmap loc urn).
Proof. apply map_lookup_total. Defined.
Global Instance urn_insert : Insert loc urn (gmap loc urn).
Proof. apply map_insert. Defined.

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
  | _              => None
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
  | AllocN e1 e2 => AllocN (subst x v e1) (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | Rand e => Rand (subst x v e)
  | DRand e => DRand (subst x v e)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => λ x, x end.

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
      | (Some BLTInt, Some BLTInt) => Some BLTInt
      | _ => None
      end
  | LtOp' x1 x2 => 
      match (base_lit_type_check x1, base_lit_type_check x2) with
      | (Some BLTInt, Some BLTInt) => Some BLTInt
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
    rewrite map_union_empty replicate_length //.
Qed.

#[local] Open Scope R.

(** Definitions for relating delayed program with nondelayed one *)
Fixpoint urn_subst (f: gmap loc nat) (bl : base_lit) : option base_lit :=
  match bl with
  | LitInt n => Some $ LitInt n
  | LitBool b => Some $ LitBool b
  | LitUnit => Some LitUnit
  | LitLoc l => Some $ LitLoc l
  | LitLbl l => (x ← f !! l; Some $ LitInt (Z.of_nat x))
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

Definition urns_f_valid (m : gmap loc urn) (f:gmap loc nat) :=
  forall l, match f !! l with
       | Some x =>
           ∃ u, m!!l=Some u /\ x ∈ u
       | None => m!!l = None \/ m!!l = Some ∅
  end
.

Fixpoint list_urns_f_valid (m:list (loc * urn)) : list (gmap loc nat):=
  match m with
    | [] => [∅]
    | (k, u)::rest =>
        let l := elements u in
        if bool_decide (l=[]) then
          list_urns_f_valid rest 
        else let x := list_urns_f_valid rest in
        (a ← l; b ← x; [<[k:=a]>b])
  end.

Lemma list_urns_f_nonempty m:
  (0<length (list_urns_f_valid m))%nat.
Proof.
  induction m; simpl; first lia.
  destruct a as [x y]. case_bool_decide; first done.
  destruct (elements y); first done.
  simpl. rewrite app_length.
  destruct (list_urns_f_valid m); simpl; first (simpl in *; lia).
  lia.
Qed. 

Lemma list_urns_f_valid_correct m f :
  urns_f_valid m f <-> 
  f ∈list_urns_f_valid (map_to_list m).
Proof.
  split.
  - rewrite /urns_f_valid.
    intros H.
    remember (map_to_list m) as lis eqn:Heqlis'.
    assert (lis ≡ₚ map_to_list m) as Heqlis.
    { subst. apply Permutation_refl. }
    clear Heqlis'.
    assert (NoDup lis.*1) as Hnodup.
    { rewrite Heqlis. apply NoDup_fst_map_to_list. }
    revert m f H Heqlis Hnodup.
    induction (lis) as [|x lis' IH]; intros m f H Heqlis Hnodup.
    + simpl. apply elem_of_list_singleton.
      apply map_eq.
      intros i.
      rewrite lookup_empty.
      symmetry in Heqlis.
      rewrite Permutation_nil_r in Heqlis.
      apply map_to_list_empty_iff in Heqlis.
      subst.
      specialize (H i).
      case_match; last done.
      destruct!/=.
    + assert (list_to_map (x::lis') = m) as Heqlis'.
      { rewrite (list_to_map_proper _ (map_to_list m)); try done.
        by rewrite list_to_map_to_list.
      }
      simpl.
      destruct x as [l u].
      assert (l∉lis'.*1) as Hnotin.
      { intros ?.
        apply NoDup_cons in Hnodup. naive_solver.
      } 
      case_bool_decide as H0.
      { apply elements_empty_inv in H0. subst.
        eapply IH; last first.
        - apply NoDup_cons in Hnodup; naive_solver.
        - simpl in *.
          rewrite map_to_list_insert in Heqlis; last by apply not_elem_of_list_to_map.
          by apply Permutation_cons_inv in Heqlis.
        - apply leibniz_equiv in H0. subst.
          intros l'.
          specialize (H l').
          case_match.
          + destruct H as (u&H1&H2).
            destruct (decide (l=l')).
            -- exfalso.
               subst. rewrite lookup_insert in H1. simplify_eq. set_solver.
            -- eexists _. split; last done.
               rewrite -H1.
               by rewrite lookup_insert_ne.
          + destruct (decide (l=l')).
            * subst. rewrite lookup_insert in H.
              left.
              by apply not_elem_of_list_to_map_1.
            * by rewrite lookup_insert_ne in H.
      }
      rewrite elem_of_list_bind.
      specialize (H l) as H'.
      case_match; last first.
      { rewrite -Heqlis' in H'.
        exfalso.
        destruct H' as [H'|H'].
        - eapply (not_elem_of_list_to_map_2 _ l).
          + rewrite <-H'. f_equal.
          + set_solver.
        - rewrite lookup_insert in H'.
          simpl in *. simplify_eq.
      }
      destruct H' as (u'&H2&H3).
      subst.
      exists n.
      split; last first.
      * rewrite lookup_insert in H2. simplify_eq.
        set_solver.
      * rewrite elem_of_list_bind.
        exists (delete l f).
        split.
        -- rewrite insert_delete_insert.
           rewrite insert_id; [set_solver|done].
        -- apply IH with (delete l (list_to_map lis')).
           ++ intros l'.
              destruct (decide (l=l')).
              ** subst. rewrite lookup_delete.
                 left.
                 apply lookup_delete.
              ** rewrite lookup_delete_ne; last done.
                 specialize (H l').
                 case_match.
                 --- destruct H as (u''&K1&K2).
                     exists u''. rewrite lookup_delete_ne; last done.
                     split; last done.
                     rewrite -K1.
                     by rewrite lookup_insert_ne.
                 --- rewrite lookup_delete_ne; last done.
                     by rewrite lookup_insert_ne in H.
           ++ rewrite delete_notin.
              ** rewrite map_to_list_to_map; first done.
                 apply NoDup_cons in Hnodup. naive_solver.
              ** by apply not_elem_of_list_to_map.
           ++ apply NoDup_cons in Hnodup. naive_solver.
  - rewrite /urns_f_valid.
    intros H.
    remember (map_to_list m) as lis eqn:Heqlis'.
    assert (lis ≡ₚ map_to_list m) as Heqlis.
    { subst. apply Permutation_refl. }
    clear Heqlis'.
    assert (NoDup lis.*1) as Hnodup.
    { rewrite Heqlis. apply NoDup_fst_map_to_list. }
    revert m f H Heqlis Hnodup.
    induction (lis) as [|x lis' IH]; intros m f H Heqlis Hnodup.
    + symmetry in Heqlis.
      rewrite Permutation_nil_r in Heqlis.
      apply map_to_list_empty_iff in Heqlis.
      subst. simpl in *.
      apply elem_of_list_singleton in H.
      subst.
      intros ?.
      repeat rewrite lookup_empty. naive_solver.
    + assert (list_to_map (x::lis') = m) as Heqlis'.
      { rewrite (list_to_map_proper _ (map_to_list m)); try done.
        by rewrite list_to_map_to_list.
      }
      simpl in H.
      destruct x as [k u].
      case_bool_decide as H'.
      { intros l.
        specialize (IH (delete k m)).
        apply elements_empty_inv in H'.
        apply leibniz_equiv in H'. subst.
        simpl in *. rewrite delete_insert in IH; last first.
        - apply not_elem_of_list_to_map. apply NoDup_cons in Hnodup. naive_solver.
        - unshelve epose proof (IH _ _ _ _) as H'; [|done|rewrite map_to_list_to_map|..].
          + apply Permutation_refl.
          + apply NoDup_cons in Hnodup. naive_solver.
          + apply NoDup_cons in Hnodup. naive_solver.
          + specialize (H' l).
            case_match.
            * destruct (decide (k=l)).
              -- subst. destruct H' as (?&H'&?).
                 exfalso. apply NoDup_cons in Hnodup.
                 apply Hnodup. rewrite elem_of_list_fmap.
                 eexists (_,_); simpl; split; first done.
                 rewrite elem_of_list_to_map; naive_solver.
              -- by rewrite lookup_insert_ne.
            * destruct (decide (k=l)).
              -- subst. rewrite lookup_insert. naive_solver.
              -- by rewrite lookup_insert_ne.
      } 
      rewrite elem_of_list_bind in H.
      destruct H as (y&H1&H2).
      rewrite elem_of_list_bind in H1.
      destruct H1 as (f'&H1&H3).
      apply elem_of_list_singleton in H1. subst.
      intros.
      destruct (decide (l=k)).
      * subst. rewrite lookup_insert.
        exists u. simpl. rewrite lookup_insert. split; first done.
        by apply elem_of_elements in H2.
      * assert (k∉lis'.*1) as Hnotin.
        { intros ?.
          apply NoDup_cons in Hnodup. naive_solver.
        }
           apply NoDup_cons in Hnodup.
        rewrite lookup_insert_ne; last done.
        eapply IH in H3; last first.
        -- naive_solver.
        -- simpl in *.
           rewrite map_to_list_insert in Heqlis.
           ++ by apply Permutation_cons_inv in Heqlis.
           ++ by apply not_elem_of_list_to_map.
        -- simpl. by rewrite lookup_insert_ne.
Qed. 


  
Definition urn_subst_equal σ (bl bl':base_lit) :=
  ∀ f, urns_f_valid (urns σ) f -> urn_subst f bl = Some bl'.

Lemma urn_subst_equal_unique σ bl bl1 bl2:
  urn_subst_equal σ bl bl1 -> urn_subst_equal σ bl bl2 -> bl1=bl2.
Proof.
  rewrite /urn_subst_equal.
  intros H1 H2.
  setoid_rewrite list_urns_f_valid_correct in H1.
  setoid_rewrite list_urns_f_valid_correct in H2.
  pose proof list_urns_f_nonempty (map_to_list (urns σ)).
  edestruct (list_urns_f_valid _) as [|x]; first (simpl in *; lia).
  epose proof H1 x _ as H1.
  epose proof H2 x _ as H2.
  rewrite H1 in H2. by simplify_eq.
  Unshelve.
  all: apply elem_of_cons; naive_solver.
Qed.

Global Instance urn_subst_equal_dec σ bl bl': Decision (urn_subst_equal σ bl bl').
Proof.
  replace (urn_subst_equal _ _ _) with
    (∀ f, f ∈ list_urns_f_valid (map_to_list (urns σ)) -> urn_subst f bl = Some bl').
  - apply list_forall_dec. apply _.
  - apply propositional_extensionality.
    rewrite /urn_subst_equal.
    split.
    + intros H ??. apply H.
      by apply list_urns_f_valid_correct.
    + intros H ??.
      apply H.
      by apply list_urns_f_valid_correct.
Qed. 

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
      if bool_decide (urn_subst_equal σ1 bl (LitBool true))
      then dret (e1, σ1)
      else if bool_decide (urn_subst_equal σ1 bl (LitBool false))
           then dret (e2, σ1)
           else dzero
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
  | Rand (Val (LitV (LitInt N))) =>
      dmap (λ n : fin _, (Val $ LitV $ LitInt n, σ1)) (dunifP (Z.to_nat N))
  | DRand (Val (LitV (LitInt N))) =>
      let l := fresh_loc σ1.(urns) in
      let N' := Z.to_nat N in
      let s := list_to_set (seq 0 (N'+1)) in
      dret (Val $ LitV $ LitLbl l, state_upd_urns <[l:=s]> σ1)
  (* (* Since our language only has integers, we use Z.to_nat, which maps positive *)
  (*    integers to the corresponding nat, and the rest to 0. We sample from *)
  (*    [dunifP N = dunif (1 + N)] to avoid the case [dunif 0 = dzero]. *) *)
  (* (* Uniform sampling from [0, 1 , ..., N] *) *)
  (* | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) => *)
  (*     dmap (λ n : fin _, (Val $ LitV $ LitInt n, σ1)) (dunifP (Z.to_nat N)) *)
  (* | AllocTape (Val (LitV (LitInt z))) => *)
  (*     let ι := fresh_loc σ1.(tapes) in *)
  (*     dret (Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := (Z.to_nat z; []) ]> σ1) *)
  (* (* Labelled sampling, conditional on tape contents *) *)
  (* | Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))) => *)
  (*     match σ1.(tapes) !! l with *)
  (*     | Some (M; ns) => *)
  (*         if bool_decide (M = Z.to_nat N) then *)
  (*           match ns  with *)
  (*           | n :: ns => *)
  (*               (* the tape is non-empty so we consume the first number *) *)
  (*               dret (Val $ LitV $ LitInt $ fin_to_nat n, state_upd_tapes <[l:=(M; ns)]> σ1) *)
  (*           | [] => *)
  (*               (* the tape is allocated but empty, so we sample from [0, 1, ..., M] uniformly *) *)
  (*               dmap (λ n : fin _, (Val $ LitV $ LitInt n, σ1)) (dunifP M) *)
  (*           end *)
  (*         else *)
  (*           (* bound did not match the bound of the tape *) *)
  (*           dmap (λ n : fin _, (Val $ LitV $ LitInt n, σ1)) (dunifP (Z.to_nat N)) *)
  (*     | None => dzero *)
  (*     end *)
  (* | Tick (Val (LitV (LitInt n))) => dret (Val $ LitV $ LitUnit, σ1) *)
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
    repeat case_match; clear -H ; inversion H; intros ; (lra || done).
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
| RandS z N (n : fin (S N)) σ:
  N = Z.to_nat z →
  head_step_rel (Rand (Val $ LitV $ LitInt z)) σ (Val $ LitV $ LitInt n) σ
| DRandS z N σ l s:
  l = fresh_loc σ.(urns) →
  N = Z.to_nat z →
  s = list_to_set (seq 0 (N+1)) ->
  head_step_rel (DRand (Val $ LitV $ LitInt z)) σ (Val $ LitV $ LitLbl l) (state_upd_urns <[l:=s]> σ).
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
         eapply (RandS _ _ 0%fin) : head_step.
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
  - inversion 1; simplify_map_eq/=; repeat try case_bool_decide; simplify_eq; try by solve_distr.
    exfalso.
    assert (LitBool true ≠ LitBool false) as H' by done; (apply H'; by eapply urn_subst_equal_unique).
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
    repeat (simplify_map_eq/=; solve_distr_mass || case_match; try (case_bool_decide; done)).
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
Canonical Structure d_prob_ectxi_lang := EctxiLanguage d_prob_lang.get_active d_prob_lang.d_prob_lang_mixin.
Canonical Structure d_prob_ectx_lang := EctxLanguageOfEctxi d_prob_ectxi_lang.
Canonical Structure d_prob_lang := LanguageOfEctx d_prob_ectx_lang.

(* Prefer prob_lang names over ectx_language names. *)
Export d_prob_lang.

Definition cfg : Type := expr * state.
