From Coq Require Import Reals Psatz.
From stdpp Require Export binders strings.
From stdpp Require Import gmap fin_maps.
From iris.algebra Require Export ofe.
From self.prelude Require Import stdpp_ext.
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
  | NegOp | MinusUnOp | ZtoBOp.
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
  | AllocTape (e : expr)
  | Rand (e : expr)
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

(** We assume the following encoding of values to 64-bit words: The least 3
significant bits of every word are a "tag", and we have 61 bits of payload,
which is enough if all pointers are 8-byte-aligned (common on 64bit
architectures). The tags have the following meaning:

0: Payload is the data for a LitV (LitInt _).
1: Payload is the data for a InjLV (LitV (LitInt _)).
2: Payload is the data for a InjRV (LitV (LitInt _)).
3: Payload is the data for a LitV (LitLoc _).
4: Payload is the data for a InjLV (LitV (LitLoc _)).
4: Payload is the data for a InjRV (LitV (LitLoc _)).
6: Payload is one of the following finitely many values, which 61 bits are more
   than enough to encode:
   LitV LitUnit, InjLV (LitV LitUnit), InjRV (LitV LitUnit),
   LitV LitPoison, InjLV (LitV LitPoison), InjRV (LitV LitPoison),
   LitV (LitBool _), InjLV (LitV (LitBool _)), InjRV (LitV (LitBool _)).
7: Value is boxed, i.e., payload is a pointer to some read-only memory area on
   the heap which stores whether this is a RecV, PairV, InjLV or InjRV and the
   relevant data for those cases. However, the boxed representation is never
   used if any of the above representations could be used.

Ignoring (as usual) the fact that we have to fit the infinite Z/loc into 61
bits, this means every value is machine-word-sized and can hence be atomically
read and written.  Also notice that the sets of boxed and unboxed values are
disjoint. *)
Definition lit_is_unboxed (l: base_lit) : Prop :=
  match l with
  (** Disallow comparing (erased) prophecies with (erased) prophecies, by
  considering them boxed. *)
  (* | LitProphecy _ | LitPoison => False *)
  | LitInt _ | LitBool _  | LitLoc _ | LitLbl _ | LitUnit => True
  end.
Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => lit_is_unboxed l
  | InjLV (LitV l) => lit_is_unboxed l
  | InjRV (LitV l) => lit_is_unboxed l
  | _ => False
  end.

Global Instance lit_is_unboxed_dec l : Decision (lit_is_unboxed l).
Proof. destruct l; simpl; exact (decide _). Defined.
Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Proof. destruct v as [ | | | [] | [] ]; simpl; exact (decide _). Defined.

(** We just compare the word-sized representation of two values, without looking
into boxed data.  This works out fine if at least one of the to-be-compared
values is unboxed (exploiting the fact that an unboxed and a boxed value can
never be equal because these are disjoint sets). *)
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

(* A tape is a product of a natural number n and a list of integers in {0,...,n} *)
Definition tape := prod nat (list nat).


Definition valid_tapes (t : gmap loc tape) : Prop :=
  map_Forall (λ _ '(b, ns), Forall (λ n, n ≤ b) ns) t.


Lemma valid_tapes_insert_fresh t n :
  valid_tapes t →
  valid_tapes (<[fresh_loc t:=(n, [])]> t).
Proof.
  rewrite /valid_tapes. intros Ht.
  rewrite map_Forall_insert; [auto|].
  apply not_elem_of_dom, fresh_loc_is_fresh.
Qed.

Lemma valid_tapes_consume t b n ns α :
  valid_tapes t →
  t !! α = Some (b, n :: ns) →
  valid_tapes (<[α:=(b, ns)]> t).
Proof.
  rewrite /valid_tapes.
  intros Ht Hα.
  apply map_Forall_insert_2; [|done].
  suff: (Forall (λ m, m ≤ b) (n :: ns)).
  { rewrite Forall_cons. by intros []. }
  eapply (map_Forall_lookup_1 _ _ _ _ Ht Hα).
Qed.

Lemma valid_tapes_leq t α b n ns :
  valid_tapes t →
  t !! α = Some (b, n :: ns) →
  n ≤ b.
Proof.
  rewrite /valid_tapes.
  intros Ht Hα.
  eapply (Forall_cons (λ n, n ≤ b) _ ns).
  apply (map_Forall_lookup_1 _ _ _ _ Ht Hα).
Qed.

(* Typeclass stuff for tapes *)
Global Instance tape_inhabited : Inhabited tape.
Proof. apply prod_inhabited; [apply Nat.inhabited | apply list_inhabited ]. Defined.
Global Instance tape_eq_dec : EqDecision tape.
Proof. solve_decision. Defined.

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
     | AllocTape e, AllocTape e' => cast_if (decide (e = e'))
     | Rand e, Rand e' => cast_if (decide (e = e'))
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
 refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 | ZtoBOp => 2 end)
  (λ n, match n with 0 => NegOp | 1 => MinusUnOp | _ => ZtoBOp end) _); by intros [].
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
     | AllocTape e => GenNode 15 [go e]
     | Rand e => GenNode 16 [go e]
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
     | GenNode 15 [e] => AllocTape (go e)
     | GenNode 16 [e] => Rand (go e)
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

Global Instance tapes_lookup_total : LookupTotal loc tape (gmap loc tape).
Proof. apply map_lookup_total. Defined.

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
  | AllocTapeCtx
  | RandCtx.

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
  | AllocTapeCtx => AllocTape e
  | RandCtx => Rand e
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
  | AllocTape (Val _)        => None
  | AllocTape e              => Some (AllocTapeCtx, e)
  | Rand (Val _)           => None
  | Rand e                 => Some (RandCtx, e)
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
  | AllocTape e => AllocTape (subst x v e)
  | Rand e => Rand (subst x v e)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => λ x, x end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt z) => Some $ LitV $ LitInt (Z.lnot z)
  | MinusUnOp, LitV (LitInt z) => Some $ LitV $ LitInt (- z)
  | ZtoBOp, LitV (LitInt z) => Some $ LitV $ LitBool (Z_to_bool z)
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
  if decide (op = EqOp) then
    if decide (vals_compare_safe v1 v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => Some $ LitV $ bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | _, _ => None
    end.

Definition state_upd_heap (f : gmap loc val → gmap loc val) (σ : state) : state :=
  {| heap := f σ.(heap); tapes := σ.(tapes) |}.
Global Arguments state_upd_heap _ !_ /.

Definition state_upd_tapes (f : gmap loc tape → gmap loc tape) (σ : state) : state :=
  {| heap := σ.(heap); tapes := f σ.(tapes) |}.
Global Arguments state_upd_tapes _ !_ /.

Lemma state_upd_tapes_twice σ l n xs ys:
  state_upd_tapes <[l:=(n,ys)]> (state_upd_tapes <[l:=(n,xs)]> σ) = state_upd_tapes <[l:=(n,ys)]> σ.
Proof.
  rewrite /state_upd_tapes.
  simpl.
  f_equal.
  apply insert_insert.
Qed.

#[local] Open Scope R.

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
  | If (Val (LitV (LitBool true))) e1 e2  =>
      dret (e1 , σ1)
  | If (Val (LitV (LitBool false))) e1 e2 =>
      dret (e2 , σ1)
  | Fst (Val (PairV v1 v2)) =>
      dret (Val v1, σ1)
  | Snd (Val (PairV v1 v2)) =>
      dret (Val v2, σ1)
  | Case (Val (InjLV v)) e1 e2 =>
      dret (App e1 (Val v), σ1)
  | Case (Val (InjRV v)) e1 e2 =>
      dret (App e2 (Val v), σ1)
  | Alloc (Val v) =>
      let ℓ := fresh_loc σ1.(heap) in
      dret (Val $ LitV $ LitLoc ℓ, state_upd_heap <[ℓ:=v]> σ1)
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
  (* We use Z.to_nat, which maps positive integers to the corresponding nat, and the rest to 0 *)
  | AllocTape (Val (LitV (LitInt z))) =>
      let ℓ := fresh_loc σ1.(tapes) in
      dret (Val $ LitV $ LitLbl ℓ, state_upd_tapes <[ℓ:=(Z.to_nat z, [])]> σ1)
  (* Uniform sampling from {0 ... m}  *)
  | Rand (Val (LitV (LitInt z))) =>
      dmap (λ (n : nat), (Val $ LitV $ LitInt n, σ1)) (dunif (Z.to_nat z)) 
  (* Labelled sampling, conditional on tape contents *)
  | Rand (Val (LitV (LitLbl l))) =>
      match σ1.(tapes) !! l with
      | Some (m, (n :: ns)) => (* the tape is non-empty so we consume the first number *)
          dret (Val $ LitV $ LitInt (n : nat), state_upd_tapes <[l:=(m, ns)]> σ1)
      | Some (m, []) => (* the tape is allocated but empty, so we sample from {0 ... n} uniformly *)
          dmap (λ (n : nat), (Val $ LitV $ LitInt n, σ1)) (dunif m)
      | None => (* if the tape is not allocated, we do a fair probabilistic choice between 0 and 1 *)
          dmap (λ (n : nat), (Val $ LitV $ LitInt n, σ1)) (dunif 1)
      end
  | _ => dzero
  end.

Definition state_step (σ1 : state) (α : loc) : distr state :=
  if bool_decide (α ∈ dom σ1.(tapes)) then
    let: (m , ns) := (σ1.(tapes) !!! α) in
    dmap (λ n, state_upd_tapes (<[α := (m , ns ++ [n])]>) σ1) (dunif m)
  else dzero.

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
  destruct ρ, Ki;
    rewrite /pmf/=;
      repeat case_match; try (done || lra); try (inversion H; lra).
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
| AllocTapeS z σ l :
  l = fresh_loc σ.(tapes) →
  head_step_rel (AllocTape (Val (LitV (LitInt z)))) σ
    (Val $ LitV $ LitLbl l) (state_upd_tapes <[l:=(Z.to_nat z, [])]> σ)
| RandTapeS l m (n : nat) ns σ :
  σ.(tapes) !! l = Some (m, (n :: ns)) →
  head_step_rel (Rand (Val (LitV (LitLbl l)))) σ (Val $ LitV $ LitInt $ n) (state_upd_tapes <[l:=(m, ns)]> σ)
| RandTapeEmptyS l n m σ :
  σ.(tapes) !! l = Some (m, []) →
  n ≤ m →
  head_step_rel (Rand $ Val $ LitV $ LitLbl l) σ (Val $ LitV $ LitInt n) σ
| RandTapeUnallocS l n σ :
  σ.(tapes) !! l = None →
  n ≤ 1 →
  head_step_rel (Rand $ Val $ LitV $ LitLbl l) σ (Val $ LitV $ LitInt n) σ
| RandNoTape n m  σ:
  n ≤ Z.to_nat m →
  head_step_rel (Rand $ Val $ LitV $ LitInt m) σ (Val $ LitV $ LitInt n) σ.

Create HintDb head_step.
Global Hint Constructors head_step_rel : head_step.

Inductive state_step_rel : state → loc → state → Prop :=
| AddTapeS α m n ns σ :
  α ∈ dom σ.(tapes) →
  σ.(tapes) !!! α = (m, ns) →
  n ≤ m →
  state_step_rel σ α (state_upd_tapes <[α := (m, ns ++ [n])]> σ).
    
Ltac inv_head_step :=
  repeat
    match goal with
    | _ => progress simplify_map_eq/=; repeat case_match; inv_distr; eauto with head_step
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : is_Some (_ !! _) |- _ => destruct H
    end.

Lemma head_step_support_equiv_rel e1 e2 σ1 σ2 :
  head_step e1 σ1 (e2, σ2) > 0 ↔ head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intros ?. destruct e1; inv_head_step.
  - inversion 1; simplify_map_eq/=; solve_distr.
Qed.

Lemma state_step_support_equiv_rel σ1 α σ2 :
  state_step σ1 α σ2 > 0 ↔ state_step_rel σ1 α σ2.
Proof.
  rewrite /state_step. split.
  - case_bool_decide; [|intros; inv_distr].
    case_match. intros ?. inv_distr.
    econstructor; eauto with lia.
  - inversion_clear 1.  
    rewrite bool_decide_eq_true_2 //.
    rewrite H1. solve_distr.
Qed. 

Lemma list_app_to_cons {A} (l : list A) :
  (∃ y ys, l = ys ++ [y]) ->
  (∃ z zs, l = z :: zs).
Proof.
  destruct l.
  - intros (y & ys & Hy).
    pose proof (app_cons_not_nil _ _ _ Hy); done.
  - intros (y & ys & Hy).
    destruct ys as [ | x xs].
    + exists y. exists []. auto.
    + exists x. exists (xs ++ [y]). auto.
Qed.

Lemma state_step_head_step_not_stuck e σ σ' α :
  state_step σ α σ' > 0 → (∃ ρ, head_step e σ ρ > 0) ↔ (∃ ρ', head_step e σ' ρ' > 0).
Proof.
  rewrite state_step_support_equiv_rel.
  inversion 1; simplify_eq.
  split; intros [[e' σ'] Hs].
  - destruct e; inv_head_step; eexists; solve_distr.
  - destruct e; inv_head_step; eexists; solve_distr. 
Qed.

Lemma state_step_mass σ α :
  α ∈ dom σ.(tapes) → SeriesC (state_step σ α) = 1.
Proof.
  intros Hdom.
  rewrite /state_step bool_decide_eq_true_2 //=.
  case_match.
  rewrite dmap_mass dunif_mass //.
Qed.

Lemma head_step_mass e σ :
  (∃ ρ, head_step e σ ρ > 0) → SeriesC (head_step e σ) = 1.
Proof.
  intros [[] Hs%head_step_support_equiv_rel].
  inversion Hs;
    repeat (simplify_eq/=; solve_distr_mass || case_match).
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
  | Alloc e => 1 + height e
  | Load e => 1 + height e
  | Store e1 e2 => 1 + height e1 + height e2
  | AllocTape e => 1 + height e
  | Rand e => 1 + height e
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

Definition get_active (σ : state) : list loc := elements (dom σ.(tapes)).

Lemma state_step_get_active_mass σ α :
  α ∈ get_active σ → SeriesC (state_step σ α) = 1.
Proof. rewrite elem_of_elements. apply state_step_mass. Qed.

Lemma prob_lang_mixin :
  EctxiLanguageMixin of_val to_val fill_item decomp_item expr_ord head_step state_step get_active.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    state_step_head_step_not_stuck, state_step_get_active_mass, head_step_mass,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val,
    decomp_fill_item, decomp_fill_item_2, expr_ord_wf, decomp_expr_ord.
Qed.

End prob_lang.

(** Language *)
Canonical Structure prob_ectxi_lang := EctxiLanguage prob_lang.get_active prob_lang.prob_lang_mixin.
Canonical Structure prob_ectx_lang := EctxLanguageOfEctxi prob_ectxi_lang.
Canonical Structure prob_lang := LanguageOfEctx prob_ectx_lang.

(* Prefer prob_lang names over ectx_language names. *)
Export prob_lang.

Definition cfg : Type := expr * state.
