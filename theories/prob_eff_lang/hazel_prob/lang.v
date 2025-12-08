From Coq Require Import Reals Psatz.
From Coq.Program Require Import Wf.
From stdpp Require Export binders strings.
From stdpp Require Import gmap fin_maps countable fin.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.prob Require Export distribution.
From clutch.common Require Import language locations.
From iris.prelude Require Import options.


Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module eff_prob_lang_sec.

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc) | LitLbl (l : loc).
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp. (* Pointer offset *)

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
  | AllocTape (e : expr)
  | Rand (e1 e2 : expr)
  (* No-op operator used for cost *)
  | Tick (e : expr)
  (* Effects *)
  | Do (e : expr) 
  | Eff (v : val) (k : list ectx_item)
  | TryWith (e1 e2 e3 : expr) (* Why expressions here, when the syntax says values? (Taken from Hazel/Tes) *)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | Cont (k : list ectx_item)
(* with ectx :=
     | EmptyCtx
     | ConsCtx (ki : ectx_item) (k : ectx) *)
with ectx_item :=
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
  | AllocTapeCtx
  | RandLCtx (v2 : val)
  | RandRCtx (e1 : expr)
  | TickCtx
  | DoCtx
  | TryWithCtx (e1 e2 : expr). (* Same as for TryWith *)


Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Definition ectx := list ectx_item.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Definition to_eff (e : expr) : option (val * ectx) :=
  match e with
  | Eff v k => Some (v, k)
  | _ => None
  end. 

Notation of_eff := Eff (only parsing).

Lemma of_to_eff e v k : to_eff e = Some (v, k) → of_eff v k = e.
Proof. destruct e=>//=. by intros [= <- <-]. Qed.



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
Proof. destruct v as [ | | | [] | [] | ]; simpl; exact (decide _). Defined.

(** We just compare the word-sized representation of two values, without looking
into boxed data.  This works out fine if at least one of the to-be-compared
values is unboxed (exploiting the fact that an unboxed and a boxed value can
never be equal because these are disjoint sets). *)
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

Definition tape := { n : nat & list (fin (S n)) }.

Global Instance tape_inhabited : Inhabited tape := populate (existT 0%nat []).
Global Instance tape_eq_dec : EqDecision tape. Proof. apply _. Defined.
Global Instance tape_countable : EqDecision tape. Proof. apply _. Qed.

Global Instance tapes_lookup_total : LookupTotal loc tape (gmap loc tape).
Proof. apply map_lookup_total. Defined.
Global Instance tapes_insert : Insert loc tape (gmap loc tape).
Proof. apply map_insert. Defined.

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
     | AllocN e1 e2, AllocN e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Load e, Load e' => cast_if (decide (e = e'))
     | Store e1 e2, Store e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | AllocTape e, AllocTape e' => cast_if (decide (e = e'))
     | Rand e1 e2, Rand e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Tick e, Tick e' => cast_if (decide (e = e'))
     | Do e, Do e' => cast_if (decide (e = e'))
     | Eff e k, Eff e' k' => cast_if_and (decide (e = e')) (decide (k = k'))
     | TryWith e1 e2 e3, TryWith e1' e2' e3' => cast_if_and3 (decide (e1 = e1')) (decide (e2 = e2')) (decide (e3 = e3'))
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
     | Cont k, Cont k' => cast_if (decide (k = k')) 
     | _, _ => right _
     end
       with goectx (k1 k2 : ectx) {struct k1} : Decision (k1 = k2) := (* Something goes wrong here *)
       (* match k1, k2 with
          | EmptyCtx, EmptyCtx => left _
          | ConsCtx ki1 k1, ConsCtx ki2 k2 => cast_if_and (decide (ki1 = ki2)) (decide (k1 = k2))
          | _, _ => right _
          end  *)
      match k1, k2 with
      | [], [] => left _
      | ki1 :: k1', ki2 :: k2' => cast_if_and (decide (k1' = k2')) (decide (ki1 = ki2))
      | _, _ => right _
      end
   with goectxi (ki1 ki2 : ectx_item) {struct ki1} : Decision (ki1 = ki2) :=
     match ki1, ki2 with
     | AppLCtx v1, AppLCtx v2 => cast_if (decide (v1 = v2))
     | AppRCtx e1, AppRCtx e2 => cast_if (decide (e1 = e2))
     | UnOpCtx op1, UnOpCtx op2 => cast_if (decide (op1 = op2))
     | BinOpLCtx op1 v1, BinOpLCtx op2 v2 => cast_if_and (decide (op1 = op2)) (decide (v1 = v2))
     | BinOpRCtx op1 e1, BinOpRCtx op2 e2 => cast_if_and (decide (op1 = op2)) (decide (e1 = e2))
     | IfCtx e1 e1', IfCtx e2 e2' => cast_if_and (decide (e1 = e2)) (decide (e1' = e2'))
     | PairLCtx v1, PairLCtx v2 => cast_if (decide (v1 = v2))
     | PairRCtx e1, PairRCtx e2 => cast_if (decide (e1 = e2))
     | FstCtx, FstCtx => left _
     | SndCtx, SndCtx => left _
     | InjLCtx, InjLCtx => left _
     | InjRCtx, InjRCtx => left _
     | CaseCtx e1 e2, CaseCtx e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | AllocNLCtx v2, AllocNLCtx v2' => cast_if (decide (v2 = v2'))
     | AllocNRCtx e1, AllocNRCtx e1' => cast_if (decide (e1 = e1'))
     | LoadCtx, LoadCtx => left _
     | StoreLCtx v2, StoreLCtx v2' => cast_if (decide (v2 = v2'))
     | StoreRCtx e1, StoreRCtx e1' => cast_if (decide (e1 = e1'))
     | AllocTapeCtx, AllocTapeCtx => left _
     | RandLCtx v2, RandLCtx v2' => cast_if (decide (v2 = v2'))
     | RandRCtx e1, RandRCtx e1' => cast_if (decide (e1 = e1'))
     | TickCtx, TickCtx => left _
     | DoCtx, DoCtx => left _
     | TryWithCtx e1 e2, TryWithCtx e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | _, _ => right _
     end
   (*  *)
       for go); try (clear go gov goectx goectxi; abstract intuition congruence). Admitted. 

Global Instance val_eq_dec : EqDecision val.
Proof.
  intros ??. case (expr_eq_dec (Val x) (Val y)).
  - intros [= ->]. by left.
  - right. by intros ->.
Qed.

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
  | LeOp => 10 | LtOp => 11 | EqOp => 12 | OffsetOp => 13
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | 12 => EqOp | _ => OffsetOp
  end) _); by intros [].
Qed.
Global Instance expr_countable : Countable expr.
Proof.
    (* set (enc :=
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
           | AllocTape e => GenNode 15 [go e]
           | Rand e1 e2 => GenNode 16 [go e1; go e2]
           | Tick e => GenNode 17 [go e]
           | Do e => GenNode 18 [go e]
           | Eff v k => GenNode 19 [gov v; goectx k]
           | TryWith e1 e2 e3 => GenNode 20 [go e1; go e2; go e3]
           end
         with gov v :=
           match v with
           | LitV l => GenLeaf (inr (inl l))
           | RecV f x e =>
              GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
           | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
           | InjLV v' => GenNode 2 [gov v']
           | InjRV v' => GenNode 3 [gov v']
           | Cont k => GenNode 4 [goectx k]
           end
       
            (* with goectx k :=
             match k with
                | EmptyCtx => GenNode 0 []
                | ConsCtx ki k => GenNode 1 [goectxi ki; goectx k]
                end *)
       
         with goectx k :=
           match k with
           | [] => GenNode 0 []
           | ki :: k => GenNode 1 [goectxi ki; goectx k]
           end
       
         with goectxi ki :=
           match ki with
           | AppLCtx v2 => GenNode 0 [gov v2]
           | AppRCtx e1 => GenNode 1 [go e1]
           | DoCtx =>  GenNode 2 []
           | TryWithCtx e2 e3 => GenNode 3 [go e2; go e3]
           | UnOpCtx op => GenNode 4 [GenLeaf (inr (inr (inl op)))]
           | BinOpLCtx op v2 => GenNode 5 [GenLeaf (inr (inr (inr op))); gov v2]
           | BinOpRCtx op e1 => GenNode 6 [GenLeaf (inr (inr (inr op))); go e1]
           | IfCtx e1 e2 => GenNode 7 [go e1; go e2]
           | PairLCtx v2 => GenNode 8 [gov v2]
           | PairRCtx e1 => GenNode 9 [go e1]
           | FstCtx => GenNode 10 []
           | SndCtx => GenNode 11 []
           | InjLCtx => GenNode 12 []
           | InjRCtx => GenNode 13 []
           | CaseCtx e1 e2 => GenNode 14 [go e1; go e2]
           | AllocNLCtx v => GenNode 15 [gov v]
           | AllocNRCtx e => GenNode 16 [go e]
           | LoadCtx => GenNode 17 []
           | StoreLCtx v2 => GenNode 18 [gov v2]
           | StoreRCtx e1 => GenNode 19 [go e1]
           | AllocTapeCtx => GenNode 20 []
           | RandLCtx v => GenNode 21 [gov v]
           | RandRCtx e => GenNode 22 [go e]
           | TickCtx => GenNode 23 []
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
           | GenNode 15 [e] => AllocTape (go e)
           | GenNode 16 [e1; e2] => Rand (go e1) (go e2)
           | GenNode 17 [e] => Tick (go e)
           | GenNode 18 [e] => Do (go e)
           | GenNode 19 [v ; k] => Eff (gov v) (goectx k)
           | GenNode 20 [e1; e2; e3] => TryWith (go e1) (go e2) (go e3)
           | _ => Val $ LitV LitUnit (* dummy *)
           end
         with gov v :=
           match v with
           | GenLeaf (inr (inl l)) => LitV l
           | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => RecV f x (go e)
           | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
           | GenNode 2 [v'] => InjLV (gov v')
           | GenNode 3 [v'] => InjRV (gov v')
           | GenNode 4 [k] => Cont (goectx k)
           | _ => LitV LitUnit (* dummy *)
           end
             with goectx k :=
           (* match k with
              | GenNode 0 _ => EmptyCtx
              | GenNode 1 [ki; k] => ConsCtx (goectxi ki) (goectx k)
              | _ => EmptyCtx (* dummy *)
              end *)
         with goectx k :=
           match k with
           | GenNode 0 _ => []
           | GenNode 1 [ki; k] => (goectxi ki) :: (goectx k)
           | _ => [] (* dummy *)
           end
         with goectxi ki :=
           match ki with
           | GenNode 0 [v] => AppLCtx (gov v)
           | GenNode 1 [e] => AppRCtx (go e)
           | GenNode 2 [] => DoCtx
           | GenNode 3 [e1; e2] => TryWithCtx (go e1) (go e2)
           | GenNode 4 [GenLeaf (inr (inr (inl op)))] => UnOpCtx op
           | GenNode 5 [GenLeaf (inr (inr (inr op))); v] => BinOpLCtx op (gov v)
           | GenNode 6 [GenLeaf (inr (inr (inr op))); e] => BinOpRCtx op (go e)
           | GenNode 7 [e1; e2] => IfCtx (go e1) (go e2)
           | GenNode 8 [v] => PairLCtx (gov v)
           | GenNode 9 [e] => PairRCtx (go e)
           | GenNode 10 [] => FstCtx
           | GenNode 11 [] => SndCtx
           | GenNode 12 [] => InjLCtx
           | GenNode 13 [] => InjRCtx
           | GenNode 14 [e1; e2] => CaseCtx (go e1) (go e2)
           | GenNode 15 [v] => AllocNLCtx (gov v)
           | GenNode 16 [e] => AllocNRCtx (go e)
           | GenNode 17 [] => LoadCtx
           | GenNode 18 [v] => StoreLCtx (gov v)
           | GenNode 19 [e] => StoreRCtx (go e)
           | GenNode 20 [] => AllocTapeCtx 
           | GenNode 21 [v] => RandLCtx (gov v)
           | GenNode 22 [e] => RandRCtx (go e)
           | GenNode 23 [] => TickCtx
           | _ => DoCtx (* dummy *)
           end 
         for go).
       refine (inj_countable' enc dec _).
       refine (fix  go      (e  : expr)      {struct e}  := _
             with gov            (v  : val)       {struct v}  := _
             with goectx         (k  : ectx)      {struct k}  := _
             with goectxi        (ki : ectx_item) {struct ki} := _ for go).
       - destruct e as [v| | | | | | | | | | | | | | | | | | | | |  ]; simpl; f_equal;
           [exact (gov v)| try done.. ]; exact (goectx k).
       - exact (gov v); f_equal.
       - destruct k as [|ki k]; simpl; f_equal; try done; exact (goectxi ki).
       - destruct ki; by f_equal. *)
      Admitted. 
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
  | AllocTapeCtx => AllocTape e
  | RandLCtx v2 => Rand e (Val v2)
  | RandRCtx e1 => Rand e1 e
  | TickCtx => Tick e
  | DoCtx => Do e
  | TryWithCtx e1 e2 => TryWith e e1 e2
  end.



Definition fill (K : ectx) (e : expr) : expr :=   foldl (flip fill_item) e K.
  (* match K with
     | EmptyCtx => e
     | ConsCtx ki k => fill_item ki (fill k e)
     end. *)


Definition decomp_item (e : expr) : option (ectx_item * expr) :=
  let noval (e : expr) (ei : ectx_item) :=
    match e with Val _ | Eff _ _ => None |  _ => Some (ei, e) end in
  match e with
  | App e1 e2      =>
      match e2 with
      | (Val v)      => noval e1 (AppLCtx v)
      | Eff _ _      => None
      | _            => Some (AppRCtx e1, e2)
      end
  | UnOp op e        => noval e (UnOpCtx op)
  | BinOp op e1 e2   =>
      match e2 with
      | Val v        => noval e1 (BinOpLCtx op v)
      | Eff _ _      => None
      | _            => Some (BinOpRCtx op e1, e2)
      end
  | If e0 e1 e2      => noval e0 (IfCtx e1 e2)
  | Pair e1 e2       =>
      match e2 with
      | Val v        => noval e1 (PairLCtx v)
      | Eff _ _      => None
      | _            => Some (PairRCtx e1, e2)
      end
  | Fst e            => noval e FstCtx
  | Snd e            => noval e SndCtx
  | InjL e           => noval e InjLCtx
  | InjR e           => noval e InjRCtx
  | Case e0 e1 e2    => noval e0 (CaseCtx e1 e2)
  | AllocN e1 e2     =>
      match e2 with
      | Val v        => noval e1 (AllocNLCtx v)
      | Eff _ _      => None
      | _            => Some (AllocNRCtx e1, e2)
      end
  | Load e           => noval e LoadCtx
  | Store e1 e2      =>
      match e2 with
      | Val v        => noval e1 (StoreLCtx v)
      | Eff _ _      => None
      | _            => Some (StoreRCtx e1, e2)
      end
  | AllocTape e      => noval e AllocTapeCtx
  | Rand e1 e2       =>
      match e2 with
      | Val v        => noval e1 (RandLCtx v)
      | Eff _ _      => None
      | _            => Some (RandRCtx e1, e2)
      end
  | Tick e           => noval e TickCtx
  | Do e             => noval e DoCtx
  | TryWith e0 e1 e2 => noval e0 (TryWithCtx e1 e2)
  | _ => None
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
  | AllocTape e => AllocTape (subst x v e)
  | Rand e1 e2 => Rand (subst x v e1) (subst x v e2)
  | Tick e => Tick (subst x v e)
  | Do e => Do (subst x v e)
  | TryWith e1 e2 e3 => TryWith (subst x v e1) (subst x v e2) (subst x v e3)
  | Eff _ _ => e 
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => λ x, x end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt z) => Some $ LitV $ LitInt (Z.lnot z)
  | MinusUnOp, LitV (LitInt z) => Some $ LitV $ LitInt (- z)
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
  | OffsetOp => LitInt (n1 + n2) (* Treat offsets as ints *)
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
  | OffsetOp => None
  end.

Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
  | LeOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 ≤ₗ l2))
  | LtOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 <ₗ l2))
  | _, _ => None
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
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => None
    end.

Definition state_upd_heap (f : gmap loc val → gmap loc val) (σ : state) : state :=
  {| heap := f σ.(heap); tapes := σ.(tapes) |}.
Global Arguments state_upd_heap _ !_ /.

Definition state_upd_tapes (f : gmap loc tape → gmap loc tape) (σ : state) : state :=
  {| heap := σ.(heap); tapes := f σ.(tapes) |}.
Global Arguments state_upd_tapes _ !_ /.

Lemma state_upd_tapes_twice σ l n xs ys :
  state_upd_tapes <[l:=(n; ys)]> (state_upd_tapes <[l:=(n; xs)]> σ) = state_upd_tapes <[l:=(n; ys)]> σ.
Proof. rewrite /state_upd_tapes /=. f_equal. apply insert_insert. Qed.

Lemma state_upd_tapes_same σ σ' l n xs ys :
  state_upd_tapes <[l:=(n; ys)]> σ = state_upd_tapes <[l:=(n; xs)]> σ' -> xs = ys.
Proof. rewrite /state_upd_tapes /=. intros K. simplify_eq.
       rewrite map_eq_iff in H.
       specialize (H l).
       rewrite !lookup_insert in H.
       by simplify_eq.
Qed.


Lemma state_upd_tapes_no_change σ l n ys :
  tapes σ !! l = Some (n; ys)-> 
  state_upd_tapes <[l:=(n; ys)]> σ = σ .
Proof.
  destruct σ as [? t]. simpl.
  intros Ht.
  f_equal.
  apply insert_id. done.
Qed.

Lemma state_upd_tapes_same' σ σ' l n xs (x y : fin (S n)) :
  state_upd_tapes <[l:=(n; xs++[x])]> σ = state_upd_tapes <[l:=(n; xs++[y])]> σ' -> x = y.
Proof. intros H. apply state_upd_tapes_same in H.
       by simplify_eq.
Qed.

Lemma state_upd_tapes_neq' σ σ' l n xs (x y : fin (S n)) :
  x≠y -> state_upd_tapes <[l:=(n; xs++[x])]> σ ≠ state_upd_tapes <[l:=(n; xs++[y])]> σ'.
Proof. move => H /state_upd_tapes_same ?. simplify_eq.
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

Lemma state_upd_tapes_heap σ l1 l2 n xs m v :
  state_upd_tapes <[l2:=(n; xs)]> (state_upd_heap_N l1 m v σ) =
  state_upd_heap_N l1 m v (state_upd_tapes <[l2:=(n; xs)]> σ).
Proof.
  by rewrite /state_upd_tapes /state_upd_heap_N /=.
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
  (* Since our language only has integers, we use Z.to_nat, which maps positive
     integers to the corresponding nat, and the rest to 0. We sample from
     [dunifP N = dunif (1 + N)] to avoid the case [dunif 0 = dzero]. *)
  (* Uniform sampling from [0, 1 , ..., N] *)
  | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) =>
      dmap (λ n : fin _, (Val $ LitV $ LitInt n, σ1)) (dunifP (Z.to_nat N))
  | AllocTape (Val (LitV (LitInt z))) =>
      let ι := fresh_loc σ1.(tapes) in
      dret (Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := (Z.to_nat z; []) ]> σ1)
  (* Labelled sampling, conditional on tape contents *)
  | Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))) =>
      match σ1.(tapes) !! l with
      | Some (M; ns) =>
          if bool_decide (M = Z.to_nat N) then
            match ns  with
            | n :: ns =>
                (* the tape is non-empty so we consume the first number *)
                dret (Val $ LitV $ LitInt $ fin_to_nat n, state_upd_tapes <[l:=(M; ns)]> σ1)
            | [] =>
                (* the tape is allocated but empty, so we sample from [0, 1, ..., M] uniformly *)
                dmap (λ n : fin _, (Val $ LitV $ LitInt n, σ1)) (dunifP M)
            end
          else
            (* bound did not match the bound of the tape *)
            dmap (λ n : fin _, (Val $ LitV $ LitInt n, σ1)) (dunifP (Z.to_nat N))
      | None => dzero
      end
  | Tick (Val (LitV (LitInt n))) => dret (Val $ LitV $ LitUnit, σ1)
  (* | Do (Val v) => dret (Eff v EmptyCtx, σ1) *)
  | Do (Val v) => dret (Eff v [], σ1)
  | TryWith (Val v) h r => dret (App r (Val v), σ1)
  | TryWith (Eff v k) h r => dret (App (App h (Val v)) (Val (Cont k)), σ1)
  | App (Val (Cont k)) (Val v) => dret (fill k (Val v), σ1)
  (* Eff v k eating up the context *)
  (* | App (Eff v1 k) (Val v2) => dret (Eff v1 (ConsCtx (AppLCtx v2) k), σ1)
     | App e (Eff v k) => dret (Eff v (ConsCtx (AppRCtx e) k), σ1)
     | UnOp op (Eff v k) => dret (Eff v (ConsCtx (UnOpCtx op) k), σ1)
     | BinOp op (Eff v1 k) (Val v2) => dret (Eff v1 (ConsCtx (BinOpLCtx op v2) k), σ1)
     | BinOp op e (Eff v k) => dret (Eff v (ConsCtx (BinOpRCtx op e) k), σ1)
     | If (Eff v k) e1 e2 => dret (Eff v (ConsCtx(IfCtx e1 e2) k), σ1)
     | Pair (Eff v1 k) (Val v2) => dret (Eff v1 (ConsCtx (PairLCtx v2) k), σ1)
     | Pair e (Eff v k) => dret (Eff v (ConsCtx (PairRCtx e) k), σ1)
     | Fst (Eff v k) => dret (Eff v (ConsCtx FstCtx k), σ1)
     | Snd (Eff v k) => dret (Eff v (ConsCtx SndCtx k), σ1)
     | InjL (Eff v k) => dret (Eff v (ConsCtx InjLCtx k), σ1)
     | InjR (Eff v k) => dret (Eff v (ConsCtx InjRCtx k), σ1)
     | Case (Eff v k) e1 e2 => dret (Eff v (ConsCtx (CaseCtx e1 e2) k), σ1)
     | AllocN (Eff v1 k) (Val v2) => dret (Eff v1 (ConsCtx (AllocNLCtx v2) k), σ1)
     | AllocN e (Eff v k) => dret (Eff v (ConsCtx (AllocNRCtx e) k), σ1)
     | Load (Eff v k) => dret (Eff v (ConsCtx LoadCtx k), σ1)
     | Store (Eff v1 k) (Val v2) => dret (Eff v1 (ConsCtx (StoreLCtx v2) k), σ1)
     | Store e (Eff v k) => dret (Eff v (ConsCtx (StoreRCtx e) k), σ1)
     | AllocTape (Eff v k) => dret (Eff v (ConsCtx AllocTapeCtx k), σ1)
     | Rand (Eff v1 k) (Val v2) => dret (Eff v1 (ConsCtx (RandLCtx v2) k), σ1)
     | Rand e (Eff v k) => dret (Eff v (ConsCtx (RandRCtx e) k), σ1)
     | Tick (Eff v k) => dret (Eff v (ConsCtx TickCtx k), σ1)
     | Do (Eff v k) => dret (Eff v (ConsCtx DoCtx k), σ1) *)
  | App (Eff v1 k) (Val v2) => dret (Eff v1 (k ++ [(AppLCtx v2)]), σ1)
  | App e (Eff v k) => dret (Eff v (k ++ [(AppRCtx e)]), σ1)
  | UnOp op (Eff v k) => dret (Eff v (k ++ [(UnOpCtx op)]), σ1)
  | BinOp op (Eff v1 k) (Val v2) => dret (Eff v1 (k ++[(BinOpLCtx op v2)]), σ1)
  | BinOp op e (Eff v k) => dret (Eff v (k ++ [(BinOpRCtx op e)]), σ1)
  | If (Eff v k) e1 e2 => dret (Eff v (k ++ [(IfCtx e1 e2)]), σ1)
  | Pair (Eff v1 k) (Val v2) => dret (Eff v1 (k ++ [(PairLCtx v2)]), σ1)
  | Pair e (Eff v k) => dret (Eff v (k ++ [(PairRCtx e)]), σ1)
  | Fst (Eff v k) => dret (Eff v (k ++ [FstCtx]), σ1)
  | Snd (Eff v k) => dret (Eff v (k ++ [SndCtx]), σ1)
  | InjL (Eff v k) => dret (Eff v (k ++ [InjLCtx]), σ1)
  | InjR (Eff v k) => dret (Eff v (k ++ [InjRCtx]), σ1)
  | Case (Eff v k) e1 e2 => dret (Eff v (k ++ [(CaseCtx e1 e2)]), σ1)
  | AllocN (Eff v1 k) (Val v2) => dret (Eff v1 (k ++ [(AllocNLCtx v2)]), σ1)
  | AllocN e (Eff v k) => dret (Eff v (k ++ [(AllocNRCtx e)]), σ1)
  | Load (Eff v k) => dret (Eff v (k ++ [LoadCtx]), σ1)
  | Store (Eff v1 k) (Val v2) => dret (Eff v1 (k ++ [(StoreLCtx v2)]), σ1)
  | Store e (Eff v k) => dret (Eff v (k ++ [(StoreRCtx e)]), σ1)
  | AllocTape (Eff v k) => dret (Eff v (k ++ [AllocTapeCtx]), σ1)
  | Rand (Eff v1 k) (Val v2) => dret (Eff v1 (k ++ [(RandLCtx v2)]), σ1)
  | Rand e (Eff v k) => dret (Eff v (k ++ [(RandRCtx e)]), σ1)
  | Tick (Eff v k) => dret (Eff v (k ++ [TickCtx]), σ1)
  | Do (Eff v k) => dret (Eff v (k ++ [DoCtx]), σ1)
  | _ => dzero
  end.

Definition state_step (σ1 : state) (α : loc) : distr state :=
  if bool_decide (α ∈ dom σ1.(tapes)) then
    let: (N; ns) := (σ1.(tapes) !!! α) in
    dmap (λ n, state_upd_tapes (<[α := (N; ns ++ [n])]>) σ1) (dunifP N)
  else dzero.

Lemma state_step_unfold σ α N ns:
  tapes σ !! α = Some (N; ns) ->
  state_step σ α = dmap (λ n, state_upd_tapes (<[α := (N; ns ++ [n])]>) σ) (dunifP N).
Proof.
  intros H.
  rewrite /state_step.
  rewrite bool_decide_eq_true_2; last first.
  { by apply elem_of_dom. }
  by rewrite (lookup_total_correct (tapes σ) α (N; ns)); last done.
Qed.

(** Basic properties about the language *)
Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof. apply foldl_app. Qed.


Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Global Instance fill_inj K : Inj (=) (=) (fill K).
Proof. induction K as [|Ki K IH]; rewrite /Inj; naive_solver. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma fill_item_eff Ki e : to_eff (fill_item Ki e) = None.
Proof. induction Ki; simplify_option_eq; eauto. Qed.

Lemma fill_val K e :
  is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  generalize dependent e.
  induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val.
Qed.

Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
Proof.  rewrite !eq_None_not_Some. eauto using fill_val. Qed.
  

Lemma fill_not_eff K e : to_eff e = None → to_eff (fill K e) = None.
Proof.
  generalize dependent e.
  induction K as [|Ki K]; eauto.
  induction Ki; simplify_option_eq; eauto.
Qed.

(* Lemma fill_eff K e v k : to_eff (fill K e) = Some (v, k) → K = [] ∧ e = Eff v k.
   Proof.
     destruct K as [|Ki K].
     - intros Heq. by rewrite (of_to_eff _ _ _ Heq).
   Admitted.  *)


(* Lemma fill_eff' K e v k : fill K e = of_eff v k → K = EmptyCtx ∧ e = Eff v k.
   Proof. intros Heq. apply fill_eff. by rewrite Heq. Qed. *)


(* Lemma alloc_fresh v σ :
     let l := Loc.fresh (dom σ.(heap)) in
     head_step (Alloc (Val v))                                  σ
               (Val $ LitV $ LitLoc l) (state_upd_heap <[l:=v]> σ).
   Proof.
     intros.
     apply AllocS.
     intros. apply (not_elem_of_dom (D := gset loc)).
     rewrite <-(Loc.add_0 l).
     by apply Loc.fresh_fresh.
   Qed. *)

Lemma val_head_stuck e σ ρ :
  head_step e σ ρ > 0 → to_val e = None.
Proof. destruct ρ, e; [|done..]. rewrite /pmf /=. lra. Qed.
Lemma eff_head_stuck e σ ρ :
  head_step e σ ρ > 0 → to_eff e = None.
Proof. destruct ρ, e; [|try done..].
       - intros ?. simpl. done.
       - rewrite /pmf /=. lra. Qed.
(* The following lemma doens't hold any longer, since Eff v N is not a value, but do take computional steps
Lemma head_ctx_step_val Ki e σ ρ :
     head_step (fill_item Ki e) σ ρ > 0 → is_Some (to_val e).
   Proof.
     destruct ρ, Ki ;
       rewrite /pmf/= ;
                 repeat case_match; clear -H ; inversion H; intros; (lra || done).
   Qed.
However, the following modification holds. *)
Lemma head_ctxi_step_val Ki e σ ρ :
  to_eff e = None -> 
     head_step (fill_item Ki e) σ ρ > 0 → is_Some (to_val e).
Proof.
  destruct ρ, Ki ;
              rewrite /pmf/= ;
              repeat case_match; clear -H ; inversion H; intros; (lra || done).
Qed. 

Lemma head_ctx_step_val K e σ ρ :
  to_eff e = None -> 
     head_step (fill K e) σ ρ > 0 → is_Some (to_val e) ∨ K = [].
Proof.
  destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
      rewrite fill_app /=.
      intros Heff ?%head_ctxi_step_val; eauto using fill_val, fill_not_eff.
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
| RandNoTapeS z N (n : fin (S N)) σ:
  N = Z.to_nat z →
  head_step_rel (Rand (Val $ LitV $ LitInt z) (Val $ LitV LitUnit)) σ (Val $ LitV $ LitInt n) σ
| AllocTapeS z N σ l :
  l = fresh_loc σ.(tapes) →
  N = Z.to_nat z →
  head_step_rel (AllocTape (Val (LitV (LitInt z)))) σ
    (Val $ LitV $ LitLbl l) (state_upd_tapes <[l := (N; []) : tape]> σ)
| RandTapeS l z N n ns σ :
  N = Z.to_nat z →
  σ.(tapes) !! l = Some ((N; n :: ns) : tape)  →
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl l)))) σ
    (Val $ LitV $ LitInt $ n) (state_upd_tapes <[l := (N; ns) : tape]> σ)
| RandTapeEmptyS l z N (n : fin (S N)) σ :
  N = Z.to_nat z →
  σ.(tapes) !! l = Some ((N; []) : tape) →
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitInt n) σ
| RandTapeOtherS l z M N ms (n : fin (S N)) σ :
  N = Z.to_nat z →
  σ.(tapes) !! l = Some ((M; ms) : tape) →
  N ≠ M →
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitInt n) σ
| TickS σ z :
  head_step_rel (Tick $ Val $ LitV $ LitInt z) σ (Val $ LitV $ LitUnit) σ
(* Do. *)
| DoS v σ :
  head_step_rel (Do (Val v)) σ (Eff v []) σ
(* TryWithEff. *)
| TryWithEffS v k e2 e3 σ :
  head_step_rel (TryWith (Eff v k) e2 e3)             σ
    (App (App e2 (Val v)) (Val (Cont k))) σ
(* TryWithRet. *)
| TryWithRetS v e2 e3 σ :
  head_step_rel (TryWith (Val v) e2 e3) σ (App e3 (Val v)) σ
| ContS k v σ :
  head_step_rel (App (Val (Cont k)) (Val v)) σ (fill k (Val v)) σ
(* AppLCtx. *)
| AppLEffS v1 k v2 σ :
  head_step_rel (App (Eff v1 k) (Val v2))    σ
    (Eff v1 (k ++ [(AppLCtx v2)])) σ
(* AppRCtx. *)
| AppREffS e1 v1 k σ :
  head_step_rel (App e1 (Eff v1 k))          σ
    (Eff v1 (k ++ [(AppRCtx e1)])) σ
(* UnOpCtx. *)
| UnOpEffS op v k σ :
  head_step_rel (UnOp op (Eff v k))         σ
    (Eff v (k ++ [(UnOpCtx op)])) σ
(* BinOpLCtx. *)
| BinOpLEffS op v1 k v2 σ :
  head_step_rel (BinOp op (Eff v1 k) (Val v2))    σ
    (Eff v1 (k ++ [(BinOpLCtx op v2)])) σ
(* BinOpRCtx. *)
| BinOpREffS op e1 v2 k σ :
  head_step_rel (BinOp op e1 (Eff v2 k))          σ
    (Eff v2 (k ++ [(BinOpRCtx op e1)])) σ
(* IfCtx. *)
| IfEffS v k e1 e2 σ :
  head_step_rel (If (Eff v k) e1 e2)         σ
    (Eff v (k ++ [(IfCtx e1 e2)])) σ
(* PairLCtx. *)
| PairLEffS v1 k v2 σ :
  head_step_rel (Pair (Eff v1 k) (Val v2))    σ
    (Eff v1 (k ++ [(PairLCtx v2)])) σ
(* PairRCtx. *)
| PairREffS e1 v2 k σ :
  head_step_rel (Pair e1 (Eff v2 k))          σ
    (Eff v2 (k ++ [(PairRCtx e1)])) σ
(* FstCtx. *)
| FstEffS v k σ :
  head_step_rel (Fst (Eff v k))       σ
    (Eff v (k ++ [FstCtx])) σ
(* SndCtx. *)
| SndEffS v k σ :
  head_step_rel (Snd (Eff v k))       σ
    (Eff v (k ++ [SndCtx])) σ
(* InjLCtx. *)
| InjLEffS v k σ :
  head_step_rel (InjL (Eff v k))       σ
    (Eff v (k ++ [InjLCtx])) σ
(* InjRCtx. *)
| InjREffS v k σ :
  head_step_rel (InjR (Eff v k))       σ
    (Eff v (k ++ [InjRCtx])) σ
(* CaseCtx. *)
| CaseEffS v k e1 e2 σ :
  head_step_rel (Case (Eff v k) e1 e2)         σ
    (Eff v (k++ [(CaseCtx e1 e2)])) σ
(* AllocNLCtx. *)
| AllocNLEffS v1 k v2 σ :
  head_step_rel (AllocN (Eff v1 k) (Val v2))      σ
    (Eff v1 (k ++ [(AllocNLCtx v2)])) σ
(* AllocNRCtx. *)
| AllocNREffS v k e σ :
  head_step_rel (AllocN e (Eff v k))      σ
    (Eff v (k ++ [(AllocNRCtx e)])) σ
(* LoadCtx. *)
| LoadEffS v k σ :
  head_step_rel (Load (Eff v k))       σ
    (Eff v (k ++ [LoadCtx])) σ
(* StoreLCtx. *)
| StoreLEffS v1 k v2 σ :
  head_step_rel (Store (Eff v1 k) (Val v2))    σ
    (Eff v1 (k ++ [(StoreLCtx v2)])) σ
(* StoreRCtx. *)
| StoreREffS e1 v2 k σ :
  head_step_rel (Store e1 (Eff v2 k))          σ
    (Eff v2 (k ++ [(StoreRCtx e1)])) σ
(* AllocTapeCtx *)
| AllocTapeEffS v k σ :
  head_step_rel (AllocTape (Eff v k)) σ (Eff v (k ++ [AllocTapeCtx])) σ
(* RandLCtx *)
| RandLEffS v1 k v2 σ :
  head_step_rel (Rand (Eff v1 k) (Val v2)) σ (Eff v1 (k ++ [(RandLCtx v2)])) σ
(* RandRCtx *)
| RandREffS e v k σ :
  head_step_rel (Rand e (Eff v k)) σ (Eff v (k ++ [(RandRCtx e)])) σ
(* TickCtx *)
| TickEffS v k σ :
  head_step_rel (Tick (Eff v k)) σ (Eff v (k ++ [TickCtx])) σ
(* DoCtx. *)
| DoEffS v k σ :
  head_step_rel (Do (Eff v k))         σ
    (Eff v (k ++ [DoCtx])) σ.


Create HintDb head_step.
Global Hint Constructors head_step_rel : head_step.
(* 0%fin always has non-zero mass, so propose this choice if the reduct is
   unconstrained. *)
Global Hint Extern 1
  (head_step_rel (Rand (Val (LitV _)) (Val (LitV LitUnit))) _ _ _) =>
         eapply (RandNoTapeS _ _ 0%fin) : head_step.
Global Hint Extern 1
  (head_step_rel (Rand (Val (LitV _)) (Val (LitV (LitLbl _)))) _ _ _) =>
         eapply (RandTapeEmptyS _ _ _ 0%fin) : head_step.
Global Hint Extern 1
  (head_step_rel (Rand (Val (LitV _)) (Val (LitV (LitLbl _)))) _ _ _) =>
         eapply (RandTapeOtherS _ _ _ _ _ 0%fin) : head_step.

Inductive state_step_rel : state → loc → state → Prop :=
| AddTapeS α N (n : fin (S N)) ns σ :
  α ∈ dom σ.(tapes) →
  σ.(tapes) !!! α = ((N; ns) : tape) →
  state_step_rel σ α (state_upd_tapes <[α := (N; ns ++ [n]) : tape]> σ).

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

(* TODO: Automate the proof *)
Lemma head_step_support_equiv_rel e1 e2 σ1 σ2 :
  head_step e1 σ1 (e2, σ2) > 0 ↔ head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intros ?. destruct e1; inv_head_step; eauto with head_step.
  - inversion 1; simplify_map_eq/=; try case_bool_decide; simplify_eq; solve_distr; try real_solver.
    + unfold head_step; induction e0; solve_distr; destruct v; solve_distr.
    + unfold head_step; induction e0; solve_distr; destruct v; solve_distr.
    + unfold head_step; induction e0; solve_distr; destruct v; solve_distr.
    + unfold head_step; induction e; solve_distr; destruct v0; solve_distr; destruct l; solve_distr.
    + unfold head_step; induction e0; solve_distr; destruct v; solve_distr; destruct l; solve_distr.
    + unfold head_step; induction e; solve_distr; destruct v0; solve_distr; destruct l; solve_distr.
Qed.

Lemma state_step_support_equiv_rel σ1 α σ2 :
  state_step σ1 α σ2 > 0 ↔ state_step_rel σ1 α σ2.
Proof.
  rewrite /state_step. split.
  - case_bool_decide; [|intros; inv_distr].
    case_match. intros ?. inv_distr.
    econstructor; eauto with lia.
  - inversion_clear 1.
    rewrite bool_decide_eq_true_2 // H1. solve_distr.
Qed.

Lemma state_step_head_step_not_stuck e σ σ' α :
  state_step σ α σ' > 0 → (∃ ρ, head_step e σ ρ > 0) ↔ (∃ ρ', head_step e σ' ρ' > 0).
Proof.
  rewrite state_step_support_equiv_rel.
  inversion_clear 1.
  split; intros [[e2 σ2] Hs].
  (* TODO: the sub goals used to be solved by [simplify_map_eq]  *)
  - destruct e; inv_head_step; try by (unshelve (eexists; solve_distr)).
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert in H11. done.
      * rewrite lookup_insert_ne // in H11. rewrite H11 in H7. done.
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert in H11. done.
      * rewrite lookup_insert_ne // in H11. rewrite H11 in H7. done.
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert in H10. done.
      * rewrite lookup_insert_ne // in H10. rewrite H10 in H7. done.
  - destruct e; inv_head_step; try by (unshelve (eexists; solve_distr)).
    + destruct (decide (α = l1)); simplify_eq.
      * apply not_elem_of_dom_2 in H11. done.
      * rewrite lookup_insert_ne // in H7. rewrite H11 in H7.  done.
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert // in H7.
        apply not_elem_of_dom_2 in H11. done.
      * rewrite lookup_insert_ne // in H7. rewrite H11 in H7. done.
    + destruct (decide (α = l1)); simplify_eq.
      * rewrite lookup_insert // in H7.
        apply not_elem_of_dom_2 in H10. done.
      * rewrite lookup_insert_ne // in H7. rewrite H10 in H7. done.
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
  | AllocTape e => 1 + height e
  | Rand e1 e2 => 1 + height e1 + height e2
  | Tick e => 1 + height e
  | Do e => 1 + height e
  | Eff v k => 1 (* I don't know *)
  | TryWith e1 e2 e3 => 1 + height e1 + height e2 + height e3
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
Lemma decomp_expr_ord Ki (e e' : expr) : decomp_item e = Some (Ki, e') → expr_ord e' e.
Proof.
  rewrite /expr_ord /decomp_item.
  destruct Ki ; repeat destruct_match ; intros [=] ; subst ; cbn ; lia.
Qed.

Lemma decomp_fill_item Ki e :
  to_eff e = None →
  to_val e = None → decomp_item (fill_item Ki e) = Some (Ki, e).
Proof. destruct Ki ; simpl ; try by repeat destruct_match. Qed.

(* TODO: this proof is slow, but I do not see how to make it faster... *)
Lemma decomp_fill_item_2 e e' Ki :
  decomp_item e = Some (Ki, e') → fill_item Ki e' = e ∧ to_val e' = None.
Proof.
  rewrite /decomp_item ;
    destruct e ; try done ;
    destruct Ki ; cbn ; repeat destruct_match ; intros [=] ; subst ; auto.
Qed.

Definition get_active (σ : state) : list loc := elements (dom σ.(tapes)).

Lemma state_step_get_active_mass σ α :
  α ∈ get_active σ → SeriesC (state_step σ α) = 1.
Proof. rewrite elem_of_elements. apply state_step_mass. Qed.

Lemma state_steps_mass σ αs :
  αs ⊆ get_active σ →
  SeriesC (foldlM state_step σ αs) = 1.
Proof.
  induction αs as [|α αs IH] in σ |-* ; intros Hact.
  { rewrite /= dret_mass //. }
  rewrite foldlM_cons.
  rewrite dbind_det //.
  - apply state_step_get_active_mass. set_solver.
  - intros σ' Hσ'. apply IH.
    apply state_step_support_equiv_rel in Hσ'.
    inversion Hσ'; simplify_eq.
    intros α' ?. rewrite /get_active /=.
    apply elem_of_elements, elem_of_dom.
    destruct (decide (α = α')); subst.
    + eexists. rewrite lookup_insert //.
    + rewrite lookup_insert_ne //.
      apply elem_of_dom. eapply elem_of_elements, Hact. by right.
Qed.

Program Fixpoint decomp (e : expr) {wf expr_ord e} : ectx * expr :=
    match decomp_item e with
    | Some (Ki, e') => let '(K, e'') := decomp e' in (K ++ [Ki], e'')
    | None => ([], e)
    end.

Solve Obligations with eauto using decomp_expr_ord, expr_ord_wf.

Definition fill_lift (K : ectx) : (expr * state) → (expr * state) :=
    λ '(e, σ), (fill K e, σ).

Definition prim_step (e1 : expr) (σ1 : state) : distr (expr * state) :=
    let '(K, e1') := decomp e1 in
    dmap (fill_lift K) (head_step e1' σ1).


Lemma decomp_unfold e :
    decomp e =
      match decomp_item e with
      | Some (Ki, e') => let '(K, e'') := decomp e' in (K ++ [Ki], e'')
      | None => ([], e)
      end.
Proof.
  rewrite /decomp WfExtensionality.fix_sub_eq_ext /= -/decomp.
  repeat case_match; try done.
Qed.

Lemma decomp_fill_comp K K' e e' :
  to_eff e = None → 
  to_val e = None → decomp e = (K', e') → decomp (fill K e) = (K' ++ K, e').
Proof.
  revert K' e e'.
  induction K as [|Ki K] using rev_ind.
  { intros ??? =>/=.  rewrite app_nil_r. done. }
  intros K' e e' Hval Hre. rewrite fill_app /=.
  intro.
  rewrite decomp_unfold.
  rewrite decomp_fill_item; [|auto using fill_not_eff |auto using fill_not_val ].
  rewrite (IHK K' _ e') //=. 
  rewrite !app_assoc //.
Qed.

Lemma decomp_inv_nil e e' :
    decomp e = ([], e') → decomp_item e = None ∧ e = e'.
Proof.
  rewrite decomp_unfold.
  destruct (decomp_item e) as [[Ki e'']|] eqn:Heq; [|by intros [=]].
  destruct (decomp e''). intros [= Hl He].
  apply app_eq_nil in Hl as (_ & Hcontra). inversion Hcontra.
Qed.

Lemma list_snoc_singleton_inv {A} (l1 l2 : list A) (a1 a2 : A) :
  l1 ++ [a1] = l2 ++ [a2] → l1 = l2 ∧ a1 = a2.
Proof.
  revert l2. induction l1 as [|a l1].
  { intros [| ? []] [=]=>//. }
  intros [].
  - intros [=]; destruct l1; simplify_eq.
  - intros [= -> []%IHl1]. simplify_eq=>//.
Qed.

Lemma decomp_inv_cons Ki K e e'' :
  decomp e = (K ++ [Ki], e'') → ∃ e', decomp_item e = Some (Ki, e') ∧ decomp e' = (K, e'').
Proof.
  rewrite decomp_unfold.
  destruct (decomp_item e) as [[Ki' e']|] eqn:Heq'.
  2 : { intros [=]. by destruct K. }
  destruct (decomp e') as [K' e'''] eqn:Heq.
  intros [= [<- <-]%list_snoc_singleton_inv ->].
  eauto.
Qed.

Lemma decomp_fill K e e' :
   decomp e = (K, e') → fill K e' = e.
Proof.
  generalize dependent e. generalize dependent e'.
  induction K as [|Ki K] using rev_ind; intros e e'.
  { intros [? ->]%decomp_inv_nil=>//. }
  intros (e'' & Hrei & Hre)%decomp_inv_cons.
      rewrite fill_app. rewrite (IHK e e''); eauto.
      by apply decomp_fill_item_2.
Qed.

Lemma decomp_val_empty K e e':
  decomp e = (K, e') → is_Some (to_val e') → K = [].
Proof.
  generalize dependent e'. generalize dependent e.
  induction K as [|Ki K] using rev_ind; [done|].
  intros ?? (e'' & Hrei & Hre)%decomp_inv_cons Hv.
  specialize (IHK _ _ Hre Hv). simplify_eq.
  apply decomp_inv_nil in Hre as [? ?]; simplify_eq.
  by apply decomp_fill_item_2 in Hrei as [_ ?%eq_None_not_Some].
Qed.   

Lemma fill_dmap e1 σ1 K :
  to_eff e1 = None →
  to_val e1 = None →
  prim_step (fill K e1) σ1 = dmap (fill_lift K) (prim_step e1 σ1).
Proof.
  intros Heff Hval. rewrite /prim_step.
  destruct (decomp e1) as [K1 e1'] eqn:Heq.
  destruct (decomp (fill _ e1)) as [K1' e1''] eqn:Heq'.
  apply (decomp_fill_comp K) in Heq; [|done|done].
  rewrite Heq in Heq'; simplify_eq.
  rewrite dmap_comp.
  apply dmap_eq; [|done].
  intros [] ? =>/=.
  f_equal. rewrite -fill_app //.
Qed.

Lemma fill_empty e :
  fill [] e = e.
Proof. done. Qed.

Lemma fill_lift_empty :
  fill_lift [] = (λ ρ, ρ).
Proof.
  extensionality ρ. destruct ρ.
  rewrite /fill_lift. done.
Qed.

Lemma val_prim_stuck e σ ρ : prim_step e σ ρ > 0 → to_val e = None.
Proof.
  intros. destruct e; eauto. unfold prim_step in H; simpl in H.
  rewrite dmap_dzero in H. rewrite dzero_0 in H. real_solver.
Qed.

  
Lemma eff_prim_stuck e σ ρ : prim_step e σ ρ > 0 → to_eff e = None.
Proof.
  intros. destruct e; eauto. unfold prim_step in H; simpl in H.
  rewrite dmap_dzero in H. rewrite dzero_0 in H. real_solver.
Qed.

Lemma step_by_val_eff K' K e1' e1 σ1 ρ :
  fill K' e1' = fill K e1 →
  to_val e1' = None →
  to_eff e1' = None →
  (head_step e1 σ1 ρ > 0)%R →
  ∃ K'', K = K'' ++ K'.
Proof.
  intros Hfill Hval Heff Hstep. revert K Hfill.
  induction K' as [|Ki' K' IH] using rev_ind=> /= K Hfill; eauto using app_nil_r.
  destruct K as [|Ki K _] using @rev_ind; simplify_eq/=.
  { rewrite fill_app in Hstep. apply head_ctxi_step_val in Hstep.
    2 : { by apply fill_not_eff. }
    apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
  rewrite !fill_app /= in Hfill.
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_val_inj in Hfill; eauto using val_head_stuck. { by apply fill_not_val. }
    apply fill_not_val. revert Hstep. apply val_head_stuck. }
  simplify_eq. destruct (IH K) as [K'' ->]; auto.
  exists K''. by rewrite assoc.
Qed.
  
Lemma state_step_prim_step_not_stuck e σ σ' α :
  state_step σ α σ' > 0 → (∃ ρ, prim_step e σ ρ > 0) ↔ (∃ ρ', prim_step e σ' ρ' > 0).
Proof.
  rewrite /prim_step.
  destruct (decomp e) as [K e'] eqn:Heq.
  intros Hs. split.
  + intros [[e2 σ2] [[e2' σ2'] [_ Hh]]%dmap_pos].
    assert (∃ ρ, head_step e' σ' ρ > 0) as [[e2'' σ2''] Hs'].
    { erewrite <-state_step_head_step_not_stuck; [|done]. eauto. }
    eexists (fill K e2'', σ2'').
    eapply dmap_pos.
    eexists (_, _). eauto.
  + intros [[e2 σ2] [[e2' σ2'] [_ Hh]]%dmap_pos].
    assert (∃ ρ, head_step e' σ ρ > 0) as [[e2'' σ2''] Hs'].
    { erewrite state_step_head_step_not_stuck; [|done]. eauto. }
    eexists (fill K e2'', σ2'').
    eapply dmap_pos.
    eexists (_, _); eauto.
Qed.

Lemma prim_step_mass e σ :
      (∃ ρ, prim_step e σ ρ > 0) → SeriesC (prim_step e σ) = 1.
Proof.
  intros [[e' σ'] Hs]. revert Hs. rewrite /prim_step.
  destruct (decomp e) as [K e1'] eqn:Heq.
  intros [[e2' σ2'] [? Hs]]%dmap_pos.
  assert (SeriesC (head_step e1' σ) = 1) as Hsum; [eauto using head_step_mass|].
  rewrite dmap_mass //.
Qed.




  
Lemma eff_prob_lang_mixin :
  LanguageMixin of_val to_val prim_step state_step get_active.
Proof.
  split; eauto using to_of_val, of_to_val, val_prim_stuck, state_step_prim_step_not_stuck, state_step_get_active_mass, prim_step_mass.
Qed.  

End eff_prob_lang_sec.

(* Prefer prob_lang names over ectx_language names. *)


Canonical Structure eff_prob_lang := Language eff_prob_lang_sec.eff_prob_lang_mixin.  

Export eff_prob_lang_sec. 

Definition cfg : Type := expr * state.


(* Neutral Evaluation Contexts. *)

Inductive Forall_ectx (P : ectx_item → Prop) : ectx → Prop :=
  | Forall_EmptyCtx : Forall_ectx P []
  | Forall_ConsCtx ki k :
     P ki → Forall_ectx P k → Forall_ectx P  (ki :: k).

Class NeutralEctxi (Ki : ectx_item) :=
  { neutral_ectxi v k σ :
      head_step_rel (fill_item Ki (Eff v k)) σ
                    (Eff v (k ++ [Ki]))        σ
  }.

Class NeutralEctx (K : ectx) :=
  { neutral_ectx : Forall_ectx NeutralEctxi K }.

Instance EmptyCtx_neutral : NeutralEctx [].
Proof. constructor. by apply Forall_EmptyCtx. Qed.
Instance ConsCtx_neutral Ki K : NeutralEctxi Ki → NeutralEctx K → NeutralEctx (Ki :: K).
Proof. constructor. apply Forall_ConsCtx; [|apply H0]; done. Qed.
Lemma ConsCtx_neutral_inv Ki K : NeutralEctx (Ki :: K) → NeutralEctx K.
Proof. intro H. inversion H. by inversion neutral_ectx0. Qed.
Lemma ConsCtx_neutral_inv' Ki K : NeutralEctx (Ki :: K) → NeutralEctxi Ki.
Proof. intro H. inversion H. by inversion neutral_ectx0. Qed.
Lemma ectx_app_neutral K K' : NeutralEctx K → NeutralEctx K' → NeutralEctx (K ++ K').
Proof.
  intros HK HK'. induction K as [| ki K]; simpl; [by apply _|].
  apply ConsCtx_neutral.
  - by apply (ConsCtx_neutral_inv' ki K).
  - by apply IHK, (ConsCtx_neutral_inv ki K).
Qed.

Instance AppLCtx_neutral v2 : NeutralEctxi (AppLCtx v2).
Proof. constructor => v k σ. by apply AppLEffS. Qed.
Instance AppRCtx_neutral e1 : NeutralEctxi (AppRCtx e1).
Proof. constructor => v k σ. by apply AppREffS. Qed.
Instance DoCtx_neutral : NeutralEctxi DoCtx.
Proof. constructor => v k σ. by apply DoEffS. Qed.
Instance UnOpCtx_neutral op : NeutralEctxi (UnOpCtx op).
Proof. constructor => v k σ. by apply UnOpEffS. Qed.
Instance BinOpLCtx_neutral op v2 : NeutralEctxi (BinOpLCtx op v2).
Proof. constructor => v k σ. by apply BinOpLEffS. Qed.
Instance BinOpRCtx_neutral op e1 : NeutralEctxi (BinOpRCtx op e1).
Proof. constructor => v k σ. by apply BinOpREffS. Qed.
Instance IfCtx_neutral e1 e2 : NeutralEctxi (IfCtx e1 e2).
Proof. constructor => v k σ. by apply IfEffS. Qed.
Instance PairLCtx_neutral v2 : NeutralEctxi (PairLCtx v2).
Proof. constructor => v k σ. by apply PairLEffS. Qed.
Instance PairRCtx_neutral e1 : NeutralEctxi (PairRCtx e1).
Proof. constructor => v k σ. by apply PairREffS. Qed.
Instance FstCtx_neutral : NeutralEctxi FstCtx.
Proof. constructor => v k σ. by apply FstEffS. Qed.
Instance SndCtx_neutral : NeutralEctxi SndCtx.
Proof. constructor => v k σ. by apply SndEffS. Qed.
Instance InjLCtx_neutral : NeutralEctxi InjLCtx.
Proof. constructor => v k σ. by apply InjLEffS. Qed.
Instance InjRCtx_neutral : NeutralEctxi InjRCtx.
Proof. constructor => v k σ. by apply InjREffS. Qed.
Instance CaseCtx_neutral e1 e2 : NeutralEctxi (CaseCtx e1 e2).
Proof. constructor => v k σ. by apply CaseEffS. Qed.
Instance AllocNLCtx_neutral v1: NeutralEctxi (AllocNLCtx v1).
Proof. constructor => v k σ. by apply AllocNLEffS. Qed.
Instance AllocNRCtx_neutral e1: NeutralEctxi (AllocNRCtx e1).
Proof. constructor => v k σ. by apply AllocNREffS. Qed.
Instance LoadCtx_neutral : NeutralEctxi LoadCtx.
Proof. constructor => v k σ. by apply LoadEffS. Qed.
Instance StoreLCtx_neutral v2 : NeutralEctxi (StoreLCtx v2).
Proof. constructor => v k σ. by apply StoreLEffS. Qed.
Instance StoreRCtx_neutral e1 : NeutralEctxi (StoreRCtx e1).
Proof. constructor => v k σ. by apply StoreREffS. Qed.

Lemma TryWithCtx_non_neutral e2 e3 : ¬ NeutralEctxi (TryWithCtx e2 e3).
Proof.
  intros ?. cut (head_step_rel
      (TryWith (Eff (LitV LitUnit) []) e2 e3)        {|tapes := ∅; heap:=∅|}
               (Eff (LitV LitUnit)
                    ((TryWithCtx e2 e3) :: [])) {|tapes := ∅; heap:=∅|});
  [inversion 1|apply H]; done.
Qed.

(** Reducible *)
  
Lemma fill_step  e1 σ1 e2 σ2 K :
  (prim_step e1 σ1 (e2, σ2) > 0)%R → (prim_step (fill K e1) σ1 (fill K e2, σ2) > 0)%R.
Proof.
  intros Hs.
  rewrite fill_dmap; [| eauto using eff_prim_stuck | eauto using val_prim_stuck].
  apply dbind_pos. eexists (_,_). split; [|done].
  rewrite dret_1_1 //. lra.
Qed.

Lemma fill_step_prob e1 σ1 e2 σ2 K :
  to_val e1 = None →
  to_eff e1 = None → 
  prim_step e1 σ1 (e2, σ2) = prim_step (fill K e1) σ1 (fill K e2, σ2).
Proof.
  intros Heff Hv. rewrite fill_dmap //.
  by erewrite (dmap_elem_eq _ (e2, σ2) _ (λ '(e0, σ0), (fill K e0, σ0))).
Qed.
  
Class head_reducible (e : expr) (σ : state) :=
  head_reducible_step : ∃ ρ, (head_step e σ ρ > 0)%R.

Lemma head_prim_step_pmf_eq e1 σ1 ρ :
    head_reducible e1 σ1 →
    prim_step e1 σ1 ρ = head_step e1 σ1 ρ.
Proof.
  intros Hred.
  rewrite /= /prim_step.
  destruct (decomp e1) as [K e1'] eqn:Heq.
  edestruct (decomp_fill _ _ _ Heq).
  destruct Hred as [ρ' Hs].
  apply eff_head_stuck in Hs as Heff.
  destruct (to_eff e1') as [(v, k)|] eqn:Heff'.
  - destruct K as [| Ki K]. { simpl. by rewrite fill_lift_empty dmap_id. }
    apply of_to_eff in Heff' as <-.
    assert (decomp (fill [Ki] (Eff v k)) = ([], fill [Ki] (Eff v k))) as H. { destruct Ki; eauto. }
    apply (decomp_fill_comp K) in H; try (destruct Ki; done). simpl in H.
    rewrite Heq in H; destruct Ki; inversion H.
  - destruct (head_ctx_step_val _ _ _ _ Heff' Hs) as [| ->].
    + assert (K = []) as -> by eauto using decomp_val_empty. 
    rewrite fill_lift_empty fill_empty dmap_id //=.
    + rewrite fill_lift_empty fill_empty dmap_id //=.
Qed.

Lemma head_prim_step_eq e1 σ1 :
  head_reducible e1 σ1 →
  prim_step e1 σ1 = head_step e1 σ1.
Proof. intros ?. apply distr_ext=>?. by eapply head_prim_step_pmf_eq. Qed.


Lemma head_step_prim_step e1 σ1 e2 σ2 :
  (head_step e1 σ1 (e2, σ2) > 0)%R → (prim_step e1 σ1 (e2, σ2) > 0)%R.
Proof.
  intros ?. erewrite head_prim_step_eq; [done|]. eexists; eauto.
Qed.

Lemma prim_step_iff e1 e2 σ1 σ2 :
  (prim_step e1 σ1 (e2, σ2) > 0)%R ↔
  ∃ K e1' e2',
    fill K e1' = e1 ∧
    fill K e2' = e2 ∧
    (head_step e1' σ1 (e2', σ2) > 0)%R.
Proof.
  split.
  - rewrite /= /prim_step. intros Hs.
    destruct (decomp e1) as [K e1'] eqn:Heq.
    edestruct (decomp_fill _ _ _ Heq).
    eapply dmap_pos in Hs as [[] [[=] ?]].
    simplify_eq. do 3 eexists; eauto.
  - intros (K & e1' & e2' & Hfill1 & Hfill2 & Hs). simplify_eq.
    apply fill_step. by apply head_step_prim_step.
Qed.


Lemma reducible_fill_item_eff Ki `{NeutralEctxi Ki} v k σ :
  reducible ((fill_item Ki (Eff v k)), σ).
Proof.
  unfold reducible. simpl. exists (Eff v (k ++ [Ki]), σ). apply head_step_prim_step.
  apply head_step_support_equiv_rel. destruct Ki; try constructor. apply TryWithCtx_non_neutral in H. done.
Qed.

Lemma reducible_fill K e σ : reducible (e, σ) → reducible ((fill K e), σ).
Proof.
  unfold reducible in *. intros [[] ?]. simpl in *. eexists; by apply fill_step.
Qed.

Lemma reducible_fill_item Ki e σ : reducible (e, σ) → reducible ((fill_item Ki e), σ).
Proof. by apply (reducible_fill [Ki]). Qed.

(* Lemma reducible_no_obs_iff (e : expr) σ : reducible_no_obs e σ ↔ reducible e σ.
   Proof.
     split.
     - apply reducible_no_obs_reducible.
     - destruct 1 as [obs [e' [σ' [efs Hstep]]]].
       case obs in Hstep; [|done].
       case efs in Hstep; [|done].
       by exists e', σ', [].
   Qed. *)

Lemma eff_irreducible v k σ : irreducible ((Eff v k), σ).
Proof.
  unfold irreducible; simpl. intro ρ. unfold prim_step. simpl. rewrite dmap_dzero. apply dzero_0.
Qed.

Lemma reducible_not_eff e σ : reducible (e, σ) → to_eff e = None.
Proof.
  intros ?. case_eq (to_eff e);[|done]. destruct p as (v, k).
  intros ?. specialize (eff_irreducible v k σ).
  rewrite (of_to_eff _ _ _ H0). by rewrite <-not_reducible.
Qed.

Lemma val_irreducible v σ : irreducible ((Val v), σ).
Proof.
  unfold irreducible; simpl. intro ρ. unfold prim_step. simpl. rewrite dmap_dzero. apply dzero_0.
Qed.

Lemma reducible_not_val e σ : reducible (e, σ) → to_val e = None.
Proof.
  intros ?. case_eq (to_val e); [|done]. intros ??.
  specialize (val_irreducible v σ). rewrite (of_to_val _ _ H0). by rewrite <- not_reducible.
Qed.  
(** Pure steps. *)

(* Record pure_prim_step (e1 e2 : expr) := {
     pure_prim_step_safe σ : (prim_step e1 σ (e2, σ) > 0)%R;
     pure_prim_step_det σ1 e2' σ2 :
       (prim_step e1 σ1 (e2', σ2) > 0)%R → σ2 = σ1 ∧ e2' = e2
   }. *)
Record pure_prim_step (e1 e2 : expr) := {
    pure_prim_step_safe σ1 : reducible (e1, σ1);
    pure_prim_step_det σ : prim_step e1 σ (e2, σ) = 1;
  }.

(* Lemma prim_step_inv' e1 σ1 κs e2 σ2 efs :
     prim_step' e1 σ1 κs e2 σ2 efs → κs = [] ∧ efs = [].
   Proof. by case κs; case efs; try inversion 1. Qed. *)

Lemma pure_prim_step_imp_reducible e1 e2 :
  pure_prim_step e1 e2 → (∀ σ, reducible (e1, σ)).
Proof. intros [Hstep ?] ?. eauto. Qed.

Lemma pure_prim_step_imp_det e1 e2 :
  pure_prim_step e1 e2 → ∀ σ1 e2' σ2', (prim_step e1 σ1 (e2', σ2') > 0)%R → e2 = e2' ∧ σ1 = σ2'.
Proof.
  intros [? Hdet] σ1 e2' σ2' Hstep. specialize Hdet with (σ := σ1).
  apply pmf_1_eq_dret in Hdet. rewrite Hdet in Hstep.
  apply dret_pos in Hstep; by simplify_eq.
Qed.
  
(* Lemma pure_prim_stepI e1 e2 :
     (∀ σ, (head_step e1 σ (e2, σ) > 0)%R) →
     (∀ σ1 e2' σ2, (prim_step e1 σ1 (e2', σ2) > 0)%R → σ2 = σ1 ∧ e2' = e2) →
     pure_prim_step e1 e2.
   Proof.
     intros Hhead_step Hstep_det. split.
     - intros σ. eexists _. by apply head_step_prim_step.
     - intros σ.
       assert (head_reducible e1 σ) as Hred. { eexists. apply Hhead_step. }
       apply head_prim_step_eq in Hred as ->.
   Admitted. *)
(*   intros Hhead_step Hstep_det. constructor; auto.
     intros ?. by apply head_step_prim_step.
   Qed. *)

(* Lemma pure_prim_stepI' e1 e2 :
     (∀ σ, head_step e1 σ e2 σ) →
     (∀ K e1', e1 = fill K e1' →
       (K = EmptyCtx) ∨ (∃ v, e1' = Val v)) →
     pure_prim_step e1 e2.
   Proof.
     intros Hstep Hfill; apply pure_prim_stepI; auto.
     intros ???. inversion 1.
     case (Hfill _ _ H0) as [->|(v & ->)]; [|by inversion H2].
     simpl in H0, H1, H2. simplify_eq.
     specialize (Hstep σ1) as H3.
     inversion H2; simplify_eq; try naive_solver;
     inversion H3; simplify_eq; try naive_solver.
     - unfold state_upd_heap in H4. simpl in H4.
       rewrite lookup_insert in H4. done.
     - split; [|done]. destruct σ1 as [σ1].
       by rewrite /state_upd_heap /= insert_insert.
   Qed. *)

(* Lemma val_not_pure v e : ¬ pure_prim_step (Val v) e.
   Proof.
     intros Hstep.
     specialize (pure_prim_step_imp_reducible _ _ Hstep {|heap:=∅|}) as H.
     specialize (reducible_not_val (Val v) {|heap:=∅|} H); done.
   Qed.
   
   Lemma val_not_pure' v e e' : to_val e = Some v → ¬ pure_prim_step e e'.
   Proof. intro H1; rewrite <- (of_to_val _ _ H1). by apply val_not_pure. Qed.
   
   Lemma eff_not_pure v k e : ¬ pure_prim_step (Eff v k) e.
   Proof.
     intros H0.
     specialize (pure_prim_step_imp_reducible _ _ H0 {|heap:=∅|}).
     specialize (eff_irreducible v k {|heap:=∅|}).
     by rewrite <-not_reducible.
   Qed.
   
   Lemma eff_not_pure' v k e e' : to_eff e = Some (v, k) → ¬ pure_prim_step e e'.
   Proof. intro H1; rewrite <- (of_to_eff _ _ _ H1). by apply eff_not_pure. Qed. *)
   
   Lemma pure_prim_step_unop op v v' :
     un_op_eval op v = Some v' →
       pure_prim_step (UnOp op (Val v)) (Val v').
   Proof.
     intros.
     apply Build_pure_prim_step.
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. constructor. done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty H. rewrite dmap_dret.
       by apply dret_1_1.
   Qed.
   
   Lemma pure_prim_step_binop op v1 v2 v' :
     bin_op_eval op v1 v2 = Some v' →
       pure_prim_step (BinOp op (Val v1) (Val v2)) (Val v').
   Proof.
     intros.
     apply Build_pure_prim_step.
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. constructor. done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty H. rewrite dmap_dret.
       by apply dret_1_1.
   Qed. 
   
   Lemma pure_prim_step_beta f x e v :
     pure_prim_step ((App (Val $ RecV f x e) (Val v)))
                    (subst' x v (subst' f (RecV f x e) e)).
   Proof.
     apply Build_pure_prim_step.
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. apply BetaS. done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty. rewrite dmap_dret.
       by apply dret_1_1.
   Qed. 
   
   Lemma pure_prim_step_rec f x e :
     pure_prim_step (Rec f x e) (Val $ RecV f x e).
   Proof.
     apply Build_pure_prim_step.
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. apply RecS.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty. rewrite dmap_dret.
       by apply dret_1_1.
   Qed.
   
   Lemma pure_prim_step_InjL v :
     pure_prim_step (InjL $ Val v) (Val $ InjLV v).
   Proof.
     apply Build_pure_prim_step.
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. constructor; done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty. rewrite dmap_dret.
       by apply dret_1_1.
   Qed.
   
   Lemma pure_prim_step_InjR v :
     pure_prim_step (InjR $ Val v) (Val $ InjRV v).
   Proof.
     apply Build_pure_prim_step.
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. constructor; done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty. rewrite dmap_dret.
       by apply dret_1_1.
   Qed.
   
   Lemma pure_prim_step_case_InjL v e1 e2 :
     pure_prim_step (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
   Proof.
    apply Build_pure_prim_step.
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. constructor; done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty. rewrite dmap_dret.
       by apply dret_1_1.
   Qed.
   
   Lemma pure_prim_step_case_InjR v e1 e2 :
     pure_prim_step (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
   Proof.
     apply Build_pure_prim_step.
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. constructor; done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty. rewrite dmap_dret.
       by apply dret_1_1.
   Qed.
   
   Lemma pure_prim_step_if e1 e2 b :
     pure_prim_step (If (Val $ LitV $ LitBool b) e1 e2) (if b then e1 else e2).
   Proof.
     destruct b.
     { apply Build_pure_prim_step. 
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. simpl.  constructor; done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty. rewrite dmap_dret.
       by apply dret_1_1. }
     { apply Build_pure_prim_step. 
       - intros ?. eexists. apply head_step_prim_step.
         apply head_step_support_equiv_rel. simpl.  constructor; done.
       - intros ?. unfold prim_step. simpl.
         rewrite fill_lift_empty. rewrite dmap_dret.
         by apply dret_1_1. }
    Qed.
   
   Lemma pure_prim_step_if_true e1 e2 :
     pure_prim_step (If (Val $ LitV $ LitBool true) e1 e2) e1.
   Proof. by apply pure_prim_step_if. Qed.
   
   Lemma pure_prim_step_if_false e1 e2 :
     pure_prim_step (If (Val $ LitV $ LitBool false) e1 e2) e2.
   Proof. by apply pure_prim_step_if. Qed.
   
   Lemma pure_prim_step_pair v1 v2 :
     pure_prim_step (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
   Proof.
     apply Build_pure_prim_step. 
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. simpl.  constructor; done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty. rewrite dmap_dret.
       by apply dret_1_1.
   Qed.
   
   Lemma pure_prim_step_Fst v1 v2 :
     pure_prim_step (Fst (Val $ PairV v1 v2)) (Val v1).
   Proof.
     apply Build_pure_prim_step. 
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. simpl.  constructor; done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty. rewrite dmap_dret.
       by apply dret_1_1.
   Qed.
   
   Lemma pure_prim_step_Snd v1 v2 :
     pure_prim_step (Snd (Val $ PairV v1 v2)) (Val v2).
   Proof.
    apply Build_pure_prim_step. 
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. simpl.  constructor; done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty. rewrite dmap_dret.
       by apply dret_1_1.
   Qed.
   
   Lemma pure_prim_step_try_with_val v e₂ e₃ :
     pure_prim_step (TryWith (Val v) e₂ e₃) (App e₃ (Val v)).
   Proof.
    apply Build_pure_prim_step. 
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. simpl.  constructor; done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty. rewrite dmap_dret.
       by apply dret_1_1.
   Qed.
   
   Lemma pure_prim_step_do v :
     pure_prim_step (Do (Val v)) (Eff v []).
   Proof.
     apply Build_pure_prim_step. 
     - intros ?. eexists. apply head_step_prim_step.
       apply head_step_support_equiv_rel. simpl.  constructor; done.
     - intros ?. unfold prim_step. simpl.
       rewrite fill_lift_empty. rewrite dmap_dret.
       by apply dret_1_1.
   Qed. 

Lemma pure_prim_step_eff Ki `{NeutralEctxi Ki} v k :
  pure_prim_step (fill_item Ki (Eff v k)) (Eff v (k ++ [Ki])).
Proof.
  split.
  { intros ?. exists (Eff v (k ++ [Ki]), σ1). simpl. apply head_step_prim_step. rewrite head_step_support_equiv_rel.
    destruct Ki; try constructor.
       by apply TryWithCtx_non_neutral in H. }
  intros ?. destruct Ki; try (simpl; unfold prim_step; simpl; rewrite fill_lift_empty; repeat destruct_match; rewrite dmap_dret; by apply dret_1_1).
  by apply TryWithCtx_non_neutral in H.
Qed.

(* Lemma test K e1 σ1 e2 σ2:
     to_val e1 = None →
     to_eff e1 = None →
     head_reducible e1 σ1 →
     (prim_step (fill K e1) σ1 (e2, σ2) > 0)%R →
       ∃ e2', e2 = fill K e2' ∧ (head_step e1 σ1 (e2', σ2) > 0)%R.
   Proof.
     intros Hval Heff [[e2'' σ2''] HhstepK] Hstep.
     apply prim_step_iff in Hstep as (K' & e1' & e2' & HKe1 & HKe2 & Hs).
     symmetry in HKe1.
     edestruct (step_by_val_eff K) as [K'' HK]; eauto using val_head_stuck; simplify_eq/=.
     rewrite fill_app in HKe1; simplify_eq.
     exists (fill K'' e2'). rewrite fill_app. split; [done|].
     apply eff_head_stuck in Hs as Heff'; eauto.
     destruct (head_ctx_step_val _ _ _ _ Heff' HhstepK) as [[]%not_eq_None_Some|HK'].
     { by eapply val_head_stuck. }
     subst. rewrite !fill_empty //. 
   Qed.
   
   Lemma Ectxi_prim_step_inv Ki e e2 σ1 σ2 :
     to_val e = None →
     to_eff e = None →
     head_reducible e σ1 →
     (prim_step (fill_item Ki e) σ1 (e2, σ2) > 0)%R →
     ∃ e', (prim_step e σ1 (e', σ2) > 0)%R ∧ e2 = fill_item Ki e'.
   Proof.
     intros ??? Hstep.
     pose proof (test [Ki] e σ1 e2 σ2 H H0) as (e' & HKe' & Hs); eauto.
     exists e'. split; eauto. by apply head_step_prim_step.
   Qed.
   
   Lemma Ectx_prim_step_inv K e e2 σ1 σ2 :
     to_val e = None →
     to_eff e = None →
     head_reducible e σ1 → 
     (prim_step (fill K e) σ1 (e2, σ2) > 0)%R →
     ∃ e', (prim_step e σ1 (e', σ2) > 0)%R ∧ e2 = fill K e'.
   Proof.
     intros ????. pose proof (test K _ _ _ _ H H0 H1 H2) as (e' & HKe' & Hs).
     exists e'. split; [ by apply head_step_prim_step |done]. 
   Qed. *)

Lemma pure_prim_step_fill_item Ki e e' :
  pure_prim_step e e' → pure_prim_step (fill_item Ki e) (fill_item Ki e').
Proof.
  intros [Hsafe Hdet]. split.
  - intros σ. by apply (reducible_fill [Ki]).
  - intros σ.
    rewrite -(fill_step_prob _ _ _ _ [Ki]) //; eauto using reducible_not_eff, reducible_not_val.
    Unshelve. { exact σ. } { exact σ. }
Qed.  
(*   constructor. 
     - intros ?. apply (fill_step _ _ _ _ [Ki] (pure_prim_step_safe _ _ H _)). 
     - intros ??? Hstep. 
       have not_val : to_val e = None.
       { by apply (reducible_not_val _ σ1),
                  (pure_prim_step_imp_reducible _ e'). }
       have not_eff : to_eff e = None.
       { by apply (reducible_not_eff _ σ1),
           (pure_prim_step_imp_reducible _ e'). }
       eapply pure_prim_step_imp_reducible in H.
       destruct (Ectxi_prim_step_inv Ki e _ _ _ not_val not_eff H Hstep) as [e'' [He'' ->]].
       by destruct (pure_prim_step_det _ _ H _ _ _ He'') as [-> ->].
   Qed. *)

Lemma pure_prim_step_fill K e e' :
  pure_prim_step e e' → pure_prim_step (fill K e) (fill K e').
Proof.
  generalize dependent e. generalize dependent e'.
  induction K as [|Ki K]; [done|].
  intros ???. simpl. destruct Ki; apply IHK; apply pure_prim_step_fill_item; done.
Qed.

Lemma tc_pure_prim_step_fill K e e' :
  tc pure_prim_step e e' → tc pure_prim_step (fill K e) (fill K e').
Proof.
  induction 1.
  - apply tc_once.
    by apply pure_prim_step_fill.
  - apply (tc_l _ _ (fill K y)); [|done].
    by apply pure_prim_step_fill.
Qed.

Lemma rtc_pure_prim_step_fill K e e' :
  rtc pure_prim_step e e' → rtc pure_prim_step (fill K e) (fill K e').
Proof.
  induction 1; [done|].
  apply (rtc_l _ _ (fill K y)); [|done].
  by apply pure_prim_step_fill.
Qed.

Lemma tc_pure_prim_step_fill_item Ki e e' :
  tc pure_prim_step e e' → tc pure_prim_step (fill_item Ki e) (fill_item Ki e').
Proof. by apply (tc_pure_prim_step_fill [Ki]). Qed.

Lemma rtc_pure_prim_step_fill_item Ki e e' :
  rtc pure_prim_step e e' → rtc pure_prim_step (fill_item Ki e) (fill_item Ki e').
Proof. by apply (rtc_pure_prim_step_fill [Ki]). Qed.

(* Lemma reducible_fill_item_inv Ki e σ :
     to_val e = None →
     to_eff e = None →
     reducible ((fill_item Ki e) σ) →
     reducible e σ.
   Proof.
     intros ??. unfold reducible; simpl; unfold prim_step'; simpl.
     intros [obs [e₂ [σ' [efs Hstep]]]].
     case obs in Hstep; [|done].
     case efs in Hstep; [|done].
     destruct (Ectxi_prim_step_inv _ _ _ _ _ H H0 Hstep) as [e' [Hstep' _]].
     by exists [], e', σ', [].
   Qed. *)

Lemma rtc_pure_prim_step_eff `{NeutralEctx K} v k :
  rtc pure_prim_step (fill K (Eff v k)) (Eff v (k ++ K)).
Proof.
  generalize dependent k.
  induction K as [|Ki K]; intros k.
  - rewrite app_nil_r. done.
  - specialize (ConsCtx_neutral_inv' _ _ H) as Ki_neutral.
    specialize (ConsCtx_neutral_inv  _ _ H) as  K_neutral.
    apply (rtc_l _ _(fill K (Eff v (k ++ [Ki])))); simpl.
    + apply pure_prim_step_fill. by apply pure_prim_step_eff. 
    + assert (k ++ Ki :: K = (k ++ [Ki]) ++ K) as ->. { rewrite -app_assoc. done. }
      by apply IHK.
Qed.



