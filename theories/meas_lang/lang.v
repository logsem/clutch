From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp.analysis Require Import reals measure.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp classical_sets.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.prob.monad Require Export laws.

(*
From Coq Require Import Reals Psatz.
From stdpp Require Export binders strings.
From stdpp Require Import fin.
From stdpp Require Import gmap fin_maps countable fin.
From clutch.prob Require Export distribution.
From clutch.common Require Export language ectx_language ectxi_language locations.
From iris.prelude Require Import options.
From mathcomp Require Import ssrbool eqtype fintype choice all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed normedtype sequences esum numfun measure lebesgue_measure lebesgue_integral.
*)



Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Global Instance classical_eq_dec {T : Type} : EqDecision T.
Proof.  intros ? ?; apply ClassicalEpsilon.excluded_middle_informative. Defined.

Module meas_lang.

Context {R : realType}.

Inductive base_lit : Type :=
  | LitInt (n : Z)
  | LitBool (b : bool)
  | LitUnit
  | LitLoc (l : loc)
  | LitLbl (l : loc)
  | LitReal (r : R).
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
  (* Finite probabilistic choice *)
  | AllocTape (e : expr)
  | Rand (e1 e2 : expr)
  (* Real probabilistic choice *)
  | AllocUTape (e : expr)
  | URand (e1 e2 : expr)
  (* No-op operator used for cost *)
  | Tick (e : expr)
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



(* This part of the sigma algebra is not discrete *)
(* MARKUSDE: Externalizing the fin bound here also simplifies definitions *)
Definition history : Type := nat -> option nat.


(* Tapes in the computable fragment *)
Record tape : Type := {
  tape_bound : nat;
  tape_state : nat;
  tape_histo : history
}.

(* All values of the tape are within the tape bound *)
Definition tape_inbounds (t : tape) : Prop :=
  forall n : nat,
    tape_histo t n = None \/
    exists v : nat, tape_histo t n = Some v /\ v < tape_bound t.

(* All tape values prior to state have been determined *)
Definition tape_history_deterministic (t : tape) : Prop :=
  forall i : nat, i < tape_state t -> exists v : nat, tape_histo t i = Some v.

(* External correctness of tapes *)
Definition tape_wf (t : tape) : Prop := tape_inbounds t /\ tape_history_deterministic t.

Definition emptyHistory : history := fun _ => None.

Definition emptyTape (bound : nat) : tape :=
  {| tape_bound := bound ;
     tape_state := 0 ;
     tape_histo := emptyHistory
  |}.

(* History lookup: look through absolute history *)
Global Instance history_lookup : Lookup nat nat history := fun i => fun h => h i.

(* Tape lookup: look relative to current index. t !! 0  will be the next sample. *)
Global Instance tape_rel_lookup : Lookup nat nat tape := fun i => fun t => (tape_histo t (i + tape_state t)).

Definition historyUpdateUnsafe (i : nat) (v : option nat) (h : history) : history
  := fun i' => if i' =? i then v else h i'.

Global Instance history_insert : Insert nat (option nat) history := historyUpdateUnsafe.

Definition tapeUpdateUnsafe (i : nat) (v : option nat) (t : tape) : tape :=
  {| tape_bound := tape_bound t;
     tape_state := tape_state t;
     tape_histo := <[ (i + tape_state t) := v ]> (tape_histo t)
  |}.

Global Instance tape_insert : Insert nat (option nat) tape := tapeUpdateUnsafe.


(* Advance the tape by 1, returning an updated tape and the first sample on the tape. *)
Program Definition tapeNext (t : tape) (H : isSome (t !! 0)) : nat * tape
  := match (t !! 0) with
     | None => _
     | Some v =>
         (v,
          {| tape_bound := tape_bound t;
             tape_state := 1 + tape_state t;
             tape_histo := tape_histo t |})
     end.
Next Obligation. by move=>/= ? H1 H2; symmetry in H2; rewrite H2//= in H1. Defined.

(* Representation predicates for common tape structures *)

Definition tapeHasPrefix (t : tape) (l : list nat) : Prop
  := forall i : nat, i < length l -> t !! i = l !! i.

Definition tapeEmptyAfter (t : tape) (b : nat) : Prop
  := forall i : nat, i >= b -> t !! i = None.

(* Tapes a la base clutch *)
Definition finiteTape (t : tape) (l : list nat) : Prop
  :=   tapeHasPrefix t l
     /\ tapeEmptyAfter t (length l)
     /\ tape_wf t.



(* TODO: realIsBinarySequence (cannonical form w/ 0-termination on dyadic numbers) *)

Definition tapeHasInfinitePrefix (t : tape) (f : nat -> nat) : Prop
  := forall i : nat, t !! i = Some (f i).

(* TODO: tapeIsRealInRange (l : R) ... := bound = 1, tapeHasInfinitePrefic *)
(* tapeOfReal ... ?*)

(* Tape with "Junk" prefix *)
Definition tapeHasEventually (t : tape) (l : list nat) : Prop
  := exists offset: nat, forall i : nat, i < length l -> t !! (i + offset) = l !! i.


Global Instance tape_inhabited : Inhabited tape := populate (emptyTape 0).
Global Instance tapes_lookup_total : LookupTotal loc tape (gmap loc tape).
Proof. apply map_lookup_total. Defined.
Global Instance tapes_insert : Insert loc tape (gmap loc tape).
Proof. apply map_insert. Defined.


(* Tapes for the real-valued fragment *)
Definition utape : Type := list R.
Global Instance utape_inhabited : Inhabited utape := populate [].
Global Instance utapes_lookup_total : LookupTotal loc utape (gmap loc utape).
Proof. apply map_lookup_total. Defined.
Global Instance utapes_insert : Insert loc utape (gmap loc utape).
Proof. apply map_insert. Defined.



(** The state: a [loc]-indexed heap of [val]s, and [loc]-indexed tapes, and [loc]-indexed utapes *)
Record state : Type := {
  heap   : gmap loc val;
  tapes  : gmap loc tape;
  utapes : gmap loc utape
}.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; tapes := inhabitant; utapes := inhabitant |}.
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
  | AllocTapeCtx
  | AllocUTapeCtx
  | RandLCtx (v2 : val)
  | RandRCtx (e1 : expr)
  | URandLCtx (v2 : val)
  | URandRCtx (e1 : expr)
  | TickCtx.

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
  | AllocUTapeCtx => AllocUTape e
  | RandLCtx v2 => Rand e (Val v2)
  | RandRCtx e1 => Rand e1 e
  | URandLCtx v2 => URand e (Val v2)
  | URandRCtx e1 => URand e1 e
  | TickCtx => Tick e
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
  | AllocTape e    => noval e AllocTapeCtx
  | AllocUTape e   => noval e AllocUTapeCtx
  | Rand e1 e2     =>
      match e2 with
      | Val v      => noval e1 (RandLCtx v)
      | _          => Some (RandRCtx e1, e2)
      end
  | URand e1 e2    =>
      match e2 with
      | Val v      => noval e1 (URandLCtx v)
      | _          => Some (URandRCtx e1, e2)
      end
  | Tick e         => noval e TickCtx
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
  | AllocTape e => AllocTape (subst x v e)
  | AllocUTape e => AllocUTape (subst x v e)
  | Rand e1 e2 => Rand (subst x v e1) (subst x v e2)
  | URand e1 e2 => URand (subst x v e1) (subst x v e2)
  | Tick e => Tick (subst x v e)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => λ x, x end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt z) => Some $ LitV $ LitInt (Z.lnot z)
  | MinusUnOp, LitV (LitInt z) => Some $ LitV $ LitInt (- z)
  | MinusUnOp, LitV (LitReal r) => Some $ LitV $ LitReal (- r)%R
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

Definition bin_op_eval_real (op : bin_op) (r1 r2 : R) : option base_lit :=
  match op with
  | PlusOp => Some $ LitReal (r1 + r2)
  | MinusOp => Some $ LitReal (r1 - r2)
  | MultOp => Some $ LitReal (r1 * r2)
  | LeOp => Some $ LitBool (r1 <= r2)
  | LtOp => Some $ LitBool (r1 < r2)
  | EqOp => Some $ LitBool (decide (r1 = r2))
  | _ => None
  end%R.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    if decide (v1 = v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1 , v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => Some $ LitV $ bin_op_eval_int op n1 n2
    | LitV (LitReal r1), LitV (LitReal r2) => LitV <$> bin_op_eval_real op r1 r2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => None
    end.

Definition state_upd_heap (f : gmap loc val → gmap loc val) (σ : state) : state :=
  {| heap := f σ.(heap); tapes := σ.(tapes); utapes := σ.(utapes) |}.
Global Arguments state_upd_heap _ !_ /.

Definition state_upd_tapes (f : gmap loc tape → gmap loc tape) (σ : state) : state :=
  {| heap := σ.(heap); tapes := f σ.(tapes); utapes := σ.(utapes) |}.
Global Arguments state_upd_tapes _ !_ /.

Definition state_upd_utapes (f : gmap loc utape → gmap loc utape) (σ : state) : state :=
  {| heap := σ.(heap); tapes := σ.(tapes); utapes := f σ.(utapes) |}.
Global Arguments state_upd_utapes _ !_ /.

Lemma state_upd_tapes_twice σ l xs ys :
  state_upd_tapes <[ l := ys ]> (state_upd_tapes <[ l := xs ]> σ) = state_upd_tapes <[ l:= ys ]> σ.
Proof. rewrite /state_upd_tapes /=. f_equal. apply insert_insert. Qed.

Lemma state_upd_tapes_same σ σ' l xs ys :
  state_upd_tapes <[l:=ys]> σ = state_upd_tapes <[l:=xs]> σ' -> xs = ys.
Proof. rewrite /state_upd_tapes /=. intros K. simplify_eq.
       rewrite map_eq_iff in H.
       specialize (H l).
       rewrite !lookup_insert in H.
       by simplify_eq.
Qed.

Lemma state_upd_tapes_no_change σ l ys :
  tapes σ !! l = Some ys ->
  state_upd_tapes <[l := ys]> σ = σ .
Proof.
  destruct σ as [? t]. simpl.
  intros Ht.
  f_equal.
  apply insert_id. done.
Qed.

(*
Lemma state_upd_tapes_same' σ σ' l n xs (x y : stdpp.fin.fin (S n)) :
  state_upd_tapes <[l:=(fin (n; xs++[x]))]> σ = state_upd_tapes <[l:=(fin(n; xs++[y]))]> σ' -> x = y.
Proof. intros H. apply state_upd_tapes_same in H. by simplify_eq. Qed.

Lemma state_upd_tapes_neq' σ σ' l n xs (x y : stdpp.fin.fin (S n)) :
  x≠y -> state_upd_tapes <[l:=(fin(n; xs++[x]))]> σ ≠ state_upd_tapes <[l:=(fin(n; xs++[y]))]> σ'.
Proof. move => H /state_upd_tapes_same ?. simplify_eq. Qed.
*)

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
  revert k l; induction vs as [|v' vs IH] => l' l /=.
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

Lemma state_upd_tapes_heap σ l1 l2 xs m v :
  state_upd_tapes <[l2:=xs]> (state_upd_heap_N l1 m v σ) =
  state_upd_heap_N l1 m v (state_upd_tapes <[l2:=xs]> σ).
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

Section pointed_instances.
  Local Open Scope classical_set_scope.
  (** states are pointed *)
  (* Maybe define a builder for this? Any sdtpp inhabited type -> mathcomp pointed type *)

  (* Fail Check (<<discr state>> : measurableType _).  *)
  HB.instance Definition _ := gen_eqMixin state.
  HB.instance Definition _ := gen_choiceMixin state.
  HB.instance Definition _ := isPointed.Build state inhabitant.
  (* Check (<<discr state>> : measurableType _). *)

  (** expr is pointed *)
  (* Fail Check (<<discr expr>> : measurableType _).  *)
  HB.instance Definition _ := gen_eqMixin expr.
  HB.instance Definition _ := gen_choiceMixin expr.
  HB.instance Definition _ := isPointed.Build expr inhabitant.
  (* Check (<<discr expr>> : measurableType _).  *)

  (** loc is pointed *)
  (* Fail Check (<<discr loc>> : measurableType _).  *)
  HB.instance Definition _ := gen_eqMixin loc.
  HB.instance Definition _ := gen_choiceMixin loc.
  HB.instance Definition _ := isPointed.Build loc inhabitant.
  (* Check (<<discr loc>> : measurableType _).  *)

  (** cfg is pointed (automatic) *)
  (* Check (<<discr cfg>> : measurableType _).  *)

  (** state * loc is pointed (automatic) *)
  (* Check (<<discr (state * loc)>> : measurableType _). *)

End pointed_instances.

Definition cfg : Type := expr * state.

Section meas_semantics.
  Local Open Scope classical_set_scope.
  Context {R : realType}.
  Notation giryM := (giryM (R := R)).
  Local Open Scope expr_scope.


  Definition head_stepM_def (c : cfg) : giryM <<discr cfg>> :=
    let (e1, σ1) := c in
    match e1 with
    | Rec f x e =>
        giryM_ret R ((Val $ RecV f x e, σ1) : <<discr cfg>>)
    | Pair (Val v1) (Val v2) =>
        giryM_ret R ((Val $ PairV v1 v2, σ1) : <<discr cfg>>)
    | InjL (Val v) =>
        giryM_ret R ((Val $ InjLV v, σ1) : <<discr cfg>>)
    | InjR (Val v) =>
        giryM_ret R ((Val $ InjRV v, σ1) : <<discr cfg>>)
    | App (Val (RecV f x e1)) (Val v2) =>
        giryM_ret R ((subst' x v2 (subst' f (RecV f x e1) e1) , σ1) : <<discr cfg>>)
    | UnOp op (Val v) =>
        match un_op_eval op v with
          | Some w => giryM_ret R ((Val w, σ1) : <<discr cfg>>)
          | _ => giryM_zero
        end
    | BinOp op (Val v1) (Val v2) =>
        match bin_op_eval op v1 v2 with
          | Some w => giryM_ret R ((Val w, σ1) : <<discr cfg>>)
          | _ => giryM_zero
        end
    | If (Val (LitV (LitBool true))) e1 e2  =>
        giryM_ret R ((e1 , σ1) : <<discr cfg>>)
    | If (Val (LitV (LitBool false))) e1 e2 =>
        giryM_ret R ((e2 , σ1) : <<discr cfg>>)
    | Fst (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v1 , σ1) : <<discr cfg>>) (* Syntax error when I remove the space between v1 and , *)
    | Snd (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v2, σ1) : <<discr cfg>>)
    | Case (Val (InjLV v)) e1 e2 =>
        giryM_ret R ((App e1 (Val v), σ1) : <<discr cfg>>)
    | Case (Val (InjRV v)) e1 e2 =>
        giryM_ret R ((App e2 (Val v), σ1) : <<discr cfg>>)
    | AllocN (Val (LitV (LitInt N))) (Val v) =>
        let ℓ := fresh_loc σ1.(heap) in
        if bool_decide (0 < Z.to_nat N)%nat
          then giryM_ret R ((Val $ LitV $ LitLoc ℓ, state_upd_heap_N ℓ (Z.to_nat N) v σ1) : <<discr cfg>>)
          else giryM_zero
    | Load (Val (LitV (LitLoc l))) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val v, σ1) : <<discr cfg>>)
          | None => giryM_zero
        end
    | Store (Val (LitV (LitLoc l))) (Val w) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val $ LitV LitUnit, state_upd_heap <[l:=w]> σ1) : <<discr cfg>>)
          | None => giryM_zero
        end

    (* FIXME: Finish implementation for tapes *)

    (*
    (* Uniform sampling from [0, 1 , ..., N] *)
    | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) =>
        giryM_map
          (m_discr (fun (n : 'I_(S (Z.to_nat N))) => ((Val $ LitV $ LitInt n, σ1) : <<discr cfg>>)))
          (giryM_unif (Z.to_nat N))
    | AllocTape (Val (LitV (LitInt z))) =>
        let ι := fresh_loc σ1.(tapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := (fin (Z.to_nat z; [])) ]> σ1) : <<discr cfg>>)
     *)

    (*
    (* Labelled sampling, conditional on tape contents *)
    | Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))) =>
        match σ1.(tapes) !! l with
        | Some (M; ns) =>
            if bool_decide (M = Z.to_nat N) then
              match ns  with
              | n :: ns =>
                  (* the tape is non-empty so we consume the first number *)
                  giryM_ret R ((Val $ LitV $ LitInt $ fin_to_nat n, state_upd_tapes <[l:=(fin(M; ns))]> σ1) : <<discr cfg>>)
              | [] =>
                  giryM_map
                    (m_discr (fun (n : 'I_(S (Z.to_nat M))) => ((Val $ LitV $ LitInt n, σ1) : <<discr cfg>>)))
                    (giryM_unif (Z.to_nat _))
              end
            else
              (* bound did not match the bound of the tape *)
              giryM_map
                (m_discr (fun (n : 'I_(S (Z.to_nat M))) => ((Val $ LitV $ LitInt n, σ1) : <<discr cfg>>)))
                  (giryM_unif (Z.to_nat _))
        | None => mzero
        end
        *)
    | Tick (Val (LitV (LitInt n))) => giryM_ret R ((Val $ LitV $ LitUnit, σ1) : <<discr cfg>>)
    | _ => giryM_zero
    end.

  (* head_stepM is a measurable map because it is a function out of a discrete space.

     After we add continuous varaibles this argument gets more complex. It is not
     true in general that the match-wise composition of measurable maps is measurable. *)

  Definition head_stepM : measurable_map <<discr cfg>> (giryM <<discr cfg>>)
    := m_discr head_stepM_def.

  (* Instead, we may consider restructing the semantics to use 'I_m instead of (fin m)
  Definition fin_of_Im (m : nat) : 'I_m -> stdpp.fin.fin m.
  Admitted.
   *)

  Definition state_stepM_def (c : state * loc) : giryM (<<discr state>>) :=
    let (σ1, α) := c in
    if bool_decide (α ∈ dom σ1.(tapes)) then
      giryM_zero
      (*
      let: (N; ns) := (σ1.(tapes) !!! α) in
      giryM_map
        (m_discr (λ (n : 'I_(S N)), (state_upd_tapes (<[α := fin (N; ns ++ [ fin_of_Im _ n : stdpp.fin.fin (S N)])]>) σ1) : <<discr state>>))
        (giryM_unif _)
      *)
    else giryM_zero.

  Definition state_stepM : measurable_map <<discr (state * loc)>> (giryM <<discr state>>)
    := m_discr state_stepM_def.

End meas_semantics.


(*
(*
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
*)

(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

(* ??? *)
(*
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

*)

(** A relational characterization of the support of [head_step] to make it easier to
    do inversion and prove reducibility easier c.f. lemma below *)
(*
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
  head_step_rel (Tick $ Val $ LitV $ LitInt z) σ (Val $ LitV $ LitUnit) σ.
*)
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

(*
Lemma head_step_support_equiv_rel e1 e2 σ1 σ2 :
  head_step e1 σ1 (e2, σ2) > 0 ↔ head_step_rel e1 σ1 e2 σ2.
Proof.
  split.
  - intros ?. destruct e1; inv_head_step; eauto with head_step.
  - inversion 1; simplify_map_eq/=; try case_bool_decide; simplify_eq; solve_distr; done.
Qed.
*)

(*
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
*)
(*
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
*)
(*
Lemma state_step_mass σ α :
  α ∈ dom σ.(tapes) → SeriesC (state_step σ α) = 1.
Proof.
  intros Hdom.
  rewrite /state_step bool_decide_eq_true_2 //=.
  case_match.
  rewrite dmap_mass dunif_mass //.
Qed.
*)
(*
Lemma head_step_mass e σ :
  (∃ ρ, head_step e σ ρ > 0) → SeriesC (head_step e σ) = 1.
Proof.
  intros [[] Hs%head_step_support_equiv_rel].
  inversion Hs;
    repeat (simplify_map_eq/=; solve_distr_mass || case_match; try (case_bool_decide; done)).
Qed.
*)
Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. destruct Ki2, Ki1; naive_solver eauto with f_equal. Qed.
*)
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
  | AllocUTape e => 1 + height e
  | Rand e1 e2 => 1 + height e1 + height e2
  | URand e1 e2 => 1 + height e1 + height e2
  | Tick e => 1 + height e
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

Definition get_active (σ : state) : list loc := elements (dom σ.(tapes)).


(*
Lemma state_step_get_active_mass σ α :
  α ∈ get_active σ → SeriesC (state_step σ α) = 1.
Proof. rewrite elem_of_elements. apply state_step_mass. Qed.
*)

(*
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
*)

(*
Lemma meas_lang_mixin :
  EctxiLanguageMixin of_val to_val fill_item decomp_item expr_ord head_step state_step get_active.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    state_step_head_step_not_stuck, state_step_get_active_mass, head_step_mass,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val,
    decomp_fill_item, decomp_fill_item_2, expr_ord_wf, decomp_expr_ord.
Qed.
*)
End meas_lang.
(*
(*
(** Language *)
Canonical Structure meas_ectxi_lang := EctxiLanguage prob_lang.get_active prob_lang.prob_lang_mixin.
Canonical Structure meas_ectx_lang := EctxLanguageOfEctxi prob_ectxi_lang.
Canonical Structure meas_lang := LanguageOfEctx prob_ectx_lang.

(* Prefer prob_lang names over ectx_language names. *)
Export meas_lang.

*)
*)
