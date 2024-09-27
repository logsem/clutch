From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.

From Coq Require Export Reals.
From clutch.prob.monad Require Export laws.
From mathcomp.analysis Require Export Rstruct.

From mathcomp Require Import classical_sets.

(* Fix giryM to be the giry type with stdlib-valued real numbers *)
Notation giryM := (giryM (R := R)).

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

(* Instances for Z *)
HB.instance Definition _ := gen_eqMixin Z.
HB.instance Definition _ := gen_choiceMixin Z.
HB.instance Definition _ := isPointed.Build Z inhabitant.

(* Instances for loc *)
HB.instance Definition _ := gen_eqMixin loc.
HB.instance Definition _ := gen_choiceMixin loc.
HB.instance Definition _ := isPointed.Build loc inhabitant.

Module meas_lang.

Inductive base_lit_pre : Type :=
  | LitInt (n : Z)
  | LitBool (b : bool)
  | LitUnit
  | LitLoc (l : loc)
  | LitLbl (l : loc)
  | LitReal (r : ((R : realType) : measurableType _)).

Inductive un_op : Set :=
  | NegOp | MinusUnOp.

Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp. (* Pointer offset *)

(* exprs, parameterized by type of base_lits B*)
Inductive exprB (B : Type) :=
  (* Values *)
  | Val (v : valB B)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : exprB B)
  | App (e1 e2 : exprB B)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : exprB B)
  | BinOp (op : bin_op) (e1 e2 : exprB B)
  | If (e0 e1 e2 : exprB B)
  (* Products *)
  | Pair (e1 e2 : exprB B)
  | Fst (e : exprB B)
  | Snd (e : exprB B)
  (* Sums *)
  | InjL (e : exprB B)
  | InjR (e : exprB B)
  | Case (e0 : exprB B) (e1 : exprB B) (e2 : exprB B)
  (* Heap *)
  | AllocN (e1 e2 : exprB B) (* Array length and initial value *)
  | Load (e : exprB B)
  | Store (e1 : exprB B) (e2 : exprB B)
  (* Finite probabilistic choice *)
  | AllocTape (e : exprB B)
  | Rand (e1 e2 : exprB B)
  (* Real probabilistic choice *)
  | AllocUTape
  | URand (e : exprB B)
  (* No-op operator used for cost *)
  | Tick (e : exprB B)
with valB (B : Type) :=
  | LitV (l : B)
  | RecV (f x : binder) (e : exprB B)
  | PairV (v1 v2 : valB B)
  | InjLV (v : valB B)
  | InjRV (v : valB B).

Local Open Scope classical_set_scope.

(** Define a sigma-algebra on base-lit *)

(* s ∈ base_lit_generators iff s is a lifted measurable set of Z, bool, loc, lbl, unit, or R. *)
Definition base_lit_generators : set (set (base_lit_pre)) :=
    (image setT (fun M => image M LitInt)) `|`
    (image setT (fun M => image M LitBool)) `|`
    (image setT (fun M => image M LitLoc)) `|`
    (image setT (fun M => image M LitLbl)) `|`
    (image (@measurable _ (R : realType)) (fun M => image M LitReal)) `|`
    [set [set LitUnit]].

HB.instance Definition _ := gen_eqMixin base_lit_pre.
HB.instance Definition _ := gen_choiceMixin base_lit_pre.
HB.instance Definition _ := isPointed.Build base_lit_pre LitUnit.

Local Lemma base_lit_meas_obligation : ∀ A : set base_lit_pre, <<s base_lit_generators >> A → <<s base_lit_generators  >> (~` A).
Proof. eapply sigma_algebraC. Qed.

(* There's got to be a way to delete this *)
HB.instance Definition _ := @isMeasurable.Build (sigma_display base_lit_generators)
  base_lit_pre
  <<s base_lit_generators>> (@sigma_algebra0 _ setT base_lit_generators) base_lit_meas_obligation
  (@sigma_algebra_bigcup _ setT base_lit_generators).

Definition base_lit : measurableType _ := g_sigma_algebraType base_lit_generators.

(** Lift sigma algebra on base lits to exprs *)

(* expr_pre, val_pre: expressions with base_lit values *)
Definition expr_pre : Type := exprB base_lit.
Definition val_pre : Type := valB base_lit.

(* exprS, valS: expressions with set of base_lit values *)
Definition exprS : Type := exprB (set base_lit).
Definition valS : Type := valB (set base_lit).


(* True when e is an expression where all leaves are measurable sets *)
Fixpoint is_expr_with_measurable_leaves (e : exprS) : Prop :=
  match e with
  | Val v          => is_val_with_measurable_leaves v
  | Var x          => True
  | Rec f x e      => is_expr_with_measurable_leaves e
  | App e1 e2      => is_expr_with_measurable_leaves e1 /\ is_expr_with_measurable_leaves e2
  | UnOp op e      => is_expr_with_measurable_leaves e
  | BinOp op e1 e2 => is_expr_with_measurable_leaves e1 /\ is_expr_with_measurable_leaves e2
  | If e0 e1 e2    => is_expr_with_measurable_leaves e0 /\ is_expr_with_measurable_leaves e1 /\
                      is_expr_with_measurable_leaves e2
  | Pair e1 e2     => is_expr_with_measurable_leaves e1 /\ is_expr_with_measurable_leaves e2
  | Fst e1         => is_expr_with_measurable_leaves e1
  | Snd e1         => is_expr_with_measurable_leaves e1
  | InjL e1        => is_expr_with_measurable_leaves e1
  | InjR e1        => is_expr_with_measurable_leaves e1
  | Case e0 e1 e2  => is_expr_with_measurable_leaves e0 /\ is_expr_with_measurable_leaves e1 /\
                      is_expr_with_measurable_leaves e2
  | AllocN e1 e2   => is_expr_with_measurable_leaves e1 /\ is_expr_with_measurable_leaves e2
  | Load e         => is_expr_with_measurable_leaves e
  | Store e1 e2    => is_expr_with_measurable_leaves e1 /\ is_expr_with_measurable_leaves e2
  | AllocTape e    => is_expr_with_measurable_leaves e
  | Rand e1 e2     => is_expr_with_measurable_leaves e1 /\ is_expr_with_measurable_leaves e2
  | AllocUTape     => True
  | URand e        => is_expr_with_measurable_leaves e
  | Tick e         => is_expr_with_measurable_leaves e
  end
  with
    is_val_with_measurable_leaves (v : valS) : Prop :=
    match v with
    | LitV v       => @measurable _ base_lit v
    | RecV f x e   => is_expr_with_measurable_leaves e
    | PairV v1 v2  => is_val_with_measurable_leaves v1 /\ is_val_with_measurable_leaves v2
    | InjLV v      => is_val_with_measurable_leaves v
    | InjRV v      => is_val_with_measurable_leaves v
    end.

Definition all_expr_with_meas_leaves : set exprS := is_expr_with_measurable_leaves.
Definition all_val_with_meas_leaves : set valS := is_val_with_measurable_leaves.

(* Takes a tree with measurable sets of base_lit for litV and
   returns a set of trees with base_lit for litV *)
Fixpoint cylinder_tree (e : exprS) : set expr_pre :=
  match e with
  | Val v          => image (cylinder_tree_v v) (Val _)
  | Var x          => [set (Var _ x)]
  | Rec f x e      => set0
  | App e1 e2      => set0
  | UnOp op e      => set0
  | BinOp op e1 e2 => set0
  | If e0 e1 e2    => set0
  | Pair e1 e2     => set0
  | Fst e1         => set0
  | Snd e1         => set0
  | InjL e1        => set0
  | InjR e1        => set0
  | Case e0 e1 e2  => set0
  | AllocN e1 e2   => set0
  | Load e         => set0
  | Store e1 e2    => set0
  | AllocTape e    => set0
  | Rand e1 e2     => set0
  | AllocUTape     => set0
  | URand e        => set0
  | Tick e         => set0
  end
  with
    cylinder_tree_v (v : valS) : set val_pre :=
    match v with
    | LitV b       => set0
    | RecV f x e   => set0
    | PairV v1 v2  => set0
    | InjLV v      => set0
    | InjRV v      => set0
    end.

(* The sigma algebra on exprs is generated by the set of all cylinder trees *)
Definition expr_subbase : set (set expr_pre) := image all_expr_with_meas_leaves cylinder_tree.
Definition val_subbase : set (set val_pre) := image all_val_with_meas_leaves cylinder_tree_v.

Definition expr : Type := g_sigma_algebraType expr_subbase.
Definition val : Type  := g_sigma_algebraType val_subbase.

Local Open Scope classical_set_scope.

HB.instance Definition _ := gen_eqMixin expr.
HB.instance Definition _ := gen_choiceMixin expr.
HB.instance Definition _ := isPointed.Build expr (Val base_lit (LitV _ LitUnit)).

Local Lemma expr_meas_obligation : ∀ A : set expr, <<s expr_subbase >> A → <<s expr_subbase >> (~` A).
Proof. eapply sigma_algebraC. Qed.

(* There's got to be a way to delete this *)
HB.instance Definition _ := @isMeasurable.Build (sigma_display expr_subbase)
  expr
  <<s expr_subbase>> (@sigma_algebra0 _ setT expr_subbase) expr_meas_obligation
  (@sigma_algebra_bigcup _ setT expr_subbase).

HB.instance Definition _ := gen_eqMixin val.
HB.instance Definition _ := gen_choiceMixin val.
HB.instance Definition _ := isPointed.Build val (LitV _ LitUnit).

Local Lemma val_meas_obligation : ∀ A : set val, <<s val_subbase >> A → <<s val_subbase >> (~` A).
Proof. eapply sigma_algebraC. Qed.


(* There's got to be a way to delete this *)
HB.instance Definition _ := @isMeasurable.Build (sigma_display val_subbase)
  val
  <<s val_subbase>> (@sigma_algebra0 _ setT val_subbase) val_meas_obligation
  (@sigma_algebra_bigcup _ setT val_subbase).


Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation of_val := (@Val base_lit) (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.


(* This part of the sigma algebra is not discrete *)
(* MARKUSDE: Externalizing the fin bound here also simplifies definitions. *)
(* Will need this to be a separate type for HB. Infinite product sigma algebra. *)
Definition tape_content_t (A : Type) : Type := nat -> option A.

Record tape (A : Type) : Type := {
  tape_position : nat;
  tape_contents : tape_content_t A
}.

(* Tapes in the computable fragment *)
Record btape : Type := {
    btape_tape :> tape nat;
    btape_bound : nat
}.

(* All values of the tape are within the tape bound *)
Definition btape_inbounds (t : btape): Prop :=
  forall n : nat,
    tape_contents _ t n = None \/
    exists v : nat, tape_contents _ t n = Some v /\ v < btape_bound t.

(* All tape values prior to state have been determined *)
Definition tape_history_deterministic {A} (t : tape A) : Prop :=
  forall i : nat, i < tape_position _ t -> exists v : A, tape_contents _ t i = Some v.

Definition emptyTapeContents {A : Type} : tape_content_t A := fun _ => None.

Definition emptyTape {A : Type} : tape A :=
  {| tape_position := 0 ;
     tape_contents := emptyTapeContents
  |}.

(* History lookup: look through absolute history *)
Global Instance tape_content_lookup {A} : Lookup nat A (tape_content_t A) := fun i => fun h => h i.

(* Tape lookup: look relative to current index. t !! 0  will be the next sample. *)
Global Instance tape_rel_lookup {A} : Lookup nat A (tape A) := fun i => fun t => (tape_contents _ t (i + tape_position _ t)).

Definition tape_content_update_unsafe {A} (i : nat) (v : option A) (h : tape_content_t A) : tape_content_t A
  := fun i' => if i' =? i then v else h i'.

Global Instance tape_content_insert {A} : Insert nat (option A) (tape_content_t A) := tape_content_update_unsafe.

Definition tapeUpdateUnsafe {A} (i : nat) (v : option A) (t : tape A) : tape A :=
  {| tape_position := tape_position _ t;
     tape_contents := <[ (i + tape_position _ t) := v ]> (tape_contents _ t)
  |}.

Global Instance tape_insert {A} : Insert nat (option A) (tape A) := tapeUpdateUnsafe.

Program Definition tapeAdvance {A} (t : tape A) : tape A
  := {| tape_position := 1 + tape_position _ t; tape_contents := tape_contents _ t |}.

(* Advance the tape by 1, returning an updated tape and the first sample on the tape. *)
Program Definition tapeNext {A} (t : tape A) (H : isSome (t !! 0)) : A * (tape A)
  := match (t !! 0) with
     | None => _
     | Some v =>
         (v,
          {| tape_position := 1 + tape_position _ t;
             tape_contents := tape_contents _ t |})
     end.
Next Obligation. by move=>/= ? ? H1 H2; symmetry in H2; rewrite H2//= in H1. Defined.

(* Representation predicates for common tape structures *)

Definition tapeHasPrefix {A} (t : tape A) (l : list A) : Prop
  := forall i : nat, i < length l -> t !! i = l !! i.

Definition tapeEmptyAfter {A} (t : tape A) (b : nat) : Prop
  := forall i : nat, i >= b -> t !! i = None.


(* Tapes a la base clutch *)
Definition isFiniteTape (t : btape) (l : list nat) : Prop
  :=   tapeHasPrefix t l
     /\ tapeEmptyAfter t (length l)
     /\ btape_inbounds t
     /\ tape_history_deterministic t.


(* TODO: realIsBinarySequence (cannonical form w/ 0-termination on dyadic numbers) *)

Definition tapeHasInfinitePrefix {A} (t : tape A) (f : nat -> A) : Prop
  := forall i : nat, t !! i = Some (f i).

(* TODO: tapeIsRealInRange (l : R) ... := bound = 1, tapeHasInfinitePrefic *)
(* tapeOfReal ... ?*)

(* Tape with "Junk" prefix *)
Definition tapeHasEventually {A} (t : tape A) (l : list A) : Prop
  := exists offset: nat, forall i : nat, i < length l -> t !! (i + offset) = l !! i.

Global Instance tape_inhabited {A} : Inhabited (tape A) := populate emptyTape.
Global Instance tapes_lookup_total {A} : LookupTotal loc (tape A) (gmap loc (tape A)).
Proof. apply map_lookup_total. Defined.
Global Instance tapes_insert {A} : Insert loc (tape A) (gmap loc (tape A)).
Proof. apply map_insert. Defined.

(* Tapes of real numbers *)
Definition utape : Type := tape R.

(* FIXME: Generalize, if it works *)
Definition btape_generators : set (set btape) :=
  (fun S => exists bound position index value : nat,
      S = [set {| btape_tape :=
                   {| tape_position := position ;
                      tape_contents := (fun i => if (i =? index) then Some value else None) |} ;
                  btape_bound := bound |}] \/
      S = [set {| btape_tape :=
                   {| tape_position := position ;
                      tape_contents := (fun _ => None) |} ;
                  btape_bound := bound |}]).

HB.instance Definition _ := gen_eqMixin btape.
HB.instance Definition _ := gen_choiceMixin btape.
HB.instance Definition _ := isPointed.Build btape {| btape_tape := emptyTape; btape_bound := 0 |}.

Local Lemma btape_meas_obligation : ∀ A : set btape, <<s btape_generators>> A → <<s btape_generators >> (~` A).
Proof. eapply sigma_algebraC. Qed.

(* There's got to be a way to delete this *)
HB.instance Definition _ := @isMeasurable.Build (sigma_display btape_generators)
  btape
  <<s btape_generators>> (@sigma_algebra0 _ setT btape_generators) btape_meas_obligation
  (@sigma_algebra_bigcup _ setT btape_generators).






(* FIXME: Generalize, if it works *)
Definition utape_generators : set (set utape) :=
  (fun S : set utape => exists position index : nat, ∃ M : (set R),
      (@measurable _ (R : realType) M) /\
      S = image M
            (fun r => {| tape_position := position;
                       tape_contents := (fun i => if (i =? index) then Some r else None) |} : utape) \/
      S = [set {| tape_position := position ; tape_contents := (fun _ => None )|}]).

HB.instance Definition _ := gen_eqMixin utape.
HB.instance Definition _ := gen_choiceMixin utape.
HB.instance Definition _ := isPointed.Build utape emptyTape.

Local Lemma utape_meas_obligation : ∀ A : set utape, <<s utape_generators>> A → <<s utape_generators >> (~` A).
Proof. eapply sigma_algebraC. Qed.

(* There's got to be a way to delete this *)
HB.instance Definition _ := @isMeasurable.Build (sigma_display utape_generators)
  utape
  <<s utape_generators>> (@sigma_algebra0 _ setT utape_generators) utape_meas_obligation
  (@sigma_algebra_bigcup _ setT utape_generators).



(** The state: a [loc]-indexed heap of [val]s, and [loc]-indexed tapes, and [loc]-indexed utapes *)
Record state : Type := {
  heap   : gmap loc val;
  tapes  : gmap loc btape;
  utapes : gmap loc utape
}.


Definition state_generators : set (set state) := setT.
  (* FIXME *)
  (*
  (fun S : set state =>
     forall l : loc,
      exists SV : set val,
      exists ST : set btape,
      exists SU : set utape,
      measurable SV /\
      measurable ST /\
      measurable SU /\
      image S (fun st => st.(heap) !! l) = SV ).
*)

HB.instance Definition _ := gen_eqMixin state.
HB.instance Definition _ := gen_choiceMixin state.
HB.instance Definition _ := isPointed.Build state {| heap := gmap_empty; tapes := gmap_empty; utapes := gmap_empty |}.

Local Lemma state_meas_obligation : ∀ A : set state, <<s state_generators>> A → <<s state_generators >> (~` A).
Proof. eapply sigma_algebraC. Qed.

(* There's got to be a way to delete this *)
HB.instance Definition _ := @isMeasurable.Build (sigma_display state_generators)
  state
  <<s state_generators>> (@sigma_algebra0 _ setT state_generators) state_meas_obligation
  (@sigma_algebra_bigcup _ setT state_generators).






(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

(*
Global Instance state_inhabited : Inhabited state := populate {| heap := gmap_empty; tapes := gmap_empty; utapes := gmap_empty |}.
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).
*)

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
  | RandLCtx (v2 : val)
  | RandRCtx (e1 : expr)
  | URandCtx
  | TickCtx.


(* FIXME: Hide cosntructors, so that we don't need to mention base_lit *)


(*
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
  | URandCtx => URand e
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
  | Rand e1 e2     =>
      match e2 with
      | Val v      => noval e1 (RandLCtx v)
      | _          => Some (RandRCtx e1, e2)
      end
  | URand e        => noval e URandCtx
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
  | AllocUTape => AllocUTape
  | Rand e1 e2 => Rand (subst x v e1) (subst x v e2)
  | URand e => URand (subst x v e)
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
  | LeOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 <= r2)%R
  | LtOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 < r2)%R
  | EqOp => Some $ LitBool $ bool_decide $ classical.make_decision (r1 = r2)%R
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

Definition state_upd_tapes (f : gmap loc btape → gmap loc btape) (σ : state) : state :=
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

(* #[local] Open Scope R.  *)



Section pointed_instances.
  Local Open Scope classical_set_scope.

  (* Fail Check (<<discr state>> : measurableType _).  *)
  HB.instance Definition _ := gen_eqMixin state.
  HB.instance Definition _ := gen_choiceMixin state.
  HB.instance Definition _ := isPointed.Build state inhabitant.
  (* Check (<<discr state>> : measurableType _). *)

  (** cfg is pointed (automatic) *)
  (* Check (<<discr cfg>> : measurableType _).  *)

  (** state * loc is pointed (automatic) *)
  (* Check (<<discr (state * loc)>> : measurableType _). *)

  (** R is pointed *)
  Check (<<discr R>> : measurableType _).

End pointed_instances.


Section meas_semantics.
  Local Open Scope classical_set_scope.
  Local Open Scope expr_scope.

  Definition discr_cfg : measurableType _ := (<<discr expr>> * <<discr state>>)%type.

  Definition head_stepM_def (c : discr_cfg) : giryM discr_cfg :=
    let (e1, σ1) := c in
    match e1 with
    | Rec f x e =>
        giryM_ret R ((Val $ RecV f x e, σ1) : discr_cfg)
    | Pair (Val v1) (Val v2) =>
        giryM_ret R ((Val $ PairV v1 v2, σ1) : discr_cfg)
    | InjL (Val v) =>
        giryM_ret R ((Val $ InjLV v, σ1) : discr_cfg)
    | InjR (Val v) =>
        giryM_ret R ((Val $ InjRV v, σ1) : discr_cfg)
    | App (Val (RecV f x e1)) (Val v2) =>
        giryM_ret R ((subst' x v2 (subst' f (RecV f x e1) e1) , σ1) : discr_cfg)
    | UnOp op (Val v) =>
        match un_op_eval op v with
          | Some w => giryM_ret R ((Val w, σ1) : discr_cfg)
          | _ => giryM_zero
        end
    | BinOp op (Val v1) (Val v2) =>
        match bin_op_eval op v1 v2 with
          | Some w => giryM_ret R ((Val w, σ1) : discr_cfg)
          | _ => giryM_zero
        end
    | If (Val (LitV (LitBool true))) e1 e2  =>
        giryM_ret R ((e1 , σ1) : discr_cfg)
    | If (Val (LitV (LitBool false))) e1 e2 =>
        giryM_ret R ((e2 , σ1) : discr_cfg)
    | Fst (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v1 , σ1) : discr_cfg) (* Syntax error when I remove the space between v1 and , *)
    | Snd (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v2, σ1) : discr_cfg)
    | Case (Val (InjLV v)) e1 e2 =>
        giryM_ret R ((App e1 (Val v), σ1) : discr_cfg)
    | Case (Val (InjRV v)) e1 e2 =>
        giryM_ret R ((App e2 (Val v), σ1) : discr_cfg)
    | AllocN (Val (LitV (LitInt N))) (Val v) =>
        let ℓ := fresh_loc σ1.(heap) in
        if bool_decide (0 < Z.to_nat N)%nat
          then giryM_ret R ((Val $ LitV $ LitLoc ℓ, state_upd_heap_N ℓ (Z.to_nat N) v σ1) : discr_cfg)
          else giryM_zero
    | Load (Val (LitV (LitLoc l))) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val v, σ1) : discr_cfg)
          | None => giryM_zero
        end
    | Store (Val (LitV (LitLoc l))) (Val w) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val $ LitV LitUnit, state_upd_heap <[l:=w]> σ1) : discr_cfg)
          | None => giryM_zero
        end
    (* Uniform sampling from [0, 1 , ..., N] *)
    | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) =>
        giryM_map
          (m_discr (fun (n : 'I_(S (Z.to_nat N))) => ((Val $ LitV $ LitInt n, σ1) : discr_cfg)))
          (giryM_unif (Z.to_nat N))
    | AllocTape (Val (LitV (LitInt z))) =>
        let ι := fresh_loc σ1.(tapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := {| btape_tape := emptyTape ; btape_bound := (Z.to_nat z) |} ]> σ1) : discr_cfg)
    (* Rand with a tape *)
    | Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))) =>
        match σ1.(tapes) !! l with
        | Some btape =>
            (* There exists a tape with label l *)
            let τ := btape.(btape_tape) in
            let M := btape.(btape_bound) in
            if (bool_decide (M = Z.to_nat N)) then
              (* Tape bounds match *)
              match (τ !! 0) with
              | Some v =>
                  (* There is a next value on the tape *)
                  let σ' := state_upd_tapes <[ l := {| btape_tape := (tapeAdvance τ); btape_bound := M |} ]> σ1 in
                  (giryM_ret R ((Val $ LitV $ LitInt $ Z.of_nat v, σ') : discr_cfg))
              | None =>
                  (* Next slot on tape is empty *)
                  giryM_map
                    (m_discr (fun (v : 'I_(S (Z.to_nat N))) =>
                       (* Fill the tape head with new sample *)
                       let τ' := <[ (0 : nat) := Some (v : nat) ]> τ in
                       (* Advance the tape *)
                       let σ' := state_upd_tapes <[ l := {| btape_tape := (tapeAdvance τ'); btape_bound := M |} ]> σ1 in
                       (* Return the new sample and state *)
                       ((Val $ LitV $ LitInt $ Z.of_nat v, σ') : discr_cfg)))
                   (giryM_unif (Z.to_nat N))
              end
            else
              (* Tape bounds do not match *)
              (* Do not advance the tape, but still generate a new sample *)
              giryM_map
                (m_discr (fun (n : 'I_(S (Z.to_nat N))) => ((Val $ LitV $ LitInt n, σ1) : discr_cfg)))
                (giryM_unif (Z.to_nat N))
        | None => giryM_zero
        end
    | AllocUTape =>
        let ι := fresh_loc σ1.(utapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_utapes <[ ι := emptyTape ]> σ1) : discr_cfg)
    (* Urand with no tape *)
    | URand (Val (LitV LitUnit)) =>
        giryM_map
          (m_discr (fun u => ((Val $ LitV $ LitReal u, σ1) : discr_cfg)))
          giryM_zero
    (* Urand with a tape *)
    | URand (Val (LitV (LitLbl l))) =>
        match σ1.(utapes) !! l with
        | Some τ =>
            (* tape l is allocated *)
            match (τ !! 0) with
            | Some u =>
                (* Head has a sample *)
                let σ' := state_upd_utapes <[ l := (tapeAdvance τ) ]> σ1 in
                (giryM_ret R ((Val $ LitV $ LitReal u, σ') : discr_cfg))
            | None =>
                (* Head has no sample *)
                giryM_map
                  (m_discr (fun (u : R) =>
                    (* Fill tape head with new sample *)
                    let τ' := <[ (0 : nat) := Some u ]> τ in
                    (* Advance tape *)
                    let σ' := state_upd_utapes <[ l := (tapeAdvance τ') ]> σ1 in
                    (* Return the update value an state *)
                    ((Val $ LitV $ LitReal u, σ') : discr_cfg)))
                  giryM_zero
            end
        | None => giryM_zero
        end
    | Tick (Val (LitV (LitInt n))) => giryM_ret R ((Val $ LitV $ LitUnit, σ1) : discr_cfg)
    | _ => giryM_zero
    end.

  (* I don't care if this this true; we will delete it soon and replace it with a proof for the real SA. *)
  Local Lemma head_stepM_def_measurable :
    @measurable_fun _ _ discr_cfg (giryM discr_cfg) setT head_stepM_def.
  Proof. Admitted.

  HB.instance Definition _ :=
    isMeasurableMap.Build _ _ _ _ _ head_stepM_def_measurable.

  Definition head_stepM : measurable_map (<<discr expr>> * <<discr state>>)%type (giryM (<<discr expr>> * <<discr state>>)%type) :=
    head_stepM_def.

End meas_semantics.


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

Local Open Scope classical_set_scope.

(** A relational characterization of the support of [head_step] to make it easier to
    do inversion and prove reducibility easier c.f. lemma below *)
Inductive head_step_rel : expr -> state -> expr -> state → Prop :=
(* Values *)
| RecS f x e σ :
  head_step_rel (Rec f x e) σ (Val $ RecV f x e) σ
| PairS v1 v2 σ :
  head_step_rel (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ
| InjLS v σ :
  head_step_rel (InjL $ Val v) σ (Val $ InjLV v) σ
| InjRS v σ :
  head_step_rel (InjR $ Val v) σ (Val $ InjRV v) σ

(* Pure reductions *)
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

(* Heap *)
| AllocNS z N v σ l :
  l = fresh_loc σ.(heap) →
  N = Z.to_nat z →
  (0 < N)%nat ->
  head_step_rel
    (AllocN (Val (LitV (LitInt z))) (Val v)) σ
    (Val $ LitV $ LitLoc l) (state_upd_heap_N l N v σ)
| LoadS l v σ :
  σ.(heap) !! l = Some v →
  head_step_rel (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ
| StoreS l v w σ :
  σ.(heap) !! l = Some v →
  head_step_rel (Store (Val $ LitV $ LitLoc l) (Val w)) σ
    (Val $ LitV LitUnit) (state_upd_heap <[l:=w]> σ)

(* Rand *)
| RandNoTapeS z N (n_int : Z) (n_nat : nat) σ:
  N = Z.to_nat z →
  n_nat < N ->
  Z.of_nat n_nat = n_int ->
  head_step_rel (Rand (Val $ LitV $ LitInt z) (Val $ LitV LitUnit)) σ (Val $ LitV $ LitInt n_int) σ
| AllocTapeS z N σ l :
  l = fresh_loc σ.(tapes) →
  N = Z.to_nat z →
  head_step_rel (AllocTape (Val (LitV (LitInt z)))) σ
    (Val $ LitV $ LitLbl l) (state_upd_tapes <[l := {| btape_tape := emptyTape ; btape_bound := N |}]> σ)
| RandTapeS l z N n b b' σ :
  N = Z.to_nat z →
  σ.(tapes) !! l = Some {| btape_tape := b ; btape_bound := N |} ->
  b !! 0 = Some (Z.to_nat n) ->
  b' = tapeAdvance b ->
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl l)))) σ
    (Val $ LitV $ LitInt $ n) (state_upd_tapes <[l := {| btape_tape := b' ; btape_bound := N|}]> σ)
| RandTapeEmptyS l z N (n_nat : nat) (n_int : Z) σ :
  N = Z.to_nat z →
  Z.of_nat n_nat = n_int ->
  n_nat < N ->
  σ.(tapes) !! l = Some {| btape_tape := emptyTape; btape_bound := N |} →
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitInt n_nat) σ
| RandTapeOtherS l z M N b (n_nat : nat) (n_int : Z) σ :
  N = Z.to_nat z →
  Z.of_nat n_nat = n_int ->
  n_nat < N ->
  σ.(tapes) !! l = Some {| btape_tape := b ; btape_bound := M |} →
  N ≠ M →
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitInt n_int) σ

(* Urand *)
| URandNoTapeS (r : R) σ :
  (0 <= r)%R ->
  (r <= 1)%R ->
  head_step_rel (URand (Val $ LitV LitUnit)) σ (Val $ LitV $ LitReal r) σ
| AllocUTapeS σ l :
  l = fresh_loc σ.(tapes) →
  head_step_rel AllocUTape σ
    (Val $ LitV $ LitLbl l) (state_upd_utapes <[l := emptyTape]> σ)
| URandTapeS l b b' r σ :
  σ.(utapes) !! l = Some b ->
  b !! 0 = Some r ->
  b' = tapeAdvance b ->
  head_step_rel (URand (Val (LitV (LitLbl l)))) σ
    (Val $ LitV $ LitReal $ r) (state_upd_utapes <[l := b]> σ)
| URandTapeEmptyS l (r : R) b σ :
  (0 <= r)%R ->
  (r <= 1)%R ->
  σ.(utapes) !! l = Some b →
  head_step_rel (URand (Val $ LitV $ LitLbl l)) σ (Val $ LitV $ LitReal r) σ

(* Tick *)
| TickS σ z :
  head_step_rel (Tick $ Val $ LitV $ LitInt z) σ (Val $ LitV $ LitUnit) σ.

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

(*
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
  - inversion 1; simplify_map_eq/=; try case_bool_decide; simplify_eq; solve_distr; done.
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
  | AllocUTape => 1
  | Rand e1 e2 => 1 + height e1 + height e2
  | URand e => 1 + height e
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

Local Open Scope classical_set_scope.

Definition fill_item_mf K := m_discr (fill_item K : <<discr expr>> -> <<discr expr>>).

Definition meas_lang_mixin :
  @MeasEctxiLanguageMixin _ _ _ <<discr expr>> <<discr val>> <<discr state>> ectx_item
    of_val to_val fill_item_mf decomp_item expr_ord head_stepM_def.
Proof.
  split.
Admitted.

***)
End meas_lang.
(*

(** Language *)


Canonical Structure meas_ectxi_lang := MeasEctxiLanguage meas_lang.head_stepM meas_lang.meas_lang_mixin.
Canonical Structure meas_ectx_lang := MeasEctxLanguageOfEctxi meas_ectxi_lang.
Canonical Structure meas_lang := MeasLanguageOfEctx meas_ectx_lang.

(* Prefer meas_lang names over ectx_language names. *)
Export meas_lang.
*)
