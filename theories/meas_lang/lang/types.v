(* TODO cleanup imports *)
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export laws extras.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude.
(* From Coq Require Import Reals Psatz.
From stdpp Require Export binders strings.
From stdpp Require Import fin.
From stdpp Require Import gmap fin_maps countable fin.
From clutch.prob Require Export distribution.
From clutch.common Require Export language ectx_language ectxi_language locations.
From iris.prelude Require Import options.
From mathcomp Require Import ssrbool eqtype fintype choice all_algebra finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From mathcomp.analysis Require Import reals ereal signed normedtype sequences esum numfun measure lebesgue_measure lebesgue_integral. *)


(** Syntax for an expressions with general leaves *)

(** A base_lit with leaves of type TZ/TB/TL/TR *)
Inductive base_lit_pre {TZ TB TL TR : Type} : Type :=
  | LitInt  (n : TZ)
  | LitBool (b : TB)
  | LitUnit
  | LitLoc  (l : TL)
  | LitLbl  (l : TL)
  | LitReal (r : TR).

Inductive un_op : Set :=
  | NegOp | MinusUnOp.

Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp. (* Pointer offset *)

(** An expression and value with leaves of type TZ/TB/TL/TR *)
Local Open Scope classical_set_scope.
Inductive expr_pre {TZ TB TL TR : Type} :=
  (* Values *)
  | Val (v : val_pre)
  (* Base lambda calculus *)
  | Var (x : <<discr binder>>)
  | Rec (f x : <<discr binder>>) (e : expr_pre)
  | App (e1 e2 : expr_pre)
  (* Base types and their operations *)
  | UnOp (op : <<discr un_op>>) (e : expr_pre)
  | BinOp (op : <<discr bin_op>>) (e1 e2 : expr_pre)
  | If (e0 e1 e2 : expr_pre)
  (* Products *)
  | Pair (e1 e2 : expr_pre)
  | Fst (e : expr_pre)
  | Snd (e : expr_pre)
  (* Sums *)
  | InjL (e : expr_pre)
  | InjR (e : expr_pre)
  | Case (e0 e1 e2 : expr_pre)
  (* Heap *)
  | AllocN (e1 e2 : expr_pre) (* Array length and initial value *)
  | Load (e : expr_pre)
  | Store (e1 e2 : expr_pre)
  (* Finite probabilistic choice *)
  | AllocTape (e : expr_pre)
  | Rand (e1 e2 : expr_pre)
  (* Real probabilistic choice *)
  | AllocUTape
  | URand (e : expr_pre)
  (* No-op operator used for cost *)
  | Tick (e : expr_pre)
with val_pre {TZ TB TL TR : Type} :=
  | LitV (l : @base_lit_pre TZ TB TL TR)
  | RecV (f x : <<discr binder>>) (e : expr_pre)
  | PairV (v1 v2 : val_pre)
  | InjLV (v : val_pre)
  | InjRV (v : val_pre).

Scheme expr_pre_mut := Induction for expr_pre Sort Prop
with val_pre_mut := Induction for val_pre Sort Prop.

(* Instances for un_op *)
HB.instance Definition _ := gen_eqMixin un_op.
HB.instance Definition _ := gen_choiceMixin un_op.
HB.instance Definition _ := isPointed.Build un_op NegOp.

(* Instances for bin_op *)
HB.instance Definition _ := gen_eqMixin bin_op.
HB.instance Definition _ := gen_choiceMixin bin_op.
HB.instance Definition _ := isPointed.Build bin_op PlusOp.




Section functor.

Context {TZ1 TB1 TL1 TR1 : Type}.
Context {TZ2 TB2 TL2 TR2 : Type}.
Variable FInt : TZ1 -> TZ2.
Variable FBool : TB1 -> TB2.
Variable FLoc : TL1 -> TL2.
Variable FLbl : TL1 -> TL2.
Variable FReal : TR1 -> TR2.

Definition base_lit_pre_F (b : @base_lit_pre TZ1 TB1 TL1 TR1) : @base_lit_pre TZ2 TB2 TL2 TR2 :=
  match b with
  | LitInt n  => LitInt $ FInt n
  | LitBool b => LitBool $ FBool b
  | LitUnit   => LitUnit
  | LitLoc l  => LitLoc $ FLoc l
  | LitLbl l  => LitLbl $ FLbl l
  | LitReal r => LitReal $ FReal r
  end.

Fixpoint expr_pre_F (e : @expr_pre TZ1 TB1 TL1 TR1) : @expr_pre TZ2 TB2 TL2 TR2 :=
  match e with
  | Val v          => Val (val_pre_F v)
  | Var x          => Var x
  | Rec f x e      => Rec f x (expr_pre_F e)
  | App e1 e2      => App (expr_pre_F e1) (expr_pre_F e2)
  | UnOp op e      => UnOp op (expr_pre_F e)
  | BinOp op e1 e2 => BinOp op (expr_pre_F e1) (expr_pre_F e2)
  | If e1 e2 e3    => If (expr_pre_F e1) (expr_pre_F e2) (expr_pre_F e3)
  | Pair e1 e2     => Pair (expr_pre_F e1) (expr_pre_F e2)
  | Fst e          => Fst (expr_pre_F e)
  | Snd e          => Snd (expr_pre_F e)
  | InjL e         => InjL (expr_pre_F e)
  | InjR e         => InjR (expr_pre_F e)
  | Case e1 e2 e3  => Case (expr_pre_F e1) (expr_pre_F e2) (expr_pre_F e3)
  | AllocN e1 e2   => AllocN (expr_pre_F e1) (expr_pre_F e2)
  | Load e         => Load (expr_pre_F e)
  | Store e1 e2    => Store (expr_pre_F e1) (expr_pre_F e2)
  | AllocTape e    => AllocTape (expr_pre_F e)
  | Rand e1 e2     => Rand (expr_pre_F e1) (expr_pre_F e2)
  | AllocUTape     => AllocUTape
  | URand e        => URand (expr_pre_F e)
  | Tick e         => Tick (expr_pre_F e)
  end with val_pre_F (v : @val_pre TZ1 TB1 TL1 TR1) : @val_pre TZ2 TB2 TL2 TR2 :=
  match v with
  | LitV v         => LitV (base_lit_pre_F v)
  | RecV f x e     => RecV f x (expr_pre_F e)
  | PairV v1 v2    => PairV (val_pre_F v1) (val_pre_F v2)
  | InjLV v1       => InjLV (val_pre_F v1)
  | InjRV v1       => InjRV (val_pre_F v1)
  end.
End functor.



Section expr_algebra.
  (** Defines the sigma algebra over expressions *)
  Local Open Scope classical_set_scope.

  Definition TZ : measurableType default_measure_display := <<discr Z>>.
  Definition TB : measurableType default_measure_display := <<discr bool>>.
  Definition TL : measurableType default_measure_display := <<discr loc>>.
  Definition TR : measurableType default_measure_display := (R : realType).

  Definition base_lit_S : Type := @base_lit_pre (set TZ) (set TB) (set TL) (set TR).
  Definition val_S      : Type := @val_pre      (set TZ) (set TB) (set TL) (set TR).
  Definition expr_S     : Type := @expr_pre     (set TZ) (set TB) (set TL) (set TR).

  Definition base_lit_T : Type := @base_lit_pre TZ TB TL TR.
  Definition val_T      : Type := @val_pre      TZ TB TL TR.
  Definition expr_T     : Type := @expr_pre     TZ TB TL TR.

  (* Cylinder constructions *)

  (* Trees with sets on their leaves -> sets of trees with values on their leaves *)
  Definition base_lit_ST (b : base_lit_S) : set base_lit_T :=
    match b with
    | LitInt  s => image s LitInt
    | LitBool s => image s LitBool
    | LitUnit   => [set    LitUnit]
    | LitLoc  s => image s LitLoc
    | LitLbl  s => image s LitLbl
    | LitReal s => image s LitReal
    end.

  Fixpoint expr_ST (e : expr_S) : set expr_T :=
    match e with
    | Val v          => image (val_ST v) Val
    | Var x          => [set (Var x)]
    | Rec f x e      => image  (expr_ST e)   (Rec f x)
    | App e1 e2      => image2 (expr_ST e1) (expr_ST e2) App
    | UnOp op e      => image  (expr_ST e)  (UnOp op)
    | BinOp op e1 e2 => image2 (expr_ST e1) (expr_ST e2) (BinOp op)
    | If e0 e1 e2    => image3 (expr_ST e0) (expr_ST e1) (expr_ST e2) If
    | Pair e1 e2     => image2 (expr_ST e1) (expr_ST e2) Pair
    | Fst e1         => image  (expr_ST e1) Fst
    | Snd e1         => image  (expr_ST e1) Snd
    | InjL e1        => image  (expr_ST e1) InjL
    | InjR e1        => image  (expr_ST e1) InjR
    | Case e0 e1 e2  => image3 (expr_ST e0) (expr_ST e1) (expr_ST e2) Case
    | AllocN e1 e2   => image2 (expr_ST e1) (expr_ST e2) AllocN
    | Load e         => image  (expr_ST e)  Load
    | Store e1 e2    => image2 (expr_ST e1) (expr_ST e2) Store
    | AllocTape e    => image  (expr_ST e)  AllocTape
    | Rand e1 e2     => image2 (expr_ST e1) (expr_ST e2) Rand
    | AllocUTape     => [set AllocUTape]
    | URand e        => image  (expr_ST e)  URand
    | Tick e         => image  (expr_ST e)  Tick
    end
    with
      val_ST (v : val_S) : set val_T :=
      match v with
      | LitV b       => image  (base_lit_ST b) LitV
      | RecV f x e   => image  (expr_ST e) (RecV f x)
      | PairV v1 v2  => image2 (val_ST v1) (val_ST v2) PairV
      | InjLV v      => image  (val_ST v) InjLV
      | InjRV v      => image  (val_ST v) InjRV
      end.


  (* All trees with measurable sets on their leaves *)
  Definition base_lit_ML : set base_lit_S :=
    fun b =>
      match b with
      | LitInt  s => measurable s
      | LitBool s => measurable s
      | LitUnit   => True
      | LitLoc  s => measurable s
      | LitLbl  s => measurable s
      | LitReal s => measurable s
      end.

  Fixpoint expr_ML (e : expr_S) : Prop :=
    match e with
    | Val v          => val_ML v
    | Var x          => True
    | Rec f x e      => expr_ML e
    | App e1 e2      => expr_ML e1 /\ expr_ML e2
    | UnOp op e      => expr_ML e
    | BinOp op e1 e2 => expr_ML e1 /\ expr_ML e2
    | If e0 e1 e2    => expr_ML e0 /\ expr_ML e1 /\ expr_ML e2
    | Pair e1 e2     => expr_ML e1 /\ expr_ML e2
    | Fst e1         => expr_ML e1
    | Snd e1         => expr_ML e1
    | InjL e1        => expr_ML e1
    | InjR e1        => expr_ML e1
    | Case e0 e1 e2  => expr_ML e0 /\ expr_ML e1 /\ expr_ML e2
    | AllocN e1 e2   => expr_ML e1 /\ expr_ML e2
    | Load e         => expr_ML e
    | Store e1 e2    => expr_ML e1 /\ expr_ML e2
    | AllocTape e    => expr_ML e
    | Rand e1 e2     => expr_ML e1 /\ expr_ML e2
    | AllocUTape     => True
    | URand e        => expr_ML e
    | Tick e         => expr_ML e
    end
  with
    val_ML (v : val_S) : Prop :=
      match v with
      | LitV b       => base_lit_ML b
      | RecV f x e   => expr_ML e
      | PairV v1 v2  => val_ML v1 /\ val_ML v2
      | InjLV v      => val_ML v
      | InjRV v      => val_ML v
      end.

  (* Cylinders: Generators for the sigma algebra *)
  Definition base_lit_cyl : set (set base_lit_T) := image base_lit_ML base_lit_ST.
  Definition expr_cyl     : set (set expr_T)     := image expr_ML     expr_ST.
  Definition val_cyl      : set (set val_T)      := image val_ML      val_ST.

  (* Generate sigma algebras from the cylinders *)

  HB.instance Definition _ := gen_eqMixin base_lit_T.
  HB.instance Definition _ := gen_choiceMixin base_lit_T.
  HB.instance Definition _ := isPointed.Build base_lit_T LitUnit.

  HB.instance Definition _ := gen_eqMixin val_T.
  HB.instance Definition _ := gen_choiceMixin val_T.
  HB.instance Definition _ := isPointed.Build val_T (LitV LitUnit).

  HB.instance Definition _ := gen_eqMixin expr_T.
  HB.instance Definition _ := gen_choiceMixin expr_T.
  HB.instance Definition _ := isPointed.Build expr_T (Val (LitV LitUnit)).

  (* FIXME: Remove! *)
  Local Lemma base_lit_meas_obligation :
    ∀ A : set base_lit_T, <<s base_lit_cyl>> A → <<s base_lit_cyl >> (~` A).
  Proof. eapply sigma_algebraC. Qed.
  Local Lemma val_meas_obligation :
    ∀ A : set val_T, <<s val_cyl>> A → <<s val_cyl >> (~` A).
  Proof. eapply sigma_algebraC. Qed.
  Local Lemma expr_meas_obligation :
    ∀ A : set expr_T, <<s expr_cyl>> A → <<s expr_cyl >> (~` A).
  Proof. eapply sigma_algebraC. Qed.

  HB.instance Definition _ := @isMeasurable.Build
    (sigma_display base_lit_cyl)
    base_lit_T
    <<s base_lit_cyl>>
    (@sigma_algebra0 _ setT base_lit_cyl)
    base_lit_meas_obligation
    (@sigma_algebra_bigcup _ setT base_lit_cyl).

  HB.instance Definition _ := @isMeasurable.Build
    (sigma_display val_cyl)
    val_T
    <<s val_cyl>>
    (@sigma_algebra0 _ setT val_cyl)
    val_meas_obligation
    (@sigma_algebra_bigcup _ setT val_cyl).

  HB.instance Definition _ := @isMeasurable.Build
    (sigma_display expr_cyl)
    expr_T
    <<s expr_cyl>>
    (@sigma_algebra0 _ setT expr_cyl)
    expr_meas_obligation
    (@sigma_algebra_bigcup _ setT expr_cyl).

End expr_algebra.


(** User-facing measurableTypes for base_lit, expr, and val *)
Definition base_lit : measurableType base_lit_cyl.-sigma := base_lit_T.
Definition expr : measurableType expr_cyl.-sigma := expr_T.
Definition val : measurableType val_cyl.-sigma := val_T.

(** Constructors for expressions with the fixed and measurable base types. *)
Definition LitIntC  v       : base_lit_T := LitInt v.
Definition LitBoolC v       : base_lit_T := LitBool v.
Definition LitUnitC         : base_lit_T := LitUnit.
Definition LitLocC  v       : base_lit_T := LitLoc v.
Definition LitLblC  v       : base_lit_T := LitLbl v.
Definition LitRealC v       : base_lit_T := LitReal v.

Definition ValC v           : expr_T     := Val v.
Definition VarC x           : expr_T     := Var x.
Definition RecC f x e       : expr_T     := Rec f x e.
Definition AppC e1 e2       : expr_T     := App e1 e2.
Definition UnOpC op e       : expr_T     := UnOp op e.
Definition BinOpC op e1 e2  : expr_T     := BinOp op e1 e2.
Definition IfC e0 e1 e2     : expr_T     := If e0 e1 e2.
Definition PairC e1 e2      : expr_T     := Pair e1 e2.
Definition FstC e1          : expr_T     := Fst e1.
Definition SndC e1          : expr_T     := Snd e1.
Definition InjLC e1         : expr_T     := InjL e1.
Definition InjRC e1         : expr_T     := InjR e1.
Definition CaseC e0 e1 e2   : expr_T     := Case e0 e1 e2.
Definition AllocNC e1 e2    : expr_T     := AllocN e1 e2.
Definition LoadC e          : expr_T     := Load e.
Definition StoreC e1 e2     : expr_T     := Store e1 e2.
Definition AllocTapeC e     : expr_T     := AllocTape e.
Definition RandC e1 e2      : expr_T     := Rand e1 e2.
Definition AllocUTapeC      : expr_T     := AllocUTape.
Definition URandC e         : expr_T     := URand e.
Definition TickC e          : expr_T     := Tick e.

Definition LitVC b          : val_T      := LitV b.
Definition RecVC f x e      : val_T      := RecV f x e.
Definition PairVC v1 v2     : val_T      := PairV v1 v2.
Definition InjLVC v         : val_T      := InjLV v.
Definition InjRVC v         : val_T      := InjRV v.
