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

(* Instances for binder *)
HB.instance Definition _ := gen_eqMixin binder.
HB.instance Definition _ := gen_choiceMixin binder.
HB.instance Definition _ := isPointed.Build binder inhabitant.

(* Instances for loc *)
HB.instance Definition _ := gen_eqMixin loc.
HB.instance Definition _ := gen_choiceMixin loc.
HB.instance Definition _ := isPointed.Build loc inhabitant.


Section subspaces.
  Local Open Scope classical_set_scope.

  (** Mathcomp needs measurable spaces to be pointed
      This means that we could only construct subset spaces for nonempty subsets
      And this seems to confuse HB.

      For now, it's easier to define is_sub_measurable as an unbundled type not
      in the hierarchy, and re-prove the results we need about it. Many of them
      can be copy-pasted.

      The reason we want subspace measurability is to define the measurability of
      projection functions and constructors. This allows us to prove that head_step
      is measurable (in the HB sense). If we need these functions to be HB measurable
      elsewhere, we may need to figure out how to get proper subset spaces in
      the hierarchy.
   *)


  (* A set S is measurable in the space T1|_E *)
  Definition sub_measurable {d1} {T1 : measurableType d1} (E S : set T1) : Prop :=
    [set (E `&` m) | m in (d1.-measurable : set (set T1))] S.

  Lemma sub_measurable0 {d1} {T1 : measurableType d1} (E : set T1) : sub_measurable E set0.
  Proof. Admitted.

  Lemma sub_measurableC {d1} {T1 : measurableType d1} (E S : set T1) :
    sub_measurable E S -> sub_measurable E (E `\` S).
  Proof. Admitted.

  Lemma bigcup_sub_measurableC {d1} {T : measurableType d1} (E: set T) (F : sequences.sequence (set T)) (P : set nat) :
    (∀ k : nat, P k → sub_measurable E (F k)) → sub_measurable E (\bigcup_(i in P) F i).
  Proof. Admitted.

  (*
  Definition sub {T : Type} (E : set T) : Type := { x : T & E x }.

  Definition to_ambient {T: Type} (E : set T) (X : set (sub E)) : set T := [set (projT1 x) | x in X].

  Definition is_sub_measurable_ambient {d1} {T1 : measurableType d1} (E : set T1) (S : set (sub E)) : Prop :=
    is_sub_measurable E (to_ambient E S).

  (* f is a measurable function from the real subset measure space to T2. Unbundled because it confuses the hierarchy *)
  Definition is_sub_measurable_out {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2} (E : set T1) (f : (sub E) -> T2) : Prop :=
    forall S : set T2, d2.-measurable S -> is_sub_measurable_ambient E (preimage f S). *)



  (* f and g agree on E
  Definition sub_fn_restricts (T1 T2 : Type) (E : set T1) (f : (sub E) -> T2) (g : T1 -> T2) : Prop :=
    forall x : T1, forall H : E x, f (existT x H) = g x.
  *)

  (* TODO: If a set is sub_measurable, and a function out of it is a sub-measurable function, the restriction to the set is mathcomp-measurable *)
  Lemma mathcomp_restriction_is_measurable {d1 d2} {T1 : measurableType d1} {T2 : measurableType d2}
    (E : set T1) (HE : d1.-measurable E) (f : T1 -> T2) :
    @measurable_fun _ _ T1 T2 E f ->
    @measurable_fun _ _ T1 T2 setT (f \_ E).
  Proof.
    intro H.
    unfold measurable_fun.
    intros ? S SMeas.
    rewrite setTI.
    unfold restrict.
    unfold preimage.
    unfold measurable_fun in H.
    have H' := H HE S SMeas; clear H.
    destruct (ExcludedMiddle (S point)).
    - (* point is in S *)
      suffices X : (~` E) `|` (E `&` f @^-1` S) = [set t | S (if t \in E then f t else point)].
      { have H'' := measurableU _ _ (measurableC HE) H'.
        rewrite X in H''.
        by apply H''. }
      apply functional_extensionality.
      intro t.
      simpl.
      apply propext.
      split.
      + intros [ Ht | [Ht Hs] ].
        * by rewrite (memNset Ht).
        * by rewrite (mem_set Ht).
      + intros HS.
        destruct (ExcludedMiddle (E t)).
        * right.
          rewrite (mem_set H1) in HS.
          split; done.
        * by left.
    - (* point is not in S, preimage is .... *)
      suffices X : (E `&` f @^-1` S) = [set t | S (if t \in E then f t else point)].
      { by rewrite X in H'; apply H'. }
      apply functional_extensionality.
      intro t.
      simpl.
      apply propext.
      split.
      + intros [Ht HS].
        by rewrite (mem_set Ht).
      + intros HS.
        destruct (ExcludedMiddle (E t)).
        * rewrite (mem_set H1) in HS.
          split; done.
        * exfalso.
          apply H.
          by rewrite (memNset H1) in HS.
  Qed.

End subspaces.









Module meas_lang.

(* Type of base_lit, parameterized by leaf types *)
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
  | Tick (e : expr_pre )
with val_pre {TZ TB TL TR : Type} :=
  | LitV (l : @base_lit_pre TZ TB TL TR)
  | RecV (f x : <<discr binder>>) (e : expr_pre)
  | PairV (v1 v2 : val_pre)
  | InjLV (v : val_pre)
  | InjRV (v : val_pre).


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





(* Instances for un_op *)
HB.instance Definition _ := gen_eqMixin un_op.
HB.instance Definition _ := gen_choiceMixin un_op.
HB.instance Definition _ := isPointed.Build un_op NegOp.

(* Instances for bin_op *)
HB.instance Definition _ := gen_eqMixin bin_op.
HB.instance Definition _ := gen_choiceMixin bin_op.
HB.instance Definition _ := isPointed.Build bin_op PlusOp.



Section expr_algebra.
  (** Defines the sigma algebra over expressions *)
  Local Open Scope classical_set_scope.

  (* FIXME: move *)
  Definition image3 {TA TB TC rT} (A : set TA) (B : set TB) (C : set TC) (f : TA -> TB -> TC -> rT) :=
    [set z | exists2 x, A x & exists2 y, B y & exists2 w, C w & f x y w = z].
  Arguments image3 _ _ _ _ _ _ _ _ /.

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


  (* User-facing types *)
  Definition base_lit : measurableType base_lit_cyl.-sigma := base_lit_T.
  Definition expr : measurableType expr_cyl.-sigma := expr_T.
  Definition val : measurableType val_cyl.-sigma := val_T.


  (** Constructors for expressions with the fixed and measurable base types. *)
  Definition LitIntC  v : base_lit_T := LitInt v.
  Definition LitBoolC v : base_lit_T := LitBool v.
  Definition LitUnitC   : base_lit_T := LitUnit.
  Definition LitLocC  v : base_lit_T := LitLoc v.
  Definition LitLblC  v : base_lit_T := LitLbl v.
  Definition LitRealC v : base_lit_T := LitReal v.

  Definition ValC v           : expr_T := Val v.
  Definition VarC x           : expr_T := Var x.
  Definition RecC f x e       : expr_T := Rec f x e.
  Definition AppC e1 e2       : expr_T := App e1 e2.
  Definition UnOpC op e       : expr_T := UnOp op e.
  Definition BinOpC op e1 e2  : expr_T := BinOp op e1 e2.
  Definition IfC e0 e1 e2     : expr_T := If e0 e1 e2.
  Definition PairC e1 e2      : expr_T := Pair e1 e2.
  Definition FstC e1          : expr_T := Fst e1.
  Definition SndC e1          : expr_T := Snd e1.
  Definition InjLC e1         : expr_T := InjL e1.
  Definition InjRC e1         : expr_T := InjR e1.
  Definition CaseC e0 e1 e2   : expr_T := Case e0 e1 e2.
  Definition AllocNC e1 e2    : expr_T := AllocN e1 e2.
  Definition LoadC e          : expr_T := Load e.
  Definition StoreC e1 e2     : expr_T := Store e1 e2.
  Definition AllocTapeC e     : expr_T := AllocTape e.
  Definition RandC e1 e2      : expr_T := Rand e1 e2.
  Definition AllocUTapeC      : expr_T := AllocUTape.
  Definition URandC e         : expr_T := URand e.
  Definition TickC e          : expr_T := Tick e.

  Definition LitVC b      : val_T  := LitV b.
  Definition RecVC f x e  : val_T  := RecV f x e.
  Definition PairVC v1 v2 : val_T  := PairV v1 v2.
  Definition InjLVC v     : val_T  := InjLV v.
  Definition InjRVC v     : val_T  := InjRV v.



  (** Uncurried form: These ones can be shown to be measurable directly *)
  Definition LitIntU  (v : TZ) := LitIntC v.
  Definition LitBoolU (v : TB) := LitBoolC v.
  Definition LitUnitU          := LitUnitC.
  Definition LitLocU  (v : TL) := LitLocC v.
  Definition LitLblU  (v : TL) := LitLblC v.
  Definition LitRealU (v : TR) := LitRealC v.

  Definition ValU (v : val)                                         := ValC v.
  Definition VarU (v : <<discr binder>>)                            := VarC v.
  Definition RecU (v : <<discr binder>> * <<discr binder>> * expr)  := RecC v.1.1 v.1.2 v.2.
  Definition AppU (v : expr * expr)                                 := AppC v.1 v.2.
  Definition UnOpU (v : <<discr un_op>> * expr)                     := UnOpC v.1 v.2.
  Definition BinOpU (v : <<discr bin_op>> * expr * expr)            := BinOpC v.1.1 v.1.2 v.2.
  Definition IfU (v : expr * expr * expr)                           := IfC v.1.1 v.1.2 v.2.
  Definition PairU (v : expr * expr)                                := PairC v.1 v.2.
  Definition FstU (v : expr)                                        := FstC v.
  Definition SndU (v : expr)                                        := SndC v.
  Definition InjLU (v : expr)                                       := InjLC v.
  Definition InjRU (v : expr)                                       := InjRC v.
  Definition CaseU (v : expr * expr * expr)                         := CaseC v.1.1 v.1.2 v.2.
  Definition AllocNU (v : expr * expr)                              := AllocNC v.1 v.2.
  Definition LoadU (v : expr)                                       := LoadC v.
  Definition StoreU (v : expr * expr)                               := StoreC v.1 v.2.
  Definition AllocTapeU (v : expr)                                  := AllocTapeC v.
  Definition RandU (v : expr * expr)                                := RandC v.1 v.2.
  Definition AllocUTapeU                                            := AllocUTapeC.
  Definition UrandU (v : expr)                                      := URandC v.
  Definition TickU (v : expr)                                       := TickC v.

  Definition LitVU (v : base_lit)                                   := LitVC v.
  Definition RecVU (v : <<discr binder>> * <<discr binder>> * expr) := RecC v.1.1 v.1.2 v.2.
  Definition PairVU (v : val * val)                                 := PairVC v.1 v.2.
  Definition InjLVU (v : val)                                       := InjLVC v.
  Definition InjRVU (v : val)                                       := InjRVC v.

  (** FIXME: Use measurable_uncurry to get measurability of the uncurried versions? *)

End expr_algebra.



Section expr_measurability.
  Local Open Scope classical_set_scope.

  Local Lemma MZ {d} {T : measurableType d} (S : set T)  : S = set0 -> measurable S.
  Proof. by move=>->; apply measurable0. Qed.

  Local Lemma MT {d} {T : measurableType d} (S : set T)  : S = setT -> measurable S.
  Proof. by move=>->; eapply @measurableT. Qed.

  Local Lemma Prod2Decomp {T1 T2 T : Type} (P1 : set T1) (P2 : set T2) (FU : T1 * T2 -> T) :
    (∀ {a b c d}, curry FU a b = curry FU c d -> b = d) ->
    [set t | (exists2 x : T1, P1 x & exists2 y : T2, P2 y & (curry FU) x y = FU t) ] =
    [set t | (exists2 x : T1, True    & exists2 y : T2, P2 y & (curry FU) x y = FU t) ] `&`
    [set t | (exists2 x : T1, P1 x & exists2 y : T2, True    & (curry FU) x y = FU t) ].
  Proof.
    move=> R.
    apply/seteqP; split=> x/=.
    - move=> [a ? [b ? <-]].
      split; (exists a; [done|]; exists b; done).
    - move=> [[a ?] [b ?]] <- [c ? [d ?]] H.
      exists c; [done|]; exists b; [done|].
      rewrite <- H.
      f_equal.
      symmetry.
      apply (R _ _ _ _ H).
  Qed.

  Local Lemma Prod3Decomp {T1 T2 T3 T : Type} (P1 : set T1) (P2 : set T2) (P3 : set T3) (FU : T1 * T2 * T3 -> T) :
    [set t | (exists2 x : T1, P1 x & exists2 y : T2, P2 y & exists2 z : T3, P3 z & (curry3 FU) x y z = FU t) ] =
    [set t | (exists2 x : T1, P1 x & exists2 y : T2, True    & exists2 z : T3, True    & (curry3 FU) x y z = FU t) ] `&`
    [set t | (exists2 x : T1, True    & exists2 y : T2, P2 y & exists2 z : T3, True    & (curry3 FU) x y z = FU t) ] `&`
    [set t | (exists2 x : T1, True    & exists2 y : T2, True    & exists2 z : T3, P3 z & (curry3 FU) x y z = FU t) ].
  Proof. Admitted.



  (** Measurability of the projection and constructor functions *)

  (** Base_lit constructors, uncurried *)
  Lemma LitIntU_measurable : measurable_fun setT LitIntU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    1: {
         suffices R : [set t | (exists2 x : <<discr Z >>, n x & LitInt x = LitIntU t)] = n.
         { simpl in HD; by rewrite R. }
         apply/seteqP; split=> x/=; [by move=> [v ?] [<-] |].
         move=> ?.
         by exists x.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma LitBoolU_measurable : measurable_fun setT LitBoolU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    2: {
         suffices R : [set t | (exists2 x : <<discr _ >>, b x & LitBool x = LitBoolU t)] = b.
         { simpl in HD; by rewrite R. }
         apply/seteqP; split=> x/=; [by move=> [v ?] [<-] |].
         move=> ?.
         by exists x.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  (*
  Lemma LitUnitU_measurable : measurable_fun setT LitUnitU.
  Proof. Admitted.
  *)

  Lemma LitLocU_measurable : measurable_fun setT LitLocU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    4: {
         suffices R : [set t | (exists2 x : <<discr _ >>, l x & LitLoc x = LitLocU t)] = l.
         { simpl in HD; by rewrite R. }
         apply/seteqP; split=> x/=; [by move=> [v ?] [<-] |].
         move=> ?.
         by exists x.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma LitLblU_measurable : measurable_fun setT LitLblU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    5: {
         suffices R : [set t | (exists2 x : <<discr _ >>, l x & LitLbl x = LitLblU t)] = l.
         { simpl in HD; by rewrite R. }
         apply/seteqP; split=> x/=; [by move=> [v ?] [<-] |].
         move=> ?.
         by exists x.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma LitRealU_measurable : measurable_fun setT LitRealU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    6: {
         suffices R : [set t | (exists2 x : R, r x & LitReal x = LitRealU t)] = r.
         { simpl in HD; by rewrite R. }
         apply/seteqP; split=> x/=; [by move=> [v ?] [<-] |].
         move=> ?.
         by exists x.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.


  (** Expr Constructors: Each *C function is (.. * ... * ...) / expr -measurable *)
  Lemma ValU_measurable : measurable_fun setT ValU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    1: {
         apply sub_sigma_algebra.
         exists v; [done|].
         apply/seteqP; split=> x/=; [move=> ?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma VarU_measurable : measurable_fun setT VarU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    2: { by rewrite /measurable/=/discr_meas/=. }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma RecU_measurable : measurable_fun setT RecU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    rewrite /preimage/=.
    destruct D.
    3: {
      simpl.
      suffices -> :
        [set t | (exists2 x0 : expr_T, expr_ST D x0 & Rec f x x0 = RecU t)] =
        [set t | (exists2 x0 : expr_T, expr_ST D x0 & t.2 = x0)] `&`
        ( [set t | t.1.1 = f ] `&`
          [set t | t.1.2 = x ]).
      { apply measurableI.
        - apply sub_sigma_algebra.
          rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          right.
          simpl in HD.
          exists (expr_ST D).
          { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D. }
          rewrite setTI.
          apply/predeqP; simpl; split.
          + by move=>?; exists x0.2.
          + by move=>[??]->.
        - apply measurableI.
          + apply sub_sigma_algebra.
            rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
            left.
            simpl in HD.
            exists [set t | t.1 = f].
            { apply sub_sigma_algebra.
              simpl.
              left.
              exists [set f]. { by rewrite /measurable/=/discr_meas/=. }
              by rewrite setTI /=. }
            by rewrite setTI /=.
          + apply sub_sigma_algebra.
            rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
            left.
            simpl in HD.
            exists [set t | t.2 = x].
            { apply sub_sigma_algebra.
              simpl.
              right.
              exists [set x]. { by rewrite /measurable/=/discr_meas/=. }
              by rewrite setTI /=. }
            by rewrite setTI /=.
      }
      apply/seteqP; split=> y/=.
      - move=> [a ? [<- <- <-]].
        split; [|by intuition].
        by exists a.
      - move=> [[e ?] He [<- <-]].
        exists e; [done|].
        by destruct y; rewrite <-He; simpl; intuition.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.


  Lemma AppU_measurable : measurable_fun setT AppU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    4: {
         simpl in HD.
         destruct HD as [HD0 HD1].
         rewrite Prod2Decomp.
         { apply measurableI.
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             right.
             exists (expr_ST D2).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??][?<-]].
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             left.
             exists (expr_ST D1).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??[<- ?]]].
        }
        by move=>????[??]//.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma UnOpU_measurable : measurable_fun setT UnOpU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    5: {
      simpl.
      suffices -> :
        [set t | (exists2 x : expr_T, expr_ST D x & UnOp op x = UnOpU t)] =
        [set t | exists x0 : expr_T, exists o, (expr_ST D x0 /\ UnOp o x0 = UnOpU t)] `&`
        [set t | t.1 = op ].
      { apply measurableI.
        + rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          apply sub_sigma_algebra.
          simpl in HD.
          simpl.
          right.
          exists (expr_ST D).
          { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D. }
          rewrite setTI /=.
          apply/seteqP; split=> x/=.
          + move=>?. exists x.2. exists x.1. split; [done|]. by intuition.
          + move=> [? [? [? H]]].
            inversion H.
            by rewrite <- H2.
        + rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          apply sub_sigma_algebra.
          simpl.
          left.
          exists [set op]. { by rewrite /measurable/=/discr_meas/=. }
          by rewrite setTI /=. }
      apply/seteqP; split=> y/=.
      - move=> [a ? [-> Ha]]; split; [|done].
        exists a. exists y.1. split; [done|].
        by rewrite Ha //=.
      - move=> [[a [? [? Ha]]] <-].
        simpl in HD.
        exists a; [done|].
        destruct y; simpl.
        rewrite /UnOpU/UnOpC/=.
        f_equal.
        inversion Ha. by intuition.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma BinOpU_measurable : measurable_fun setT BinOpU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    6: {
      suffices -> :
         [set t | (exists2 x : expr_T, expr_ST D1 x & exists2 y : expr_T, expr_ST D2 y & BinOp op x y = BinOpU t)] =
        ([set t | (exists2 x : expr_T, expr_ST D1 x & exists2 y : expr_T, True            & exists op, BinOp op x y = BinOpU t)] `&`
         [set t | (exists2 x : expr_T, True            & exists2 y : expr_T, expr_ST D2 y & exists op, BinOp op x y = BinOpU t)]) `&`
        [set t | t.1.1 = op ].
      { simpl in HD.
        destruct HD as [HD0 HD1].
        apply measurableI.
        apply measurableI.
        - apply sub_sigma_algebra; rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          left.
          exists (setT `*` (expr_ST D1)).
          { apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=.
            right.
            exists (expr_ST D1). { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1.  }
            rewrite setTI.
            rewrite /setX/=.
            apply/seteqP; split=> x/=; by intuition.
          }
          rewrite setTI.
          apply/seteqP; split=> x/=.
          + move=> [? ?].
            exists x.1.2; [done|].
            exists x.2; [done|].
            exists x.1.1.
            destruct x as [[??]?].
            by intuition.
          + move=> [??][??][?][?<-?].
            by intuition.
        - apply sub_sigma_algebra; rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          right.
          exists (expr_ST D2).
          { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
          rewrite setTI.
          apply/seteqP; split=> y/=.
          + move=> H.
            exists y.1.2; [done|].
            exists y.2; [done|].
            exists y.1.1.
            destruct y as [yy yyy]; destruct yy; simpl.
            by rewrite /BinOpU/=.
          + by move=> [? _ [? ?]] [? [? ?]] <-.
        - apply sub_sigma_algebra; rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          left.
          exists ([set op] `*` setT).
          { apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=.
            left.
            exists [set op]. { by rewrite /discr_meas/measurable/=/expr_cyl/=. }
            rewrite setTI.
            rewrite /setX/=.
            apply/seteqP; split=> x/=; by intuition.
          }
          rewrite setTI.
          apply/seteqP; split=> x/=.
          + move=> [? ?]; done.
          + by intuition.
      }
      apply/seteqP; split=> y/=.
      - move=> [? W][? Z][A B C].
        rewrite B in W.
        rewrite C in Z.
        split; [split|].
        + exists y.1.2; [done|]; exists y.2; [done|]; exists y.1.1; done.
        + exists y.1.2; [done|]; exists y.2; [done|]; exists y.1.1; done.
        + by intuition.
      - move=> [[[? p][??]]].
        move=> [?[? H1 ?]].
        rewrite H1 in p.
        move=> [??][? p2][?[?? H2]]Hop.
        rewrite H2 in p2.
        exists y.1.2; [done|].
        exists y.2; [done|].
        destruct y as [[??]?].
        rewrite /BinOpU/BinOpC/=.
        simpl in Hop.
        by rewrite Hop.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma IfU_measurable : measurable_fun setT IfU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    7: {
      simpl in HD.
      destruct HD as [HD0 [HD1 HD2]].
      rewrite Prod3Decomp.
      apply measurableI.
      apply measurableI.
      - apply sub_sigma_algebra.
        rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        left.
        exists (expr_ST D1 `*` setT).
        { apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=.
          left.
          exists (expr_ST D1). { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1.  }
          rewrite setTI.
          rewrite /setX/=.
          apply/seteqP; split=> x/=; by intuition.
        }
        rewrite setTI.
        apply/seteqP; split=> x/=.
        + move=> [? _].
          exists x.1.1; [done|].
          exists x.1.2; [done|].
          exists x.2; [done|].
          destruct x as [[??]?].
          by intuition.
        + move=> [??][??][??][<-]??.
          by intuition.
      - apply sub_sigma_algebra.
        rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        left.
        exists (setT `*` expr_ST D2).
        { apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=.
          right.
          exists (expr_ST D2). { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
          rewrite setTI.
          rewrite /setX/=.
          apply/seteqP; split=> x/=; by intuition.
        }
        rewrite setTI.
        apply/seteqP; split=> x/=.
        + move=> [? ?].
          exists x.1.1; [done|].
          exists x.1.2; [done|].
          exists x.2; [done|].
          destruct x as [[??]?].
          by intuition.
        + move=> [??][??][??][? <- ?].
          by intuition.
      - apply sub_sigma_algebra.
        rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        right.
        exists (expr_ST D3).  { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D3. }
        rewrite setTI.
        apply/seteqP; split=> x/=.
        + move=>?.
          exists x.1.1; [done|].
          exists x.1.2; [done|].
          exists x.2; [done|].
          destruct x as [[??]?].
          by intuition.
        + move=> [??][??][??][??<-].
          by intuition.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma PairU_measurable : measurable_fun setT PairU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    8: {
         simpl in HD.
         destruct HD as [HD0 HD1].
         rewrite Prod2Decomp.
         { apply measurableI.
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             right.
             exists (expr_ST D2).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??][?<-]].
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             left.
             exists (expr_ST D1).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??[<- ?]]].
        }
        by move=>????[??]//.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma FstU_measurable : measurable_fun setT FstU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    9: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         simpl in HD.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma SndU_measurable : measurable_fun setT SndU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    10: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         simpl in HD.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma InjLU_measurable : measurable_fun setT InjLU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    11: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         simpl in HD.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma InjRU_measurable : measurable_fun setT InjRU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    12: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         simpl in HD.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma CaseU_measurable : measurable_fun setT CaseU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    13: {
      simpl in HD.
      destruct HD as [HD0 [HD1 HD2]].
      rewrite Prod3Decomp.
      apply measurableI.
      apply measurableI.
      - apply sub_sigma_algebra.
        rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        left.
        exists (expr_ST D1 `*` setT).
        { apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=.
          left.
          exists (expr_ST D1). { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1.  }
          rewrite setTI.
          rewrite /setX/=.
          apply/seteqP; split=> x/=; by intuition.
        }
        rewrite setTI.
        apply/seteqP; split=> x/=.
        + move=> [? _].
          exists x.1.1; [done|].
          exists x.1.2; [done|].
          exists x.2; [done|].
          destruct x as [[??]?].
          by intuition.
        + move=> [??][??][??][<-]??.
          by intuition.
      - apply sub_sigma_algebra.
        rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        left.
        exists (setT `*` expr_ST D2).
        { apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=.
          right.
          exists (expr_ST D2). { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
          rewrite setTI.
          rewrite /setX/=.
          apply/seteqP; split=> x/=; by intuition.
        }
        rewrite setTI.
        apply/seteqP; split=> x/=.
        + move=> [? ?].
          exists x.1.1; [done|].
          exists x.1.2; [done|].
          exists x.2; [done|].
          destruct x as [[??]?].
          by intuition.
        + move=> [??][??][??][? <- ?].
          by intuition.
      - apply sub_sigma_algebra.
        rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
        right.
        exists (expr_ST D3).  { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D3. }
        rewrite setTI.
        apply/seteqP; split=> x/=.
        + move=>?.
          exists x.1.1; [done|].
          exists x.1.2; [done|].
          exists x.2; [done|].
          destruct x as [[??]?].
          by intuition.
        + move=> [??][??][??][??<-].
          by intuition.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma AllocNU_measurable : measurable_fun setT AllocNU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    14: {
         simpl in HD.
         destruct HD as [HD0 HD1].
         rewrite Prod2Decomp.
         { apply measurableI.
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             right.
             exists (expr_ST D2).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??][?<-]].
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             left.
             exists (expr_ST D1).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??[<- ?]]].
        }
        by move=>????[??]//.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma LoadU_measurable : measurable_fun setT LoadU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    15: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         simpl in HD.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma StoreU_measurable : measurable_fun setT StoreU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    16: {
         simpl in HD.
         destruct HD as [HD0 HD1].
         rewrite Prod2Decomp.
         { apply measurableI.
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             right.
             exists (expr_ST D2).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??][?<-]].
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             left.
             exists (expr_ST D1).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??[<- ?]]].
        }
        by move=>????[??]//.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma AllocTapeU_measurable : measurable_fun setT AllocTapeU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    17: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma RandU_measurable : measurable_fun setT RandU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    18: {
         simpl in HD.
         destruct HD as [HD0 HD1].
         rewrite Prod2Decomp.
         { apply measurableI.
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             right.
             exists (expr_ST D2).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??][?<-]].
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             left.
             exists (expr_ST D1).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??[<- ?]]].
        }
        by move=>????[??]//.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  (*
  Lemma AllocUTapeU_measurable : measurable_fun setT AllocUTapeU.
  *)

  Lemma UrandU_measurable : measurable_fun setT UrandU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    20: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma TickU_measurable : measurable_fun setT TickU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    21: {
         apply sub_sigma_algebra.
         rewrite /expr_cyl/=.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  (** Val constructors *)

  Lemma LitVU_measurable : measurable_fun setT LitVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    1: {
         apply sub_sigma_algebra.
         rewrite /base_lit_cyl/=.
         exists l; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma RecVU_measurable : measurable_fun setT RecVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    3: {
      simpl.
      suffices -> :
        [set t | (exists2 x0 : expr_T, expr_ST D x0 & Rec f x x0 = RecVU t)] =
        [set t | (exists2 x0 : expr_T, expr_ST D x0 & t.2 = x0)] `&`
        ( [set t | t.1.1 = f ] `&`
          [set t | t.1.2 = x ]).
      { apply measurableI.
        - apply sub_sigma_algebra.
          rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
          right.
          simpl in HD.
          exists (expr_ST D).
          { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D. }
          rewrite setTI.
          apply/predeqP; simpl; split.
          + by move=>?; exists x0.2.
          + by move=>[??]->.
        - apply measurableI.
          + apply sub_sigma_algebra.
            rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
            left.
            simpl in HD.
            exists [set t | t.1 = f].
            { apply sub_sigma_algebra.
              simpl.
              left.
              exists [set f]. { by rewrite /measurable/=/discr_meas/=. }
              by rewrite setTI /=. }
            by rewrite setTI /=.
          + apply sub_sigma_algebra.
            rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
            left.
            simpl in HD.
            exists [set t | t.2 = x].
            { apply sub_sigma_algebra.
              simpl.
              right.
              exists [set x]. { by rewrite /measurable/=/discr_meas/=. }
              by rewrite setTI /=. }
            by rewrite setTI /=.
      }
      apply/seteqP; split=> y/=.
      - move=> [a ? [b ? <-]].
        split.
        + exists a; done.
        + by intuition.
      - move=> [[? ? ] [H [<- <-]]].
        exists y.2.
        + by rewrite H.
        + destruct y as [[??]?]; by rewrite /=.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma PairVU_measurable : measurable_fun setT PairVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    3: {
         simpl in HD.
         destruct HD as [HD0 HD1].
         rewrite Prod2Decomp.
         { apply measurableI.
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             right.
             exists (val_ST D2).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D2. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??][?<-]].
           - apply sub_sigma_algebra.
             rewrite /measurable/=/preimage_classes/preimage_class/preimage/=.
             left.
             exists (val_ST D1).
             { by apply sub_sigma_algebra; rewrite /measurable/=/expr_cyl/=; exists D1. }
             rewrite setTI.
             apply/seteqP; split=> x/=.
             + by move=>?; exists x.1; [done|]; exists x.2; done.
             + by move=> [??[??[<- ?]]].
        }
        by move=>????[??]//.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma InjLVU_measurable : measurable_fun setT InjLVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    4: {
         apply sub_sigma_algebra.
         rewrite /base_lit_cyl/=.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.

  Lemma InjRVU_measurable : measurable_fun setT InjRVU.
  Proof.
    eapply measurability; [by eauto|].
    rewrite /preimage_class/subset.
    move=> S /= [X [D HD <-] <-]; rewrite setTI.
    destruct D; rewrite /preimage/=.
    5: {
         apply sub_sigma_algebra.
         rewrite /base_lit_cyl/=.
         exists D; [done|].
         apply/seteqP; split=> x/=; [move=>?; by exists x|].
         move=> [? ? H].
         inversion H as [H1].
         by rewrite <- H1.
    }
    all: apply MZ; apply /predeqP =>y /=; split; [| by move=>?].
    all: try by move=> ?//.
    all: try by move=> [?]//.
    all: try by move=> [??[???]]//.
    all: try by move=> [??[??[???]]]//.
  Qed.


  (** Projections: Each projection function is a measurable_fun from the respective cover set
      in expr to a product space. *)

  Definition base_lit_shape : Type := @base_lit_pre () () () ().
  Definition val_shape      : Type := @val_pre () () () ().
  Definition expr_shape     : Type := @expr_pre () () () ().

  (*
  FIXME: Old version-- delete me if not used

  Inductive shape_base_lit : base_lit -> base_lit_shape -> Prop :=
  | sh_LitInt n  : shape_base_lit (LitInt n)  (LitInt ())
  | sh_LitBool b : shape_base_lit (LitBool b) (LitBool ())
  | sh_LitUnit   : shape_base_lit LitUnit     LitUnit
  | sh_LitLoc l  : shape_base_lit (LitLoc l)  (LitLoc ())
  | sh_LitLbl l  : shape_base_lit (LitLbl l)  (LitLbl ())
  | sh_LitReal r : shape_base_lit (LitReal r) (LitReal ()).

  Inductive shape_expr : expr -> expr_shape -> Prop :=
  | sh_Val v s : shape_val v s -> shape_expr (Val v) (Val s)
  | sh_Var x : shape_expr (Var x) (Var x)
  | sh_Rec f x e s : shape_expr e s -> shape_expr (Rec f x e) (Rec f x s)
  | sh_App e1 s1 e2 s2 : shape_expr e1 s1 -> shape_expr e2 s2 -> shape_expr (App e1 e2) (App s1 s2)
  | sh_UnOp op e s : shape_expr e s -> shape_expr (UnOp op e) (UnOp op s)
  | sh_BinOp op e1 s1 e2 s2 : shape_expr e1 s1 -> shape_expr e2 s2 -> shape_expr (BinOp op e1 e2) (BinOp op s1 s2)
  | sh_If e1 s1 e2 s2 e3 s3 : shape_expr e1 s1 -> shape_expr e2 s2 -> shape_expr e3 s3 -> shape_expr (If e1 e2 e3) (If s1 s2 s3)
  | sh_Pair e1 s1 e2 s2 : shape_expr e1 s1 -> shape_expr e2 s2 -> shape_expr (Pair e1 e2) (Pair s1 s2)
  | sh_Fst e1 s1 : shape_expr e1 s1 -> shape_expr (Fst e1) (Fst s1)
  | sh_Snd e1 s1 : shape_expr e1 s1 -> shape_expr (Snd e1) (Snd s1)
  | sh_InjL e1 s1 : shape_expr e1 s1 -> shape_expr (InjL e1) (InjL s1)
  | sh_InjR e1 s1 : shape_expr e1 s1 -> shape_expr (InjR e1) (InjR s1)
  | sh_Case e1 s1 e2 s2 e3 s3 : shape_expr e1 s1 -> shape_expr e2 s2 -> shape_expr e3 s3 -> shape_expr (Case e1 e2 e3) (Case s1 s2 s3)
  | sh_AllocN e1 s1 e2 s2 : shape_expr e1 s1 -> shape_expr e2 s2 -> shape_expr (AllocN e1 e2) (AllocN s1 s2)
  | sh_Load e1 s1 : shape_expr e1 s1 -> shape_expr (Load e1) (Load s1)
  | sh_Store e1 s1 e2 s2 : shape_expr e1 s1 -> shape_expr e2 s2 -> shape_expr (Store e1 e2) (Store s1 s2)
  | sh_AllocTape e1 s1 : shape_expr e1 s1 -> shape_expr (AllocTape e1) (AllocTape s1)
  | sh_Rand e1 s1 e2 s2 : shape_expr e1 s1 -> shape_expr e2 s2 -> shape_expr (Rand e1 e2) (Rand s1 s2)
  | sh_AllocUTape : shape_expr AllocUTape AllocUTape
  | sh_URand e1 s1 : shape_expr e1 s1 -> shape_expr (URand e1) (URand s1)
  | sh_Tick e1 s1 : shape_expr e1 s1 -> shape_expr (Tick e1) (Tick s1)
  with
  shape_val : val -> val_shape -> Prop :=
  | sh_LitV v s : shape_base_lit v s -> shape_val (LitV v) (LitV s)
  | sh_RecV f x e s : shape_expr e s -> shape_val (RecV f x e) (RecV f x s)
  | sh_PairV e1 e2 s1 s2 : shape_val e1 s1 -> shape_val e2 s2 -> shape_val (PairV e1 e2) (PairV s1 s2)
  | sh_InjLV e1 s1 : shape_val e1 s1 -> shape_val (InjLV e1) (InjLV s1).

  Scheme expr_shape_mut_ind := Induction for shape_expr Sort Prop
      with val_shape_mut_ind := Induction for shape_val Sort Prop.
   *)


   (** Get the shape of an expression *)

   Definition shape_base_lit : base_lit -> base_lit_shape :=
    base_lit_pre_F (cst ()) (cst ()) (cst ()) (cst ()) (cst ()).

   Definition shape_val : val -> val_shape :=
    val_pre_F (cst ()) (cst ()) (cst ()) (cst ()) (cst ()).

   Definition shape_expr : expr -> expr_shape :=
    expr_pre_F (cst ()) (cst ()) (cst ()) (cst ()) (cst ()).


   (** Get a generator for all expressions with a given shape *)

   Definition gen_base_lit : base_lit_shape -> base_lit_S :=
    base_lit_pre_F (cst setT) (cst setT) (cst setT) (cst setT) (cst setT).

   Definition gen_val : val_shape -> val_S :=
    val_pre_F (cst setT) (cst setT) (cst setT) (cst setT) (cst setT).

   Definition gen_expr : expr_shape -> expr_S :=
    expr_pre_F (cst setT) (cst setT) (cst setT) (cst setT) (cst setT).


  (** The set of all expressions with a given shape is singly generated *)

  Lemma base_lit_shape_cyl (s : base_lit_shape) : [set e | shape_base_lit e = s] = base_lit_ST (gen_base_lit s).
  Proof.
    apply /predeqP =>b.
    destruct b; simpl.
    all: split; [ by move <-; rewrite //=; eexists _; eauto | ].
    all: move=> H.
    all: destruct s as [x|x| |x|x|x]; simpl in H.
    all: try done.
    all: try by destruct H as [? ?].
    all: by destruct x.
  Qed.

  Lemma expr_shape_cyl (s : expr_shape) : [set e | shape_expr e = s] = expr_ST (gen_expr s).
  Proof. Admitted.

  Lemma val_shape_cyl (s : val_shape) : [set e | shape_val e = s] = val_ST (gen_val s).
  Proof. Admitted.



  (** Decompose the set of expressions into a countable union over expr_shape *)

  Definition expr_shape_enum (n : nat) : expr_shape. Admitted.

  Definition val_shape_enum (n : nat) : val_shape. Admitted.

  Definition base_lit_shape_enum (n : nat) : base_lit_shape. Admitted.

  (* I only need surjectivity to prove that I don't miss any trees, so I'll use a definition
     of surjectivity appropriate for that (not the HB one, it gives us nothing) *)

  Lemma expr_shape_enum_surj (e : expr_shape) : exists n, expr_shape_enum n = e.
  Proof. Admitted.

  Lemma val_shape_enum_surj (e : val_shape) : exists n, val_shape_enum n = e.
  Proof. Admitted.

  Lemma base_lit_shape_enum_surj (e : base_lit_shape) : exists n, base_lit_shape_enum n = e.
  Proof. Admitted.

  Definition base_lit_seq : sequences.sequence (set base_lit) :=
    fun n => shape_base_lit @^-1` [set base_lit_shape_enum n].

  Definition expr_seq : sequences.sequence (set expr) :=
    fun n => shape_expr @^-1` [set expr_shape_enum n].

  Definition val_seq : sequences.sequence (set val) :=
    fun n => shape_val @^-1` [set val_shape_enum n].

  Lemma base_lit_shape_decomp : (\bigcup_n base_lit_seq n) = setT.
  Proof.
    rewrite <- subTset => e He.
    case (base_lit_shape_enum_surj (shape_base_lit e)) as [n Hn].
    exists n; [done|].
    by rewrite /base_lit_seq Hn //=.
  Qed.

  Lemma expr_shape_decomp : (\bigcup_n expr_seq n) = setT.
  Proof.
    rewrite <- subTset => e He.
    case (expr_shape_enum_surj (shape_expr e)) as [n Hn].
    exists n; [done|].
    by rewrite /expr_seq Hn //=.
  Qed.

  Lemma val_shape_decomp : (\bigcup_n val_seq n) = setT.
  Proof.
    rewrite <- subTset => e He.
    case (val_shape_enum_surj (shape_val e)) as [n Hn].
    exists n; [done|].
    by rewrite /val_seq Hn //=.
  Qed.


  (**  A cover of the expr, val, and base_lit type, by constructor. *)
  Definition ecov_val        : set expr     := [set e  | ∃ v,         e = ValC v].
  Definition ecov_var        : set expr     := [set e  | ∃ s,         e = VarC s].
  Definition ecov_rec        : set expr     := [set e  | ∃ f x e,     e = RecC f x e].
  Definition ecov_app        : set expr     := [set e  | ∃ e1 e2,     e = AppC e1 e2].
  Definition ecov_unop       : set expr     := [set e  | ∃ op e,      e = UnOpC op e].
  Definition ecov_binop      : set expr     := [set e  | ∃ op e1 e2,  e = BinOpC op e1 e2].
  Definition ecov_if         : set expr     := [set e  | ∃ e1 e2 e3,  e = IfC e1 e2 e3].
  Definition ecov_pair       : set expr     := [set e  | ∃ e1 e2,     e = PairC e1 e2].
  Definition ecov_fst        : set expr     := [set e  | ∃ e,         e = FstC e].
  Definition ecov_snd        : set expr     := [set e  | ∃ e,         e = SndC e].
  Definition ecov_injl       : set expr     := [set e  | ∃ e,         e = InjLC e].
  Definition ecov_injr       : set expr     := [set e  | ∃ e,         e = InjRC e].
  Definition ecov_alloc      : set expr     := [set e  | ∃ e1 e2,     e = AllocN e1 e2].
  Definition ecov_load       : set expr     := [set e  | ∃ e,         e = LoadC e].
  Definition ecov_store      : set expr     := [set e  | ∃ e1 e2,     e = StoreC e1 e2].
  Definition ecov_alloctape  : set expr     := [set e  | ∃ e,         e = AllocTapeC e].
  Definition ecov_rand       : set expr     := [set e  | ∃ e1 e2,     e = RandC e1 e2].
  Definition ecov_allocutape : set expr     := [set e  |              e = AllocUTapeC].
  Definition ecov_urand      : set expr     := [set e  | ∃ e,         e = URandC e].
  Definition ecov_tick       : set expr     := [set e  | ∃ e,         e = TickC e].

  Definition vcov_lit        : set val      := [set e  | ∃ v,      e = LitVC v].
  Definition vcov_rec        : set val      := [set e  | ∃ f x e0, e = RecVC f x e0].
  Definition vcov_pair       : set val      := [set e  | ∃ v1 v2,  e = PairVC v1 v2].
  Definition vcov_injlv      : set val      := [set e  | ∃ v,      e = InjLVC v].
  Definition vcov_injrv      : set val      := [set e  | ∃ v,      e = InjRVC v].

  Definition bcov_LitInt     : set base_lit := [set e  | ∃ v, e = LitIntC  v].
  Definition bcov_LitBool    : set base_lit := [set e  | ∃ v, e = LitBoolC v].
  Definition bcov_LitUnit    : set base_lit := [set e  |      e = LitUnitC  ].
  Definition bcov_LitLoc     : set base_lit := [set e  | ∃ v, e = LitLoc   v].
  Definition bcov_LitLbl     : set base_lit := [set e  | ∃ v, e = LitLbl   v].
  Definition bcov_LitReal    : set base_lit := [set e  | ∃ v, e = LitReal  v].

  (** Cover set measurability *)
  (* NOTE:
      I think that in principle we could have proven these by first showing a projection
      function is measurable, and then showing that it is the preimage of setT. However,
      for the indirect method we have to use (no restricted SA's) this does not work,
      because (measurable_fun Dom) requires we show Dom is measurable a priori.
   *)
  (* Both will use the decomposition argument. *)
  Lemma bcov_LitInt_meas  : measurable bcov_LitInt.
  Proof.
    apply sub_sigma_algebra.
    rewrite /base_lit_cyl/=.
    exists (LitInt setT).
    { by rewrite /=/measurable/=/discr_meas/=. }
    rewrite /bcov_LitInt/=.
    apply /predeqP =>y /=.
    split.
    - by move=> [x??]; exists x.
    - by move=> [x?]; exists x.
  Qed.

  Lemma bcov_LitBool_meas : measurable bcov_LitBool. Proof. Admitted.
  Lemma bcov_LitUnit_meas : measurable bcov_LitUnit. Proof. Admitted.
  Lemma bcov_LitLoc_meas  : measurable bcov_LitLoc.  Proof. Admitted.
  Lemma bcov_LitLbl_meas  : measurable bcov_LitLbl.  Proof. Admitted.
  Lemma bcov_LitReal_meas : measurable bcov_LitReal. Proof. Admitted.

  Lemma ecov_val_meas        : measurable ecov_val. Proof. Admitted.
  Lemma ecov_var_meas        : measurable ecov_var. Proof. Admitted.
  Lemma ecov_rec_meas        : measurable ecov_rec. Proof. Admitted.
  Lemma ecov_app_meas        : measurable ecov_app. Proof. Admitted.
  Lemma ecov_unop_meas       : measurable ecov_unop. Proof. Admitted.
  Lemma ecov_binop_meas      : measurable ecov_binop. Proof. Admitted.
  Lemma ecov_if_meas         : measurable ecov_if. Proof. Admitted.
  Lemma ecov_pair_meas       : measurable ecov_pair. Proof. Admitted.
  Lemma ecov_fst_meas        : measurable ecov_fst. Proof. Admitted.
  Lemma ecov_snd_meas        : measurable ecov_snd. Proof. Admitted.
  Lemma ecov_injl_meas       : measurable ecov_injl. Proof. Admitted.
  Lemma ecov_injr_meas       : measurable ecov_injr. Proof. Admitted.
  Lemma ecov_alloc_meas      : measurable ecov_alloc. Proof. Admitted.
  Lemma ecov_load_meas       : measurable ecov_load. Proof. Admitted.
  Lemma ecov_store_meas      : measurable ecov_store. Proof. Admitted.
  Lemma ecov_alloctape_meas  : measurable ecov_alloctape. Proof. Admitted.
  Lemma ecov_rand_meas       : measurable ecov_rand. Proof. Admitted.
  Lemma ecov_allocutape_meas : measurable ecov_allocutape. Proof. Admitted.
  Lemma ecov_urand_meas      : measurable ecov_urand. Proof. Admitted.
  Lemma ecov_tick_meas       : measurable ecov_tick. Proof. Admitted.

  Lemma vcov_lit_meas        : measurable vcov_lit. Proof. Admitted.
  Lemma vcov_rec_meas        : measurable vcov_rec. Proof. Admitted.
  Lemma vcov_pair_meas       : measurable vcov_pair. Proof. Admitted.
  Lemma vcov_injlv_meas      : measurable vcov_injlv. Proof. Admitted.
  Lemma vcov_injrv_meas      : measurable vcov_injrv. Proof. Admitted.



  (** Projection functions *)
  Definition 𝜋_LitInt_z  (b : base_lit) : TZ := match b with | LitInt  v => v | _ => point end.
  Definition 𝜋_LitBool_b (b : base_lit) : TB := match b with | LitBool v => v | _ => point end.
  Definition 𝜋_LitLoc_l  (b : base_lit) : TL := match b with | LitLoc  v => v | _ => point end.
  Definition 𝜋_LitLbl_l  (b : base_lit) : TL := match b with | LitLbl  v => v | _ => point end.
  Definition 𝜋_LitReal_r (b : base_lit) : TR := match b with | LitReal v => v | _ => point end.

  Definition 𝜋_LitV_v    (v : val)      : base_lit         := match v with | LitV v => v | _ => point end.
  Definition 𝜋_RecV_f    (v : val)      : <<discr binder>> := match v with | RecV f _ _ => f | _ => point end.
  Definition 𝜋_RecV_x    (v : val)      : <<discr binder>> := match v with | RecV _ x _ => x | _ => point end.
  Definition 𝜋_RecV_e    (v : val)      : expr             := match v with | RecV _ _ e => e | _ => point end.
  Definition 𝜋_PairV_l   (v : val)      : val              := match v with | PairV r _ => r | _ => point end.
  Definition 𝜋_PairV_r   (v : val)      : val              := match v with | PairV _ r => r | _ => point end.
  Definition 𝜋_InjLV_v   (v : val)      : val              := match v with | InjLV r => r | _ => point end.
  Definition 𝜋_InjRV_v   (v : val)      : val              := match v with | InjRV r => r | _ => point end.


  Definition 𝜋_Val_v        (e : expr)     : val              := match e with | Val r => r | _ => point end.
  Definition 𝜋_Var_v        (e : expr)     : <<discr binder>> := match e with | Var x => x | _ => point end.
  Definition 𝜋_Rec_f        (e : expr)     : <<discr binder>> := match e with | Rec f _ _ => f | _ => point end.
  Definition 𝜋_Rec_x        (e : expr)     : <<discr binder>> := match e with | Rec _ x _ => x | _ => point end.
  Definition 𝜋_Rec_e        (e : expr)     : expr             := match e with | Rec _ _ e => e | _ => point end.
  Definition 𝜋_UnOp_op      (e : expr)     : <<discr un_op>>  := match e with | UnOp op _ => op | _ => point end.
  Definition 𝜋_UnOp_e       (e : expr)     : expr             := match e with | UnOp _  e => e | _ => point end.
  Definition 𝜋_BinOp_op     (e : expr)     : <<discr bin_op>> := match e with | BinOp op _ _ => op | _ => point end.
  Definition 𝜋_BinOp_l      (e : expr)     : expr             := match e with | BinOp _  e _ => e | _ => point end.
  Definition 𝜋_BinOp_r      (e : expr)     : expr             := match e with | BinOp _  _ e => e | _ => point end.
  Definition 𝜋_App_l        (e : expr)     : expr             := match e with | App e _ => e | _ => point end.
  Definition 𝜋_App_r        (e : expr)     : expr             := match e with | App _ e => e | _ => point end.
  Definition 𝜋_If_c         (e : expr)     : expr             := match e with | If e _ _ => e | _ => point end.
  Definition 𝜋_If_l         (e : expr)     : expr             := match e with | If _ e _ => e | _ => point end.
  Definition 𝜋_If_r         (e : expr)     : expr             := match e with | If _ _ e => e | _ => point end.
  Definition 𝜋_Pair_l       (e : expr)     : expr             := match e with | Pair e _ => e | _ => point end.
  Definition 𝜋_Pair_r       (e : expr)     : expr             := match e with | Pair _ e => e | _ => point end.
  Definition 𝜋_Fst_e        (e : expr)     : expr             := match e with | Fst e => e | _ => point end.
  Definition 𝜋_Snd_e        (e : expr)     : expr             := match e with | Snd e => e | _ => point end.
  Definition 𝜋_InjL_e       (e : expr)     : expr             := match e with | InjL e => e | _ => point end.
  Definition 𝜋_InjR_e       (e : expr)     : expr             := match e with | InjR e => e | _ => point end.
  Definition 𝜋_AllocN_N     (e : expr)     : expr             := match e with | AllocN e _ => e | _ => point end.
  Definition 𝜋_AllocN_e     (e : expr)     : expr             := match e with | AllocN _ e => e | _ => point end.
  Definition 𝜋_Load_e       (e : expr)     : expr             := match e with | Load e => e | _ => point end.
  Definition 𝜋_Store_l      (e : expr)     : expr             := match e with | Store e _ => e | _ => point end.
  Definition 𝜋_Store_e      (e : expr)     : expr             := match e with | Store _ e => e | _ => point end.
  Definition 𝜋_AllocTape_e  (e : expr)     : expr             := match e with | AllocTape e => e | _ => point end.
  Definition 𝜋_Rand_t       (e : expr)     : expr             := match e with | Rand e _ => e | _ => point end.
  Definition 𝜋_Rand_N       (e : expr)     : expr             := match e with | Rand _ e => e | _ => point end.
  Definition 𝜋_URand_e      (e : expr)     : expr             := match e with | URand e => e | _ => point end.
  Definition 𝜋_Tick_e       (e : expr)     : expr             := match e with | Tick e => e | _ => point end.


  (** Projection functions measurability *)
  Lemma 𝜋_LitInt_z_meas  : measurable_fun bcov_LitInt 𝜋_LitInt_z. Proof. Admitted.
  Lemma 𝜋_LitBool_b_meas : measurable_fun bcov_LitBool 𝜋_LitBool_b. Proof. Admitted.
  Lemma 𝜋_LitLoc_l_meas  : measurable_fun bcov_LitLoc 𝜋_LitLoc_l. Proof. Admitted.
  Lemma 𝜋_LitLbl_l_meas  : measurable_fun bcov_LitLbl 𝜋_LitLbl_l. Proof. Admitted.
  Lemma 𝜋_LitReal_r_meas : measurable_fun bcov_LitReal 𝜋_LitReal_r. Proof. Admitted.

  Lemma 𝜋_LitV_v_meas    : measurable_fun vcov_lit   𝜋_LitV_v. Proof. Admitted.
  Lemma 𝜋_RecV_f_meas    : measurable_fun vcov_rec   𝜋_RecV_f. Proof. Admitted.
  Lemma 𝜋_RecV_x_meas    : measurable_fun vcov_rec   𝜋_RecV_x. Proof. Admitted.
  Lemma 𝜋_RecV_e_meas    : measurable_fun vcov_rec   𝜋_RecV_e. Proof. Admitted.
  Lemma 𝜋_PairV_l_meas   : measurable_fun vcov_pair  𝜋_PairV_l. Proof. Admitted.
  Lemma 𝜋_PairV_r_meas   : measurable_fun vcov_pair  𝜋_PairV_r. Proof. Admitted.
  Lemma 𝜋_InjLV_v_meas   : measurable_fun vcov_injlv 𝜋_InjLV_v. Proof. Admitted.
  Lemma 𝜋_InjRV_v_meas   : measurable_fun vcov_injrv 𝜋_InjLV_v. Proof. Admitted.

  Lemma 𝜋_Val_v_meas         : measurable_fun ecov_val 𝜋_Val_v. Proof. Admitted.
  Lemma 𝜋_Var_v_meas         : measurable_fun ecov_var 𝜋_Var_v. Proof. Admitted.
  Lemma 𝜋_Rec_f_meas         : measurable_fun ecov_rec 𝜋_Rec_f. Proof. Admitted.
  Lemma 𝜋_Rec_x_meas         : measurable_fun ecov_rec 𝜋_Rec_x. Proof. Admitted.
  Lemma 𝜋_Rec_e_meas         : measurable_fun ecov_rec 𝜋_Rec_e. Proof. Admitted.
  Lemma 𝜋_App_l_meas         : measurable_fun ecov_app 𝜋_App_l. Proof. Admitted.
  Lemma 𝜋_App_r_meas         : measurable_fun ecov_app 𝜋_App_r. Proof. Admitted.
  Lemma 𝜋_UnOp_op_meas       : measurable_fun ecov_unop 𝜋_UnOp_op. Proof. Admitted.
  Lemma 𝜋_UnOp_e_meas        : measurable_fun ecov_unop 𝜋_UnOp_e. Proof. Admitted.
  Lemma 𝜋_BinOp_op_meas      : measurable_fun ecov_binop 𝜋_BinOp_op. Proof. Admitted.
  Lemma 𝜋_BinOp_l_meas       : measurable_fun ecov_binop 𝜋_BinOp_l. Proof. Admitted.
  Lemma 𝜋_BinOp_r_meas       : measurable_fun ecov_binop 𝜋_BinOp_r. Proof. Admitted.
  Lemma 𝜋_If_c_meas          : measurable_fun ecov_if 𝜋_If_c. Proof. Admitted.
  Lemma 𝜋_If_l_meas          : measurable_fun ecov_if 𝜋_If_l. Proof. Admitted.
  Lemma 𝜋_If_r_meas          : measurable_fun ecov_if 𝜋_If_r. Proof. Admitted.
  Lemma 𝜋_Pair_l_meas        : measurable_fun ecov_pair 𝜋_Pair_l. Proof. Admitted.
  Lemma 𝜋_Pair_r_meas        : measurable_fun ecov_pair 𝜋_Pair_r. Proof. Admitted.
  Lemma 𝜋_Fst_e_meas         : measurable_fun ecov_fst 𝜋_Fst_e. Proof. Admitted.
  Lemma 𝜋_Snd_e_meas         : measurable_fun ecov_snd 𝜋_Snd_e. Proof. Admitted.
  Lemma 𝜋_InjL_e_meas        : measurable_fun ecov_injl 𝜋_InjL_e. Proof. Admitted.
  Lemma 𝜋_InjR_e_meas        : measurable_fun ecov_injr 𝜋_InjR_e. Proof. Admitted.
  Lemma 𝜋_AllocN_N_meas      : measurable_fun ecov_alloc 𝜋_AllocN_N. Proof. Admitted.
  Lemma 𝜋_AllocN_e_meas      : measurable_fun ecov_alloc 𝜋_AllocN_e. Proof. Admitted.
  Lemma 𝜋_Load_e_meas        : measurable_fun ecov_load 𝜋_Load_e. Proof. Admitted.
  Lemma 𝜋_Store_l_meas       : measurable_fun ecov_store 𝜋_Store_l. Proof. Admitted.
  Lemma 𝜋_Store_e_meas       : measurable_fun ecov_store 𝜋_Store_e. Proof. Admitted.
  Lemma 𝜋_AllocTape_e_meas   : measurable_fun ecov_alloctape 𝜋_AllocTape_e. Proof. Admitted.
  Lemma 𝜋_Rand_t_meas        : measurable_fun ecov_rand 𝜋_Rand_t. Proof. Admitted.
  Lemma 𝜋_Rand_N_meas        : measurable_fun ecov_rand 𝜋_Rand_N. Proof. Admitted.
  Lemma 𝜋_URand_e_meas       : measurable_fun ecov_urand 𝜋_URand_e. Proof. Admitted.
  Lemma 𝜋_Tick_e_meas        : measurable_fun ecov_tick 𝜋_Tick_e. Proof. Admitted.
  

End expr_measurability.




(**  General lemmas about tapes *)

Definition tape_content_t (A : Type) : Type := nat -> option A.

Record tape (A : Type) : Type := {
  tape_position : nat;
  tape_contents : tape_content_t A
}.

Definition emptyTapeContents {A : Type} : tape_content_t A := fun _ => None.

Definition emptyTape {A : Type} : tape A :=
  {| tape_position := 0 ;
     tape_contents := emptyTapeContents
  |}.

(* History lookup: look through absolute history *)
Global Instance tape_content_lookup {A} : Lookup nat A (tape_content_t A) := fun i => fun h => h i.

(**  Specialize tapes to btapes and utapes, construct siga algebra *)
Section tapes_algebra.
  Local Open Scope classical_set_scope.


  (* Tapes in the computable fragment *)
  Record pre_btape : Type := {
      btape_tape :> tape nat;
      btape_bound : nat
  }.

  (* Tapes of real numbers *)
 Definition pre_utape : Type := tape R.


  (* FIXME: move *)
  Definition image4 {TA TB TC TD rT} (A : set TA) (B : set TB) (C : set TC) (D : set TD) (f : TA -> TB -> TC -> TD -> rT) :=
    [set z | exists2 x, A x & exists2 y, B y & exists2 w, C w & exists2 v, D v & f x y w v = z].
  Arguments image4 _ _ _ _ _ _ _ _ _ /.

  Definition btape_basis_emp : set (set pre_btape) :=
    let bound_set : set nat := setT in
    let pos_set : set nat := setT in

    (* The set of all btapes such that
       - the bound is b
       - the position is p
       - the content is empty *)
    let construct b p :=
      [set {| btape_tape := {| tape_position := p; tape_contents := (fun _ => None) |} ;
              btape_bound := b |}] in
    image2 bound_set pos_set construct.

  Program Definition btape_basis_full : set (set pre_btape) :=
    let bound_set : set nat := setT in
    let pos_set   : set nat := setT in
    let index_set : set nat := setT in
    let value_set : set nat := setT in

    (* The set of all btapes such that
       - the bound is b
       - the position is p
       - the content at index i is set to the value v *)
    let construct b p i v :=
      (fun bt =>
         exists contents,
           bt = {| btape_tape := {| tape_position := p; tape_contents := contents |}; btape_bound := b|} /\
           contents !! i = Some v) in

    image4 bound_set pos_set index_set value_set construct.

  Definition btape_basis := btape_basis_emp `|` btape_basis_full.

  HB.instance Definition _ := gen_eqMixin pre_btape.
  HB.instance Definition _ := gen_choiceMixin pre_btape.
  HB.instance Definition _ := isPointed.Build pre_btape {| btape_tape := emptyTape ; btape_bound := 0 |}.

  Local Lemma btape_meas_obligation : ∀ A : set pre_btape, <<s btape_basis>> A → <<s btape_basis>> (~` A).
  Proof. eapply sigma_algebraC. Qed.

  HB.instance Definition _ := @isMeasurable.Build
    (sigma_display btape_basis)
    pre_btape
    <<s btape_basis>>
    (@sigma_algebra0 _ setT btape_basis)
    btape_meas_obligation
    (@sigma_algebra_bigcup _ setT btape_basis).


  Definition utape_basis_emp : set (set pre_utape) :=
    let pos_set : set nat := setT in

    (* The set of all utapes such that
       - the position is p
       - the content is empty *)
    let construct p :=
      [set {| tape_position := p; tape_contents := (fun _ => None) |}] in
    image pos_set construct.

  (* FIXME: This should not return a singleton! *)
  Definition utape_basis_full : set (set pre_utape) :=
    let pos_set   : set nat := setT in
    let index_set : set nat := setT in
    let value_set : set (set (R : realType)) := 'measurable in

    (* The set of all utapes such that
       - the position is p
       - the content at position i is set to some value in set_of_v *)
    let construct p i set_of_v :=
        (fun ut =>
           exists contents r,
             ut = {| tape_position := p; tape_contents := contents |} /\
             contents !! i = Some r /\
             set_of_v r) in
    image3 pos_set index_set value_set construct.

  Definition utape_basis : set (set pre_utape) := utape_basis_emp `|` utape_basis_full.

  HB.instance Definition _ := gen_eqMixin pre_utape.
  HB.instance Definition _ := gen_choiceMixin pre_utape.
  HB.instance Definition _ := isPointed.Build pre_utape emptyTape.

  Local Lemma utape_meas_obligation : ∀ A : set pre_utape, <<s utape_basis>> A → <<s utape_basis>> (~` A).
  Proof. eapply sigma_algebraC. Qed.

  HB.instance Definition _ := @isMeasurable.Build
    (sigma_display utape_basis)
    pre_utape
    <<s utape_basis>>
    (@sigma_algebra0 _ setT utape_basis)
    utape_meas_obligation
    (@sigma_algebra_bigcup _ setT utape_basis).


  (* User-facing types *)
  Definition btape : measurableType btape_basis.-sigma := pre_btape.
  Definition utape : measurableType utape_basis.-sigma := pre_utape.

End tapes_algebra.


(* btape and utape definitions *)

(* All values of the tape are within the tape bound *)
Definition btape_inbounds (t : btape): Prop :=
  forall n : nat,
    tape_contents _ t n = None \/
    exists v : nat, tape_contents _ t n = Some v /\ v < btape_bound t.

(* All tape values prior to state have been determined *)
Definition tape_history_deterministic {A} (t : tape A) : Prop :=
  forall i : nat, i < tape_position _ t -> exists v : A, tape_contents _ t i = Some v.

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

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.


Section state_algebra.

  Local Open Scope classical_set_scope.

  (** The state: a [loc]-indexed heap of [val]s, and [loc]-indexed tapes, and [loc]-indexed utapes *)
  Record state_pre : Type := {
    heap   : gmap loc val;
    tapes  : gmap loc btape;
    utapes : gmap loc utape
  }.

  Definition gmap_loc_cyl_emp d (T : measurableType d) : set (set (gmap loc T)) :=
    [set (fun g => forall l, g !! l = None)].

  Definition gmap_loc_cyl_full d (T : measurableType d) : set (set (gmap loc T)) :=
    let loc_set   : set loc := setT in
    let T_set     : set (set T) := d.-measurable in

    (* The set of all gmaps such that
        - the value at position l is set to an element in the set ts *)
    let construct (l : loc) (ts : set T) : set (gmap loc T) :=
      fun g => exists v : T, g !! l = Some v /\ ts v in
    image2 loc_set T_set construct.

  Definition gmap_loc_cyl d (T : measurableType d) : set (set (gmap loc T)) :=
    gmap_loc_cyl_emp d T `|` gmap_loc_cyl_full d T.

  (* The set of all states such that
     each field is a gmap cylinder
   *)
  Program Definition state_cyl : set (set state_pre) :=
    let hs_set := gmap_loc_cyl _ val in
    let ts_set := gmap_loc_cyl _ btape in
    let us_set := gmap_loc_cyl _ utape in
    let construct (hs : set (gmap loc val)) (ht : set (gmap loc btape)) (hu : set (gmap loc utape)) : set state_pre :=
      fun σ =>
        exists g1 : gmap loc val,
        exists g2 : gmap loc btape,
        exists g3 : gmap loc utape,
        σ = {| heap := g1; tapes := g2; utapes := g3|} /\
        hs g1 /\
        ht g2 /\
        hu g3
      in
    image3 hs_set ts_set us_set construct.

  HB.instance Definition _ := gen_eqMixin state_pre.
  HB.instance Definition _ := gen_choiceMixin state_pre.
  HB.instance Definition _ := isPointed.Build state_pre {| heap := gmap_empty; tapes := gmap_empty; utapes := gmap_empty |}.


  Local Lemma state_pre_meas_obligation : ∀ A : set state_pre, <<s state_cyl>> A → <<s state_cyl>> (~` A).
  Proof. eapply sigma_algebraC. Qed.

  (* There's got to be a way to delete this *)
  HB.instance Definition _ := @isMeasurable.Build
    (sigma_display state_cyl)
    state_pre
    <<s state_cyl>>
    (@sigma_algebra0 _ setT state_cyl)
    state_pre_meas_obligation
    (@sigma_algebra_bigcup _ setT state_cyl).

  Definition state : measurableType state_cyl.-sigma := state_pre.

End state_algebra.




(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj {T1 T2 T3 T4 : Type} : Inj (=) (=) (@of_val T1 T2 T3 T4).
Proof. intros ??. congruence. Qed.

Global Instance state_inhabited : Inhabited state := populate {| heap := gmap_empty; tapes := gmap_empty; utapes := gmap_empty |}.
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
  | RandLCtx (v2 : val)
  | RandRCtx (e1 : expr)
  | URandCtx
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


Definition binder_eq (b1 b2 : <<discr binder>> ) : bool. Admitted.

(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y =>  if (binder_eq x y) then Val v else Var y
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
  | MinusUnOp, LitV (LitInt z) => Some $ LitV $ LitInt (- z)%Z
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


(*
Section pointed_instances.
  Local Open Scope classical_set_scope.

  (* Fail Check (<<discr state>> : measurableType _).  *)
  (*  HB.instance Definition _ := gen_eqMixin state. *)
  (*  HB.instance Definition _ := gen_choiceMixin state. *)
  (* HB.instance Definition _ := isPointed.Build state inhabitant. *)
  (* Check (<<discr state>> : measurableType _). *)

  (** cfg is pointed (automatic) *)
  (* Check (<<discr cfg>> : measurableType _).  *)

  (** state * loc is pointed (automatic) *)
  (* Check (<<discr (state * loc)>> : measurableType _). *)

  (** R is pointed *)
  (* Check (<<discr R>> : measurableType _). *)

End pointed_instances.
*)


Definition fin_to_nat {N : nat} (x : 'I_(S N)) : Z.
Admitted.

Definition cfg : measurableType _ := (expr * state)%type.


Section unif.
  Local Open Scope ereal_scope.
  Local Open Scope classical_set_scope.
  (* Uniform space over [0, 1]*)
  Definition unif_base : subprobability _ R := uniform_prob (@Num.Internals.ltr01 R).

End unif.



Section meas_semantics.
  Local Open Scope ereal_scope.
  Local Open Scope classical_set_scope.

  (** Hierarchy sets that cover cfg.
      The second block of sets are a cover cfg, which is slightly finer, and are used
      to prove measurability of head_stepM.
   *)


  Definition cover_rec             : set cfg := [set c | ∃ f x e σ,      c = (Rec f x e, σ) ].
  Definition cover_pair            : set cfg := [set c | ∃ v1 v2 σ,      c = (Pair (Val v1) (Val v2), σ) ].
  Definition cover_injL            : set cfg := [set c | ∃ v σ,          c = (InjL v, σ) ].
  Definition cover_injR            : set cfg := [set c | ∃ v σ,          c = (InjR v, σ) ].
  Definition cover_app             : set cfg := [set c | ∃ f x e1 v2 σ,  c = (App (Val (RecV f x e1)) (Val v2) , σ) ].
  Definition cover_unop_ok         : set cfg := [set c | ∃ v op w σ,     c = (UnOp op (Val v), σ) /\ un_op_eval op v = Some w].
  Definition cover_unop_stuck      : set cfg := [set c | ∃ v op σ,       c = (UnOp op (Val v), σ) /\ un_op_eval op v = None ].
  Definition cover_binop_ok        : set cfg := [set c | ∃ v1 v2 op w σ, c = (BinOp op (Val v1) (Val v2), σ) /\ bin_op_eval op v1 v2 = Some w].
  Definition cover_binop_stuck     : set cfg := [set c | ∃ v1 v2 op σ,   c = (BinOp op (Val v1) (Val v2), σ) /\ bin_op_eval op v1 v2 = None].
  Definition cover_ifT             : set cfg := [set c | ∃ e1 e2 σ,      c = (If (Val (LitV (LitBool true))) e1 e2, σ) ].
  Definition cover_ifF             : set cfg := [set c | ∃ e1 e2 σ,      c = (If (Val (LitV (LitBool false))) e1 e2, σ) ].
  Definition cover_fst             : set cfg := [set c | ∃ v1 v2 σ,      c = (Fst (Val (PairV v1 v2)), σ) ].
  Definition cover_snd             : set cfg := [set c | ∃ v1 v2 σ,      c = (Snd (Val (PairV v1 v2)), σ) ].
  Definition cover_caseL           : set cfg := [set c | ∃ v e1 e2 σ,    c = (Case (Val (InjLV v)) e1 e2, σ) ].
  Definition cover_caseR           : set cfg := [set c | ∃ v e1 e2 σ,    c = (Case (Val (InjRV v)) e1 e2, σ) ].
  Definition cover_allocN_ok       : set cfg := [set c | ∃ N v σ,        c = (AllocN (Val (LitV (LitInt N))) (Val v), σ) /\ bool_decide (0 < Z.to_nat N)%nat = true].
  Definition cover_allocN_stuck    : set cfg := [set c | ∃ N v σ,        c = (AllocN (Val (LitV (LitInt N))) (Val v), σ) /\ bool_decide (0 < Z.to_nat N)%nat = false].
  Definition cover_load_ok         : set cfg := [set c | ∃ l w σ,        c = (Load (Val (LitV (LitLoc l))), σ) /\ σ.(heap) !! l = Some w].
  Definition cover_load_stuck      : set cfg := [set c | ∃ l σ,          c = (Load (Val (LitV (LitLoc l))), σ) /\ σ.(heap) !! l = None].
  Definition cover_store_ok        : set cfg := [set c | ∃ l w w' σ,     c = (Store (Val (LitV (LitLoc l))) (Val w), σ) /\ σ.(heap) !! l = Some w'].
  Definition cover_store_stuck     : set cfg := [set c | ∃ l w σ,        c = (Store (Val (LitV (LitLoc l))) (Val w), σ) /\ σ.(heap) !! l = None ].
  Definition cover_randE           : set cfg := [set c | ∃ N σ,          c = (Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)), σ) ].
  Definition cover_alloctape       : set cfg := [set c | ∃ z σ,          c = (AllocTape (Val (LitV (LitInt z))), σ) ].
  Definition cover_randT_notape    : set cfg := [set c | ∃ N l σ,        c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = None ].
  Definition cover_randT_mismatch  : set cfg := [set c | ∃ N l b σ,      c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = false)].
  Definition cover_randT_empty     : set cfg := [set c | ∃ N l b σ,      c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = true) /\ (b.(btape_tape) !! 0) = None].
  Definition cover_randT           : set cfg := [set c | ∃ N l b n σ,    c = (Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))), σ) /\ σ.(tapes) !! l = Some b /\ (bool_decide (b.(btape_bound) = Z.to_nat N) = true) /\ (b.(btape_tape) !! 0) = Some n].
  Definition cover_allocutape      : set cfg := [set c | ∃ σ,            c = (AllocUTape, σ) ].
  Definition cover_urandE          : set cfg := [set c | ∃ σ,            c = (URand (Val (LitV LitUnit)), σ) ].
  Definition cover_urandT_notape   : set cfg := [set c | ∃ σ l,          c = (URand (Val (LitV (LitLbl l))), σ) /\ σ.(utapes) !! l = None ].
  Definition cover_urandT_empty    : set cfg := [set c | ∃ σ l τ,        c = (URand (Val (LitV (LitLbl l))), σ) /\ σ.(utapes) !! l = Some τ /\ (τ !! 0) = None].
  Definition cover_urandT          : set cfg := [set c | ∃ σ l τ v,      c = (URand (Val (LitV (LitLbl l))), σ) /\ σ.(utapes) !! l = Some τ /\ (τ !! 0) = Some v].
  Definition cover_tick            : set cfg := [set c | ∃ σ n,          c = (Tick (Val (LitV (LitInt n))), σ) ].
  Definition cover_maybe_stuck     : set cfg := setT.


  Definition cfg_cover : list (set cfg) := [
    cover_rec;
    cover_pair;
    cover_injL;
    cover_injR;
    cover_app;
    cover_unop_ok;
    cover_unop_stuck;
    cover_binop_ok;
    cover_binop_stuck;
    cover_ifT;
    cover_ifF;
    cover_fst;
    cover_snd;
    cover_caseL;
    cover_caseR;
    cover_allocN_ok;
    cover_allocN_stuck;
    cover_load_ok;
    cover_load_stuck;
    cover_store_stuck;
    cover_store_ok;
    cover_randE;
    cover_alloctape;
    cover_randT_notape;
    cover_randT_mismatch;
    cover_randT_empty;
    cover_randT;
    cover_allocutape;
    cover_urandE;
    cover_urandT_notape;
    cover_urandT_empty;
    cover_urandT;
    cover_tick;
    cover_maybe_stuck
  ].

  Lemma cfg_cover_is_cover : List.fold_right setU set0 cfg_cover = setT.
  Proof.
    rewrite /cfg_cover/=/cover_maybe_stuck.
    rewrite setTU.
    repeat rewrite setUT.
    done.
  Qed.


  (** Prove that the cover is measurable *)
  (* Do some of them by hand, and then try to factor out general lemmas *)
  (* I'm most worried about the ones that go more than one layer deep *)


  Lemma cover_rec_measurable : measurable cover_rec.
  Proof.
    rewrite measurable_prod_measurableType.
    apply sub_gen_smallest.
    simpl.
    exists [set c | ∃ (f x0 : binder) (e : expr_pre), c = Rec f x0 e]; last first.
    { exists setT; [eapply measurableT|].
      rewrite /setX/cover_rec/= predeqE.
      move=> [e σ] /=.
      rewrite and_True.
      admit. }

  (* TODO: projections to be measurable, and binders to be countable. *)
  (* Pull out the bunders to a countabke union *)
  (* Then, this is the preimage of (setT : expr) under the measurable function Rec. *)
  Admitted.


  (* TODO: Factor out the individual step functions? *)
  Definition urand_step : measurable_map ((R : realType) : measurableType _) cfg.
  Admitted.


  Definition urand_tape_step : measurable_map ((R : realType) : measurableType _) cfg.
  Admitted.
    (* This funciton needs to do this: *)
    (* (fun (u : R) =>
         (* Fill tape head with new sample *)
         let τ' := <[ (0 : nat) := Some u ]> τ in
         (* Advance tape *)
         let σ' := state_upd_utapes <[ l := (tapeAdvance τ') ]> σ1 in
         (* Return the update value an state *)
         ((Val $ LitV $ LitReal u, σ') : cfg)) *)


  (* TODO: Prove the measurability of each function when restructed to the cover set *)
  (* Try to think of a general lemma? *)
  (* May need to redefine point, not sure. *)




  Definition head_stepM_def (c : cfg) : giryM cfg :=
    let (e1, σ1) := c in
    match e1 with
    | Rec f x e =>
        giryM_ret R ((Val $ RecV f x e, σ1) : cfg)
    | Pair (Val v1) (Val v2) =>
        giryM_ret R ((Val $ PairV v1 v2, σ1) : cfg)
    | InjL (Val v) =>
        giryM_ret R ((Val $ InjLV v, σ1) : cfg)
    | InjR (Val v) =>
        giryM_ret R ((Val $ InjRV v, σ1) : cfg)
    | App (Val (RecV f x e1)) (Val v2) =>
        giryM_ret R ((subst' x v2 (subst' f (RecV f x e1) e1) , σ1) : cfg)
    | UnOp op (Val v) =>
        match un_op_eval op v with
          | Some w => giryM_ret R ((Val w, σ1) : cfg)
          | _ => giryM_zero
        end
    | BinOp op (Val v1) (Val v2) =>
        match bin_op_eval op v1 v2 with
          | Some w => giryM_ret R ((Val w, σ1) : cfg)
          | _ => giryM_zero
        end
    | If (Val (LitV (LitBool true))) e1 e2  =>
        giryM_ret R ((e1 , σ1) : cfg)
    | If (Val (LitV (LitBool false))) e1 e2 =>
        giryM_ret R ((e2 , σ1) : cfg)
    | Fst (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v1 , σ1) : cfg) (* Syntax error when I remove the space between v1 and , *)
    | Snd (Val (PairV v1 v2)) =>
        giryM_ret R ((Val v2, σ1) : cfg)
    | Case (Val (InjLV v)) e1 e2 =>
        giryM_ret R ((App e1 (Val v), σ1) : cfg)
    | Case (Val (InjRV v)) e1 e2 =>
        giryM_ret R ((App e2 (Val v), σ1) : cfg)
    | AllocN (Val (LitV (LitInt N))) (Val v) =>
        let ℓ := fresh_loc σ1.(heap) in
        if bool_decide (0 < Z.to_nat N)%nat
          then giryM_ret R ((Val $ LitV $ LitLoc ℓ, state_upd_heap_N ℓ (Z.to_nat N) v σ1) : cfg)
          else giryM_zero
    | Load (Val (LitV (LitLoc l))) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val v, σ1) : cfg)
          | None => giryM_zero
        end
    | Store (Val (LitV (LitLoc l))) (Val w) =>
        match σ1.(heap) !! l with
          | Some v => giryM_ret R ((Val $ LitV LitUnit, state_upd_heap <[l:=w]> σ1) : cfg)
          | None => giryM_zero
        end
    (* Uniform sampling from [0, 1 , ..., N] *)
    | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) =>
        giryM_map
          (m_discr (fun (n : 'I_(S (Z.to_nat N))) => ((Val $ LitV $ LitInt $ fin_to_nat n, σ1) : cfg)))
          (giryM_unif (Z.to_nat N))
    | AllocTape (Val (LitV (LitInt z))) =>
        let ι := fresh_loc σ1.(tapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_tapes <[ι := {| btape_tape := emptyTape ; btape_bound := (Z.to_nat z) |} ]> σ1) : cfg)
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
                  (giryM_ret R ((Val $ LitV $ LitInt $ Z.of_nat v, σ') : cfg))
              | None =>
                  (* Next slot on tape is empty *)
                  giryM_map
                    (m_discr (fun (v : 'I_(S (Z.to_nat N))) =>
                       (* Fill the tape head with new sample *)
                       let τ' := <[ (0 : nat) := Some (v : nat) ]> τ in
                       (* Advance the tape *)
                       let σ' := state_upd_tapes <[ l := {| btape_tape := (tapeAdvance τ'); btape_bound := M |} ]> σ1 in
                       (* Return the new sample and state *)
                       ((Val $ LitV $ LitInt $ Z.of_nat v, σ') : cfg)))
                   (giryM_unif (Z.to_nat N))
              end
            else
              (* Tape bounds do not match *)
              (* Do not advance the tape, but still generate a new sample *)
              giryM_map
                (m_discr (fun (n : 'I_(S (Z.to_nat N))) => (((Val $ LitV $ LitInt $ fin_to_nat n) : <<discr expr>>), σ1) : cfg))
                (giryM_unif (Z.to_nat N))
        | None => giryM_zero
        end
    | AllocUTape =>
        let ι := fresh_loc σ1.(utapes) in
        giryM_ret R ((Val $ LitV $ LitLbl ι, state_upd_utapes <[ ι := emptyTape ]> σ1) : cfg)
    (* Urand with no tape *)
    | URand (Val (LitV LitUnit)) => giryM_zero (* FIXME giryM_map urand_step unif_base *)
    (* Urand with a tape *)
    | URand (Val (LitV (LitLbl l))) =>
        match σ1.(utapes) !! l with
        | Some τ =>
            (* tape l is allocated *)
            match (τ !! 0) with
            | Some u =>
                (* Head has a sample *)
                let σ' := state_upd_utapes <[ l := (tapeAdvance τ) ]> σ1 in
                (giryM_ret R ((Val $ LitV $ LitReal u, σ') : cfg))
            | None =>
                (* Head has no sample *)
                giryM_zero
                (* FIXME giryM_map urand_tape_step unif_base *)
            end
        | None => giryM_zero
        end
    | Tick (Val (LitV (LitInt n))) => giryM_ret R ((Val $ LitV $ LitUnit, σ1) : cfg)
    | _ => giryM_zero
    end.



  (*
  Lemma cover_rec_restrict : measurable_fun cover_rec (restrict cover_rec head_stepM_def).
  Proof.
    *)





  (** TODO: Can I prove a general lemma about "apply a measurable function to each constructor" instead? *)
  Local Lemma head_stepM_def_measurable :
    @measurable_fun _ _ cfg (giryM cfg) setT head_stepM_def.
  Proof.
    Check measurable_by_cover_list.
  Admitted.

  HB.instance Definition _ :=
    isMeasurableMap.Build _ _ _ _ _ head_stepM_def_measurable.

  Definition head_stepM : measurable_map cfg (giryM cfg) :=
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
  head_step_rel (Rand (Val (LitV (LitInt z))) (Val $ LitV $ LitLbl l)) σ  (Val $ LitV $ LitInt $ n_int) σ
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
(* TODO: Uncomment the slow proof *)
Lemma decomp_expr_ord Ki e e' : decomp_item e = Some (Ki, e') → expr_ord e' e.
Proof. Admitted.
(*
  rewrite /expr_ord /decomp_item.
  destruct Ki ; repeat destruct_match ; intros [=] ; subst ; cbn ; lia.
Qed. *)

Lemma decomp_fill_item Ki e :
  to_val e = None → decomp_item (fill_item Ki e) = Some (Ki, e).
Proof. destruct Ki ; simpl ; by repeat destruct_match. Qed.

(* TODO: this proof is slow, but I do not see how to make it faster... *)
(* TODO: Uncomment the slow proof *)
Lemma decomp_fill_item_2 e e' Ki :
  decomp_item e = Some (Ki, e') → fill_item Ki e' = e ∧ to_val e' = None.
Proof. Admitted.
(*
  rewrite /decomp_item ;
    destruct e ; try done ;
    destruct Ki ; cbn ; repeat destruct_match ; intros [=] ; subst ; auto.
Qed. *)

Local Open Scope classical_set_scope.

Definition fill_item_mf (K : ectx_item) : measurable_map expr expr.
Admitted.
(*   := m_discr (fill_item K : <<discr expr>> -> <<discr expr>>).  *)

Definition meas_lang_mixin :
  @MeasEctxiLanguageMixin _ _ _ expr val state ectx_item
    of_val to_val fill_item_mf decomp_item expr_ord head_stepM_def.
Proof.
  split.
  - apply to_of_val.
  - apply of_to_val.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.


End meas_lang.

(** Language *)


Canonical Structure meas_ectxi_lang := MeasEctxiLanguage meas_lang.head_stepM meas_lang.meas_lang_mixin.
Canonical Structure meas_ectx_lang := MeasEctxLanguageOfEctxi meas_ectxi_lang.
Canonical Structure meas_lang := MeasLanguageOfEctx meas_ectx_lang.

(* Prefer meas_lang names over ectx_language names. *)
Export meas_lang.
