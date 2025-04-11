(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap countable.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections cfg types.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

Notation of_val := ValC (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Lemma to_val_meas : measurable_fun setT to_val.
Proof. Admitted.


Global Instance of_val_inj : Inj (=) (=) (@of_val).
Proof. intros ?? H. by inversion H. Qed.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.


(**
   TODO: Measure space on ectx_item (cylinder construction, simple)
   Measurable projections and constructors
   Measure space on noval
   fill_item and decomp are measurable functions
 *)

Local Open Scope classical_set_scope.

(** Syntax for evaluation contexts *)
Inductive ectx_item_pre {TZ TB TL TR : Type} : Type :=
  | AppLCtx (v2 : @val_pre TZ TB TL TR)
  | AppRCtx (e1 : @expr_pre TZ TB TL TR)
  | UnOpCtx (op : <<discr un_op>>)
  | BinOpLCtx (op : <<discr bin_op>>) (v2 : @val_pre TZ TB TL TR)
  | BinOpRCtx (op : bin_op) (e1 : @expr_pre TZ TB TL TR)
  | IfCtx (e1 e2 : @expr_pre TZ TB TL TR)
  | PairLCtx (v2 : @val_pre TZ TB TL TR)
  | PairRCtx (e1 : @expr_pre TZ TB TL TR)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : @expr_pre TZ TB TL TR) (e2 : @expr_pre TZ TB TL TR)
  | AllocCtx
  | LoadCtx
  | StoreLCtx (v2 : @val_pre TZ TB TL TR)
  | StoreRCtx (e1 : @expr_pre TZ TB TL TR)
  | AllocTapeCtx
  | RandLCtx (v2 : @val_pre TZ TB TL TR)
  | RandRCtx (e1 : @expr_pre TZ TB TL TR)
  | URandCtx
  | TickCtx.

(*
Definition ectx_item_pre_F (k : @ectx_item_pre TZ1 TB1 TL1 TR1) : @ectx_item_pre TZ2 TB2 TL2 TR2 :=
  match k with
  | AppLCtx v2 =>
  | AppRCtx e1 =>
  | UnOpCtx op =>
  | BinOpLCtx op v2 =>
  | BinOpRCtx op e1 =>
  | IfCtx e1 e2 =>
  | PairLCtx v2 =>
  | PairRCtx e1 =>
  | FstCtx =>
  | SndCtx =>
  | InjLCtx =>
  | InjRCtx =>
  | CaseCtx e1 e2 =>
  | AllocNLCtx v2 =>
  | AllocNRCtx e1 =>
  | LoadCtx =>
  | StoreLCtx v2 =>
  | StoreRCtx e1 =>
  | AllocTapeCtx =>
  | RandLCtx v2 =>
  | RandRCtx e1 =>
  | URandCtx =>
  | TickCtx =>
  end.
*)

Section functor.
Context {TZ1 TB1 TL1 TR1 : Type}.
Context {TZ2 TB2 TL2 TR2 : Type}.
Variable FInt : TZ1 -> TZ2.
Variable FBool : TB1 -> TB2.
Variable FLoc : TL1 -> TL2.
Variable FLbl : TL1 -> TL2.
Variable FReal : TR1 -> TR2.

Definition ectx_item_pre_F (k : @ectx_item_pre TZ1 TB1 TL1 TR1) : @ectx_item_pre TZ2 TB2 TL2 TR2 :=
  match k with
  | AppLCtx v2 => AppLCtx (val_pre_F FInt FBool FLoc FLbl FReal v2)
  | AppRCtx e1 => AppRCtx (expr_pre_F FInt FBool FLoc FLbl FReal e1)
  | UnOpCtx op => UnOpCtx op
  | BinOpLCtx op v2 => BinOpLCtx op (val_pre_F FInt FBool FLoc FLbl FReal v2)
  | BinOpRCtx op e1 => BinOpRCtx op (expr_pre_F FInt FBool FLoc FLbl FReal e1)
  | IfCtx e1 e2 => IfCtx (expr_pre_F FInt FBool FLoc FLbl FReal e1) (expr_pre_F FInt FBool FLoc FLbl FReal e2)
  | PairLCtx v2 => PairLCtx (val_pre_F FInt FBool FLoc FLbl FReal v2)
  | PairRCtx e1 => PairRCtx (expr_pre_F FInt FBool FLoc FLbl FReal e1)
  | FstCtx => FstCtx
  | SndCtx => SndCtx
  | InjLCtx => InjLCtx
  | InjRCtx => InjRCtx
  | CaseCtx e1 e2 => CaseCtx (expr_pre_F FInt FBool FLoc FLbl FReal e1) (expr_pre_F FInt FBool FLoc FLbl FReal e2)
  | AllocCtx => AllocCtx
  | LoadCtx => LoadCtx
  | StoreLCtx v2 => StoreLCtx (val_pre_F FInt FBool FLoc FLbl FReal v2)
  | StoreRCtx e1 => StoreRCtx (expr_pre_F FInt FBool FLoc FLbl FReal e1)
  | AllocTapeCtx => AllocTapeCtx
  | RandLCtx v2 => RandLCtx (val_pre_F FInt FBool FLoc FLbl FReal v2)
  | RandRCtx e1 => RandRCtx (expr_pre_F FInt FBool FLoc FLbl FReal e1)
  | URandCtx => URandCtx
  | TickCtx => TickCtx
  end.

End functor.



Section ectx_item_algebra.
  Definition ectx_item_S : Type := @ectx_item_pre (set <<discr Z>>) (set <<discr bool>>) (set <<discr loc>>) (set ((R : realType) : measurableType _)).
  Definition ectx_item_T : Type := @ectx_item_pre <<discr Z>> <<discr bool>> <<discr loc>> ((R : realType) : measurableType _).
  Definition ectx_item_ST (k : ectx_item_S) : set ectx_item_T :=
    match k with
    | AppLCtx v2 => image (val_ST v2) AppLCtx
    | AppRCtx e1 => image (expr_ST e1) AppRCtx
    | UnOpCtx op => [set UnOpCtx op]
    | BinOpLCtx op v2 => image (val_ST v2) (BinOpLCtx op)
    | BinOpRCtx op e1 => image (expr_ST e1) (BinOpRCtx op)
    | IfCtx e1 e2 => image2 (expr_ST e1) (expr_ST e2) IfCtx
    | PairLCtx v2 => image (val_ST v2) PairLCtx
    | PairRCtx e1 => image (expr_ST e1) PairRCtx
    | FstCtx => [set FstCtx]
    | SndCtx => [set SndCtx]
    | InjLCtx => [set InjLCtx]
    | InjRCtx => [set InjRCtx]
    | CaseCtx e1 e2 => image2 (expr_ST e1) (expr_ST e2) CaseCtx
    | AllocCtx => [set AllocCtx]
    | LoadCtx => [set LoadCtx]
    | StoreLCtx v2 => image (val_ST v2) StoreLCtx
    | StoreRCtx e1 =>  image (expr_ST e1) StoreRCtx
    | AllocTapeCtx => [set AllocTapeCtx]
    | RandLCtx v2 => image (val_ST v2) RandLCtx
    | RandRCtx e1 => image (expr_ST e1) RandRCtx
    | URandCtx => [set URandCtx]
    | TickCtx => [set TickCtx]
    end.

  Definition ectx_item_ML : set ectx_item_S :=
    fun k =>
      match k with
      | AppLCtx v2 => val_ML v2
      | AppRCtx e1 => expr_ML e1
      | UnOpCtx op => True
      | BinOpLCtx op v2 => val_ML v2
      | BinOpRCtx op e1 => expr_ML e1
      | IfCtx e1 e2 => expr_ML e1 /\ expr_ML e2
      | PairLCtx v2 => val_ML v2
      | PairRCtx e1 => expr_ML e1
      | FstCtx => True
      | SndCtx => True
      | InjLCtx => True
      | InjRCtx => True
      | CaseCtx e1 e2 => expr_ML e1 /\ expr_ML e2
      | AllocCtx => True
      | LoadCtx => True
      | StoreLCtx v2 => val_ML v2
      | StoreRCtx e1 => expr_ML e1
      | AllocTapeCtx => True
      | RandLCtx v2 => val_ML v2
      | RandRCtx e1 => expr_ML e1
      | URandCtx => True
      | TickCtx => True
      end.

  Definition ectx_item_cyl : set (set ectx_item_T) := image ectx_item_ML ectx_item_ST.

  HB.instance Definition _ := gen_eqMixin ectx_item_T.
  HB.instance Definition _ := gen_choiceMixin ectx_item_T.
  HB.instance Definition _ := isPointed.Build ectx_item_T FstCtx.

  (* FIXME: Remove *)
  Local Lemma ectx_item_meas_obligation :
    ∀ A : set ectx_item_T, <<s ectx_item_cyl>> A → <<s ectx_item_cyl >> (~` A).
  Proof. eapply sigma_algebraC. Qed.

  HB.instance Definition _ := @isMeasurable.Build
    (sigma_display ectx_item_cyl)
    ectx_item_T
    <<s ectx_item_cyl>>
    (@sigma_algebra0 _ setT ectx_item_cyl)
    ectx_item_meas_obligation
    (@sigma_algebra_bigcup _ setT ectx_item_cyl).

End ectx_item_algebra.

Definition ectx_item_display : measure_display := (sigma_display ectx_item_cyl).
Definition ectx_item : measurableType ectx_item_cyl.-sigma := ectx_item_T.

Global Instance : SigmaAlgebra ectx_item_display ectx_item_T :=
  {| axioms := @Measurable.class ectx_item_display ectx_item_T |}.

(** Constructors into the measurableType, curried  *)
Definition AppLCtxC v2      : ectx_item := AppLCtx v2.
Definition AppRCtxC e1      : ectx_item := AppRCtx e1.
Definition UnOpCtxC op      : ectx_item := UnOpCtx op.
Definition BinOpLCtxC op v2 : ectx_item := BinOpLCtx op v2.
Definition BinOpRCtxC op e1 : ectx_item := BinOpRCtx op e1.
Definition IfCtxC e1 e2     : ectx_item := IfCtx e1 e2.
Definition PairLCtxC v2     : ectx_item := PairLCtx v2.
Definition PairRCtxC e1     : ectx_item := PairRCtx e1.
Definition FstCtxC          : ectx_item := FstCtx.
Definition SndCtxC          : ectx_item := SndCtx.
Definition InjLCtxC         : ectx_item := InjLCtx.
Definition InjRCtxC         : ectx_item := InjRCtx.
Definition CaseCtxC e1 e2   : ectx_item := CaseCtx e1 e2.
Definition AllocCtxC        : ectx_item := AllocCtx.
Definition LoadCtxC         : ectx_item := LoadCtx.
Definition StoreLCtxC v2    : ectx_item := StoreLCtx v2.
Definition StoreRCtxC e1    : ectx_item := StoreRCtx e1.
Definition AllocTapeCtxC    : ectx_item := AllocTapeCtx.
Definition RandLCtxC v2     : ectx_item := RandLCtx v2.
Definition RandRCtxC e1     : ectx_item := RandRCtx e1.
Definition URandCtxC        : ectx_item := URandCtx.
Definition TickCtxC         : ectx_item := TickCtx.

(** Constructors into the measurableType, uncurried *)
Definition AppLCtxU (v : val)                         := AppLCtxC v.
Definition AppRCtxU (v : expr)                        := AppRCtxC v.
Definition UnOpCtxU (v : <<discr un_op>>)             := UnOpCtxC v.
Definition BinOpLCtxU (v : <<discr bin_op>> * val)    := BinOpLCtxC v.1 v.2.
Definition BinOpRCtxU (v : <<discr bin_op>> * expr)   := BinOpRCtxC v.1 v.2.
Definition IfCtxU (v : expr * expr)                   := IfCtxC v.1 v.2.
Definition PairLCtxU (v : val)                        := PairLCtxC v.
Definition PairRCtxU (v : expr)                       := PairRCtxC v.
Definition FstCtxU                                    := FstCtxC.
Definition SndCtxU                                    := SndCtxC.
Definition InjLCtxU                                   := InjLCtxC.
Definition InjRCtxU                                   := InjRCtxC.
Definition CaseCtxU (v : expr * expr)                 := CaseCtxC v.1 v.2.
Definition AllocCtxU                                  := AllocCtxC.
Definition LoadCtxU                                   := LoadCtxC.
Definition StoreLCtxU (v : val)                       := StoreLCtxC v.
Definition StoreRCtxU (v : expr)                      := StoreRCtxC v.
Definition AllocTapeCtxU                              := AllocTapeCtxC.
Definition RandLCtxU (v : val)                        := RandLCtxC v.
Definition RandRCtxU (v : expr)                       := RandRCtxC v.
Definition URandCtxU                                  := URandCtxC.
Definition TickCtxU                                   := TickCtxC.


Section ConstructorMeasurable.

  Lemma AppLCtxU_measurable : measurable_fun setT AppLCtxU.
  Proof. Admitted.
  Hint Resolve AppLCtxU_measurable : measlang.

  Lemma AppRCtxU_measurable : measurable_fun setT AppRCtxU.
  Proof. Admitted.
  Hint Resolve AppRCtxU_measurable : measlang.

  Lemma UnOpCtxU_measurable : measurable_fun setT UnOpCtxU.
  Proof. Admitted.
  Hint Resolve UnOpCtxU_measurable : measlang.

  Lemma BinOpLCtxU_measurable : measurable_fun setT BinOpLCtxU.
  Proof. Admitted.
  Hint Resolve BinOpLCtxU_measurable : measlang.

  Lemma BinOpRCtxU_measurable : measurable_fun setT BinOpRCtxU.
  Proof. Admitted.
  Hint Resolve BinOpRCtxU_measurable : measlang.

  Lemma IfCtxU_measurable : measurable_fun setT IfCtxU.
  Proof. Admitted.
  Hint Resolve IfCtxU_measurable : measlang.

  Lemma PairLCtxU_measurable : measurable_fun setT PairLCtxU.
  Proof. Admitted.
  Hint Resolve PairLCtxU_measurable : measlang.

  Lemma PairRCtxU_measurable : measurable_fun setT PairRCtxU.
  Proof. Admitted.
  Hint Resolve PairRCtxU_measurable : measlang.

  Lemma CaseCtxU_measurable : measurable_fun setT CaseCtxU.
  Proof. Admitted.
  Hint Resolve CaseCtxU_measurable : measlang.

  Lemma StoreLCtxU_measurable : measurable_fun setT StoreLCtxU.
  Proof. Admitted.
  Hint Resolve StoreLCtxU_measurable : measlang.

  Lemma StoreRCtxU_measurable : measurable_fun setT StoreRCtxU.
  Proof. Admitted.
  Hint Resolve StoreRCtxU_measurable : measlang.

  Lemma RandLCtxU_measurable : measurable_fun setT RandLCtxU.
  Proof. Admitted.
  Hint Resolve RandLCtxU_measurable : measlang.

  Lemma RandRCtxU_measurable : measurable_fun setT RandRCtxU.
  Proof. Admitted.
  Hint Resolve RandRCtxU_measurable : measlang.

  Hint Resolve AppLCtxU_measurable   : mf_fun.
  Hint Resolve AppRCtxU_measurable   : mf_fun.
  Hint Resolve UnOpCtxU_measurable   : mf_fun.
  Hint Resolve BinOpLCtxU_measurable : mf_fun.
  Hint Resolve BinOpRCtxU_measurable : mf_fun.
  Hint Resolve IfCtxU_measurable     : mf_fun.
  Hint Resolve PairLCtxU_measurable  : mf_fun.
  Hint Resolve PairRCtxU_measurable  : mf_fun.
  Hint Resolve CaseCtxU_measurable   : mf_fun.
  Hint Resolve StoreLCtxU_measurable : mf_fun.
  Hint Resolve StoreRCtxU_measurable : mf_fun.
  Hint Resolve RandLCtxU_measurable  : mf_fun.
  Hint Resolve RandRCtxU_measurable  : mf_fun.

End ConstructorMeasurable.



Section Shapes.

Definition ectx_item_shape : Type := @ectx_item_pre () () () ().

Definition shape_ectx_item {T1 T2 T3 T4} : @ectx_item_pre T1 T2 T3 T4 -> ectx_item_shape :=
 ectx_item_pre_F (cst ()) (cst ()) (cst ()) (cst ()) (cst ()).

Definition gen_ectx_item : ectx_item_shape -> ectx_item_S :=
 ectx_item_pre_F (cst setT) (cst setT) (cst setT) (cst setT) (cst setT).

Lemma ectx_item_generator s : ectx_item_ML (gen_ectx_item s).
Proof.
  rewrite /ectx_item_ML/gen_ectx_item/ectx_item_pre_F.
  destruct s; try done.
  (* Apply the val and expr generator lemmas *)
Admitted.


Lemma ectx_item_shape_cyl (s : ectx_item_shape) : [set e | shape_ectx_item e = s] = ectx_item_ST (gen_ectx_item s).
Proof. Admitted.

Fixpoint ectx_item_shape_encode (e: ectx_item_shape):=
  match e with
  | AppLCtx v2 => GenNode 0 [val_shape_encode v2]
  | AppRCtx e1 => GenNode 1 [expr_shape_encode e1]
  | UnOpCtx op => GenNode 2 [GenLeaf (inr (inr (inl op)))]
  | BinOpLCtx op v2 => GenNode 3 [GenLeaf (inr (inr (inr op))); val_shape_encode v2] 
  | BinOpRCtx op e1 => GenNode 4 [GenLeaf (inr (inr (inr op))); expr_shape_encode e1]
  | IfCtx e1 e2 => GenNode 5 [expr_shape_encode e1; expr_shape_encode e2]
  | PairLCtx v2 => GenNode 6 [val_shape_encode v2]
  | PairRCtx e1 => GenNode 7 [expr_shape_encode e1]
  | FstCtx => GenNode 8 []
  | SndCtx => GenNode 9 []
  | InjLCtx => GenNode 10 []
  | InjRCtx => GenNode 11 []
  | CaseCtx e1 e2 => GenNode 12 [expr_shape_encode e1; expr_shape_encode e2]
  | AllocCtx => GenNode 13 []
  | LoadCtx => GenNode 14 []
  | StoreLCtx v2 => GenNode 15 [val_shape_encode v2]
  | StoreRCtx e1 => GenNode 16 [expr_shape_encode e1]
  | AllocTapeCtx => GenNode 17 []
  | RandLCtx v2 => GenNode 18 [val_shape_encode v2]
  | RandRCtx e1 => GenNode 19 [expr_shape_encode e1]
  | URandCtx => GenNode 20 []
  | TickCtx => GenNode 21 []
  end.

Fixpoint ectx_item_shape_decode t : ectx_item_shape :=
  match t with
    | GenNode 0 [v]=> AppLCtx (val_shape_decode v)
    | GenNode 1 [e1]=> AppRCtx (expr_shape_decode e1)
    | GenNode 2 [GenLeaf (inr (inr (inl op)))]=> UnOpCtx op
    | GenNode 3 [GenLeaf (inr (inr (inr op))); v]=> BinOpLCtx op (val_shape_decode v)
    | GenNode 4 [GenLeaf (inr (inr (inr op))); e]=> BinOpRCtx op (expr_shape_decode e)
    | GenNode 5 [e1; e2]=> IfCtx (expr_shape_decode e1) (expr_shape_decode e2)
    | GenNode 6 [v2]=>  PairLCtx (val_shape_decode v2)
    | GenNode 7 [e1 ]=> PairRCtx (expr_shape_decode e1)
    | GenNode 8 []=>  FstCtx
    | GenNode 9 []=> SndCtx
    | GenNode 10 []=> InjLCtx
    | GenNode 11 []=> InjRCtx
    | GenNode 12 [e1; e2]=> CaseCtx (expr_shape_decode e1) (expr_shape_decode e2)
    | GenNode 13 []=> AllocCtx
    | GenNode 14 []=>  LoadCtx
    | GenNode 15 [v2]=> StoreLCtx (val_shape_decode v2)
    | GenNode 16 [e1]=> StoreRCtx (expr_shape_decode e1)
    | GenNode 17 []=> AllocTapeCtx
    | GenNode 18 [v2]=> RandLCtx (val_shape_decode v2)
    | GenNode 19 [e1]=> RandRCtx (expr_shape_decode e1)
    | GenNode 20 []=>  URandCtx
    | GenNode 21 []=> TickCtx
    | _ => (* random one*)  AllocTapeCtx
  end.

Lemma ectx_item_shape_decode_encode e: ectx_item_shape_decode(ectx_item_shape_encode e) = e.
Proof.
  revert e.
  fix FIX 1.
  Local Opaque val_shape_encode.
  rewrite /ectx_item_shape_decode/ectx_item_shape_encode.
  intros [| | | | | | | | | | | | | | | | | | | | |]; simpl; try rewrite val_shape_decode_encode; try rewrite !expr_shape_decode_encode; done.
Qed.

Definition ectx_item_shape_enum (n : nat) : ectx_item_shape :=
  match decode_nat n with
  | Some t => ectx_item_shape_decode t
  | None => AllocTapeCtx
  end.

Lemma ectx_item_shape_enum_surj (e : ectx_item_shape) : exists n, ectx_item_shape_enum n = e.
Proof.
  exists (encode_nat $ ectx_item_shape_encode $ e).
  rewrite /ectx_item_shape_enum.
  by rewrite decode_encode_nat ectx_item_shape_decode_encode.
Qed.

Definition ectx_item_seq : sequences.sequence (set ectx_item) :=
  fun n => shape_ectx_item @^-1` [set ectx_item_shape_enum n].

Lemma ectx_item_shape_decompT: (\bigcup_n ectx_item_seq n) = setT.
Proof.
  rewrite <- subTset => e He.
  case (ectx_item_shape_enum_surj (shape_ectx_item e)) as [n Hn].
  exists n; [done|].
  by rewrite /ectx_item_seq Hn //=.
Qed.

Lemma ectx_item_shape_decomp S : (\bigcup_n (S `&` ectx_item_seq n)) = S.
Proof. by rewrite <- setI_bigcupr, ectx_item_shape_decompT, setIT. Qed.

End Shapes.


Section Projections.

Definition 𝜋_AppLCtx_v      (k : ectx_item) : val := match k with | AppLCtx v => v | _ => point end.
Definition 𝜋_AppRCtx_e      (k : ectx_item) : expr := match k with | AppRCtx v => v | _ => point end.
Definition 𝜋_UnOpCtx_op     (k : ectx_item) : <<discr un_op>> := match k with | UnOpCtx v => v | _ => point end.
Definition 𝜋_BinOpLCtx_op   (k : ectx_item) : <<discr bin_op>>:= match k with | BinOpLCtx v _ => v | _ => point end.
Definition 𝜋_BinOpLCtx_v    (k : ectx_item) : val := match k with | BinOpLCtx _ v => v | _ => point end.
Definition 𝜋_BinOpRCtx_op   (k : ectx_item) : <<discr bin_op>>:= match k with | BinOpRCtx v _ => v | _ => point end.
Definition 𝜋_BinOpRCtx_e    (k : ectx_item) : expr := match k with | BinOpRCtx _ v => v | _ => point end.
Definition 𝜋_IfCtx_l        (k : ectx_item) : expr := match k with | IfCtx v _ => v | _ => point end.
Definition 𝜋_IfCtx_r        (k : ectx_item) : expr := match k with | IfCtx _ v => v | _ => point end.
Definition 𝜋_PairLCtx_v     (k : ectx_item) : val := match k with | PairLCtx v => v | _ => point end.
Definition 𝜋_PairRCtx_e     (k : ectx_item) : expr := match k with | PairRCtx v => v | _ => point end.
Definition 𝜋_CaseCtx_l      (k : ectx_item) : expr := match k with | CaseCtx v _ => v | _ => point end.
Definition 𝜋_CaseCtx_r      (k : ectx_item) : expr := match k with | CaseCtx _ v => v | _ => point end.
Definition 𝜋_StoreLCtx_v    (k : ectx_item) : val := match k with | StoreLCtx v => v | _ => point end.
Definition 𝜋_StoreRCtx_e    (k : ectx_item) : expr := match k with | StoreRCtx v => v | _ => point end.
Definition 𝜋_RandLCtx_v     (k : ectx_item) : val := match k with | RandLCtx v => v | _ => point end.
Definition 𝜋_RandRCtx_e     (k : ectx_item) : expr := match k with | RandRCtx v => v | _ => point end.

End Projections.


Section Cover.

Definition ectx_item_cov_AppLCtx      : set ectx_item := image setT AppLCtxU.
Definition ectx_item_cov_AppRCtx      : set ectx_item := image setT AppLCtxU.
Definition ectx_item_cov_UnOpCtx      : set ectx_item := image setT UnOpCtxU.
Definition ectx_item_cov_BinOpLCtx    : set ectx_item := image setT BinOpLCtxU.
Definition ectx_item_cov_BinOpRCtx    : set ectx_item := image setT BinOpRCtxU.
Definition ectx_item_cov_IfCtx        : set ectx_item := image setT IfCtxU.
Definition ectx_item_cov_PairLCtx     : set ectx_item := image setT PairLCtxU.
Definition ectx_item_cov_PairRCtx     : set ectx_item := image setT PairRCtxU.
Definition ectx_item_cov_FstCtx       : set ectx_item := [set FstCtx].
Definition ectx_item_cov_SndCtx       : set ectx_item := [set SndCtx].
Definition ectx_item_cov_InjLCtx      : set ectx_item := [set InjLCtx].
Definition ectx_item_cov_InjRCtx      : set ectx_item := [set InjRCtx].
Definition ectx_item_cov_CaseCtx      : set ectx_item := image setT CaseCtxU.
Definition ectx_item_cov_AllocCtx     : set ectx_item := [set AllocCtx].
Definition ectx_item_cov_LoadCtx      : set ectx_item := [set LoadCtx].
Definition ectx_item_cov_StoreLCtx    : set ectx_item := image setT StoreLCtx.
Definition ectx_item_cov_StoreRCtx    : set ectx_item := image setT StoreRCtx.
Definition ectx_item_cov_AllocTapeCtx : set ectx_item := [set AllocTapeCtx].
Definition ectx_item_cov_RandLCtx     : set ectx_item := image setT RandLCtxU.
Definition ectx_item_cov_RandRCtx     : set ectx_item := image setT RandRCtxU.
Definition ectx_item_cov_URandCtx     : set ectx_item := [set URandCtx].
Definition ectx_item_cov_TickCtx      : set ectx_item := [set TickCtx].


Lemma ectx_item_cov_AppLCtx_meas      : measurable ectx_item_cov_AppLCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_AppLCtx_meas      : measlang.

Lemma ectx_item_cov_AppRCtx_meas      : measurable ectx_item_cov_AppRCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_AppRCtx_meas      : measlang.

Lemma ectx_item_cov_UnOpCtx_meas      : measurable ectx_item_cov_UnOpCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_UnOpCtx_meas      : measlang.

Lemma ectx_item_cov_BinOpLCtx_meas    : measurable ectx_item_cov_BinOpLCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_BinOpLCtx_meas    : measlang.

Lemma ectx_item_cov_BinOpRCtx_meas    : measurable ectx_item_cov_BinOpRCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_BinOpRCtx_meas    : measlang.

Lemma ectx_item_cov_IfCtx_meas        : measurable ectx_item_cov_IfCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_IfCtx_meas        : measlang.

Lemma ectx_item_cov_PairLCtx_meas     : measurable ectx_item_cov_PairLCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_PairLCtx_meas     : measlang.

Lemma ectx_item_cov_PairRCtx_meas     : measurable ectx_item_cov_PairRCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_PairRCtx_meas     : measlang.

Lemma ectx_item_cov_FstCtx_meas       : measurable ectx_item_cov_FstCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_FstCtx_meas       : measlang.

Lemma ectx_item_cov_SndCtx_meas       : measurable ectx_item_cov_SndCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_SndCtx_meas       : measlang.

Lemma ectx_item_cov_InjLCtx_meas      : measurable ectx_item_cov_InjLCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_InjLCtx_meas      : measlang.

Lemma ectx_item_cov_InjRCtx_meas      : measurable ectx_item_cov_InjRCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_InjRCtx_meas      : measlang.

Lemma ectx_item_cov_CaseCtx_meas      : measurable ectx_item_cov_CaseCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_CaseCtx_meas      : measlang.

Lemma ectx_item_cov_AllocCtx_meas     : measurable ectx_item_cov_AllocCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_AllocCtx_meas   : measlang.

Lemma ectx_item_cov_LoadCtx_meas      : measurable ectx_item_cov_LoadCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_LoadCtx_meas      : measlang.

Lemma ectx_item_cov_StoreLCtx_meas    : measurable ectx_item_cov_StoreLCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_StoreLCtx_meas    : measlang.

Lemma ectx_item_cov_StoreRCtx_meas    : measurable ectx_item_cov_StoreRCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_StoreRCtx_meas    : measlang.

Lemma ectx_item_cov_AllocTapeCtx_meas : measurable ectx_item_cov_AllocTapeCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_AllocTapeCtx_meas : measlang.

Lemma ectx_item_cov_RandLCtx_meas     : measurable ectx_item_cov_RandLCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_RandLCtx_meas     : measlang.

Lemma ectx_item_cov_RandRCtx_meas     : measurable ectx_item_cov_RandRCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_RandRCtx_meas     : measlang.

Lemma ectx_item_cov_URandCtx_meas     : measurable ectx_item_cov_URandCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_URandCtx_meas     : measlang.

Lemma ectx_item_cov_TickCtx_meas      : measurable ectx_item_cov_TickCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_TickCtx_meas      : measlang.


Hint Resolve ectx_item_cov_AppLCtx_meas      : mf_set.
Hint Resolve ectx_item_cov_AppRCtx_meas      : mf_set.
Hint Resolve ectx_item_cov_UnOpCtx_meas      : mf_set.
Hint Resolve ectx_item_cov_BinOpLCtx_meas    : mf_set.
Hint Resolve ectx_item_cov_BinOpRCtx_meas    : mf_set.
Hint Resolve ectx_item_cov_IfCtx_meas        : mf_set.
Hint Resolve ectx_item_cov_PairLCtx_meas     : mf_set.
Hint Resolve ectx_item_cov_PairRCtx_meas     : mf_set.
Hint Resolve ectx_item_cov_FstCtx_meas       : mf_set.
Hint Resolve ectx_item_cov_SndCtx_meas       : mf_set.
Hint Resolve ectx_item_cov_InjLCtx_meas      : mf_set.
Hint Resolve ectx_item_cov_InjRCtx_meas      : mf_set.
Hint Resolve ectx_item_cov_CaseCtx_meas      : mf_set.
Hint Resolve ectx_item_cov_AllocCtx_meas     : mf_set.
Hint Resolve ectx_item_cov_LoadCtx_meas      : mf_set.
Hint Resolve ectx_item_cov_StoreLCtx_meas    : mf_set.
Hint Resolve ectx_item_cov_StoreRCtx_meas    : mf_set.
Hint Resolve ectx_item_cov_AllocTapeCtx_meas : mf_set.
Hint Resolve ectx_item_cov_RandLCtx_meas     : mf_set.
Hint Resolve ectx_item_cov_RandRCtx_meas     : mf_set.
Hint Resolve ectx_item_cov_URandCtx_meas     : mf_set.
Hint Resolve ectx_item_cov_TickCtx_meas      : mf_set.

End Cover.


Section Projection_measurability.

Lemma 𝜋_AppLCtx_v_meas    : measurable_fun ectx_item_cov_AppLCtx 𝜋_AppLCtx_v.
Proof. Admitted.
Hint Resolve 𝜋_AppLCtx_v_meas    : measlang.

Lemma 𝜋_AppRCtx_e_meas    : measurable_fun ectx_item_cov_AppRCtx 𝜋_AppRCtx_e.
Proof. Admitted.
Hint Resolve 𝜋_AppRCtx_e_meas    : measlang.

Lemma 𝜋_UnOpCtx_op_meas   : measurable_fun ectx_item_cov_UnOpCtx 𝜋_UnOpCtx_op.
Proof. Admitted.
Hint Resolve 𝜋_UnOpCtx_op_meas   : measlang.

Lemma 𝜋_BinOpLCtx_op_meas : measurable_fun ectx_item_cov_BinOpLCtx 𝜋_BinOpLCtx_op.
Proof. Admitted.
Hint Resolve 𝜋_BinOpLCtx_op_meas : measlang.

Lemma 𝜋_BinOpLCtx_v_meas  : measurable_fun ectx_item_cov_BinOpLCtx 𝜋_BinOpLCtx_v.
Proof. Admitted.
Hint Resolve 𝜋_BinOpLCtx_v_meas  : measlang.

Lemma 𝜋_BinOpRCtx_op_meas : measurable_fun ectx_item_cov_BinOpRCtx 𝜋_BinOpRCtx_op.
Proof. Admitted.
Hint Resolve 𝜋_BinOpRCtx_op_meas : measlang.

Lemma 𝜋_BinOpRCtx_e_meas  : measurable_fun ectx_item_cov_BinOpRCtx 𝜋_BinOpRCtx_e.
Proof. Admitted.
Hint Resolve 𝜋_BinOpRCtx_e_meas  : measlang.

Lemma 𝜋_IfCtx_l_meas      : measurable_fun ectx_item_cov_IfCtx 𝜋_IfCtx_l.
Proof. Admitted.
Hint Resolve 𝜋_IfCtx_l_meas      : measlang.

Lemma 𝜋_IfCtx_r_meas      : measurable_fun ectx_item_cov_IfCtx 𝜋_IfCtx_l.
Proof. Admitted.
Hint Resolve 𝜋_IfCtx_r_meas      : measlang.

Lemma 𝜋_PairLCtx_v_meas   : measurable_fun ectx_item_cov_PairLCtx 𝜋_PairLCtx_v.
Proof. Admitted.
Hint Resolve 𝜋_PairLCtx_v_meas   : measlang.

Lemma 𝜋_PairRCtx_e_meas   : measurable_fun ectx_item_cov_PairRCtx 𝜋_PairRCtx_e.
Proof. Admitted.
Hint Resolve 𝜋_PairRCtx_e_meas   : measlang.

Lemma 𝜋_CaseCtx_l_meas    : measurable_fun ectx_item_cov_CaseCtx 𝜋_CaseCtx_l.
Proof. Admitted.
Hint Resolve 𝜋_CaseCtx_l_meas    : measlang.

Lemma 𝜋_CaseCtx_r_meas    : measurable_fun ectx_item_cov_CaseCtx 𝜋_CaseCtx_r.
Proof. Admitted.
Hint Resolve 𝜋_CaseCtx_r_meas    : measlang.

Lemma 𝜋_StoreLCtx_v_meas  : measurable_fun ectx_item_cov_StoreLCtx 𝜋_StoreLCtx_v.
Proof. Admitted.
Hint Resolve 𝜋_StoreLCtx_v_meas  : measlang.

Lemma 𝜋_StoreRCtx_e_meas  : measurable_fun ectx_item_cov_StoreRCtx 𝜋_StoreRCtx_e.
Proof. Admitted.
Hint Resolve 𝜋_StoreRCtx_e_meas  : measlang.

Lemma 𝜋_RandLCtx_v_meas   : measurable_fun ectx_item_cov_RandLCtx 𝜋_RandLCtx_v.
Proof. Admitted.
Hint Resolve 𝜋_RandLCtx_v_meas   : measlang.

Lemma 𝜋_RandRCtx_e_meas   : measurable_fun ectx_item_cov_RandRCtx 𝜋_RandRCtx_e.
Proof. Admitted.
Hint Resolve 𝜋_RandRCtx_e_meas   : measlang.

Hint Resolve 𝜋_AppLCtx_v_meas    : mf_fun.
Hint Resolve 𝜋_AppRCtx_e_meas    : mf_fun.
Hint Resolve 𝜋_UnOpCtx_op_meas   : mf_fun.
Hint Resolve 𝜋_BinOpLCtx_op_meas : mf_fun.
Hint Resolve 𝜋_BinOpLCtx_v_meas  : mf_fun.
Hint Resolve 𝜋_BinOpRCtx_op_meas : mf_fun.
Hint Resolve 𝜋_BinOpRCtx_e_meas  : mf_fun.
Hint Resolve 𝜋_IfCtx_l_meas      : mf_fun.
Hint Resolve 𝜋_IfCtx_r_meas      : mf_fun.
Hint Resolve 𝜋_PairLCtx_v_meas   : mf_fun.
Hint Resolve 𝜋_PairRCtx_e_meas   : mf_fun.
Hint Resolve 𝜋_CaseCtx_l_meas    : mf_fun.
Hint Resolve 𝜋_CaseCtx_r_meas    : mf_fun.
Hint Resolve 𝜋_StoreLCtx_v_meas  : mf_fun.
Hint Resolve 𝜋_StoreRCtx_e_meas  : mf_fun.
Hint Resolve 𝜋_RandLCtx_v_meas   : mf_fun.
Hint Resolve 𝜋_RandRCtx_e_meas   : mf_fun.

End Projection_measurability.

Definition fill_item (x : (ectx_item * expr)%type) : expr :=
  let (Ki, e) := x in
  match x.1 with
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
  | RandLCtx v2 => Rand e (Val v2)
  | RandRCtx e1 => Rand e1 e
  | URandCtx => URand e
  | TickCtx => Tick e
  end.


Definition fill_item_AppLCtx      : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp AppU $
  mProd snd (ssrfun.comp ValU $ ssrfun.comp 𝜋_AppLCtx_v $ fst).

Definition fill_item_AppRCtx      : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp AppU $
  mProd (ssrfun.comp 𝜋_AppRCtx_e fst) snd.

Definition fill_item_UnOpCtx      : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp UnOpU $
  mProd (ssrfun.comp 𝜋_UnOpCtx_op fst) snd.

 Definition fill_item_BinOpLCtx    : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp BinOpU $
  mProd
    (mProd
      (ssrfun.comp 𝜋_BinOpLCtx_op $ fst)
      snd)
    (ssrfun.comp ValU $ ssrfun.comp 𝜋_BinOpLCtx_v $ fst).

Definition fill_item_BinOpRCtx    : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp BinOpU $
  mProd
    (mProd
      (ssrfun.comp 𝜋_BinOpLCtx_op $ fst)
      (ssrfun.comp 𝜋_BinOpRCtx_e $ fst))
    snd.

Definition fill_item_IfCtx        : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp IfU $
  mProd (mProd snd (ssrfun.comp 𝜋_IfCtx_l fst)) (ssrfun.comp 𝜋_IfCtx_r fst).

Definition fill_item_PairLCtx     : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp PairU $
  mProd
    snd
    (ssrfun.comp ValU $ ssrfun.comp 𝜋_PairLCtx_v $ fst).

Definition fill_item_PairRCtx     : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp PairU $
  mProd
    (ssrfun.comp 𝜋_PairRCtx_e $ fst)
    snd.

Definition fill_item_FstCtx       : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp FstU snd.

Definition fill_item_SndCtx       : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp SndU snd.

Definition fill_item_InjLCtx      : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp InjLU snd.

Definition fill_item_InjRCtx      : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp InjRU snd.

Definition fill_item_CaseCtx      : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp CaseU $
  mProd (mProd snd (ssrfun.comp 𝜋_CaseCtx_l fst)) (ssrfun.comp 𝜋_CaseCtx_r fst).

Definition fill_item_AllocCtx     : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp AllocU $ snd.

Definition fill_item_LoadCtx      : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp LoadU $ snd.

Definition fill_item_StoreLCtx    : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp StoreU $
  mProd
    snd
    (ssrfun.comp ValU $ ssrfun.comp 𝜋_StoreLCtx_v $ fst).

Definition fill_item_StoreRCtx    : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp StoreU $
  mProd
    (ssrfun.comp 𝜋_StoreRCtx_e $ fst)
    snd.

Definition fill_item_AllocTapeCtx : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp AllocTapeU $ snd.

Definition fill_item_RandLCtx     : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp RandU $
  mProd
    snd
    (ssrfun.comp ValU $ ssrfun.comp 𝜋_RandLCtx_v $ fst).

Definition fill_item_RandRCtx     : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp RandU $
  mProd
    (ssrfun.comp 𝜋_RandRCtx_e $ fst)
    snd.

Definition fill_item_URandCtx     : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp UrandU $ snd.

Definition fill_item_TickCtx      : (ectx_item  * expr)%type -> expr :=
  ssrfun.comp TickU $ snd.

Lemma fill_item_AppLCtx_meas      : measurable_fun (setX ectx_item_cov_AppLCtx      setT) fill_item_AppLCtx.
Proof. Admitted.
Lemma fill_item_AppRCtx_meas      : measurable_fun (setX ectx_item_cov_AppRCtx      setT) fill_item_AppRCtx.
Proof. Admitted.
Lemma fill_item_UnOpCtx_meas      : measurable_fun (setX ectx_item_cov_UnOpCtx      setT) fill_item_UnOpCtx.
Proof. Admitted.
Lemma fill_item_BinOpLCtx_meas    : measurable_fun (setX ectx_item_cov_BinOpLCtx    setT) fill_item_BinOpLCtx.
Proof. Admitted.
Lemma fill_item_BinOpRCtx_meas    : measurable_fun (setX ectx_item_cov_BinOpRCtx    setT) fill_item_BinOpRCtx.
Proof. Admitted.
Lemma fill_item_IfCtx_meas        : measurable_fun (setX ectx_item_cov_IfCtx        setT) fill_item_IfCtx.
Proof. Admitted.
Lemma fill_item_PairLCtx_meas     : measurable_fun (setX ectx_item_cov_PairLCtx     setT) fill_item_PairLCtx.
Proof. Admitted.
Lemma fill_item_PairRCtx_meas     : measurable_fun (setX ectx_item_cov_PairRCtx     setT) fill_item_PairRCtx.
Proof. Admitted.
Lemma fill_item_FstCtx_meas       : measurable_fun (setX ectx_item_cov_FstCtx       setT) fill_item_FstCtx.
Proof. Admitted.
Lemma fill_item_SndCtx_meas       : measurable_fun (setX ectx_item_cov_SndCtx       setT) fill_item_SndCtx.
Proof. Admitted.
Lemma fill_item_InjLCtx_meas      : measurable_fun (setX ectx_item_cov_InjLCtx      setT) fill_item_InjLCtx.
Proof. Admitted.
Lemma fill_item_InjRCtx_meas      : measurable_fun (setX ectx_item_cov_InjRCtx      setT) fill_item_InjRCtx.
Proof. Admitted.
Lemma fill_item_CaseCtx_meas      : measurable_fun (setX ectx_item_cov_CaseCtx      setT) fill_item_CaseCtx.
Proof. Admitted.
Lemma fill_item_AllocCtx_meas     : measurable_fun (setX ectx_item_cov_AllocCtx   setT) fill_item_AllocCtx.
Proof. Admitted.
Lemma fill_item_LoadCtx_meas      : measurable_fun (setX ectx_item_cov_LoadCtx      setT) fill_item_LoadCtx.
Proof. Admitted.
Lemma fill_item_StoreLCtx_meas    : measurable_fun (setX ectx_item_cov_StoreLCtx    setT) fill_item_StoreLCtx.
Proof. Admitted.
Lemma fill_item_StoreRCtx_meas    : measurable_fun (setX ectx_item_cov_StoreRCtx    setT) fill_item_StoreRCtx.
Proof. Admitted.
Lemma fill_item_AllocTapeCtx_meas : measurable_fun (setX ectx_item_cov_AllocTapeCtx setT) fill_item_AllocTapeCtx.
Proof. Admitted.
Lemma fill_item_RandLCtx_meas     : measurable_fun (setX ectx_item_cov_RandLCtx     setT) fill_item_RandLCtx.
Proof. Admitted.
Lemma fill_item_RandRCtx_meas     : measurable_fun (setX ectx_item_cov_RandRCtx     setT) fill_item_RandRCtx.
Proof. Admitted.
Lemma fill_item_URandCtx_meas     : measurable_fun (setX ectx_item_cov_URandCtx     setT) fill_item_URandCtx.
Proof. Admitted.
Lemma fill_item_TickCtx_meas      : measurable_fun (setX ectx_item_cov_TickCtx      setT) fill_item_TickCtx.
Proof. Admitted.

Hint Resolve fill_item_AppLCtx_meas      : mf_fun.
Hint Resolve fill_item_AppRCtx_meas      : mf_fun.
Hint Resolve fill_item_UnOpCtx_meas      : mf_fun.
Hint Resolve fill_item_BinOpLCtx_meas    : mf_fun.
Hint Resolve fill_item_BinOpRCtx_meas    : mf_fun.
Hint Resolve fill_item_IfCtx_meas        : mf_fun.
Hint Resolve fill_item_PairLCtx_meas     : mf_fun.
Hint Resolve fill_item_PairRCtx_meas     : mf_fun.
Hint Resolve fill_item_FstCtx_meas       : mf_fun.
Hint Resolve fill_item_SndCtx_meas       : mf_fun.
Hint Resolve fill_item_InjLCtx_meas      : mf_fun.
Hint Resolve fill_item_InjRCtx_meas      : mf_fun.
Hint Resolve fill_item_CaseCtx_meas      : mf_fun.
Hint Resolve fill_item_AllocCtx_meas     : mf_fun.
Hint Resolve fill_item_LoadCtx_meas      : mf_fun.
Hint Resolve fill_item_StoreLCtx_meas    : mf_fun.
Hint Resolve fill_item_StoreRCtx_meas    : mf_fun.
Hint Resolve fill_item_AllocTapeCtx_meas : mf_fun.
Hint Resolve fill_item_RandLCtx_meas     : mf_fun.
Hint Resolve fill_item_RandRCtx_meas     : mf_fun.
Hint Resolve fill_item_URandCtx_meas     : mf_fun.
Hint Resolve fill_item_TickCtx_meas      : mf_fun.

Definition fill_item' (x : (ectx_item * expr)%type) : expr :=
  match x.1 with
  | AppLCtx v2      => fill_item_AppLCtx x
  | AppRCtx e1      => fill_item_AppRCtx x
  | UnOpCtx op      => fill_item_UnOpCtx x
  | BinOpLCtx op v2 => fill_item_BinOpLCtx x
  | BinOpRCtx op e1 => fill_item_BinOpRCtx x
  | IfCtx e1 e2     => fill_item_IfCtx x
  | PairLCtx v2     => fill_item_PairLCtx x
  | PairRCtx e1     => fill_item_PairRCtx x
  | FstCtx          => fill_item_FstCtx x
  | SndCtx          => fill_item_SndCtx x
  | InjLCtx         => fill_item_InjLCtx x
  | InjRCtx         => fill_item_InjRCtx x
  | CaseCtx e1 e2   => fill_item_CaseCtx x
  | AllocCtx        => fill_item_AllocCtx x
  | LoadCtx         => fill_item_LoadCtx x
  | StoreLCtx v2    => fill_item_StoreLCtx x
  | StoreRCtx e1    => fill_item_StoreRCtx x
  | AllocTapeCtx    => fill_item_AllocTapeCtx x
  | RandLCtx v2     => fill_item_RandLCtx x
  | RandRCtx e1     => fill_item_RandRCtx x
  | URandCtx        => fill_item_URandCtx x
  | TickCtx         => fill_item_TickCtx x
  end.


Lemma fill_item'_meas_fun : measurable_fun setT fill_item'. Admitted.

Lemma fill_item_fill_item'_eq : fill_item' = fill_item. Admitted.

Lemma fill_item_meas_fun : measurable_fun setT fill_item. Admitted.

Definition noval (x : expr * ectx_item) : option (ectx_item * expr)%type :=
  match x.1 with
  | Val _ => None
  | _ => Some (snd x, fst x)
  end.

Lemma noval_measurable : measurable_fun setT noval.
Proof. Admitted.
Hint Resolve noval_measurable : measlang.

Definition decomp_item (e : expr) : option (ectx_item * expr)%type :=
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
  | Alloc e        => noval e AllocCtx
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


Definition decomp_cov_app_val    : set expr :=
  setI ecov_app $
  preimage 𝜋_AppU $
  setX setT ecov_val.

Definition decomp_cov_app_expr   : set expr :=
  setI ecov_app $
  preimage 𝜋_AppU $
  setX setT (~` ecov_val).

Definition decomp_cov_unop       : set expr :=
  ecov_unop.

Definition decomp_cov_binop_val  : set expr :=
  setI ecov_binop $
  preimage 𝜋_BinOpU $
  setX setT ecov_val.

Definition decomp_cov_binop_expr : set expr :=
  setI ecov_binop $
  preimage 𝜋_BinOpU $
  setX setT (~` ecov_val).

Definition decomp_cov_if         : set expr :=
  ecov_if.

Definition decomp_cov_pair_val   : set expr :=
  setI ecov_pair $
  preimage 𝜋_PairU $
  setX setT ecov_val.

Definition decomp_cov_pair_expr  : set expr :=
  setI ecov_pair $
  preimage 𝜋_PairU $
  setX setT (~` ecov_val).

Definition decomp_cov_fst        : set expr :=
  ecov_fst.

Definition decomp_cov_snd        : set expr :=
  ecov_snd.

Definition decomp_cov_injl       : set expr :=
  ecov_injl.

Definition decomp_cov_injr       : set expr :=
  ecov_injr.

Definition decomp_cov_case       : set expr :=
  ecov_case.

Definition decomp_cov_alloc      : set expr :=
  ecov_alloc.

Definition decomp_cov_load       : set expr :=
  ecov_load.

Definition decomp_cov_store_val  : set expr :=
  setI ecov_store $
  preimage 𝜋_StoreU $
  setX setT ecov_val.

Definition decomp_cov_store_expr : set expr :=
  setI ecov_store $
  preimage 𝜋_StoreU $
  setX setT (~` ecov_val).

Definition decomp_cov_alloctape  : set expr :=
  ecov_alloctape.

Definition decomp_cov_rand_val   : set expr :=
  setI ecov_rand $
  preimage 𝜋_RandU $
  setX setT ecov_val.

Definition decomp_cov_rand_expr  : set expr :=
  setI ecov_rand $
  preimage 𝜋_RandU $
  setX setT (~` ecov_val).

Definition decomp_cov_urand      : set expr :=
  ecov_urand.

Definition decomp_cov_tick       : set expr :=
  ecov_tick.

Definition decomp_cov_stuck      : set expr. Admitted. (* Complement of the union of the prior cases.*)

Lemma decomp_cov_app_val_meas     : measurable decomp_cov_app_val. Proof. Admitted.
Lemma decomp_cov_app_expr_meas    : measurable decomp_cov_app_expr. Proof. Admitted.
Lemma decomp_cov_unop_meas        : measurable decomp_cov_unop. Proof. Admitted.
Lemma decomp_cov_binop_val_meas   : measurable decomp_cov_binop_val. Proof. Admitted.
Lemma decomp_cov_binop_expr_meas  : measurable decomp_cov_binop_expr. Proof. Admitted.
Lemma decomp_cov_if_meas          : measurable decomp_cov_if. Proof. Admitted.
Lemma decomp_cov_pair_val_meas    : measurable decomp_cov_pair_val. Proof. Admitted.
Lemma decomp_cov_pair_expr_meas   : measurable decomp_cov_pair_expr. Proof. Admitted.
Lemma decomp_cov_fst_meas         : measurable decomp_cov_fst. Proof. Admitted.
Lemma decomp_cov_snd_meas         : measurable decomp_cov_snd. Proof. Admitted.
Lemma decomp_cov_injl_meas        : measurable decomp_cov_injl. Proof. Admitted.
Lemma decomp_cov_injr_meas        : measurable decomp_cov_injr. Proof. Admitted.
Lemma decomp_cov_case_meas        : measurable decomp_cov_case. Proof. Admitted.
Lemma decomp_cov_alloc_meas       : measurable decomp_cov_alloc. Proof. Admitted.
Lemma decomp_cov_load_meas        : measurable decomp_cov_load. Proof. Admitted.
Lemma decomp_cov_store_val_meas   : measurable decomp_cov_store_val. Proof. Admitted.
Lemma decomp_cov_store_expr_meas  : measurable decomp_cov_store_expr. Proof. Admitted.
Lemma decomp_cov_alloctape_meas   : measurable decomp_cov_alloctape. Proof. Admitted.
Lemma decomp_cov_rand_val_meas    : measurable decomp_cov_rand_val. Proof. Admitted.
Lemma decomp_cov_rand_expr_meas   : measurable decomp_cov_rand_expr. Proof. Admitted.
Lemma decomp_cov_urand_meas       : measurable decomp_cov_urand. Proof. Admitted.
Lemma decomp_cov_tick_meas        : measurable decomp_cov_tick. Proof. Admitted.
Lemma decomp_cov_stuck_meas       : measurable decomp_cov_stuck. Proof. Admitted.

Hint Resolve decomp_cov_app_val_meas     : measlang.
Hint Resolve decomp_cov_app_expr_meas    : measlang.
Hint Resolve decomp_cov_unop_meas        : measlang.
Hint Resolve decomp_cov_binop_val_meas   : measlang.
Hint Resolve decomp_cov_binop_expr_meas  : measlang.
Hint Resolve decomp_cov_if_meas          : measlang.
Hint Resolve decomp_cov_pair_val_meas    : measlang.
Hint Resolve decomp_cov_pair_expr_meas   : measlang.
Hint Resolve decomp_cov_fst_meas         : measlang.
Hint Resolve decomp_cov_snd_meas         : measlang.
Hint Resolve decomp_cov_injl_meas        : measlang.
Hint Resolve decomp_cov_injr_meas        : measlang.
Hint Resolve decomp_cov_case_meas        : measlang.
Hint Resolve decomp_cov_alloc            : measlang.
Hint Resolve decomp_cov_load_meas        : measlang.
Hint Resolve decomp_cov_store_val_meas   : measlang.
Hint Resolve decomp_cov_store_expr_meas  : measlang.
Hint Resolve decomp_cov_alloctape_meas   : measlang.
Hint Resolve decomp_cov_rand_val_meas    : measlang.
Hint Resolve decomp_cov_rand_expr_meas   : measlang.
Hint Resolve decomp_cov_urand_meas       : measlang.
Hint Resolve decomp_cov_tick_meas        : measlang.
Hint Resolve decomp_cov_stuck_meas       : measlang.

Definition decomp_app_val    : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_App_l (ssrfun.comp AppLCtxU $ ssrfun.comp 𝜋_Val_v $ 𝜋_App_r).

Definition decomp_app_expr   : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp Some $
  mProd (ssrfun.comp AppRCtxU 𝜋_App_l) 𝜋_App_r.

Definition decomp_unop       : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_UnOp_e (ssrfun.comp UnOpCtxU 𝜋_UnOp_op).

Definition decomp_binop_val  : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_BinOp_l (ssrfun.comp BinOpLCtxU $ mProd 𝜋_BinOp_op (ssrfun.comp 𝜋_Val_v 𝜋_BinOp_r)).

Definition decomp_binop_expr : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp Some $
  mProd (ssrfun.comp BinOpRCtxU $ mProd 𝜋_BinOp_op 𝜋_BinOp_l) 𝜋_BinOp_r.

Definition decomp_if         : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_If_c (ssrfun.comp IfCtxU $ mProd 𝜋_If_l 𝜋_If_r).

Definition decomp_pair_val   : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_Pair_l (ssrfun.comp PairLCtxU $ 𝜋_Val_v).

Definition decomp_pair_expr  : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp Some $
  mProd (ssrfun.comp PairRCtxU 𝜋_Pair_l) 𝜋_Pair_r.

Definition decomp_fst        : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_Fst_e (cst FstCtxU).

Definition decomp_snd        : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_Snd_e (cst SndCtxU).

Definition decomp_injl       : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_InjL_e (cst InjLCtxU).

Definition decomp_injr       : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_InjR_e (cst InjRCtxU).

Definition decomp_case       : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_Case_c (ssrfun.comp CaseCtxU $ mProd 𝜋_Case_l 𝜋_Case_r).

Definition decomp_alloc     : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_Alloc_e (cst AllocCtxU).

Definition decomp_load       : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_Load_e (cst LoadCtxU).

Definition decomp_store_val  : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_Store_l (ssrfun.comp StoreLCtxU $ ssrfun.comp 𝜋_Val_v 𝜋_Store_e).

Definition decomp_store_expr : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp Some $
  mProd (ssrfun.comp StoreRCtxU 𝜋_Store_l) 𝜋_Store_e.

Definition decomp_alloctape  : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_AllocTape_e (cst AllocTapeCtxU).

Definition decomp_rand_val   : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_Rand_t (ssrfun.comp RandLCtxU $ ssrfun.comp 𝜋_Val_v 𝜋_Rand_N).

Definition decomp_rand_expr  : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp Some $
  mProd (ssrfun.comp RandRCtxU 𝜋_Rand_t) 𝜋_Rand_N.

Definition decomp_urand      : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_URand_e (cst URandCtxU).

Definition decomp_tick       : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_Tick_e (cst TickCtxU).

Definition decomp_stuck      : expr -> (option (ectx_item * expr)%type) :=
  cst None.

Lemma decomp_app_val_meas    : measurable_fun decomp_cov_app_val    decomp_app_val. Proof. Admitted.
Lemma decomp_app_expr_meas   : measurable_fun decomp_cov_app_expr   decomp_app_expr. Proof. Admitted.
Lemma decomp_unop_meas       : measurable_fun decomp_cov_unop       decomp_unop. Proof. Admitted.
Lemma decomp_binop_val_meas  : measurable_fun decomp_cov_binop_val  decomp_binop_val. Proof. Admitted.
Lemma decomp_binop_expr_meas : measurable_fun decomp_cov_binop_expr decomp_binop_expr. Proof. Admitted.
Lemma decomp_if_meas         : measurable_fun decomp_cov_if         decomp_if. Proof. Admitted.
Lemma decomp_pair_val_meas   : measurable_fun decomp_cov_pair_val   decomp_pair_val. Proof. Admitted.
Lemma decomp_pair_expr_meas  : measurable_fun decomp_cov_pair_expr  decomp_pair_expr. Proof. Admitted.
Lemma decomp_fst_meas        : measurable_fun decomp_cov_fst        decomp_fst. Proof. Admitted.
Lemma decomp_snd_meas        : measurable_fun decomp_cov_snd        decomp_snd. Proof. Admitted.
Lemma decomp_injl_meas       : measurable_fun decomp_cov_injl       decomp_injl. Proof. Admitted.
Lemma decomp_injr_meas       : measurable_fun decomp_cov_injr       decomp_injr. Proof. Admitted.
Lemma decomp_case_meas       : measurable_fun decomp_cov_case       decomp_case. Proof. Admitted.
Lemma decomp_alloc_meas      : measurable_fun decomp_cov_alloc      decomp_alloc. Proof. Admitted.
Lemma decomp_load_meas       : measurable_fun decomp_cov_load       decomp_load. Proof. Admitted.
Lemma decomp_store_val_meas  : measurable_fun decomp_cov_store_val  decomp_store_val. Proof. Admitted.
Lemma decomp_store_expr_meas : measurable_fun decomp_cov_store_expr decomp_store_expr. Proof. Admitted.
Lemma decomp_alloctape_meas  : measurable_fun decomp_cov_alloctape  decomp_alloctape. Proof. Admitted.
Lemma decomp_rand_val_meas   : measurable_fun decomp_cov_rand_val   decomp_rand_val. Proof. Admitted.
Lemma decomp_rand_expr_meas  : measurable_fun decomp_cov_rand_expr  decomp_rand_expr. Proof. Admitted.
Lemma decomp_urand_meas      : measurable_fun decomp_cov_urand      decomp_urand. Proof. Admitted.
Lemma decomp_tick_meas       : measurable_fun decomp_cov_tick       decomp_tick. Proof. Admitted.
Lemma decomp_stuck_meas      : measurable_fun decomp_cov_stuck      decomp_stuck. Proof. Admitted.

Hint Resolve decomp_app_val_meas    : measlang.
Hint Resolve decomp_app_expr_meas   : measlang.
Hint Resolve decomp_unop_meas       : measlang.
Hint Resolve decomp_binop_val_meas  : measlang.
Hint Resolve decomp_binop_expr_meas : measlang.
Hint Resolve decomp_if_meas         : measlang.
Hint Resolve decomp_pair_val_meas   : measlang.
Hint Resolve decomp_pair_expr_meas  : measlang.
Hint Resolve decomp_fst_meas        : measlang.
Hint Resolve decomp_snd_meas        : measlang.
Hint Resolve decomp_injl_meas       : measlang.
Hint Resolve decomp_injr_meas       : measlang.
Hint Resolve decomp_case_meas       : measlang.
Hint Resolve decomp_alloc_meas      : measlang.
Hint Resolve decomp_load_meas       : measlang.
Hint Resolve decomp_store_val_meas  : measlang.
Hint Resolve decomp_store_expr_meas : measlang.
Hint Resolve decomp_alloctape_meas  : measlang.
Hint Resolve decomp_rand_val_meas   : measlang.
Hint Resolve decomp_rand_expr_meas  : measlang.
Hint Resolve decomp_urand_meas      : measlang.
Hint Resolve decomp_tick_meas       : measlang.
Hint Resolve decomp_stuck_meas      : measlang.

Definition decomp_item' (e : expr) : option (ectx_item * expr)%type :=
  match e with
  | App _ (Val _)      => decomp_app_val e
  | App _ _            => decomp_app_expr e
  | UnOp _ _           => decomp_unop e
  | BinOp _ _ (Val _)  => decomp_binop_val e
  | BinOp _ _ _        => decomp_binop_expr e
  | If _ _ _           => decomp_if e
  | Pair _ (Val _)     => decomp_pair_val e
  | Pair _ _           => decomp_pair_expr e
  | Fst _              => decomp_fst e
  | Snd _              => decomp_snd e
  | InjL _             => decomp_injl e
  | InjR _             => decomp_injr e
  | Case _ _ _         => decomp_case e
  | Alloc _            => decomp_alloc e
  | Load _             => decomp_load e
  | Store _ (Val _)    => decomp_store_val e
  | Store _ _          => decomp_store_expr e
  | AllocTape _        => decomp_alloctape e
  | Rand _ (Val _)     => decomp_rand_val e
  | Rand _ _           => decomp_rand_expr e
  | URand _            => decomp_urand e
  | Tick _             => decomp_tick e
  | _                  => decomp_stuck e
  end.

Lemma decomp_item'_meas_fun : measurable_fun setT decomp_item'.
Admitted.

Lemma decomp_item_decomp_eq : decomp_item' = decomp_item. Admitted.

Lemma decomp_item_meas_fun : measurable_fun setT decomp_item. Admitted.


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
  | Alloc e1 => 1 + height e1 
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
  to_val e = None → decomp_item (fill_item (Ki, e)) = Some (Ki, e).
Proof. Admitted.
(*  Proof. destruct Ki ; simpl ; by repeat destruct_match. Qed. *)

(* TODO: this proof is slow, but I do not see how to make it faster... *)
(* TODO: Uncomment the slow proof *)
Lemma decomp_fill_item_2 e e' Ki :
  decomp_item e = Some (Ki, e') → fill_item (Ki, e') = e ∧ to_val e' = None.
Proof. Admitted.
(*
  rewrite /decomp_item ;
    destruct e ; try done ;
    destruct Ki ; cbn ; repeat destruct_match ; intros [=] ; subst ; auto.
Qed. *)

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item (Ki1, e1) = fill_item (Ki2, e2) → Ki1 = Ki2.
Proof. destruct Ki2, Ki1. (*  naive_solver eauto with f_equal. Qed. *) Admitted.

Lemma fill_item_some Ki e : is_Some (to_val (fill_item (Ki, e))) → is_Some (to_val e).
Proof. Admitted.
