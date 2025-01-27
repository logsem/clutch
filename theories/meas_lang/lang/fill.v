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
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections cfg types.



Local Open Scope classical_set_scope.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Global Instance of_val_inj {T1 T2 T3 T4 : Type} : Inj (=) (=) (@of_val T1 T2 T3 T4).
Proof. intros ??. congruence. Qed.

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
  | AllocNLCtx (v2 : @val_pre TZ TB TL TR)
  | AllocNRCtx (e1 : @expr_pre TZ TB TL TR)
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
  | AllocNLCtx v2 => AllocNLCtx (val_pre_F FInt FBool FLoc FLbl FReal v2)
  | AllocNRCtx e1 => AllocNRCtx (expr_pre_F FInt FBool FLoc FLbl FReal e1)
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
  Definition ectx_item_S : Type := @ectx_item_pre (set TZ) (set TB) (set TL) (set TR).
  Definition ectx_item_T : Type := @ectx_item_pre TZ TB TL TR.
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
    | AllocNLCtx v2 => image (val_ST v2) AllocNLCtx
    | AllocNRCtx e1 => image (expr_ST e1) AllocNRCtx
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
      | AllocNLCtx v2 => val_ML v2
      | AllocNRCtx e1 => expr_ML e1
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

Definition ectx_item : measurableType ectx_item_cyl.-sigma := ectx_item_T.


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
Definition AllocNLCtxC v2   : ectx_item := AllocNLCtx v2.
Definition AllocNRCtxC e1   : ectx_item := AllocNRCtx e1.
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
Definition AllocNLCtxU (v : val)                      := AllocNLCtxC v.
Definition AllocNRCtxU (v : expr)                     := AllocNRCtxC v.
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

  Lemma AllocNLCtxU_measurable : measurable_fun setT AllocNLCtxU.
  Proof. Admitted.
  Hint Resolve AllocNLCtxU_measurable : measlang.

  Lemma AllocNRCtxU_measurable : measurable_fun setT AllocNRCtxU.
  Proof. Admitted.
  Hint Resolve AllocNRCtxU_measurable : measlang.

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

Definition ectx_item_shape_enum (n : nat) : ectx_item_shape. Admitted.

Lemma ectx_item_shape_enum_surj (e : ectx_item_shape) : exists n, ectx_item_shape_enum n = e.
Proof. Admitted.

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
Definition 𝜋_BinOpRCtx_v    (k : ectx_item) : expr := match k with | BinOpRCtx _ v => v | _ => point end.
Definition 𝜋_IfCtx_l        (k : ectx_item) : expr := match k with | IfCtx v _ => v | _ => point end.
Definition 𝜋_IfCtx_r        (k : ectx_item) : expr := match k with | IfCtx _ v => v | _ => point end.
Definition 𝜋_PairLCtx_v     (k : ectx_item) : val := match k with | PairLCtx v => v | _ => point end.
Definition 𝜋_PairRCtx_e     (k : ectx_item) : expr := match k with | PairRCtx v => v | _ => point end.
Definition 𝜋_CaseCtx_l      (k : ectx_item) : expr := match k with | CaseCtx v _ => v | _ => point end.
Definition 𝜋_CaseCtx_r      (k : ectx_item) : expr := match k with | CaseCtx _ v => v | _ => point end.
Definition 𝜋_AllocNLCtx_v   (k : ectx_item) : val := match k with | AllocNLCtx v => v | _ => point end.
Definition 𝜋_AllocNRCtx_e   (k : ectx_item) : expr := match k with | AllocNRCtx v => v | _ => point end.
Definition 𝜋_StoreLCtx_v    (k : ectx_item) : val := match k with | StoreLCtx v => v | _ => point end.
Definition 𝜋_StoreRCtx_e    (k : ectx_item) : expr := match k with | StoreRCtx v => v | _ => point end.
Definition 𝜋_RandLCtx_v     (k : ectx_item) : val := match k with | RandLCtx v => v | _ => point end.
Definition 𝜋_RandRCtx_e     (k : ectx_item) : expr := match k with | RandRCtx v => v | _ => point end.

End Projections.


Section Cover.

Definition ectx_item_cov_AppLCtx      : set ectx_item := [set e | ∃ x, e = AppLCtx x].
Definition ectx_item_cov_AppRCtx      : set ectx_item := [set e | ∃ x, e = AppLCtx x].
Definition ectx_item_cov_UnOpCtx      : set ectx_item := [set e | ∃ x, e = UnOpCtx x].
Definition ectx_item_cov_BinOpLCtx    : set ectx_item := [set e | ∃ x y, e = BinOpLCtx x y].
Definition ectx_item_cov_BinOpRCtx    : set ectx_item := [set e | ∃ x y, e = BinOpRCtx x y].
Definition ectx_item_cov_IfCtx        : set ectx_item := [set e | ∃ x y, e = IfCtx x y].
Definition ectx_item_cov_PairLCtx     : set ectx_item := [set e | ∃ x, e = PairLCtx x].
Definition ectx_item_cov_PairRCtx     : set ectx_item := [set e | ∃ x, e = PairRCtx x].
Definition ectx_item_cov_FstCtx       : set ectx_item := [set FstCtx].
Definition ectx_item_cov_SndCtx       : set ectx_item := [set SndCtx].
Definition ectx_item_cov_InjLCtx      : set ectx_item := [set InjLCtx].
Definition ectx_item_cov_InjRCtx      : set ectx_item := [set InjRCtx].
Definition ectx_item_cov_CaseCtx      : set ectx_item := [set e | ∃ x y, e = CaseCtx x y].
Definition ectx_item_cov_AllocNLCtx   : set ectx_item := [set e | ∃ x, e = AllocNLCtx x].
Definition ectx_item_cov_AllocNRCtx   : set ectx_item := [set e | ∃ x, e = AllocNRCtx x].
Definition ectx_item_cov_LoadCtx      : set ectx_item := [set LoadCtx].
Definition ectx_item_cov_StoreLCtx    : set ectx_item := [set e | ∃ x, e = StoreLCtx x].
Definition ectx_item_cov_StoreRCtx    : set ectx_item := [set e | ∃ x, e = StoreRCtx x].
Definition ectx_item_cov_AllocTapeCtx : set ectx_item := [set AllocTapeCtx].
Definition ectx_item_cov_RandLCtx     : set ectx_item := [set e | ∃ x, e = RandLCtx x].
Definition ectx_item_cov_RandRCtx     : set ectx_item := [set e | ∃ x, e = RandRCtx x].
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

Lemma ectx_item_cov_AllocNLCtx_meas   : measurable ectx_item_cov_AllocNLCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_AllocNLCtx_meas   : measlang.

Lemma ectx_item_cov_AllocNRCtx_meas   : measurable ectx_item_cov_AllocNRCtx.
Proof. Admitted.
Hint Resolve ectx_item_cov_AllocNRCtx_meas   : measlang.

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

Lemma 𝜋_BinOpRCtx_v_meas  : measurable_fun ectx_item_cov_BinOpRCtx 𝜋_BinOpRCtx_v.
Proof. Admitted.
Hint Resolve 𝜋_BinOpRCtx_v_meas  : measlang.

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

Lemma 𝜋_AllocNLCtx_v_meas : measurable_fun ectx_item_cov_AllocNLCtx 𝜋_AllocNLCtx_v.
Proof. Admitted.
Hint Resolve 𝜋_AllocNLCtx_v_meas : measlang.

Lemma 𝜋_AllocNRCtx_e_meas : measurable_fun ectx_item_cov_AllocNRCtx 𝜋_AllocNRCtx_e.
Proof. Admitted.
Hint Resolve 𝜋_AllocNRCtx_e_meas : measlang.

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

End Projection_measurability.

(** Since the pattern matching for fill is so simple, we don't need to define an
 aux cover for it. *)






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


(** TODO: I'm pretty sure I could do this, but I want to be sure I dont't need it
 to be a measurable function (ectx_item x expr) -> expr first. That would involve putting
 a measure on ectx_item, which is not hard. *)
Definition fill_item_mf (K : ectx_item) : measurable_map expr expr.
Admitted.
(*   := m_discr (fill_item K : <<discr expr>> -> <<discr expr>>).  *)
