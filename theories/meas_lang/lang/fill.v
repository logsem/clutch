(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap countable tactics.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import measure lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections cfg types prelude.

Require Import mathcomp.reals_stdlib.Rstruct.
Require Import mathcomp.reals.reals.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

Notation of_val := ValC (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Lemma to_val_meas : measurable_fun setT to_val.
Proof.
  have -> : to_val = if_in ecov_val (Some \o 𝜋_Val_v) (cst None).
  { apply funext; intro x; rewrite /to_val/if_in.
    destruct x.
    1: { rewrite bool_decide_eq_true_2; [by f_equal|by rewrite /ecov_val//=; eexists _; eauto]. }
    all: rewrite bool_decide_eq_false_2 /ecov_val//=.
    all: intros [? ? HK]; by inversion HK.
  }
  eapply @if_in_meas_fun.
  { by eauto with mf_set. }
  { by eapply @measurableT. }
  { mf_cmp_tree.
    { by apply Some_meas_fun. }
    { by rewrite setIT; apply 𝜋_Val_v_meas. }
  }
  by eapply measurable_cst.
Qed.

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

  (* Lemmas from constructors.v *)
  Local Lemma MZ {d} {T : measurableType d} (S : set T)  : S = set0 -> measurable S.
  Proof. by move=>->; apply measurable0. Qed.
  Hint Resolve MZ : measlang.
  Ltac ctor_triv_case :=
    apply MZ; apply /predeqP =>y /=; split; [| by move=>?];
    (by move=> ?//) +
    (by move=> [?]//) +
    (by move=> [??[???]]//) +
    (by move=> [??[??[???]]]//).

  Lemma AppLCtxU_measurable : measurable_fun setT AppLCtxU.
  Proof. into_gen_measurable. intros ?[? [x ?<-]<-].
         rewrite setTI.
         destruct x; rewrite /preimage/=.
         1:{ apply sub_sigma_algebra.
             eexists v2; first done.
             rewrite eqEsubset. split; intros ?.
             - naive_solver.
             - intros [???]. unfold AppLCtxU, AppLCtxC in *. by simplify_eq. 
         }
         all: ctor_triv_case.
  Qed.
  Hint Resolve AppLCtxU_measurable : measlang.

  Lemma AppRCtxU_measurable : measurable_fun setT AppRCtxU.
  Proof. into_gen_measurable. intros ?[? [x ?<-]<-].
         rewrite setTI.
         destruct x; rewrite /preimage/=.
         all: try ctor_triv_case.
         apply sub_sigma_algebra.
         eexists e1; first done.
         rewrite eqEsubset. split; intros ?.
         - naive_solver.
         - intros [???]. unfold AppRCtxU, AppRCtxC in *. by simplify_eq.
  Qed.
  Hint Resolve AppRCtxU_measurable : measlang.

  Lemma UnOpCtxU_measurable : measurable_fun setT UnOpCtxU.
  Proof. into_gen_measurable. intros ?[? [x ?<-] <-]. 
         rewrite setTI.
         destruct x; rewrite /preimage/=.
         all: try ctor_triv_case.
         done.
  Qed.
  Hint Resolve UnOpCtxU_measurable : measlang.

  Lemma BinOpLCtxU_measurable : measurable_fun setT BinOpLCtxU.
  Proof. into_gen_measurable. intros ?[? [x ?<-] <-]. 
         rewrite setTI.
         destruct x; rewrite /preimage/=.
         all: try ctor_triv_case.
         have ->: ([set t | (exists2 x : val_T, val_ST v2 x & BinOpLCtx op x = BinOpLCtxU t)] =
                   [set t | (t.1= op)] `&`
                   [set t | (exists2 x : val_T, val_ST v2 x & t.2 = x)]
           ).
         { rewrite eqEsubset; split; intros [??]; simpl.
           - intros [?? H2].
             rewrite /BinOpLCtxU/BinOpLCtxC in H2. simplify_eq.
             naive_solver.
           - intros [-> [??->]].
             naive_solver.
         }
         apply measurableI.
         - apply sub_sigma_algebra. rewrite /preimage_set_system/=.
           left. exists [set op]; first done.
           by rewrite setTI.
         - apply sub_sigma_algebra.
           right. rewrite /preimage_set_system/=.
           exists (val_ST v2).
           { apply sub_sigma_algebra. rewrite /val_cyl/=. naive_solver. }
           rewrite setTI.
           rewrite eqEsubset; split; intros [??]; simpl; first naive_solver.
           intros [??<-]. naive_solver.
  Qed.
  Hint Resolve BinOpLCtxU_measurable : measlang.

  Lemma BinOpRCtxU_measurable : measurable_fun setT BinOpRCtxU.
  Proof. into_gen_measurable. intros ?[? [x ?<-] <-]. 
         rewrite setTI.
         destruct x; rewrite /preimage/=.
         all: try ctor_triv_case.
         have ->: ([set t | (exists2 x : expr_T, expr_ST e1 x & BinOpRCtx op x = BinOpRCtxU t)] =
                   [set t | (t.1= op)] `&`
                   [set t | (exists2 x : expr_T, expr_ST e1 x & t.2 = x)]
           ).
         { rewrite eqEsubset; split; intros [??]; simpl.
           - intros [?? H2].
             rewrite /BinOpRCtxU/BinOpRCtxC in H2. simplify_eq.
             naive_solver.
           - intros [-> [??->]].
             naive_solver.
         }
         apply measurableI.
         - apply sub_sigma_algebra. rewrite /preimage_set_system/=.
           left. exists [set op]; first done.
           by rewrite setTI.
         - apply sub_sigma_algebra.
           right. rewrite /preimage_set_system/=.
           exists (expr_ST e1).
           { apply sub_sigma_algebra. rewrite /expr_cyl/=. naive_solver. }
           rewrite setTI.
           rewrite eqEsubset; split; intros [??]; simpl; first naive_solver.
           intros [??<-]. naive_solver.
  Qed.
  Hint Resolve BinOpRCtxU_measurable : measlang.

  Lemma IfCtxU_measurable : measurable_fun setT IfCtxU.
  Proof. into_gen_measurable. intros ?[?[x?<-]<-].
         rewrite setTI.
         destruct x; rewrite /preimage/=; try ctor_triv_case.
         have ->: ([set t | (exists2 x,
                                expr_ST e1 x & exists2 y : expr_T, expr_ST e2 y & IfCtx x y = IfCtxU t)]=
                    [set t | (exists2 x, expr_ST e1 x & t.1 = x)] `&`
                      [set t | (exists2 y, expr_ST e2 y & t.2 = y)]                                              ).
         { rewrite eqEsubset; split; intros [??]; simpl.
           - intros [?? [?? H2]].
             rewrite /IfCtxU/IfCtxC in H2. simplify_eq.
             naive_solver.
           - intros [[][]]; subst.
             naive_solver.
         }
         apply measurableI.
         - apply sub_sigma_algebra. rewrite /preimage_set_system/=.
           left. exists (expr_ST e1).
           { apply sub_sigma_algebra. rewrite /expr_cyl/=. naive_solver. }
           rewrite setTI.
           rewrite eqEsubset; split; intros [??]; simpl; first naive_solver.
           intros [??<-]. naive_solver.
         - apply sub_sigma_algebra.
           right. rewrite /preimage_set_system/=.
           exists (expr_ST e2).
           { apply sub_sigma_algebra. rewrite /expr_cyl/=. naive_solver. }
           rewrite setTI.
           rewrite eqEsubset; split; intros [??]; simpl; first naive_solver.
           intros [??<-]. naive_solver.
  Qed.
  Hint Resolve IfCtxU_measurable : measlang.

  Lemma PairLCtxU_measurable : measurable_fun setT PairLCtxU.
  Proof. into_gen_measurable. intros ?[? [x ?<-]<-].
         rewrite setTI.
         destruct x; rewrite /preimage/=.
         all: try ctor_triv_case.
         apply sub_sigma_algebra.
         eexists v2; first done.
         rewrite eqEsubset. split; intros ?.
         - naive_solver.
         - intros [???]. unfold PairLCtxU, PairLCtxC in *. by simplify_eq.
  Qed.
  Hint Resolve PairLCtxU_measurable : measlang.

  Lemma PairRCtxU_measurable : measurable_fun setT PairRCtxU.
  Proof. into_gen_measurable. intros ?[? [x ?<-]<-].
         rewrite setTI.
         destruct x; rewrite /preimage/=.
         all: try ctor_triv_case.
         apply sub_sigma_algebra.
         eexists e1; first done.
         rewrite eqEsubset. split; intros ?.
         - naive_solver.
         - intros [???]. unfold PairRCtxU, PairRCtxC in *. by simplify_eq.
  Qed.
  Hint Resolve PairRCtxU_measurable : measlang.

  Lemma CaseCtxU_measurable : measurable_fun setT CaseCtxU.
  Proof. into_gen_measurable. intros ?[?[x?<-]<-].
         rewrite setTI.
         destruct x; rewrite /preimage/=; try ctor_triv_case.
         have ->: ([set t | (exists2 x,
                                expr_ST e1 x & exists2 y : expr_T, expr_ST e2 y & CaseCtx x y = CaseCtxU t)]=
                    [set t | (exists2 x, expr_ST e1 x & t.1 = x)] `&`
                      [set t | (exists2 y, expr_ST e2 y & t.2 = y)]                                              ).
         { rewrite eqEsubset; split; intros [??]; simpl.
           - intros [?? [?? H2]].
             rewrite /CaseCtxU/CaseCtxC in H2. simplify_eq.
             naive_solver.
           - intros [[][]]; subst.
             naive_solver.
         }
         apply measurableI.
         - apply sub_sigma_algebra. rewrite /preimage_set_system/=.
           left. exists (expr_ST e1).
           { apply sub_sigma_algebra. rewrite /expr_cyl/=. naive_solver. }
           rewrite setTI.
           rewrite eqEsubset; split; intros [??]; simpl; first naive_solver.
           intros [??<-]. naive_solver.
         - apply sub_sigma_algebra.
           right. rewrite /preimage_set_system/=.
           exists (expr_ST e2).
           { apply sub_sigma_algebra. rewrite /expr_cyl/=. naive_solver. }
           rewrite setTI.
           rewrite eqEsubset; split; intros [??]; simpl; first naive_solver.
           intros [??<-]. naive_solver.
  Qed.
  Hint Resolve CaseCtxU_measurable : measlang.

  Lemma StoreLCtxU_measurable : measurable_fun setT StoreLCtxU.
  Proof. into_gen_measurable. intros ?[? [x ?<-]<-].
         rewrite setTI.
         destruct x; rewrite /preimage/=.
         all: try ctor_triv_case.
         apply sub_sigma_algebra.
         eexists v2; first done.
         rewrite eqEsubset. split; intros ?.
         - naive_solver.
         - intros [???]. unfold StoreLCtxU, StoreLCtxC in *. by simplify_eq.
  Qed.
  Hint Resolve StoreLCtxU_measurable : measlang.

  Lemma StoreRCtxU_measurable : measurable_fun setT StoreRCtxU.
  Proof. into_gen_measurable. intros ?[? [x ?<-]<-].
         rewrite setTI.
         destruct x; rewrite /preimage/=.
         all: try ctor_triv_case.
         apply sub_sigma_algebra.
         eexists e1; first done.
         rewrite eqEsubset. split; intros ?.
         - naive_solver.
         - intros [???]. unfold StoreRCtxU, StoreRCtxC in *. by simplify_eq.
  Qed. 
  Hint Resolve StoreRCtxU_measurable : measlang.

  Lemma RandLCtxU_measurable : measurable_fun setT RandLCtxU.
  Proof. into_gen_measurable. intros ?[? [x ?<-]<-].
         rewrite setTI.
         destruct x; rewrite /preimage/=.
         all: try ctor_triv_case.
         apply sub_sigma_algebra.
         eexists v2; first done.
         rewrite eqEsubset. split; intros ?.
         - naive_solver.
         - intros [???]. unfold RandLCtxU, RandLCtxC in *. by simplify_eq.
  Qed. 
  Hint Resolve RandLCtxU_measurable : measlang.

  Lemma RandRCtxU_measurable : measurable_fun setT RandRCtxU.
  Proof. into_gen_measurable. intros ?[? [x ?<-]<-].
         rewrite setTI.
         destruct x; rewrite /preimage/=.
         all: try ctor_triv_case.
         apply sub_sigma_algebra.
         eexists e1; first done.
         rewrite eqEsubset. split; intros ?.
         - naive_solver.
         - intros [???]. unfold RandRCtxU, RandRCtxC in *. by simplify_eq.
  Qed. 
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
  destruct s; try done; try apply gen_val_generator; try apply gen_expr_generator;
    split; apply gen_expr_generator.
Qed.


Lemma ectx_item_shape_cyl (s : ectx_item_shape) : [set e | shape_ectx_item e = s] = ectx_item_ST (gen_ectx_item s).
Proof.
  rewrite eqEsubset; split; intros e; simpl.
  - intros <-.
    destruct e; simpl.
    all: try done.
    all: try (eexists _; last done; by rewrite <- val_shape_cyl).
    all: try (eexists _; last done; by rewrite <- expr_shape_cyl).
    all: (eexists _; last eexists _; last done; by rewrite <-expr_shape_cyl).
  - destruct s; simpl.
    all: try (intros [? H]; subst; simpl; f_equal; rewrite -val_shape_cyl in H; simpl in H; by subst).
    all: try (intros [? H]; subst; simpl; f_equal; rewrite -expr_shape_cyl in H; simpl in H; by subst).
    all: try by intros ->.
    all: intros [? H[? H']];subst; simpl; f_equal; rewrite -!expr_shape_cyl in H H'; simpl in H, H'; by subst.
Qed.

Definition ectx_item_shape_encode (e: ectx_item_shape):=
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

Definition ectx_item_shape_decode t : ectx_item_shape :=
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
Definition ectx_item_cov_AppRCtx      : set ectx_item := image setT AppRCtxU.
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
Proof.
  have -> : (ectx_item_cov_AppLCtx = \bigcup_n [set AppLCtxU v|v in (val_seq n)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_AppLCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [v ?<-].
      destruct (val_shape_enum_surj (shape_val v)) as [??].
      eexists _; first done. by eexists _.
    - intros [??[]]; subst. naive_solver.
  }
  apply bigcup_measurable.
  intros k _.
  apply sub_sigma_algebra.
  eexists (AppLCtx (gen_val (val_shape_enum k))).
  - rewrite //=. apply gen_val_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x ?<-]; subst.
      eexists _; last done.
      by rewrite -val_shape_cyl/= in H.
    + intros [? H <-]. eexists _; last done.
      rewrite /val_seq/= in H. rewrite -H.
      rewrite -val_shape_cyl. naive_solver.
Qed.
Hint Resolve ectx_item_cov_AppLCtx_meas      : measlang.

Lemma ectx_item_cov_AppRCtx_meas      : measurable ectx_item_cov_AppRCtx.
Proof. 
  have -> : (ectx_item_cov_AppRCtx = \bigcup_n [set AppRCtxU e|e in (expr_seq n)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_AppRCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [e ?<-].
      destruct (expr_shape_enum_surj (shape_expr e)) as [??].
      eexists _; first done. by eexists _.
    - intros [??[]]; subst. naive_solver.
  }
  apply bigcup_measurable.
  intros k _.
  apply sub_sigma_algebra.
  eexists (AppRCtx (gen_expr (expr_shape_enum k))).
  - rewrite //=. apply gen_expr_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x ?<-]; subst.
      eexists _; last done.
      by rewrite -expr_shape_cyl/= in H.
    + intros [? H <-]. eexists _; last done.
      rewrite /expr_seq/= in H. rewrite -H.
      rewrite -expr_shape_cyl. naive_solver.
Qed.
Hint Resolve ectx_item_cov_AppRCtx_meas      : measlang.

Lemma ectx_item_cov_UnOpCtx_meas      : measurable ectx_item_cov_UnOpCtx.
Proof. 
  have -> : (ectx_item_cov_UnOpCtx = \bigcup_n [set UnOpCtxU (un_op_enum n)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_UnOpCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [op ?<-].
      destruct (un_op_enum_surj op) as [??].
      eexists _; first done. by subst. 
    - intros []; subst. naive_solver.
  }
  apply bigcup_measurable.
  intros k _.
  apply sub_sigma_algebra.
  by eexists (UnOpCtx (un_op_enum k)).
Qed.
Hint Resolve ectx_item_cov_UnOpCtx_meas      : measlang.

Lemma ectx_item_cov_BinOpLCtx_meas    : measurable ectx_item_cov_BinOpLCtx.
Proof. 
  have -> : (ectx_item_cov_BinOpLCtx = \bigcup_n \bigcup_m [set BinOpLCtxU ((bin_op_enum n), v)| v in (val_seq m)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_BinOpLCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [[op v]? <-].
      destruct (bin_op_enum_surj op) as [??].
      destruct (val_shape_enum_surj (shape_val v)) as [??]; subst.
      eexists _; first done. eexists _; first done. eexists _; last done.
      by rewrite /val_seq/=.
    - intros [??[??[]]]; subst.
      by eexists (_,_).   
  }
  apply bigcup_measurable.
  intros k _.
  apply bigcup_measurable.
  intros k' _.
  apply sub_sigma_algebra.
  eexists (BinOpLCtx (bin_op_enum k) (gen_val (val_shape_enum k'))).
  - rewrite //=. apply gen_val_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x  H <-]; subst.
      eexists _; last done.
      by rewrite -val_shape_cyl/= in H.
    + intros [? H <-]. eexists _; last done.
      rewrite /val_seq/= in H. rewrite -H.
      rewrite -val_shape_cyl. naive_solver.
Qed.
Hint Resolve ectx_item_cov_BinOpLCtx_meas    : measlang.

Lemma ectx_item_cov_BinOpRCtx_meas    : measurable ectx_item_cov_BinOpRCtx.
Proof. 
  have -> : (ectx_item_cov_BinOpRCtx = \bigcup_n \bigcup_m [set BinOpRCtxU ((bin_op_enum n), e)| e in (expr_seq m)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_BinOpRCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [[op e]? <-].
      destruct (bin_op_enum_surj op) as [??].
      destruct (expr_shape_enum_surj (shape_expr e)) as [??]; subst.
      eexists _; first done. eexists _; first done. eexists _; last done.
      by rewrite /expr_seq/=.
    - intros [??[??[]]]; subst.
      by eexists (_,_).   
  }
  apply bigcup_measurable.
  intros k _.
  apply bigcup_measurable.
  intros k' _.
  apply sub_sigma_algebra.
  eexists (BinOpRCtx (bin_op_enum k) (gen_expr (expr_shape_enum k'))).
  - rewrite //=. apply gen_expr_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x  H <-]; subst.
      eexists _; last done.
      by rewrite -expr_shape_cyl/= in H.
    + intros [? H <-]. eexists _; last done.
      rewrite /expr_seq/= in H. rewrite -H.
      rewrite -expr_shape_cyl. naive_solver.
Qed.
Hint Resolve ectx_item_cov_BinOpRCtx_meas    : measlang.

Lemma ectx_item_cov_IfCtx_meas        : measurable ectx_item_cov_IfCtx.
Proof. 
  have -> : (ectx_item_cov_IfCtx = \bigcup_n \bigcup_m [set IfCtxU (e1, e2)| e1 in (expr_seq n )& e2 in (expr_seq m)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_IfCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [[e1 e2]? <-].
      destruct (expr_shape_enum_surj (shape_expr e1)) as [??]; subst.
      destruct (expr_shape_enum_surj (shape_expr e2)) as [??]; subst.
      eexists _; first done. eexists _; first done. eexists _; last eexists _; last done; done. 
    - intros [??[??[??[]]]]; subst.
      by eexists (_,_).   
  }
  apply bigcup_measurable.
  intros k _.
  apply bigcup_measurable.
  intros k' _.
  apply sub_sigma_algebra.
  eexists (IfCtx (gen_expr (expr_shape_enum k)) (gen_expr (expr_shape_enum k'))).
  - rewrite //=; split;  apply gen_expr_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x  H [? H' <-]].
      rewrite -!expr_shape_cyl/= in H H'.
      eexists _; last eexists _; last done; done.
    + intros [? H [? H' <-]].
      rewrite -!expr_shape_cyl.
      repeat eexists _; last done; done.
Qed.
Hint Resolve ectx_item_cov_IfCtx_meas        : measlang.

Lemma ectx_item_cov_PairLCtx_meas     : measurable ectx_item_cov_PairLCtx.
Proof. 
  have -> : (ectx_item_cov_PairLCtx = \bigcup_n [set PairLCtxU v|v in (val_seq n)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_PairLCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [v ?<-].
      destruct (val_shape_enum_surj (shape_val v)) as [??].
      eexists _; first done. by eexists _.
    - intros [??[]]; subst. naive_solver.
  }
  apply bigcup_measurable.
  intros k _.
  apply sub_sigma_algebra.
  eexists (PairLCtx (gen_val (val_shape_enum k))).
  - rewrite //=. apply gen_val_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x ?<-]; subst.
      eexists _; last done.
      by rewrite -val_shape_cyl/= in H.
    + intros [? H <-]. eexists _; last done.
      rewrite /val_seq/= in H. rewrite -H.
      rewrite -val_shape_cyl. naive_solver.
Qed.
Hint Resolve ectx_item_cov_PairLCtx_meas     : measlang.

Lemma ectx_item_cov_PairRCtx_meas     : measurable ectx_item_cov_PairRCtx.
Proof. 
  have -> : (ectx_item_cov_PairRCtx = \bigcup_n [set PairRCtxU e|e in (expr_seq n)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_PairRCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [e ?<-].
      destruct (expr_shape_enum_surj (shape_expr e)) as [??].
      eexists _; first done. by eexists _.
    - intros [??[]]; subst. naive_solver.
  }
  apply bigcup_measurable.
  intros k _.
  apply sub_sigma_algebra.
  eexists (PairRCtx (gen_expr (expr_shape_enum k))).
  - rewrite //=. apply gen_expr_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x ?<-]; subst.
      eexists _; last done.
      by rewrite -expr_shape_cyl/= in H.
    + intros [? H <-]. eexists _; last done.
      rewrite /expr_seq/= in H. rewrite -H.
      rewrite -expr_shape_cyl. naive_solver.
Qed.
Hint Resolve ectx_item_cov_PairRCtx_meas     : measlang.

Lemma ectx_item_cov_FstCtx_meas       : measurable ectx_item_cov_FstCtx.
Proof.
  apply sub_sigma_algebra.
  by eexists FstCtx.
Qed.
Hint Resolve ectx_item_cov_FstCtx_meas       : measlang.

Lemma ectx_item_cov_SndCtx_meas       : measurable ectx_item_cov_SndCtx.
Proof. 
  apply sub_sigma_algebra.
  by eexists SndCtx.
Qed.
Hint Resolve ectx_item_cov_SndCtx_meas       : measlang.

Lemma ectx_item_cov_InjLCtx_meas      : measurable ectx_item_cov_InjLCtx.
Proof. 
  apply sub_sigma_algebra.
  by eexists InjLCtx.
Qed.
Hint Resolve ectx_item_cov_InjLCtx_meas      : measlang.

Lemma ectx_item_cov_InjRCtx_meas      : measurable ectx_item_cov_InjRCtx.
Proof. 
  apply sub_sigma_algebra.
  by eexists InjRCtx.
Qed.
Hint Resolve ectx_item_cov_InjRCtx_meas      : measlang.

Lemma ectx_item_cov_CaseCtx_meas      : measurable ectx_item_cov_CaseCtx.
Proof. 
  have -> : (ectx_item_cov_CaseCtx = \bigcup_n \bigcup_m [set CaseCtxU (e1, e2)| e1 in (expr_seq n )& e2 in (expr_seq m)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_CaseCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [[e1 e2]? <-].
      destruct (expr_shape_enum_surj (shape_expr e1)) as [??]; subst.
      destruct (expr_shape_enum_surj (shape_expr e2)) as [??]; subst.
      eexists _; first done. eexists _; first done. eexists _; last eexists _; last done; done. 
    - intros [??[??[??[]]]]; subst.
      by eexists (_,_).   
  }
  apply bigcup_measurable.
  intros k _.
  apply bigcup_measurable.
  intros k' _.
  apply sub_sigma_algebra.
  eexists (CaseCtx (gen_expr (expr_shape_enum k)) (gen_expr (expr_shape_enum k'))).
  - rewrite //=; split;  apply gen_expr_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x  H [? H' <-]].
      rewrite -!expr_shape_cyl/= in H H'.
      eexists _; last eexists _; last done; done.
    + intros [? H [? H' <-]].
      rewrite -!expr_shape_cyl.
      repeat eexists _; last done; done.
Qed.
Hint Resolve ectx_item_cov_CaseCtx_meas      : measlang.

Lemma ectx_item_cov_AllocCtx_meas     : measurable ectx_item_cov_AllocCtx.
Proof. 
  apply sub_sigma_algebra.
  by eexists AllocCtx.
Qed.
Hint Resolve ectx_item_cov_AllocCtx_meas   : measlang.

Lemma ectx_item_cov_LoadCtx_meas      : measurable ectx_item_cov_LoadCtx.
Proof. 
  apply sub_sigma_algebra.
  by eexists LoadCtx.
Qed.
Hint Resolve ectx_item_cov_LoadCtx_meas      : measlang.

Lemma ectx_item_cov_StoreLCtx_meas    : measurable ectx_item_cov_StoreLCtx.
Proof. 
  have -> : (ectx_item_cov_StoreLCtx = \bigcup_n [set StoreLCtxU v|v in (val_seq n)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_StoreLCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [v ?<-].
      destruct (val_shape_enum_surj (shape_val v)) as [??].
      eexists _; first done. by eexists _.
    - intros [??[]]; subst. naive_solver.
  }
  apply bigcup_measurable.
  intros k _.
  apply sub_sigma_algebra.
  eexists (StoreLCtx (gen_val (val_shape_enum k))).
  - rewrite //=. apply gen_val_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x ?<-]; subst.
      eexists _; last done.
      by rewrite -val_shape_cyl/= in H.
    + intros [? H <-]. eexists _; last done.
      rewrite /val_seq/= in H. rewrite -H.
      rewrite -val_shape_cyl. naive_solver.
Qed. 
Hint Resolve ectx_item_cov_StoreLCtx_meas    : measlang.

Lemma ectx_item_cov_StoreRCtx_meas    : measurable ectx_item_cov_StoreRCtx.
Proof. 
  have -> : (ectx_item_cov_StoreRCtx = \bigcup_n [set StoreRCtxU e|e in (expr_seq n)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_StoreRCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [e ?<-].
      destruct (expr_shape_enum_surj (shape_expr e)) as [??].
      eexists _; first done. by eexists _.
    - intros [??[]]; subst. naive_solver.
  }
  apply bigcup_measurable.
  intros k _.
  apply sub_sigma_algebra.
  eexists (StoreRCtx (gen_expr (expr_shape_enum k))).
  - rewrite //=. apply gen_expr_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x ?<-]; subst.
      eexists _; last done.
      by rewrite -expr_shape_cyl/= in H.
    + intros [? H <-]. eexists _; last done.
      rewrite /expr_seq/= in H. rewrite -H.
      rewrite -expr_shape_cyl. naive_solver.
Qed.
Hint Resolve ectx_item_cov_StoreRCtx_meas    : measlang.

Lemma ectx_item_cov_AllocTapeCtx_meas : measurable ectx_item_cov_AllocTapeCtx.
Proof. 
  apply sub_sigma_algebra.
  by eexists AllocTapeCtx.
Qed.
Hint Resolve ectx_item_cov_AllocTapeCtx_meas : measlang.

Lemma ectx_item_cov_RandLCtx_meas     : measurable ectx_item_cov_RandLCtx.
Proof. 
  have -> : (ectx_item_cov_RandLCtx = \bigcup_n [set RandLCtxU v|v in (val_seq n)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_RandLCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [v ?<-].
      destruct (val_shape_enum_surj (shape_val v)) as [??].
      eexists _; first done. by eexists _.
    - intros [??[]]; subst. naive_solver.
  }
  apply bigcup_measurable.
  intros k _.
  apply sub_sigma_algebra.
  eexists (RandLCtx (gen_val (val_shape_enum k))).
  - rewrite //=. apply gen_val_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x ?<-]; subst.
      eexists _; last done.
      by rewrite -val_shape_cyl/= in H.
    + intros [? H <-]. eexists _; last done.
      rewrite /val_seq/= in H. rewrite -H.
      rewrite -val_shape_cyl. naive_solver.
Qed.
Hint Resolve ectx_item_cov_RandLCtx_meas     : measlang.

Lemma ectx_item_cov_RandRCtx_meas     : measurable ectx_item_cov_RandRCtx.
Proof. 
  have -> : (ectx_item_cov_RandRCtx = \bigcup_n [set RandRCtxU e|e in (expr_seq n)]).
  { rewrite /bigcup/=.
    rewrite /ectx_item_cov_RandRCtx.
    rewrite eqEsubset; split; intros s; simpl.
    - intros [e ?<-].
      destruct (expr_shape_enum_surj (shape_expr e)) as [??].
      eexists _; first done. by eexists _.
    - intros [??[]]; subst. naive_solver.
  }
  apply bigcup_measurable.
  intros k _.
  apply sub_sigma_algebra.
  eexists (RandRCtx (gen_expr (expr_shape_enum k))).
  - rewrite //=. apply gen_expr_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x ?<-]; subst.
      eexists _; last done.
      by rewrite -expr_shape_cyl/= in H.
    + intros [? H <-]. eexists _; last done.
      rewrite /expr_seq/= in H. rewrite -H.
      rewrite -expr_shape_cyl. naive_solver.
Qed.
Hint Resolve ectx_item_cov_RandRCtx_meas     : measlang.

Lemma ectx_item_cov_URandCtx_meas     : measurable ectx_item_cov_URandCtx.
Proof. 
  apply sub_sigma_algebra.
  by eexists URandCtx.
Qed.
Hint Resolve ectx_item_cov_URandCtx_meas     : measlang.

Lemma ectx_item_cov_TickCtx_meas      : measurable ectx_item_cov_TickCtx.
Proof. 
  apply sub_sigma_algebra.
  by eexists TickCtx.
Qed.
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
Proof. into_gen_measurable.
       rewrite /preimage_set_system.
       intros x[?[x1?<-] <-].
       apply sub_sigma_algebra.
       eexists (AppLCtx x1); first done.
       simpl. 
       rewrite eqEsubset; split; intros ?; simpl.
       - intros [?? <-]. split; last done. rewrite /ectx_item_cov_AppLCtx. naive_solver.
       - rewrite /ectx_item_cov_AppLCtx/=.
         intros [[??<-]?]. simpl in *. naive_solver.
Qed.
Hint Resolve 𝜋_AppLCtx_v_meas    : measlang.

Lemma 𝜋_AppRCtx_e_meas    : measurable_fun ectx_item_cov_AppRCtx 𝜋_AppRCtx_e.
Proof. into_gen_measurable.
       rewrite /preimage_set_system.
       intros x[?[x1?<-] <-].
       apply sub_sigma_algebra.
       eexists (AppRCtx x1); first done.
       simpl. 
       rewrite eqEsubset; split; intros ?; simpl.
       - intros [?? <-]. split; last done. rewrite /ectx_item_cov_AppRCtx. naive_solver.
       - rewrite /ectx_item_cov_AppRCtx/=.
         intros [[??<-]?]. simpl in *. naive_solver.
Qed.
Hint Resolve 𝜋_AppRCtx_e_meas    : measlang.

Lemma 𝜋_UnOpCtx_op_meas   : measurable_fun ectx_item_cov_UnOpCtx 𝜋_UnOpCtx_op.
Proof. eapply (measurability un_op_generated_by_singletons). rewrite /preimage_set_system.
       intros ? [?[x]?]; subst.
       apply sub_sigma_algebra.
       eexists (UnOpCtx x); first done.
       simpl. 
       rewrite eqEsubset; split; intros ?; simpl.
       - intros ->; split; last done.
         rewrite /ectx_item_cov_UnOpCtx. naive_solver.
       - rewrite /ectx_item_cov_UnOpCtx/=.
         intros [[]<-]; by subst.
Qed.
Hint Resolve 𝜋_UnOpCtx_op_meas   : measlang.

Lemma 𝜋_BinOpLCtx_op_meas : measurable_fun ectx_item_cov_BinOpLCtx 𝜋_BinOpLCtx_op.
Proof.
  eapply (measurability bin_op_generated_by_singletons).
  rewrite /preimage_set_system.
  intros ?. simpl.
  intros [?[op ->]<-].
  have ->: ((ectx_item_cov_BinOpLCtx `&` 𝜋_BinOpLCtx_op @^-1` [set op])=
            \bigcup_n [set BinOpLCtx op v|v in (val_seq n)]
    ).
  { rewrite eqEsubset; split; intros ?; rewrite /ectx_item_cov_BinOpLCtx/bigcup/=.
    - intros [[[op' v]]<-]. subst.
      destruct (val_shape_enum_surj (shape_val v)) as [??].
      eexists _; first done. by eexists _.
    - intros [??[??]]. subst.
      split; last done.
      eexists (_,_); naive_solver.
  }
  apply bigcup_measurable.
  intros ? _.
  apply sub_sigma_algebra.
  eexists (BinOpLCtx op (gen_val (val_shape_enum k))).
  - simpl. apply gen_val_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x ?<-]; subst.
      eexists _; last done.
      by rewrite -val_shape_cyl/= in H.
    + intros [? H <-]. eexists _; last done.
      rewrite /val_seq/= in H. rewrite -H.
      rewrite -val_shape_cyl. naive_solver.
Qed.
Hint Resolve 𝜋_BinOpLCtx_op_meas : measlang.

Lemma 𝜋_BinOpLCtx_v_meas  : measurable_fun ectx_item_cov_BinOpLCtx 𝜋_BinOpLCtx_v.
Proof.
  into_gen_measurable.
  rewrite /preimage_set_system.
  intros ?. simpl.
  intros [?[v]<-]; subst.
  have ->: ((ectx_item_cov_BinOpLCtx `&` 𝜋_BinOpLCtx_v @^-1` (val_ST v))=
            \bigcup_n [set BinOpLCtx (bin_op_enum n) v' | v' in val_ST v]
    ).
  { rewrite eqEsubset; split; intros ?; rewrite /ectx_item_cov_BinOpLCtx/bigcup/=.
    - intros [[[op]]]; subst; simpl in *. 
      destruct (bin_op_enum_surj op) as [??].
      repeat eexists _; [done..|]. by subst.
    - intros [??[??]]. subst.
      split; last done.
      by eexists (_,_). 
  }
  apply bigcup_measurable.
  intros ? _.
  apply sub_sigma_algebra.
  eexists (BinOpLCtx (bin_op_enum k) v).
  - simpl. done. 
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x ?<-]; subst.
      by eexists _. 
    + intros [? H' <-]. eexists _; last done.
      by rewrite /val_seq/= in H. 
Qed.
Hint Resolve 𝜋_BinOpLCtx_v_meas  : measlang.

Lemma 𝜋_BinOpRCtx_op_meas : measurable_fun ectx_item_cov_BinOpRCtx 𝜋_BinOpRCtx_op.
Proof. 
  eapply (measurability bin_op_generated_by_singletons).
  rewrite /preimage_set_system.
  intros ?. simpl.
  intros [?[op ->]<-].
  have ->: ((ectx_item_cov_BinOpRCtx `&` 𝜋_BinOpRCtx_op @^-1` [set op])=
            \bigcup_n [set BinOpRCtx op e|e in (expr_seq n)]
    ).
  { rewrite eqEsubset; split; intros ?; rewrite /ectx_item_cov_BinOpRCtx/bigcup/=.
    - intros [[[op' e]]<-]. subst.
      destruct (expr_shape_enum_surj (shape_expr e)) as [??].
      eexists _; first done. by eexists _.
    - intros [??[??]]. subst.
      split; last done.
      eexists (_,_); naive_solver.
  }
  apply bigcup_measurable.
  intros ? _.
  apply sub_sigma_algebra.
  eexists (BinOpRCtx op (gen_expr (expr_shape_enum k))).
  - simpl. apply gen_expr_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x ?<-]; subst.
      eexists _; last done.
      by rewrite -expr_shape_cyl/= in H.
    + intros [? H <-]. eexists _; last done.
      rewrite /expr_seq/= in H. rewrite -H.
      rewrite -expr_shape_cyl. naive_solver.
Qed.
Hint Resolve 𝜋_BinOpRCtx_op_meas : measlang.

Lemma 𝜋_BinOpRCtx_e_meas  : measurable_fun ectx_item_cov_BinOpRCtx 𝜋_BinOpRCtx_e.
Proof. 
  into_gen_measurable.
  rewrite /preimage_set_system.
  intros ?. simpl.
  intros [?[e]<-]; subst.
  have ->: ((ectx_item_cov_BinOpRCtx `&` 𝜋_BinOpRCtx_e @^-1` (expr_ST e))=
            \bigcup_n [set BinOpRCtx (bin_op_enum n) e' | e' in expr_ST e]
    ).
  { rewrite eqEsubset; split; intros ?; rewrite /ectx_item_cov_BinOpRCtx/bigcup/=.
    - intros [[[op]]]; subst; simpl in *. 
      destruct (bin_op_enum_surj op) as [??].
      repeat eexists _; [done..|]. by subst.
    - intros [??[??]]. subst.
      split; last done.
      by eexists (_,_). 
  }
  apply bigcup_measurable.
  intros ? _.
  apply sub_sigma_algebra.
  eexists (BinOpRCtx (bin_op_enum k) e).
  - simpl. done. 
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [x ?<-]; subst.
      by eexists _. 
    + intros [? H' <-]. eexists _; last done.
      by rewrite /expr_seq/= in H. 
Qed.
Hint Resolve 𝜋_BinOpRCtx_e_meas  : measlang.

Lemma 𝜋_IfCtx_l_meas      : measurable_fun ectx_item_cov_IfCtx 𝜋_IfCtx_l.
Proof. 
  into_gen_measurable.
  rewrite /preimage_set_system.
  intros ?. simpl.
  intros [?[e]<-]; subst.
  have ->: ((ectx_item_cov_IfCtx `&` 𝜋_IfCtx_l @^-1` (expr_ST e))=
            \bigcup_n [set IfCtx e' e2 | e' in expr_ST e & e2 in (expr_seq n)]
    ).
  { rewrite eqEsubset; split; intros ?; rewrite /ectx_item_cov_IfCtx/bigcup/=.
    - intros [[[e0 e1]??]]. subst.
      destruct (expr_shape_enum_surj (shape_expr e1)) as [??].
      repeat eexists _; last done; done.
    - intros [??[??[??]]]. subst.
      split; last done.
      by eexists (_,_). 
  }
  apply bigcup_measurable.
  intros k ?.
  apply sub_sigma_algebra.
  eexists (IfCtx e (gen_expr (expr_shape_enum k))).
  - simpl. split; first done. apply gen_expr_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [??[? H2 ]]. subst.
      rewrite -expr_shape_cyl in H2.
      repeat eexists _; last done; done.
    + intros [??[??<-]]. 
      repeat eexists _; try done. by rewrite -expr_shape_cyl.
Qed. 
Hint Resolve 𝜋_IfCtx_l_meas      : measlang.

Lemma 𝜋_IfCtx_r_meas      : measurable_fun ectx_item_cov_IfCtx 𝜋_IfCtx_r.
Proof. 
  into_gen_measurable.
  rewrite /preimage_set_system.
  intros ?. simpl.
  intros [?[e]<-]; subst.
  have ->: ((ectx_item_cov_IfCtx `&` 𝜋_IfCtx_r @^-1` (expr_ST e))=
            \bigcup_n [set IfCtx e1 e' | e' in expr_ST e & e1 in (expr_seq n)]
    ).
  { rewrite eqEsubset; split; intros ?; rewrite /ectx_item_cov_IfCtx/bigcup/=.
    - intros [[[e0 e1]??]]. subst.
      destruct (expr_shape_enum_surj (shape_expr e0)) as [??].
      repeat eexists _; last done; done.
    - intros [??[??[??]]]. subst.
      split; last done.
      by eexists (_,_). 
  }
  apply bigcup_measurable.
  intros k ?.
  apply sub_sigma_algebra.
  eexists (IfCtx (gen_expr (expr_shape_enum k)) e).
  - simpl. split; last done. apply gen_expr_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [? H1[? ? ]]. subst.
      rewrite -expr_shape_cyl in H1.
      repeat eexists _; last done; done.
    + intros [??[??<-]]. 
      repeat eexists _; try done. by rewrite -expr_shape_cyl.
Qed. 
Hint Resolve 𝜋_IfCtx_r_meas      : measlang.

Lemma 𝜋_PairLCtx_v_meas   : measurable_fun ectx_item_cov_PairLCtx 𝜋_PairLCtx_v.
Proof. into_gen_measurable.
       rewrite /preimage_set_system.
       intros x[?[x1?<-] <-].
       apply sub_sigma_algebra.
       eexists (PairLCtx x1); first done.
       simpl. 
       rewrite eqEsubset; split; intros ?; simpl.
       - intros [?? <-]. split; last done. rewrite /ectx_item_cov_PairLCtx. naive_solver.
       - rewrite /ectx_item_cov_PairLCtx/=.
         intros [[??<-]?]. simpl in *. naive_solver.
Qed.
Hint Resolve 𝜋_PairLCtx_v_meas   : measlang.

Lemma 𝜋_PairRCtx_e_meas   : measurable_fun ectx_item_cov_PairRCtx 𝜋_PairRCtx_e.
Proof. into_gen_measurable.
       rewrite /preimage_set_system.
       intros x[?[x1?<-] <-].
       apply sub_sigma_algebra.
       eexists (PairRCtx x1); first done.
       simpl. 
       rewrite eqEsubset; split; intros ?; simpl.
       - intros [?? <-]. split; last done. rewrite /ectx_item_cov_PairRCtx. naive_solver.
       - rewrite /ectx_item_cov_PairRCtx/=.
         intros [[??<-]?]. simpl in *. naive_solver.
Qed.
Hint Resolve 𝜋_PairRCtx_e_meas   : measlang.

Lemma 𝜋_CaseCtx_l_meas    : measurable_fun ectx_item_cov_CaseCtx 𝜋_CaseCtx_l.
Proof. 
  into_gen_measurable.
  rewrite /preimage_set_system.
  intros ?. simpl.
  intros [?[e]<-]; subst.
  have ->: ((ectx_item_cov_CaseCtx `&` 𝜋_CaseCtx_l @^-1` (expr_ST e))=
            \bigcup_n [set CaseCtx e' e2 | e' in expr_ST e & e2 in (expr_seq n)]
    ).
  { rewrite eqEsubset; split; intros ?; rewrite /ectx_item_cov_CaseCtx/bigcup/=.
    - intros [[[e0 e1]??]]. subst.
      destruct (expr_shape_enum_surj (shape_expr e1)) as [??].
      repeat eexists _; last done; done.
    - intros [??[??[??]]]. subst.
      split; last done.
      by eexists (_,_). 
  }
  apply bigcup_measurable.
  intros k ?.
  apply sub_sigma_algebra.
  eexists (CaseCtx e (gen_expr (expr_shape_enum k))).
  - simpl. split; first done. apply gen_expr_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [??[? H2 ]]. subst.
      rewrite -expr_shape_cyl in H2.
      repeat eexists _; last done; done.
    + intros [??[??<-]]. 
      repeat eexists _; try done. by rewrite -expr_shape_cyl.
Qed. 
Hint Resolve 𝜋_CaseCtx_l_meas    : measlang.

Lemma 𝜋_CaseCtx_r_meas    : measurable_fun ectx_item_cov_CaseCtx 𝜋_CaseCtx_r.
Proof. 
  into_gen_measurable.
  rewrite /preimage_set_system.
  intros ?. simpl.
  intros [?[e]<-]; subst.
  have ->: ((ectx_item_cov_CaseCtx `&` 𝜋_CaseCtx_r @^-1` (expr_ST e))=
            \bigcup_n [set CaseCtx e1 e' | e' in expr_ST e & e1 in (expr_seq n)]
    ).
  { rewrite eqEsubset; split; intros ?; rewrite /ectx_item_cov_CaseCtx/bigcup/=.
    - intros [[[e0 e1]??]]. subst.
      destruct (expr_shape_enum_surj (shape_expr e0)) as [??].
      repeat eexists _; last done; done.
    - intros [??[??[??]]]. subst.
      split; last done.
      by eexists (_,_). 
  }
  apply bigcup_measurable.
  intros k ?.
  apply sub_sigma_algebra.
  eexists (CaseCtx (gen_expr (expr_shape_enum k)) e).
  - simpl. split; last done. apply gen_expr_generator.
  - rewrite eqEsubset; split; intros ?; simpl.
    + intros [? H1[? ? ]]. subst.
      rewrite -expr_shape_cyl in H1.
      repeat eexists _; last done; done.
    + intros [??[??<-]]. 
      repeat eexists _; try done. by rewrite -expr_shape_cyl.
Qed. 
Hint Resolve 𝜋_CaseCtx_r_meas    : measlang.

Lemma 𝜋_StoreLCtx_v_meas  : measurable_fun ectx_item_cov_StoreLCtx 𝜋_StoreLCtx_v.
Proof. into_gen_measurable.
       rewrite /preimage_set_system.
       intros x[?[x1?<-] <-].
       apply sub_sigma_algebra.
       eexists (StoreLCtx x1); first done.
       simpl. 
       rewrite eqEsubset; split; intros ?; simpl.
       - intros [?? <-]. split; last done. rewrite /ectx_item_cov_StoreLCtx. naive_solver.
       - rewrite /ectx_item_cov_StoreLCtx/=.
         intros [[??<-]?]. simpl in *. naive_solver.
Qed.
Hint Resolve 𝜋_StoreLCtx_v_meas  : measlang.

Lemma 𝜋_StoreRCtx_e_meas  : measurable_fun ectx_item_cov_StoreRCtx 𝜋_StoreRCtx_e.
Proof. into_gen_measurable.
       rewrite /preimage_set_system.
       intros x[?[x1?<-] <-].
       apply sub_sigma_algebra.
       eexists (StoreRCtx x1); first done.
       simpl. 
       rewrite eqEsubset; split; intros ?; simpl.
       - intros [?? <-]. split; last done. rewrite /ectx_item_cov_StoreRCtx. naive_solver.
       - rewrite /ectx_item_cov_StoreRCtx/=.
         intros [[??<-]?]. simpl in *. naive_solver.
Qed.
Hint Resolve 𝜋_StoreRCtx_e_meas  : measlang.

Lemma 𝜋_RandLCtx_v_meas   : measurable_fun ectx_item_cov_RandLCtx 𝜋_RandLCtx_v.
Proof. into_gen_measurable.
       rewrite /preimage_set_system.
       intros x[?[x1?<-] <-].
       apply sub_sigma_algebra.
       eexists (RandLCtx x1); first done.
       simpl. 
       rewrite eqEsubset; split; intros ?; simpl.
       - intros [?? <-]. split; last done. rewrite /ectx_item_cov_RandLCtx. naive_solver.
       - rewrite /ectx_item_cov_RandLCtx/=.
         intros [[??<-]?]. simpl in *. naive_solver.
Qed.
Hint Resolve 𝜋_RandLCtx_v_meas   : measlang.

Lemma 𝜋_RandRCtx_e_meas   : measurable_fun ectx_item_cov_RandRCtx 𝜋_RandRCtx_e.
Proof. into_gen_measurable.
       rewrite /preimage_set_system.
       intros x[?[x1?<-] <-].
       apply sub_sigma_algebra.
       eexists (RandRCtx x1); first done.
       simpl. 
       rewrite eqEsubset; split; intros ?; simpl.
       - intros [?? <-]. split; last done. rewrite /ectx_item_cov_RandRCtx. naive_solver.
       - rewrite /ectx_item_cov_RandRCtx/=.
         intros [[??<-]?]. simpl in *. naive_solver.
Qed.
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
      (ssrfun.comp 𝜋_BinOpRCtx_op $ fst)
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
Proof.
  mf_unfold_fun.
  mf_cmp_tree; first by apply AppU_meas_fun. (* Why doesnt mf_done work here? *)
  pose proof ectx_item_cov_AppLCtx_meas.
  mf_prod.
  { apply: measurable_snd_restriction; ms_solve. }
  mf_cmp_tree; first apply ValU_meas_fun.
  eapply @measurable_comp; [done| | apply 𝜋_AppLCtx_v_meas|].
  { intros ?. simpl. intros [??]. naive_solver. }
  apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_AppRCtx_meas      : measurable_fun (setX ectx_item_cov_AppRCtx      setT) fill_item_AppRCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply AppU_meas_fun. 
  pose proof ectx_item_cov_AppRCtx_meas.
  mf_prod.
  2: { apply: measurable_snd_restriction; ms_solve. }
  eapply @measurable_comp; [done| | apply 𝜋_AppRCtx_e_meas|].
  { intros ?. simpl. intros [??]. naive_solver. }
  apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_UnOpCtx_meas      : measurable_fun (setX ectx_item_cov_UnOpCtx      setT) fill_item_UnOpCtx.
Proof.
  mf_unfold_fun.
  mf_cmp_tree; first by apply UnOpU_meas_fun. 
  pose proof ectx_item_cov_UnOpCtx_meas.
  mf_prod.
  2: { apply: measurable_snd_restriction; ms_solve. }
  eapply @measurable_comp; [done| | apply 𝜋_UnOpCtx_op_meas|].
  { intros ?. simpl. intros [??]. naive_solver. }
  apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_BinOpLCtx_meas    : measurable_fun (setX ectx_item_cov_BinOpLCtx    setT) fill_item_BinOpLCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply BinOpU_meas_fun. (* Why doesnt mf_done work here? *)
  pose proof ectx_item_cov_BinOpLCtx_meas.
  repeat mf_prod.
  2:{ apply: measurable_snd_restriction; ms_solve. }
  - eapply @measurable_comp; [done| | apply 𝜋_BinOpLCtx_op_meas|].
    { intros ?. simpl. intros [??]. naive_solver. }
    apply: measurable_fst_restriction; ms_solve.
  - mf_cmp_tree; first apply ValU_meas_fun.
    eapply @measurable_comp; [done| | apply 𝜋_BinOpLCtx_v_meas|].
    { intros ?. simpl. intros [??]. naive_solver. }
    apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_BinOpRCtx_meas    : measurable_fun (setX ectx_item_cov_BinOpRCtx    setT) fill_item_BinOpRCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply BinOpU_meas_fun. 
  pose proof ectx_item_cov_BinOpRCtx_meas.
  mf_prod.
  2: { apply: measurable_snd_restriction; ms_solve. }
  mf_prod.
  - eapply @measurable_comp; [done| | apply 𝜋_BinOpRCtx_op_meas|].
    { intros ?. simpl. intros [??]. naive_solver. }
    apply: measurable_fst_restriction; ms_solve.
  - eapply @measurable_comp; [done| | apply 𝜋_BinOpRCtx_e_meas|].
    { intros ?. simpl. intros [??]. naive_solver. }
    apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_IfCtx_meas        : measurable_fun (setX ectx_item_cov_IfCtx        setT) fill_item_IfCtx.
Proof.
  mf_unfold_fun.
  mf_cmp_tree; first by apply IfU_meas_fun. 
  pose proof ectx_item_cov_IfCtx_meas.
  repeat mf_prod.
  { apply: measurable_snd_restriction; ms_solve. }
  - eapply @measurable_comp; [done| | apply 𝜋_IfCtx_l_meas|].
    { intros ?. simpl. intros [??]. naive_solver. }
    apply: measurable_fst_restriction; ms_solve.
  - eapply @measurable_comp; [done| | apply 𝜋_IfCtx_r_meas|].
    { intros ?. simpl. intros [??]. naive_solver. }
    apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_PairLCtx_meas     : measurable_fun (setX ectx_item_cov_PairLCtx     setT) fill_item_PairLCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply PairU_meas_fun. 
  pose proof ectx_item_cov_PairLCtx_meas.
  mf_prod.
  1: { apply: measurable_snd_restriction; ms_solve. }
  mf_cmp_tree; first by apply ValU_meas_fun.
  eapply @measurable_comp; [done| | apply 𝜋_PairLCtx_v_meas|].
  { intros ?. simpl. intros [??]. naive_solver. }
  apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_PairRCtx_meas     : measurable_fun (setX ectx_item_cov_PairRCtx     setT) fill_item_PairRCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply PairU_meas_fun. 
  pose proof ectx_item_cov_PairRCtx_meas.
  mf_prod.
  2: { apply: measurable_snd_restriction; ms_solve. }
  eapply @measurable_comp; [done| | apply 𝜋_PairRCtx_e_meas|].
  { intros ?. simpl. intros [??]. naive_solver. }
  apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_FstCtx_meas       : measurable_fun (setX ectx_item_cov_FstCtx       setT) fill_item_FstCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply FstU_meas_fun. 
  pose proof ectx_item_cov_FstCtx_meas.
  mf_prod.
  apply: measurable_snd_restriction; ms_solve. 
Qed.
Lemma fill_item_SndCtx_meas       : measurable_fun (setX ectx_item_cov_SndCtx       setT) fill_item_SndCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply SndU_meas_fun. 
  pose proof ectx_item_cov_SndCtx_meas.
  mf_prod.
  apply: measurable_snd_restriction; ms_solve. 
Qed.
Lemma fill_item_InjLCtx_meas      : measurable_fun (setX ectx_item_cov_InjLCtx      setT) fill_item_InjLCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply InjLU_meas_fun. 
  pose proof ectx_item_cov_InjLCtx_meas.
  mf_prod.
  apply: measurable_snd_restriction; ms_solve. 
Qed.
Lemma fill_item_InjRCtx_meas      : measurable_fun (setX ectx_item_cov_InjRCtx      setT) fill_item_InjRCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply InjRU_meas_fun. 
  pose proof ectx_item_cov_InjRCtx_meas.
  mf_prod.
  apply: measurable_snd_restriction; ms_solve. 
Qed.
Lemma fill_item_CaseCtx_meas      : measurable_fun (setX ectx_item_cov_CaseCtx      setT) fill_item_CaseCtx.
Proof.
  mf_unfold_fun.
  mf_cmp_tree; first by apply CaseU_meas_fun. 
  pose proof ectx_item_cov_CaseCtx_meas.
  repeat mf_prod.
  { apply: measurable_snd_restriction; ms_solve. }
  - eapply @measurable_comp; [done| | apply 𝜋_CaseCtx_l_meas|].
    { intros ?. simpl. intros [??]. naive_solver. }
    apply: measurable_fst_restriction; ms_solve.
  - eapply @measurable_comp; [done| | apply 𝜋_CaseCtx_r_meas|].
    { intros ?. simpl. intros [??]. naive_solver. }
    apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_AllocCtx_meas     : measurable_fun (setX ectx_item_cov_AllocCtx   setT) fill_item_AllocCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply AllocU_meas_fun. 
  pose proof ectx_item_cov_AllocCtx_meas.
  mf_prod.
  apply: measurable_snd_restriction; ms_solve. 
Qed.
Lemma fill_item_LoadCtx_meas      : measurable_fun (setX ectx_item_cov_LoadCtx      setT) fill_item_LoadCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply LoadU_meas_fun. 
  pose proof ectx_item_cov_LoadCtx_meas.
  mf_prod.
  apply: measurable_snd_restriction; ms_solve. 
Qed.
Lemma fill_item_StoreLCtx_meas    : measurable_fun (setX ectx_item_cov_StoreLCtx    setT) fill_item_StoreLCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply StoreU_meas_fun. 
  pose proof ectx_item_cov_StoreLCtx_meas.
  mf_prod.
  1: { apply: measurable_snd_restriction; ms_solve. }
  mf_cmp_tree; first by apply ValU_meas_fun.
  eapply @measurable_comp; [done| | apply 𝜋_StoreLCtx_v_meas|].
  { intros ?. simpl. intros [??]. naive_solver. }
  apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_StoreRCtx_meas    : measurable_fun (setX ectx_item_cov_StoreRCtx    setT) fill_item_StoreRCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply StoreU_meas_fun. 
  pose proof ectx_item_cov_StoreRCtx_meas.
  mf_prod.
  2: { apply: measurable_snd_restriction; ms_solve. }
  eapply @measurable_comp; [done| | apply 𝜋_StoreRCtx_e_meas|].
  { intros ?. simpl. intros [??]. naive_solver. }
  apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_AllocTapeCtx_meas : measurable_fun (setX ectx_item_cov_AllocTapeCtx setT) fill_item_AllocTapeCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply AllocTapeU_meas_fun. 
  pose proof ectx_item_cov_AllocTapeCtx_meas.
  mf_prod.
  apply: measurable_snd_restriction; ms_solve. 
Qed.
Lemma fill_item_RandLCtx_meas     : measurable_fun (setX ectx_item_cov_RandLCtx     setT) fill_item_RandLCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply RandU_meas_fun. 
  pose proof ectx_item_cov_RandLCtx_meas.
  mf_prod.
  1: { apply: measurable_snd_restriction; ms_solve. }
  mf_cmp_tree; first by apply ValU_meas_fun.
  eapply @measurable_comp; [done| | apply 𝜋_RandLCtx_v_meas|].
  { intros ?. simpl. intros [??]. naive_solver. }
  apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_RandRCtx_meas     : measurable_fun (setX ectx_item_cov_RandRCtx     setT) fill_item_RandRCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply RandU_meas_fun. 
  pose proof ectx_item_cov_RandRCtx_meas.
  mf_prod.
  2: { apply: measurable_snd_restriction; ms_solve. }
  eapply @measurable_comp; [done| | apply 𝜋_RandRCtx_e_meas|].
  { intros ?. simpl. intros [??]. naive_solver. }
  apply: measurable_fst_restriction; ms_solve.
Qed.
Lemma fill_item_URandCtx_meas     : measurable_fun (setX ectx_item_cov_URandCtx     setT) fill_item_URandCtx.
Proof. mf_unfold_fun.
  mf_cmp_tree; first by apply UrandU_meas_fun. 
  pose proof ectx_item_cov_URandCtx_meas.
  mf_prod.
  apply: measurable_snd_restriction; ms_solve. 
Qed.
Lemma fill_item_TickCtx_meas      : measurable_fun (setX ectx_item_cov_TickCtx      setT) fill_item_TickCtx.
Proof. 
  mf_unfold_fun.
  mf_cmp_tree; first by apply TickU_meas_fun. 
  pose proof ectx_item_cov_TickCtx_meas.
  mf_prod.
  apply: measurable_snd_restriction; ms_solve. 
Qed.

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


Definition fill_item': (ectx_item * expr)%type -> expr :=
  if_in (ectx_item_cov_AppLCtx \o fst) fill_item_AppLCtx $
  if_in (ectx_item_cov_AppRCtx \o fst) fill_item_AppRCtx $
  if_in (ectx_item_cov_UnOpCtx \o fst) fill_item_UnOpCtx $
  if_in (ectx_item_cov_BinOpLCtx \o fst) fill_item_BinOpLCtx $
  if_in (ectx_item_cov_BinOpRCtx \o fst) fill_item_BinOpRCtx $
  if_in (ectx_item_cov_IfCtx \o fst) fill_item_IfCtx $
  if_in (ectx_item_cov_PairLCtx \o fst) fill_item_PairLCtx $
  if_in (ectx_item_cov_PairRCtx \o fst) fill_item_PairRCtx $
  if_in (ectx_item_cov_FstCtx \o fst) fill_item_FstCtx $
  if_in (ectx_item_cov_SndCtx \o fst) fill_item_SndCtx $
  if_in (ectx_item_cov_InjLCtx \o fst) fill_item_InjLCtx $
  if_in (ectx_item_cov_InjRCtx \o fst) fill_item_InjRCtx $
  if_in (ectx_item_cov_CaseCtx \o fst) fill_item_CaseCtx $
  if_in (ectx_item_cov_AllocCtx \o fst) fill_item_AllocCtx $
  if_in (ectx_item_cov_LoadCtx \o fst) fill_item_LoadCtx $
  if_in (ectx_item_cov_StoreLCtx \o fst) fill_item_StoreLCtx $
  if_in (ectx_item_cov_StoreRCtx \o fst) fill_item_StoreRCtx $
  if_in (ectx_item_cov_AllocTapeCtx \o fst) fill_item_AllocTapeCtx $
  if_in (ectx_item_cov_RandLCtx \o fst) fill_item_RandLCtx $
  if_in (ectx_item_cov_RandRCtx \o fst) fill_item_RandRCtx $
  if_in (ectx_item_cov_URandCtx \o fst) fill_item_URandCtx $
  if_in (ectx_item_cov_TickCtx \o fst) fill_item_TickCtx $
    cst inhabitant.

Local Ltac force_ectx_item_cov:=
  (first [apply ectx_item_cov_AppLCtx_meas|
          apply ectx_item_cov_AppRCtx_meas|
          apply ectx_item_cov_UnOpCtx_meas|
          apply ectx_item_cov_BinOpLCtx_meas|
          apply ectx_item_cov_BinOpRCtx_meas|
          apply ectx_item_cov_IfCtx_meas|
          apply ectx_item_cov_PairLCtx_meas|
          apply ectx_item_cov_PairRCtx_meas|
          apply ectx_item_cov_FstCtx_meas|
          apply ectx_item_cov_SndCtx_meas|
          apply ectx_item_cov_InjLCtx_meas|
          apply ectx_item_cov_InjRCtx_meas|
          apply ectx_item_cov_CaseCtx_meas|
          apply ectx_item_cov_AllocCtx_meas|
          apply ectx_item_cov_LoadCtx_meas|
          apply ectx_item_cov_StoreLCtx_meas|
          apply ectx_item_cov_StoreRCtx_meas|
          apply ectx_item_cov_AllocTapeCtx_meas|
          apply ectx_item_cov_RandLCtx_meas|
          apply ectx_item_cov_RandRCtx_meas|
          apply ectx_item_cov_URandCtx_meas|
           apply ectx_item_cov_TickCtx_meas|simpl]).

Local Ltac subset_solver :=
  intros []; simpl; elim; first [intros ->? |intros []?]; repeat split; subst; first [by intros []|intros [[]]]; subst;simplify_eq.

Lemma fill_item'_meas_fun : measurable_fun setT fill_item'.
Proof.
  rewrite /fill_item'.
  assert (∀ x, x \o fst (A:=ectx_item) (B:=expr) = x `*` setT) as Hrewrite; last rewrite !Hrewrite.
  { intros. rewrite eqEsubset; split; intros ?; naive_solver. }
  eapply @if_in_meas_fun; [ms_solve; force_ectx_item_cov |
                            ms_solve |
                            rewrite setIT; eauto with mf_fun|
    ].
  repeat  (eapply @if_in_meas_fun; [ms_solve; force_ectx_item_cov|
                            ms_solve; force_ectx_item_cov|
                            rewrite setIT setIidl; [eauto with mf_fun|subset_solver]|
          ]).
  apply measurable_cst.
Qed.


Local Ltac unfold_if_in := match goal with | |- context [(if_in (?X \o _) _)] => unfold X end.

Lemma fill_item_fill_item'_eq : fill_item' = fill_item.
Proof.
  apply functional_extensionality_dep.
  intros [Ki e].
  rewrite /fill_item'/fill_item/=.
  repeat unfold_if_in.
  repeat (apply if_in_split; simpl; intros; destruct!/=; first done).
  exfalso.
  destruct Ki; try done.
  - apply H. naive_solver.
  - apply H0; naive_solver.
  - apply H1; naive_solver.
  - apply H2; eexists (_,_); naive_solver.
  - apply H3; eexists (_,_); naive_solver.
  - apply H4; eexists (_,_); naive_solver.
  - apply H5; naive_solver.
  - apply H6; naive_solver.
  - apply H11; eexists (_,_); naive_solver.
  - apply H14; naive_solver.
  - apply H15; naive_solver.
  - apply H17; naive_solver.
  - apply H18; naive_solver.
Qed.

Lemma fill_item_meas_fun : measurable_fun setT fill_item.
Proof. rewrite -fill_item_fill_item'_eq. apply fill_item'_meas_fun. Qed. 

Definition noval (x : expr * ectx_item) : option (ectx_item * expr)%type :=
  match x.1 with
  | Val _ => None
  | _ => Some (snd x, fst x)
  end.

Lemma noval_measurable : measurable_fun setT noval.
  have -> : noval = if_in (setX ecov_val setT) (cst None) (Some \o (snd △ fst)).
  { apply funext; intro x; rewrite /noval/if_in.
    destruct x as [[]?]; simpl.
    1: { rewrite bool_decide_eq_true_2; [done|]. split; [by eexists _; eauto |done]. }
    all: rewrite bool_decide_eq_false_2 //=.
    all: intros [HK ?]; by inversion HK.
  }
  eapply @if_in_meas_fun.
  { ms_prod.
    { by eauto with mf_set. }
    { by eapply @measurableT. }
  }
  { by eapply @measurableT. }
  { by eapply @measurable_cst. }
  { apply mathcomp_measurable_fun_restiction_setT.
    { by ms_solve. }
    mf_cmp_tree.
    { by eapply @Some_meas_fun. }
    { by mf_prod. }
  }
Qed.

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

Definition decomp_cov_stuck      : set expr :=
  setC (\bigcup_(i in
            ([set
              decomp_cov_app_val    ;
              decomp_cov_app_expr   ;
              decomp_cov_unop       ;
              decomp_cov_binop_val  ;
              decomp_cov_binop_expr ;
              decomp_cov_if         ;
              decomp_cov_pair_val   ;
              decomp_cov_pair_expr  ;
              decomp_cov_fst        ;
              decomp_cov_snd        ;
              decomp_cov_injl       ;
              decomp_cov_injr       ;
              decomp_cov_case       ;
              decomp_cov_alloc      ;
              decomp_cov_load       ;
              decomp_cov_store_val  ;
              decomp_cov_store_expr ;
              decomp_cov_alloctape  ;
              decomp_cov_rand_val   ;
              decomp_cov_rand_expr  ;
              decomp_cov_tick])
              ) i)
    . (* Complement of the union of the prior cases.*)

Lemma decomp_cov_app_val_meas     : measurable decomp_cov_app_val. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_app_expr_meas    : measurable decomp_cov_app_expr. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_unop_meas        : measurable decomp_cov_unop. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_binop_val_meas   : measurable decomp_cov_binop_val. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_binop_expr_meas  : measurable decomp_cov_binop_expr. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_if_meas          : measurable decomp_cov_if. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_pair_val_meas    : measurable decomp_cov_pair_val. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_pair_expr_meas   : measurable decomp_cov_pair_expr. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_fst_meas         : measurable decomp_cov_fst. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_snd_meas         : measurable decomp_cov_snd. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_injl_meas        : measurable decomp_cov_injl. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_injr_meas        : measurable decomp_cov_injr. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_case_meas        : measurable decomp_cov_case. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_alloc_meas       : measurable decomp_cov_alloc. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_load_meas        : measurable decomp_cov_load. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_store_val_meas   : measurable decomp_cov_store_val. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_store_expr_meas  : measurable decomp_cov_store_expr. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_alloctape_meas   : measurable decomp_cov_alloctape. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_rand_val_meas    : measurable decomp_cov_rand_val. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_rand_expr_meas   : measurable decomp_cov_rand_expr. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_urand_meas       : measurable decomp_cov_urand. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_tick_meas        : measurable decomp_cov_tick. Proof. ms_unfold; ms_solve. Qed.
Lemma decomp_cov_stuck_meas       : measurable decomp_cov_stuck.
Proof.
  ms_unfold.
  apply measurableC.
  apply: fin_bigcup_measurable.
  { rewrite !cardinality.finite_setU; do! split; apply: cardinality.finite_set1. }
  intros i. simpl.
  (* I don't believe in automation. *)
  intros [[[[[[[[[[[[[[[[[[[[|]|]|]|]|]|]|]|]|]|]|]|]|]|]|]|]|]|]|]|];
    subst; ms_unfold; ms_solve.
Qed.

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
  mProd 𝜋_Pair_l (ssrfun.comp PairLCtxU $ ssrfun.comp 𝜋_Val_v $ 𝜋_Pair_r).

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
  mProd 𝜋_Rand_N (ssrfun.comp RandLCtxU $ ssrfun.comp 𝜋_Val_v 𝜋_Rand_t).

Definition decomp_rand_expr  : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp Some $
  mProd (ssrfun.comp RandRCtxU 𝜋_Rand_N) 𝜋_Rand_t.

Definition decomp_urand      : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_URand_e (cst URandCtxU).

Definition decomp_tick       : expr -> (option (ectx_item * expr)%type) :=
  ssrfun.comp noval $
  mProd 𝜋_Tick_e (cst TickCtxU).

Definition decomp_stuck      : expr -> (option (ectx_item * expr)%type) :=
  cst None.

Local Lemma setIfront {T} (A B: set T): A `&` B = A `&` (A `&` B).
Proof.
  by rewrite setIA setIid.
Qed.

Local Ltac mf_cmp_tree' :=
  eapply @measurable_comp; simpl;
  last (rewrite setIfront;
        apply @measurable_fun_setI1; [by ms_done| by ms_solve |by mf_done]); last first.

Local Ltac mf_solve' := rewrite setIfront; apply measurable_fun_setI1; last mf_done; ms_solve.
Local Ltac mf_unfold' := mf_unfold_fun; mf_unfold_dom.
Lemma decomp_app_val_meas    : measurable_fun decomp_cov_app_val    decomp_app_val.
Proof.
  mf_unfold'.
  mf_cmp_tree; first apply noval_measurable.
  mf_prod; first mf_solve'.
  mf_cmp_tree; first apply AppLCtxU_measurable.
  mf_cmp_tree'; first mf_done; ms_solve.
  intros ?. simpl. intros [?[[[]][?[]]]?]; subst; simpl in *; subst. naive_solver.
Qed.
Lemma decomp_app_expr_meas   : measurable_fun decomp_cov_app_expr   decomp_app_expr.
Proof.
  mf_unfold'.
  mf_cmp_tree; first apply: Some_meas_fun. 
  mf_prod; last mf_solve'.
  mf_cmp_tree'; first apply AppRCtxU_measurable; ms_solve.
Qed. 
Lemma decomp_unop_meas       : measurable_fun decomp_cov_unop       decomp_unop.
Proof.
  mf_unfold'.
  mf_cmp_tree; first apply noval_measurable.
  mf_prod.
  mf_cmp_tree; mf_done.
Qed.
Lemma decomp_binop_val_meas  : measurable_fun decomp_cov_binop_val  decomp_binop_val.
Proof.
  mf_unfold'.
  mf_cmp_tree; first apply noval_measurable.
  mf_prod; first mf_solve'.
  mf_cmp_tree; first apply BinOpLCtxU_measurable.
  mf_prod; first mf_solve'.
  mf_cmp_tree'; first mf_done; ms_solve.
  intros ?. simpl. intros [?[[[[]]][?[]]]]; subst; simpl in *; subst; naive_solver.
Qed.
Lemma decomp_binop_expr_meas : measurable_fun decomp_cov_binop_expr decomp_binop_expr.
Proof.
  mf_unfold'.
  mf_cmp_tree; first apply: Some_meas_fun.
  mf_prod; last mf_solve'.
  mf_cmp_tree; first apply BinOpRCtxU_measurable.
  mf_prod; mf_solve'.
Qed.
Lemma decomp_if_meas         : measurable_fun decomp_cov_if         decomp_if.
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod.
  mf_cmp_tree; first apply IfCtxU_measurable.
  mf_prod.
Qed.
Lemma decomp_pair_val_meas   : measurable_fun decomp_cov_pair_val   decomp_pair_val.
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod; first mf_solve'.
  mf_cmp_tree; first apply PairLCtxU_measurable.
  mf_cmp_tree'; first mf_done; ms_solve.
  intros ?. simpl. intros [?[[[]][?[]]]]; subst; simpl in *; subst.
  naive_solver.
Qed.
Lemma decomp_pair_expr_meas  : measurable_fun decomp_cov_pair_expr  decomp_pair_expr.
Proof.
  mf_unfold'. mf_cmp_tree; first apply: Some_meas_fun.
  mf_prod; last mf_solve'.
  mf_cmp_tree'; first apply PairRCtxU_measurable; ms_solve.
Qed.
Lemma decomp_fst_meas        : measurable_fun decomp_cov_fst        decomp_fst.
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod.
Qed.
Lemma decomp_snd_meas        : measurable_fun decomp_cov_snd        decomp_snd.
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod.
Qed.
Lemma decomp_injl_meas       : measurable_fun decomp_cov_injl       decomp_injl.
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod.
Qed.
Lemma decomp_injr_meas       : measurable_fun decomp_cov_injr       decomp_injr. 
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod.
Qed.
Lemma decomp_case_meas       : measurable_fun decomp_cov_case       decomp_case.
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod.
  mf_cmp_tree; first apply CaseCtxU_measurable.
  mf_prod.
Qed.
Lemma decomp_alloc_meas      : measurable_fun decomp_cov_alloc      decomp_alloc. 
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod.
Qed.
Lemma decomp_load_meas       : measurable_fun decomp_cov_load       decomp_load. 
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod.
Qed.
Lemma decomp_store_val_meas  : measurable_fun decomp_cov_store_val  decomp_store_val.
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod; first mf_solve'.
  mf_cmp_tree; first apply StoreLCtxU_measurable.
  mf_cmp_tree'; first mf_done; ms_solve.
  intros ?; simpl. intros [?[[[]][?[]]]]; subst; simpl in *; subst.
  naive_solver.
Qed.
Lemma decomp_store_expr_meas : measurable_fun decomp_cov_store_expr decomp_store_expr.
Proof.
  mf_unfold'. mf_cmp_tree; first apply: Some_meas_fun.
  mf_prod; last mf_solve'.
  mf_cmp_tree'; first apply StoreRCtxU_measurable; ms_solve.
Qed.
Lemma decomp_alloctape_meas  : measurable_fun decomp_cov_alloctape  decomp_alloctape. 
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod.
Qed.
Lemma decomp_rand_val_meas   : measurable_fun decomp_cov_rand_val   decomp_rand_val.
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod; first mf_solve'.
  mf_cmp_tree; first apply RandLCtxU_measurable.
  mf_cmp_tree'; first mf_done; ms_solve.
  intros ?; simpl. intros [?[[[]][?[]]]]; subst; simpl in *; subst.
  naive_solver.
Qed.
Lemma decomp_rand_expr_meas  : measurable_fun decomp_cov_rand_expr  decomp_rand_expr.
Proof.
  mf_unfold'. mf_cmp_tree; first apply: Some_meas_fun.
  mf_prod; last mf_solve'.
  mf_cmp_tree'; first apply RandRCtxU_measurable; ms_solve.
Qed.
Lemma decomp_urand_meas      : measurable_fun decomp_cov_urand      decomp_urand. 
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod.
Qed.
Lemma decomp_tick_meas       : measurable_fun decomp_cov_tick       decomp_tick. 
Proof.
  mf_unfold'. mf_cmp_tree; first apply noval_measurable.
  mf_prod.
Qed.
(* technically no need for decomp_cov_stuck *)
Lemma decomp_stuck_meas      : measurable_fun setT     decomp_stuck.
Proof.
  apply measurable_cst.
Qed.

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


Definition decomp_item' : expr -> option (ectx_item * expr)%type :=
  if_in decomp_cov_app_val decomp_app_val $
  if_in decomp_cov_app_expr decomp_app_expr $
  if_in decomp_cov_unop decomp_unop $
  if_in decomp_cov_binop_val decomp_binop_val $
  if_in decomp_cov_binop_expr decomp_binop_expr $
  if_in decomp_cov_if decomp_if $
  if_in decomp_cov_pair_val decomp_pair_val $
  if_in decomp_cov_pair_expr decomp_pair_expr $
  if_in decomp_cov_fst decomp_fst $
  if_in decomp_cov_snd decomp_snd $
  if_in decomp_cov_injl decomp_injl $
  if_in decomp_cov_injr decomp_injr $
  if_in decomp_cov_case decomp_case $
  if_in decomp_cov_alloc decomp_alloc $
  if_in decomp_cov_load decomp_load $
  if_in decomp_cov_store_val decomp_store_val $
  if_in decomp_cov_store_expr decomp_store_expr $
  if_in decomp_cov_alloctape decomp_alloctape $
  if_in decomp_cov_rand_val decomp_rand_val $
  if_in decomp_cov_rand_expr decomp_rand_expr $
  if_in decomp_cov_urand decomp_urand $
  if_in decomp_cov_tick decomp_tick $
        decomp_stuck.

Local Ltac subset_solver' :=
    intros ?; simpl; intros []; simpl in *; destruct!/=; repeat split; intros []; simpl in *; destruct!/=; naive_solver.

Lemma decomp_item'_meas_fun : measurable_fun setT decomp_item'.
Proof.
  rewrite /decomp_item'.
  eapply @if_in_meas_fun; [ms_unfold; ms_solve|ms_solve| rewrite setIT; eauto with measlang|].
  do 21 (eapply @if_in_meas_fun; [ms_unfold; ms_solve|ms_solve; ms_unfold; ms_solve
                          |rewrite setIT setIidl; [eauto with measlang|subset_solver']|
    ]).
  apply: measurable_funS; last eauto with measlang; done.
Qed. 

Local Ltac unfold_left :=
  match goal with
  | |- ?X _ = _ => unfold X; simpl
  end.

Local Ltac smart_intro := match goal with
                     | |- (@ex2 (_*_*_) _ _) => eexists (_,_,_)
                     | |- (@ex2 (_*_) _ _) => eexists (_,_)
                    | |- (@ex2 (_) _ _) => eexists (_)
                    | |- _ => simpl
                    end.

Local Ltac unfold_left' :=
  repeat (match goal with
  | H : ¬ (?X _) |- _ => unfold X in H; simpl in *
          end).

Local Ltac decomp_solver := repeat split; smart_intro; naive_solver.
Local Ltac decomp_solver' e2 H1 H2:=
  let Heqn:= fresh "e2" in destruct (to_val e2) eqn:Heqn; first apply of_to_val in Heqn; subst; [apply H1; decomp_solver|apply H2;repeat split; smart_intro; [naive_solver..|]; intros []; simplify_eq ].
Lemma decomp_item_decomp_eq : decomp_item' = decomp_item.
Proof.
  apply functional_extensionality_dep.
  intros e.
  rewrite /decomp_item'/decomp_item.
  repeat unfold_if_in.
  apply if_in_split; simpl; [intros []|intros]; destruct!/=; simpl; first done.
  repeat (apply if_in_split; simpl; [intros []|intros]; simpl in *;
    destruct!/=;
      first (unfold_left; case_match; naive_solver)).
  unfold_left'.
  destruct e as [?|?|???|e1 e2|e1 e2|op e1 e2|???|e1 e2|?|?|?|?|???|?|?|e1 e2|?|e1 e2| |?|?]; try done; exfalso.
  - decomp_solver' e2 H H0.
  - apply H1. decomp_solver.
  - decomp_solver' e2 H2 H3.
  - apply H4. decomp_solver.
  - decomp_solver' e2 H5 H6.
  - apply H7. decomp_solver.
  - apply H8. decomp_solver.
  - apply H9. decomp_solver.
  - apply H10. decomp_solver.
  - apply H11. decomp_solver.
  - apply H12. decomp_solver.
  - apply H13. decomp_solver.
  - decomp_solver' e2 H14 H15.
  - apply H16. decomp_solver.
  - decomp_solver' e2 H17 H18.
  - apply H19. decomp_solver.
  - apply H20. decomp_solver.
Qed.

Lemma decomp_item_meas_fun : measurable_fun setT decomp_item.
Proof. rewrite -decomp_item_decomp_eq. apply decomp_item'_meas_fun. Qed. 


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


(* Slow proof, but best we got *)
(* uncomment the slow proof *)
Lemma decomp_expr_ord Ki e e' : decomp_item e = Some (Ki, e') → expr_ord e' e.
Proof. Admitted.

(*
  rewrite /expr_ord /decomp_item.
  destruct Ki; repeat case_match; intros [=]; simplify_eq; simpl; lia.
Qed.
*)

Lemma decomp_fill_item Ki e :
  to_val e = None → decomp_item (fill_item (Ki, e)) = Some (Ki, e).
Proof. destruct Ki ; simpl ; by repeat destruct_match. Qed.

(* TODO: this proof is slow, but I do not see how to make it faster... *)
(* TODO: Uncomment the slow proof *)
Lemma decomp_fill_item_2 e e' Ki :
  decomp_item e = Some (Ki, e') → fill_item (Ki, e') = e ∧ to_val e' = None.
Proof. Admitted.
(*
  rewrite /decomp_item ;
    destruct e ; try done ;
    destruct Ki ; cbn ; repeat destruct_match ; intros [=] ; subst ; auto.
Qed.
 *)

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item (Ki1, e1) = fill_item (Ki2, e2) → Ki1 = Ki2.
Proof. destruct Ki2, Ki1;  naive_solver eauto with f_equal. Qed. 

Lemma fill_item_some Ki e : is_Some (to_val (fill_item (Ki, e))) → is_Some (to_val e).
Proof. by destruct Ki, e. Qed.
