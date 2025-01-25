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

Definition ectx_item : measurableType ectx_item_cyl.-sigma := 


















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
