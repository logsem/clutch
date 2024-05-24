(** (Syntactic) Typing for System F_mu_ref with tapes *)
From Autosubst Require Export Autosubst.
From stdpp Require Export stringmap fin_map_dom gmap.
From clutch.prob_lang Require Import lang notation.

Canonical Structure varO := leibnizO var.

Reserved Notation "⟦ τ ⟧" (at level 0, τ at level 70).
Reserved Notation "⟦ τ ⟧ₑ" (at level 0, τ at level 70).
Reserved Notation "⟦ Γ ⟧*" (at level 0, Γ at level 70).

(** * Types *)
Inductive type :=
  | TUnit : type
  | TNat : type
  | TInt : type
  | TBool : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TRec : {bind 1 of type} → type
  | TForall : {bind 1 of type} → type
  | TExists : {bind 1 of type} → type
  | TVar : var → type
  | TRef : type → type
  | TTape : type.

(** Which types are unboxed -- we can only do CAS on locations which hold unboxed types *)
Inductive UnboxedType : type → Prop :=
  | UnboxedTUnit : UnboxedType TUnit
  | UnboxedTNat : UnboxedType TNat
  | UnboxedTInt : UnboxedType TInt
  | UnboxedTBool : UnboxedType TBool
  | UnboxedTRef τ : UnboxedType (TRef τ).

(** Types which support direct equality test (which coincides with ctx equiv).
    This is an auxiliary notion. *)
Inductive EqType : type → Prop :=
  | EqTUnit : EqType TUnit
  | EqTNat : EqType TNat
  | EqTInt : EqType TInt
  | EqTBool : EqType TBool
  | EqTProd τ τ' : EqType τ → EqType τ' → EqType (TProd τ τ')
  | EqSum τ τ' : EqType τ → EqType τ' → EqType (TSum τ τ')
  (* | EQRef τ : EqType (Tref τ) *)
.

Lemma unboxed_type_ref_or_eqtype τ :
  UnboxedType τ → (EqType τ ∨ (∃ τ', τ = TRef τ') ∨ τ = TTape).
Proof. inversion 1; first [ left; by econstructor | right; naive_solver ]. Qed.

(** Autosubst instances *)
Global Instance Ids_type : Ids type. derive. Defined.
Global Instance Rename_type : Rename type. derive. Defined.
Global Instance Subst_type : Subst type. derive. Defined.
Global Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Definition binop_int_res_type (op : bin_op) : option type :=
  match op with
  | MultOp => Some TInt | PlusOp => Some TInt | MinusOp => Some TInt
  | RemOp => Some TInt | QuotOp => Some TInt
  | EqOp => Some TBool | LeOp => Some TBool | LtOp => Some TBool
  | _ => None
  end.
Definition binop_bool_res_type (op : bin_op) : option type :=
  match op with
  | XorOp => Some TBool | EqOp => Some TBool
  | _ => None
  end.
Definition unop_int_res_type (op : un_op) : option type :=
  match op with
  | MinusUnOp => Some TInt
  | _ => None
  end.
Definition unop_bool_res_type (op : un_op) : option type :=
  match op with
  | NegOp => Some TBool
  | _ => None
  end.

Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Notation "()" := TUnit : FType_scope.
Notation "# x" := (TVar x) : FType_scope.
Infix "*" := TProd : FType_scope.
Notation "(*)" := TProd (only parsing) : FType_scope.
Infix "+" := TSum : FType_scope.
Notation "(+)" := TSum (only parsing) : FType_scope.
Infix "→" := TArrow : FType_scope.
Notation "(→)" := TArrow (only parsing) : FType_scope.

Notation "μ: τ" :=
  (TRec τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "∀: τ" :=
  (TForall τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "∃: τ" :=
  (TExists τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "'ref' τ" := (TRef τ%ty) (at level 10, τ at next level, right associativity): FType_scope.

(** * Typing judgements *)
Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).
Reserved Notation "⊢ᵥ v : τ" (at level 20, v, τ at next level).

(* Shift all the indices in the context by one, *)
(*    used when inserting a new type interpretation in Δ. *)
Notation "⤉ Γ" := (Autosubst_Classes.subst (ren (+1)) <$> Γ) (at level 10, format "⤉ Γ").


(** We model type-level lambdas and applications as thunks *)
Notation "Λ: e" := (λ: <>, e)%E (at level 200, only parsing).
Notation "Λ: e" := (λ: <>, e)%V (at level 200, only parsing) : val_scope.
Notation "'TApp' e" := (App e%E #()%E) (at level 200, only parsing).

(* To unfold a recursive type, we need to take a step. We thus define the
unfold operator to be the identity function. *)
Definition rec_unfold : val := λ: "x", "x".
Definition unpack : val := λ: "x" "y", "y" "x".

Notation "'unpack:' x := e1 'in' e2" := (unpack e1%E (Lam x%binder e2%E))
  (at level 200, x at level 1, e1, e2 at level 200, only parsing) : expr_scope.

Notation "'unpack:' x := e1 'in' e2" := (unpack e1%E (LamV x%binder e2%E))
  (at level 200, x at level 1, e1, e2 at level 200, only parsing) : val_scope.

(** Operation lifts *)
Global Instance insert_binder (A : Type): Insert binder A (stringmap A) :=
  binder_insert.

(** Typing itclutch *)
Inductive typed : stringmap type → expr → type → Prop :=
  | Var_typed Γ x τ :
     Γ !! x = Some τ →
     Γ ⊢ₜ Var x : τ
  | Val_typed Γ v τ :
     ⊢ᵥ v : τ →
     Γ ⊢ₜ Val v : τ
  | BinOp_typed_int Γ op e1 e2 τ :
     Γ ⊢ₜ e1 : TInt → Γ ⊢ₜ e2 : TInt →
     binop_int_res_type op = Some τ →
     Γ ⊢ₜ BinOp op e1 e2 : τ
  | BinOp_typed_bool Γ op e1 e2 τ :
     Γ ⊢ₜ e1 : TBool → Γ ⊢ₜ e2 : TBool →
     binop_bool_res_type op = Some τ →
     Γ ⊢ₜ BinOp op e1 e2 : τ
  | UnOp_typed_int Γ op e τ :
     Γ ⊢ₜ e : TInt →
     unop_int_res_type op = Some τ →
     Γ ⊢ₜ UnOp op e : τ
  | UnOp_typed_bool Γ op e τ :
     Γ ⊢ₜ e : TBool →
     unop_bool_res_type op = Some τ →
     Γ ⊢ₜ UnOp op e : τ
  | UnboxedEq_typed Γ e1 e2 τ :
     UnboxedType τ →
     Γ ⊢ₜ e1 : τ → Γ ⊢ₜ e2 : τ →
     Γ ⊢ₜ BinOp EqOp e1 e2 : TBool
  | Pair_typed Γ e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 →
     Γ ⊢ₜ Pair e1 e2 : τ1 * τ2
  | Fst_typed Γ e τ1 τ2 :
     Γ ⊢ₜ e : τ1 * τ2 →
     Γ ⊢ₜ Fst e : τ1
  | Snd_typed Γ e τ1 τ2 :
     Γ ⊢ₜ e : τ1 * τ2 →
     Γ ⊢ₜ Snd e : τ2
  | InjL_typed Γ e τ1 τ2 :
     Γ ⊢ₜ e : τ1 →
     Γ ⊢ₜ InjL e : τ1 + τ2
  | InjR_typed Γ e τ1 τ2 :
     Γ ⊢ₜ e : τ2 →
     Γ ⊢ₜ InjR e : τ1 + τ2
  | Case_typed Γ e0 e1 e2 τ1 τ2 τ3 :
     Γ ⊢ₜ e0 : τ1 + τ2 →
     Γ ⊢ₜ e1 : (τ1 → τ3) →
     Γ ⊢ₜ e2 : (τ2 → τ3) →
     Γ ⊢ₜ Case e0 e1 e2 : τ3
  | If_typed Γ e0 e1 e2 τ :
     Γ ⊢ₜ e0 : TBool →
     Γ ⊢ₜ e1 : τ →
     Γ ⊢ₜ e2 : τ →
     Γ ⊢ₜ If e0 e1 e2 : τ
  | Rec_typed Γ f x e τ1 τ2 :
     <[f:=(τ1 → τ2)%ty]>(<[x:=τ1]>Γ) ⊢ₜ e : τ2 →
     Γ ⊢ₜ (Rec f x e) : (τ1 → τ2)
  | App_typed Γ e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : (τ1 → τ2) →
     Γ ⊢ₜ e2 : τ1 →
     Γ ⊢ₜ App e1 e2 : τ2
 | TLam_typed Γ e τ :
     ⤉ Γ ⊢ₜ e : τ →
     Γ ⊢ₜ (Λ: e) : ∀: τ
  | TApp_typed Γ e τ τ' :
     Γ ⊢ₜ e : (∀: τ) →
     Γ ⊢ₜ e #() : τ.[τ'/]
  | TFold Γ e τ :
     Γ ⊢ₜ e : τ.[(μ: τ)%ty/] →
     Γ ⊢ₜ e : (μ: τ)
  | TUnfold Γ e τ :
     Γ ⊢ₜ e : (μ: τ)%ty →
     Γ ⊢ₜ rec_unfold e : τ.[(μ: τ)%ty/]
  | TPack Γ e τ τ' :
     Γ ⊢ₜ e : τ.[τ'/] →
     Γ ⊢ₜ e : (∃: τ)
  | TUnpack Γ e1 x e2 τ τ2 :
     Γ ⊢ₜ e1 : (∃: τ) →
     <[x:=τ]>(⤉ Γ) ⊢ₜ e2 : (Autosubst_Classes.subst (ren (+1)) τ2) →
     Γ ⊢ₜ (unpack: x := e1 in e2) : τ2
  | TAlloc Γ e τ : Γ ⊢ₜ e : τ → Γ ⊢ₜ Alloc e : ref τ
  | TLoad Γ e τ : Γ ⊢ₜ e : ref τ → Γ ⊢ₜ Load e : τ
  | TStore Γ e e' τ : Γ ⊢ₜ e : ref τ → Γ ⊢ₜ e' : τ → Γ ⊢ₜ Store e e' : ()
  | TAllocTape e Γ : Γ ⊢ₜ e : TNat →  Γ ⊢ₜ AllocTape e : TTape
  | TRand  Γ e1 e2 : Γ ⊢ₜ e1 : TNat → Γ ⊢ₜ e2 : TTape → Γ ⊢ₜ Rand e1 e2 : TNat
  | TRandU Γ e1 e2 : Γ ⊢ₜ e1 : TNat → Γ ⊢ₜ e2 : TUnit → Γ ⊢ₜ Rand e1 e2 : TNat
with val_typed : val → type → Prop :=
  | Unit_val_typed : ⊢ᵥ LitV LitUnit : TUnit                                       
  | Int_val_typed (n : Z) : ⊢ᵥ LitV (LitInt n) : TInt
  | Nat_val_typed (n : nat) : ⊢ᵥ LitV (LitInt n) : TNat                                               
  | Bool_val_typed (b : bool) : ⊢ᵥ LitV (LitBool b) : TBool
  | Pair_val_typed v1 v2 τ1 τ2 :
     ⊢ᵥ v1 : τ1 →
     ⊢ᵥ v2 : τ2 →
     ⊢ᵥ PairV v1 v2 : (τ1 * τ2)
  | InjL_val_typed v τ1 τ2 :
     ⊢ᵥ v : τ1 →
     ⊢ᵥ InjLV v : (τ1 + τ2)
  | InjR_val_typed v τ1 τ2 :
     ⊢ᵥ v : τ2 →
     ⊢ᵥ InjRV v : (τ1 + τ2)
  | Rec_val_typed f x e τ1 τ2 :
     <[f:=TArrow τ1 τ2]>(<[x:=τ1]>∅) ⊢ₜ e : τ2 →
     ⊢ᵥ RecV f x e : (τ1 → τ2)
  | TLam_val_typed e τ :
     ∅ ⊢ₜ e : τ →
     ⊢ᵥ (Λ: e) : (∀: τ)
where "Γ ⊢ₜ e : τ" := (typed Γ e τ)
and "⊢ᵥ e : τ" := (val_typed e τ).

Lemma binop_int_typed_safe (op : bin_op) (n1 n2 : Z) τ :
  binop_int_res_type op = Some τ → is_Some (bin_op_eval op (LitV (LitInt n1)) (LitV (LitInt n2))).
Proof. destruct op; simpl; eauto. Qed.

Lemma binop_bool_typed_safe (op : bin_op) (b1 b2 : bool) τ :
  binop_bool_res_type op = Some τ → is_Some (bin_op_eval op (LitV (LitBool b1)) (LitV (LitBool b2))).
Proof. destruct op; naive_solver. Qed.


Lemma unop_int_typed_safe (op : un_op) (n : Z) τ :
  unop_int_res_type op = Some τ → is_Some (un_op_eval op (LitV (LitInt n))).
Proof. destruct op; simpl; eauto.  Qed.

Lemma unop_bool_typed_safe (op : un_op) (b : bool) τ :
  unop_bool_res_type op = Some τ → is_Some (un_op_eval op (LitV (LitBool b))).
Proof. destruct op; naive_solver. Qed.
