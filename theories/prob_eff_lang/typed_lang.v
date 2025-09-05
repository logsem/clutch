From stdpp                Require Export gmap stringmap.
From clutch.prob_eff_lang Require Export lang notation deep_handler.

(* typed_lang.v *)

(* This file contains the definition of a type system for a simple language
   with support for effect handlers. For now, the language does not contain
   heap-manipulating instructions and the type system does not handle effect
   polymorphism.
*)


(** * Language Constructs. *)

Definition bind' : val := λ: "x" "y", "y" "x".
Definition Bind (e1 e2 : expr) : expr := bind' e1 e2.
Notation "'bind:' x := e1 'in' e2" := (Bind e1%E (Lam x%binder e2%E))
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'bind:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.
Notation "'bind:' x := e1 'in' e2" := (Bind e1%E (LamV x%binder e2%E))
  (at level 200, x at level 1, e1, e2 at level 200,
   format "'[' 'bind:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : val_scope.

Definition Ret (e : expr) : expr := e.
Notation "'ret:' e" := (Ret e%E)
  (at level 200, e at level 200,
   format "'[' 'ret:'  e ']'") : expr_scope.

Definition TLamV' (e : expr) : val  := LamV BAnon e.
Definition TLam'  (e : expr) : expr := Lam  BAnon e.
Notation "'Λ:' e" := (TLamV' e%E)
  (at level 200, e at level 200,
   format "'[' 'Λ:'  e ']'") : val_scope.
Notation "'Λ:' e" := (TLam' e%E)
  (at level 200, e at level 200,
   format "'[' 'Λ:'  e ']'") : expr_scope.

Definition TApp' (e : expr) : expr := App e #()%V.
Notation "e '<_>'" := (TApp' e%E)
  (at level 10,
   format "'[' e '<_>' ']'") : expr_scope.


(** * Syntactic Types. *)

Inductive ty :=
  (* Base types. *)
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TBot  : ty
  (* Arrow type. *)
  | TArr : ty → eff_ty → ty
  (* Effect polymorphic type. *)
  | TForall : ty → ty
  (* Reference type constructor. *)
  | TRef : ty → ty
  | TTape : ty
                  
with eff_ty :=
  (* Effect type. *)
  | TEff : eff_sig → ty → eff_ty

with eff_sig :=
  (* Effect signature. *)
  | TSig : ty → ty → eff_sig
  | TVar : nat → eff_sig.


Section induction_principle.
  Variables (P : ty → Prop).

  Hypothesis
    (TUnit_case : P TUnit)
    (TBool_case : P TBool)
    (TInt_case  : P TInt)
    (TBot_case : P TBot)
    (TTape_case : P TTape)


    (TArrSig_case  : ∀ α β₁ β₂ β,
       P α → P β₁ → P β₂ → P β → P (TArr α (TEff (TSig β₁ β₂) β)))
    (TArrVar_case  : ∀ α n β,
       P α → P β → P (TArr α (TEff (TVar n) β)))

    (TForall_case  : ∀ α,
       P α → P (TForall α))

    (TRef_case  : ∀ α,
       P α → P (TRef α)).

  Definition ty_ind' : ∀ α, P α :=
    fix ty_ind' (α : ty) : P α :=
      match α with
      | TUnit => TUnit_case
      | TBool => TBool_case
      | TInt => TInt_case
      | TBot => TBot_case
      | TTape => TTape_case
      | TArr α (TEff (TSig β₁ β₂) β) =>
          TArrSig_case _ _ _ _ (ty_ind' α) (ty_ind' β₁) (ty_ind' β₂) (ty_ind' β)
      | TArr α (TEff (TVar n) β) =>
          TArrVar_case _ _ _ (ty_ind' α) (ty_ind' β)
      | TForall α =>
          TForall_case _ (ty_ind' α)
      | TRef α =>
          TRef_case _ (ty_ind' α)
                    
      end.

End induction_principle.


Fixpoint ty_lift (n : nat) (α : ty) : ty :=
  match α with
  | TUnit => TUnit
  | TBool => TBool
  | TInt => TInt
  | TBot => TBot
  | TTape => TTape
  | TArr α (TEff (TSig β₁ β₂) β) =>
      let tyL := λ α, ty_lift n α in
      TArr (tyL α) (TEff (TSig (tyL β₁) (tyL β₂)) (tyL β))
  | TArr α (TEff (TVar m) β) =>
      let m' := if (m <? n) then m else S m in
      let tyL := λ α, ty_lift n α in
      TArr (tyL α) (TEff (TVar m') (tyL β))
  | TForall α => TForall (ty_lift (S n) α)
  | TRef α => TRef (ty_lift n α)
  end.

Fixpoint ty_subst (n : nat) (α α₁ α₂ : ty) : ty :=
  match α with
  | TUnit => TUnit
  | TBool => TBool
  | TInt => TInt
  | TBot => TBot
  | TTape => TTape
  | TArr α (TEff (TSig β₁ β₂) β) =>
      let tyS := λ α, ty_subst n α α₁ α₂ in
      TArr (tyS α) (TEff (TSig (tyS β₁) (tyS β₂)) (tyS β))
  | TArr α (TEff (TVar m) β) =>
      let θ :=
        if (m <? n) then (TVar m)
        else if (m =? n) then (TSig α₁ α₂)
        else (TVar (pred m))
      in
      let tyS := λ α, ty_subst n α α₁ α₂ in
      TArr (tyS α) (TEff θ (tyS β))
  | TForall α => TForall (ty_subst (S n) α (ty_lift 0 α₁) (ty_lift 0 α₂))
  | TRef α => TRef (ty_subst n α α₁ α₂)
  end.


Declare Scope ty_scope.
Bind Scope ty_scope with ty.
Bind Scope ty_scope with eff_ty.
Bind Scope ty_scope with eff_sig.
Delimit Scope ty_scope with ty.

Notation "()" := TUnit : ty_scope.
Infix "→" := TArr : ty_scope.
Notation ".< α₁ ; α₂ .> α " := (TEff (TSig α₁ α₂) α)
  (at level 100, α₁, α₂, α at level 200) : ty_scope.
Notation ".< x .> α " := (TEff (TVar x) α)
  (at level 100, x, α at level 200) : ty_scope.
Notation ".<> α " := (TEff (TSig TBot TUnit) α)
  (at level 100, α at level 200) : ty_scope.
Notation "∀: α" := (TForall α%ty)
  (at level 100, α at level 200) : ty_scope.
Notation "'ref' α" := (TRef α) (at level 10, α at next level, right associativity): ty_scope.

(** * Typing Rules. *)

Inductive ty_unboxed : ty → Prop :=
  | TUnit_unboxed : ty_unboxed TUnit
  | TBool_unboxed : ty_unboxed TBool
  | TInt_unboxed : ty_unboxed TInt
  (*| TRef_unboxed α : ty_unboxed (TRef α)*).
Existing Class ty_unboxed.
Existing Instances TUnit_unboxed TBool_unboxed TInt_unboxed (*TRef_unboxed*).

Inductive ty_un_op : un_op → ty → ty → Prop :=
  | Ty_un_op_int op : ty_un_op op TInt TInt
  | Ty_un_op_bool : ty_un_op NegOp TBool TBool.
Existing Class ty_un_op.
Existing Instances Ty_un_op_int Ty_un_op_bool.

Inductive ty_bin_op : bin_op → ty → ty → ty → Prop :=
  | Ty_bin_op_eq α :
     ty_unboxed α → ty_bin_op EqOp α α TBool
  | Ty_bin_op_arith op :
     TCElemOf op [PlusOp; MinusOp; MultOp; QuotOp; RemOp;
                  AndOp; OrOp; XorOp; ShiftLOp; ShiftROp] →
     ty_bin_op op TInt TInt TInt
  | Ty_bin_op_compare op :
     TCElemOf op [LeOp; LtOp] → ty_bin_op op TInt TInt TBool
  | Ty_bin_op_bool op :
     TCElemOf op [AndOp; OrOp; XorOp] → ty_bin_op op TBool TBool TBool.
Existing Class ty_bin_op.
Existing
Instances Ty_bin_op_eq Ty_bin_op_arith Ty_bin_op_compare Ty_bin_op_bool.

Reserved Notation "Γ ⊢ₑ e : τ" (at level 74, e, τ at next level).
Reserved Notation "Γ ⊢ₜ e : α" (at level 74, e, α at next level).
Reserved Notation "⊢ᵥ v : α" (at level 20, v, α at next level).

Inductive eff_typed : gmap string ty → expr → eff_ty → Prop :=
  (* Pure computation. *)
  | Pure_typed Γ e α :
     Γ ⊢ₜ e : α →
     Γ ⊢ₑ e : (.<> α)
  (* Bind. *)
  | Bind_typed Γ e₁ e₂ θ α β :
     Γ ⊢ₑ e₁ : (TEff θ α) →
     Γ ⊢ₜ e₂ : (α → (TEff θ β)) →
     Γ ⊢ₑ Bind e₁ e₂ : (TEff θ β)
  (* Return. *)
  | Return_typed Γ e θ α :
     Γ ⊢ₜ e : α →
     Γ ⊢ₑ Ret e : (TEff θ α)
  (* Do. *)
  | Do_typed Γ e α₁ α₂ :
     Γ ⊢ₜ e : α₁ →
     Γ ⊢ₑ (do: e) : (.< α₁ ; α₂ .> α₂)
  (* Deep handler. *)
  | Deep_try_with_typed Γ e h r α₁ α₂ α τ :
     Γ ⊢ₑ e : (.< α₁ ; α₂ .> α) →
     Γ ⊢ₜ h : (α₁ → .<> ((α₂ → τ) → τ)) →
     Γ ⊢ₜ r : (α → τ) →
     Γ ⊢ₑ (DeepTryWith e h r) : τ
with typed : gmap string ty → expr → ty → Prop :=
  (* Variables. *)
  | Var_typed Γ x α :
     Γ !! x = Some α →
     Γ ⊢ₜ Var x : α
  (* Values. *)
  | Val_typed Γ v α :
     ⊢ᵥ v : α →
     Γ ⊢ₜ v : α
  (* Erase. *)
  | Erase_typed Γ e α :
     Γ ⊢ₑ e : (.<> α) →
     Γ ⊢ₜ e : α
  (* Effect abstraction. *)
  | TLam_typed Γ e α :
     (ty_lift 0) <$> Γ ⊢ₜ e : α →
     Γ ⊢ₜ (Λ: e) : (∀: α)
  | TApp_typed Γ e α α₁ α₂ :
     Γ ⊢ₜ e : (∀: α) →
     Γ ⊢ₜ e <_> : ty_subst 0 α α₁ α₂
  (* Functions. *)
  | Rec_typed Γ f x e α τ :
     binder_insert f (α → τ)%ty (binder_insert x α Γ) ⊢ₑ e : τ →
     Γ ⊢ₜ Rec f x e : (α → τ)
  (* Heap operations. *)
  | Alloc_typed Γ e α :
     Γ ⊢ₜ e : α →
     Γ ⊢ₜ Alloc e : ref α
  | Load_typed Γ e α :
     Γ ⊢ₜ e : ref α →
     Γ ⊢ₜ Load e : α
  | Store_typed Γ e₁ e₂ α :
     Γ ⊢ₜ e₁ : ref α →
     Γ ⊢ₜ e₂ : α →
               Γ ⊢ₜ Store e₁ e₂ : ()
  | TAllocTape e Γ : Γ ⊢ₜ e : TInt →  Γ ⊢ₜ AllocTape e : TTape
  | TRand  Γ e1 e2 : Γ ⊢ₜ e1 : TInt → Γ ⊢ₜ e2 : TTape → Γ ⊢ₜ Rand e1 e2 : TInt (* Changed from Nat to Int. TODO: Add Nat type *)
  | TRandU Γ e1 e2 : Γ ⊢ₜ e1 : TInt → Γ ⊢ₜ e2 : TUnit → Γ ⊢ₜ Rand e1 e2 : TInt
with val_typed : val → ty → Prop :=
  (* Base types. *)
  | Unit_val_typed :
     ⊢ᵥ #() : ()
  | Bool_val_typed (b : bool) :
     ⊢ᵥ #b : TBool
  | Int_val_typed (i : Z) :
     ⊢ᵥ #i : TInt
  (* Functions. *)
  | Rec_val_typed f x e α τ :
     binder_insert f (α → τ)%ty (binder_insert x α ∅) ⊢ₑ e : τ →
     ⊢ᵥ RecV f x e : (α → τ)%ty
  (* Effect abstraction. *)
  | TLam_val_typed e α :
     ∅ ⊢ₜ e : α →
     ⊢ᵥ (Λ: e) : (∀: α)
where "Γ ⊢ₑ e : τ" := (eff_typed Γ e τ)
and "Γ ⊢ₜ e : α" := (typed Γ e α)
and "⊢ᵥ v : α" := (val_typed v α).


(** * Derived Typing Rules. *)

(* Application *)
Lemma App_typed Γ e₁ e₂ α α' :
  Γ ⊢ₜ e₁ : (α → .<> α')%ty →
    Γ ⊢ₜ e₂ : α →
      Γ ⊢ₜ Bind (Ret e₂) e₁ : α'.
Proof.
  intros He₁ He₂.
  apply Erase_typed, (Bind_typed _ _ _ _ α); [| done].
  by apply Return_typed.
Qed.
