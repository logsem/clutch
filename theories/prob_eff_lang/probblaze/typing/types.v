From Autosubst Require Import Autosubst.
From stdpp Require Export strings gmultiset gmap stringmap.
From clutch.prob_eff_lang.probblaze Require Import syntax notation.
From iris.prelude Require Import prelude.


(* This file is mostly borrowed from TES *)
(* https://gitlab.inria.fr/cambium/tes/-/blob/main/theories/effect_system/types.v *)

(** * Syntax. *)

Section syntax.

  (* Sn effect name is a binder. *)
  Definition eff_name := string.

  (* (* S row is a list of effect signatures. *)
     Definition row := list. *)

  (* We use the three-element set [vtype] to indicate the type of the variable
     over which we quantify. *)
  (* Inductive vtype := T | R | M. *)

  Inductive vmode :=
  | OS
  | MS
  | MVar : var → vmode.

  Definition mode_to_vmode (m : mode) : vmode :=
    match m with
    | probblaze.syntax.OS => OS
    | probblaze.syntax.MS => MS
    end.

  Coercion mode_to_vmode : mode >-> vmode.
  
  (* The syntax of types and effect signatures. *)
  Inductive type :=

  (* Base types. *)
  | TBot  : type
  | TTop  : type
  | TUnit : type
  | TBool : type
  | TInt  : type
  | TNat  : type

  (* Reference type. *)
  | TRef : type → type

  (* Tape type. *)
  | TTape : type

  (* Product type. *)
  | TProd : type → type → type

  (* Sum type. *)
  | TSum : type → type → type

  (* Arrow type. *)
  | TArrow : type → row → type → type

  (* Polymorphic type. *)
  (* | TForall : vtype → type → type *)
  | TForallM : {bind 1 of vmode in type} → type

  | TForallT : {bind 1 of type} → type

  | TForallR : {bind 1 of row in type} → type

  (* Existential type. *)
  | TExists : {bind 1 of type} → type

  (* Recursive type. *)
  | TRec : {bind 1 of type} → type

  (* Type variable. *)
  | TVar : var → type

  | TBang : vmode → type → type

  with eff_sig :=

  (* Effect signature. *)
  (* TODO: Consider quantification over type variables in effect signatures. *)
  | SSig : eff_name → {bind 1 of type} → {bind 1 of type} → eff_sig

  | SFlip : vmode → eff_sig → eff_sig

  with row :=

  | RNil : row
  | RCons : eff_sig → row → row
  | RVar : var → row
  | RFlip : vmode → row → row
  | RRec : {bind 1 of row} → row.
                        
  (* (* Row variable. *)
     | RVar : nat → eff_sig. *)

  (* We introduce a shorthand for a signature
     declaring the _absence_ of an effect. *)
  Definition SAbs (s : eff_name) := SSig s TBot TTop.

  (** Autosubst instances *)
  Global Instance Ids_type : Ids type. derive. Defined.
  Global Instance Rename_type : Rename type. derive. Defined.
  Global Instance Subst_type : Subst type. derive. Defined.
  Global Instance SubstLemmas_type : SubstLemmas type. derive. Qed.

  Global Instance Ids_row : Ids row. derive. Defined.
  Global Instance Rename_row : Rename row. derive. Defined.
  Global Instance Subst_row : Subst row. derive. Defined.
  Global Instance SubstLemmas_row : SubstLemmas row. derive. Defined.

  Global Instance Ids_mode : Ids vmode. derive. Defined.
  Global Instance Rename_mode : Rename vmode. derive. Defined.
  Global Instance Subst_mode : Subst vmode. derive. Defined.
  Global Instance SubstLemmas_mode : SubstLemmas vmode. derive. Defined.
  
End syntax.



Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Notation "()" := TUnit : FType_scope.
Notation "⊥" := TBot : FType_scope.
Notation "⊤" := TTop : FType_scope.
Notation "'ℤ'" := TInt : FType_scope.
Notation "'ℕ'" := TNat : FType_scope.
Notation "'𝔹'" := TBool : FType_scope.

(* Notation "# x" := (TVar x) (at level 100, x at next level): FType_scope. *)
Infix "*" := TProd : FType_scope.
Notation "(*)" := TProd (only parsing) : FType_scope.
Infix "+" := TSum : FType_scope.
Notation "(+)" := TSum (only parsing) : FType_scope.
(* TODO: add arrow notation *)
Notation "α '-{' ρ '}-∘' β" := (TArrow α%ty ρ β%ty)
                                 (at level 100, ρ, β at level 200) : FType_scope.
Notation "α -∘ β" := (TArrow α%ty RNil β%ty)
                       (at level 100, β at level 200) : FType_scope.
Notation "α '-{' ρ '}->' β" := (TBang MS (TArrow α%ty ρ β%ty))
                                 (at level 100, ρ, β at level 200) : FType_scope.
Notation "α ⇾ β" := (TBang MS (TArrow α%ty RNil β%ty))
                       (at level 100, β at level 200) : FType_scope.
Notation "μ: τ" :=
  (TRec τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "∀T: τ" :=
  (TForallT τ%ty)
    (at level 100, τ at level 200) : FType_scope.
Notation "∀R: τ" :=
  (TForallR τ%ty)
    (at level 100, τ at level 200) : FType_scope.
Notation "∀M: τ" :=
  (TForallM τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "∃: τ" :=
  (TExists τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "'ref' τ" := (TRef τ%ty) (at level 10, τ at next level, right associativity): FType_scope.
Notation "![ m ] τ" := (TBang m τ%ty) (at level 10, τ at next level, right associativity): FType_scope.
(* Notation "! τ" := (TBang MS τ%ty) (at level 10, τ at next level, right associativity): FType_scope. *)


Section ctx.

  (* A ctx is a multiset of key-value pairs restricting the value to be the same for each instance of the key *)
  Definition ctx := gmap string (type * nat).

  (* insert sets the multiplicity to 1 *)
  Definition ctx_insert (x : string) (t : type) (Γ : ctx) : ctx := <[ x := (t, 1) ]> Γ.

  (* duplicate a variable in the ctx *)
  Definition ctx_contraction (x : string) (Γ : ctx) : ctx :=
    match Γ !! x with
    | Some (t, n) => <[ x := (t, S n) ]> Γ
    | None => Γ
    end. 

  Definition ctx_remove (x : string) (Γ : ctx) : ctx :=
  match Γ !! x with
  | Some (t, S n) => 
      if decide (n = 0) 
      then delete x Γ 
      else <[ x := (t, n) ]> Γ
  (* Not strictly necessary since we remove an instance of 0 multiplicity *)
  | Some (t, 0) => delete x Γ
  | _ => Γ
  end.

  Definition ctx_lookup (x : string) (Γ : ctx) : option type := fmap fst (Γ !! x).

  (* We shouldn't merge to ctx where (x : t) ∈ Γ1 and (x : t') ∈ Γ2 s.t. t ≠ t'  *)
  Definition merge_aux : option (type * nat) → option (type * nat) → option (type * nat) :=
    λ a b,
      match a, b with
      | x, None
      | None, x => x
      | Some (t, n), Some (t', n') => Some (t, n + n')
      end. 
  Definition ctx_append (Γ1 Γ2 : ctx) : ctx := gmap_merge _ _ _ merge_aux Γ1 Γ2.

End ctx.

Notation "'<[' x ':=c' t ']>' Γ" := (ctx_insert x t Γ).
Notation "Γ '!!c' x" := (ctx_lookup x Γ) (at level 100, x at next level).
Notation "'<[' x ':=c + ]>' Γ" := (ctx_contraction x Γ).
Notation "'<[' x ':=c - ]>' Γ" := (ctx_remove x Γ).
Notation "Γ1 ';;' Γ2" := (ctx_append Γ1 Γ2) (at level 100).

(** * Weakening Relation. *)

(** Definitions. *)

(* We define a weakening relation on types, rows, and signatures. *)

Module le.

  Inductive _mode : vmode → vmode → Prop :=
  | MOS_le (m : vmode) : _mode OS m
  | MMS_le (m : vmode) : _mode m MS
  | MTrans_le m1 m2 m3 :
    _mode m1 m2 → _mode m2 m3 → _mode m1 m3
  | MRefl_le m : _mode m m.
                               

   (* A _disjointness context_ is a map that associates an effect name [s]
     to a pair of a set of effect names [ss] and a set of row variables [js].
     This context contains the information that the dynamic instance of [s]
     does not belong to instances of [ss], and that it does not belong to any
     of the set of dynamic instances abstracted by a row variable in [js]. *)
  Definition disj_ctx : Type := gmap eff_name (gmultiset eff_name * gset nat).

  (* [merge_ctx D D'] merges [D] and [D'] by performing the key-wise
     union of effect name sets and row-variable sets. *)
  Definition merge_ctx : disj_ctx → disj_ctx → disj_ctx :=
    union_with (λ '(ss, js) '(rs, ks), Some ((ss ∪ rs), (js ∪ ks))).

  (* [disj_ctx_included D D'] holds if [D] stores less disjointness
     information than [D']. More precisely, for every set of effect names [ss],
     set of row variables [js], and effect name [s], if [D] associates [s] to
     the pair [(ss, js)], then [D'] associates [s] to a pair [(rs, ks)] such
     that [ss ⊆ rs] and [js ⊆ ks]. *)
  (* Definition disj_ctx_included : relation disj_ctx :=
       map_included (λ '(ss, js) '(rs, ks), ss ⊆ rs ∧ js ⊆ ks). *)

  (* [conc_sigs ρ] computes the (multi)set of effect names appearing in [ρ]. *)
  Fixpoint eff_name_from_sig : eff_sig → eff_name :=
    λ σ, match σ with
         | SSig s _ _ => s
         | SFlip _ σ => eff_name_from_sig σ
         end.
  
  Fixpoint conc_sigs : row → gmultiset string :=
    λ ρ,
      match ρ with
      | RNil 
      | RVar _ => ∅
      | RCons σ ρ => {[+ eff_name_from_sig σ +]} ⊎ conc_sigs ρ
      | RFlip _ ρ
      | RRec ρ => conc_sigs ρ
      end.

  (* [abst_sigs ρ] computes the set of row variables appearing in [ρ]. *)
  (* In Affect only one row variable appear in a row at the end *)
  Fixpoint abst_sigs : row → gset nat :=
    λ ρ, match ρ with
         | RNil => ∅
         | RVar i => {[i]}
         | RCons _ ρ
         | RFlip _ ρ
         | RRec ρ => abst_sigs ρ
         end. 

  (* The function [row_to_disj_ctx ρ'] builds a disjointness context by
     exploiting the assumption that there is no aliasing among the dynamic
     labels associated to a row [ρ']. *)
  Definition row_to_disj_ctx (ρ' : row) : disj_ctx :=
    set_to_map (λ s,
      (s, (conc_sigs ρ' ∖ {[+ s +]}, abst_sigs ρ'))
    ) (dom (conc_sigs ρ')).

  (* When deducing the weakening relation between two arrow types,
     we can update the disjointness context with the information
     we learn from the assumption that a row is the disjoint union
     of signatures. *)
  Definition update_disj_ctx : row → disj_ctx → disj_ctx :=
    λ ρ' D, merge_ctx (row_to_disj_ctx ρ') D.

  Inductive _eff_sig : disj_ctx → eff_sig → eff_sig → Prop :=
  (* STrans and SRefl are derivable from SCons and TTrans/TRefl *)
  | SCons_le D s α β α' β' :
    _type D α α' →
    _type D β' β →
    _eff_sig D (SSig s α β) (SSig s α' β')
             
  | SFlipIntro_le D m σ : _eff_sig D σ (SFlip m σ)
  | SFlipElim_le D σ : _eff_sig D (SFlip MS σ) σ
  | SFlipIdemp1_le D m σ : _eff_sig D (SFlip m (SFlip m σ)) (SFlip m σ)
  | SFlipIdemp2_le D m σ : _eff_sig D (SFlip m σ) (SFlip m (SFlip m σ))
  | SFlipComp_le D m' m σ' σ :
    _mode m' m → _eff_sig D σ' σ → _eff_sig D (SFlip m' σ') (SFlip m σ)
  (* SFlipComm is derivable *)

  with _row : disj_ctx → bool → row → row → Prop :=
  | RNil_le D b : _row D b RNil RNil
  | RVar_le D b i : _row D b (RVar i) (RVar i)
  | RExtend_le D b ρ σ : _row D b ρ (RCons σ ρ)
  | RSwap_le D b σ σ' ρ : _row D b (RCons σ (RCons σ' ρ)) (RCons σ' (RCons σ ρ))
  | RCons_le D b σ σ' ρ ρ' :
    _eff_sig D σ σ' →
    _row D false ρ ρ' →
    _row D b (RCons σ ρ) (RCons σ' ρ')
  (* Notice js is atmost the singleton {i} *)
  | RErase_le (D : disj_ctx) s ρ ss js :
    D !! s = Some (ss, js) →
    conc_sigs ρ ⊆ ss →
    abst_sigs ρ ⊆ js →
    _row D true (RCons (SAbs s) ρ) ρ
  | RTrans_le D b ρ1 ρ2 ρ3 :
    _row D b ρ1 ρ2 →
    _row D b ρ2 ρ3 →
    _row D b ρ1 ρ3

  | RUnfold_le D b ρ : _row D b (RRec ρ) (ρ.[RRec ρ/])
  | RFold_le D b ρ : _row D b (ρ.[RRec ρ/]) ρ

  | RFlipNil_le D b m : _row D b (RFlip m RNil) RNil
  | RFlipCons_le D b m σ ρ : _row D b (RFlip m (RCons σ ρ)) (RCons (SFlip m σ) (RFlip m ρ))
  | RFlipRec_le D b m ρ :
    _row D b (RFlip m ρ) ρ → _row D b (RFlip m (RRec ρ)) (RRec ρ)
  | RFlipElim_le D b ρ : _row D b (RFlip MS ρ) ρ
  | RFlipIntro_le D b m ρ : _row D b ρ (RFlip m ρ)
  | RFlipIdemp1_le D b m ρ : _row D b (RFlip m (RFlip m ρ)) (RFlip m ρ)
  | RFlipIdemp2_le D b m ρ : _row D b (RFlip m ρ) (RFlip m (RFlip m ρ))
  | RFlipComp_le D b m' m ρ' ρ :
    _mode m' m →
    _row D b ρ' ρ →
    _row D b (RFlip m' ρ') (RFlip m ρ)
         
         (* RFlipComm is derivable *)

  with _type : disj_ctx → type → type → Prop :=
  | TRefl_le D α : _type D α α
  | TTrans_le D α1 α2 α3 : 
    _type D α1 α2 →
    _type D α2 α3 →
    _type D α1 α3
  | TBot_le D α : _type D TBot α
  | TTop_le D α : _type D α TTop
  | TArrow_le D α α' β β' ρ ρ' b :
    let D' := update_disj_ctx ρ' D in
    _type D' α' α →
    _row D' b ρ ρ' →
    _type D' β β' →
    _type D (TArrow α ρ β) (TArrow α' ρ' β')
  | TRef_le D α β :
    _type D α β → _type D (TRef α) (TRef β)
  | TForallT_le D α β :
    _type D α β → _type D (TForallT α) (TForallT β)
  | TForallR_le D α β :
    _type D α β → _type D (TForallR α) (TForallR β)
  | TForallM_le D α β :
    _type D α β → _type D (TForallM α) (TForallM β)
  | TRec_le D α β : _type D α β → _type D (TRec α) (TRec β)
  | TProd_le D α α' β β' :
    _type D α α' → _type D β β' → _type D (TProd α β) (TProd α' β')
  | TSum_le D α α' β β' :
    _type D α α' → _type D β β' → _type D (TSum α β) (TSum α' β')
          
  | TBangBool_le D m : _type D TBool (TBang m TBool)
  | TBangUnit_le D m : _type D TUnit (TBang m TUnit)
  | TBangInt_le D m : _type D TInt (TBang m TInt)
  | TBangNat_le D m : _type D TNat (TBang m TNat)
  | TBangTop_le D m : _type D TTop (TBang m TTop)
  | TBangRef_le D m α : _type D (TRef α) (TBang m (TRef α))
                              (* TODO: unsure if this is sound. *)
  (* | TBangTape_le D m : _type D TTape (TBang m (TTape α)) *)
  | TBangOS_le D α : _type D α (TBang OS α)
  | TBangIdemp1_le D m α : _type D (TBang m α) (TBang m (TBang m α))
  | TBangIdemp2_le D m α : _type D (TBang m (TBang m α)) (TBang m α)
  | TBangElim_le D m α : _type D (TBang m α) α
  | TBangComp_le D m' m α' α :
    _mode m' m →
    _type D α α' →
    _type D (TBang m α) (TBang m' α')
          
  | TBangTForallTComm1_le D m α : _type D (TBang m (TForallT α)) (TForallT (TBang m α))
  | TBangTForallTComm2_le D m α : _type D (TForallT (TBang m α)) (TBang m (TForallT α))
  | TBangTForallRComm1_le D m α : _type D (TBang m (TForallR α)) (TForallR (TBang m α))
  | TBangTForallRComm2_le D m α : _type D (TForallR (TBang m α)) (TBang m (TForallR α)).

  Definition MultiT (τ : type) : Prop := _type ∅ τ (![MS] τ).

  Definition OnceR (ρ : row) : Prop := ∃ b, _row ∅ b (RFlip MS ρ) ρ. 

  (* Lifting Multi from types to ctx *)
  Definition MultiC (Γ : ctx) : Prop := Forall MultiT (fmap fst (fmap snd (map_to_list Γ))). 

  Inductive _mode_type : vmode → type → Prop :=
  | OS_le τ : _mode_type OS τ
  | MS_le τ : MultiT τ → _mode_type MS τ.

  Inductive _mode_ctx : vmode → ctx → Prop :=
  | NilM_le m : _mode_ctx m ∅
  | ConsM_le m x τ Γ : _mode_type m τ → _mode_ctx m Γ → _mode_ctx m (<[ x :=c τ ]> Γ).

  Inductive _row_type : row → type → Prop :=
  | Once_le ρ τ : OnceR ρ → _row_type ρ τ
  | Multi_le ρ τ : MultiT τ → _row_type ρ τ.

  Inductive _row_ctx : row → ctx → Prop :=
  | NilR_le ρ : _row_ctx ρ ∅
  | ConsR_le ρ x τ Γ : _row_type ρ τ → _row_ctx ρ Γ → _row_ctx ρ (<[ x :=c τ ]> Γ).
  
End le.

Notation "D ⊢ α ≤T α'" := (le._type D α α')
  (at level 74, α, α' at next level).
Notation "D ⊢ ρ ≤R ρ' @ b" := (le._row D b ρ ρ')
  (at level 74, ρ, ρ', b at next level).
Notation "D ⊢ σ ≤S σ'" := (le._eff_sig D σ σ')
  (at level 74, σ, σ' at next level).
Notation "⊢ m ≤M m'" := (le._mode m m')
  (at level 74, m, m' at next level).
Notation "m 'm⪯T' τ" := (le._mode_type m τ) (at level 74, τ at next level).  
Notation "m 'm⪯C' Γ" := (le._mode_ctx m Γ) (at level 74, Γ at next level).
Notation "ρ 'R⪯T' τ" := (le._row_type ρ τ) (at level 74, τ at next level).
Notation "ρ 'R⪯C' Γ" := (le._row_ctx ρ Γ) (at level 74, Γ at next level).

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

Definition binop_int_res_type (op : bin_op) : option type :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => Some TInt
  | AndOp | OrOp | XorOp => None
  | ShiftLOp | ShiftROp => Some TInt
  | LeOp | LtOp | EqOp => Some TBool
  | OffsetOp => Some TInt
  end.
Definition binop_bool_res_type (op : bin_op) : option type :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None
  | AndOp | OrOp | XorOp => Some TBool
  | ShiftLOp | ShiftROp => None
  | LeOp | LtOp => None
  | EqOp => Some TBool
  | OffsetOp => None
  end.
Definition unop_int_res_type (op : un_op) : option type :=
  match op with
  | NegOp => None
  | MinusUnOp => Some TInt
  end.
Definition unop_bool_res_type (op : un_op) : option type :=
  match op with
  | NegOp => Some TBool
  | MinusUnOp => None
  end.

(** Operation lifts *)
Global Instance insert_binder (A : Type): Insert binder A (stringmap A) :=
  binder_insert.


Module vars.

  Fixpoint _eff_sig (f : type → gset eff_name) (σ : eff_sig) : gset eff_name :=
    match σ with
    | SSig s α β => {[ s ]} ∪ (f α) ∪ (f β)
    | SFlip _ σ => _eff_sig f σ
    end.

  Fixpoint _row_pre (f : type → gset eff_name) (ρ : row) : gset eff_name :=
    match ρ with
    | RNil
    | RVar _ => ∅
    | RFlip _ ρ
    | RRec ρ => _row_pre f ρ
    | RCons σ ρ => _eff_sig f σ ∪ _row_pre f ρ
    end.

  Fixpoint _ty (α : type) : gset eff_name :=
    match α with
    | TTop
    | TBot
    | TUnit
    | TBool
    | TInt
    | TNat
    | TTape
    | TVar _ =>
        (∅ : gset eff_name)
    | TProd α β
    | TSum α β =>
        (_ty α) ∪ (_ty β)
    | TRef α
    | TRec α
    | TBang _ α
    | TExists α
    | TForallT α
    | TForallR α
    | TForallM α =>
        (_ty α)
    | TArrow α ρ β =>
        (_ty α) ∪ (_row_pre _ty ρ) ∪ (_ty β)
    end.
  
  Definition _row : row → gset eff_name :=
    _row_pre _ty.
  
  Definition _ctx (Γ : ctx) : gset eff_name :=
    ⋃ ((λ '(_, (α, _)), _ty α) <$> (map_to_list Γ)).

  (* REMARK : unsure if we need to make the check that s is free in dom Γ *)
  (* since this is probably dependent on the implementation of subst *)
  (* The assertion [fresh s Γ ρ α] holds if the string [s] is free in
     [ρ], [α], and [Γ], when seen as an effect name, and it must also not
     appear in the domain of [Γ]. *)
  Definition _fresh s Γ ρ α :=
    s ∉ vars._ctx Γ ∧
    s ∉ vars._row ρ ∧
    s ∉ vars._ty α.

End vars.


Reserved Notation "Δ '.|' Γ1 '⊢ₜ' e ':' ρ ':' τ '⊣' Γ2"
  (at level 74, Γ1, e, ρ, τ, Γ2 at next level).
Reserved Notation "'⊢ᵥ' v ':' τ"  (at level 20, v, τ at next level).

(* From clutch.prob_eff_lang.probblaze Require Import notation. *)

Inductive typed :
  stringmap unit → ctx → expr → row → type → ctx → Prop :=

| Var_typed Δ Γ x τ :
  ctx_lookup x Γ = Some τ →
  Δ .| Γ ⊢ₜ Var x : RNil : τ ⊣ (ctx_remove x Γ)

| Val_typed Δ Γ v ρ τ :
  ⊢ᵥ v : τ →
  Δ .| Γ ⊢ₜ Val v : ρ : τ ⊣ Γ

| Pair_typed Δ Γ1 Γ2 Γ3 e1 e2 ρ τ1 τ2 :
  Δ .| Γ1 ⊢ₜ e1 : ρ : τ1 ⊣ Γ2 →
                    Δ .| Γ2 ⊢ₜ e2 : ρ : τ2 ⊣ Γ3 →
                                       Δ .| Γ1 ⊢ₜ Pair e1 e2 : ρ : τ1 * τ2 ⊣ Γ3

| Fst_typed Δ Γ1 e ρ τ1 τ2 Γ2 :
  Δ .| Γ1 ⊢ₜ e : ρ : τ1 * τ2  ⊣ Γ2 →
                    Δ .| Γ1 ⊢ₜ Fst e : ρ : τ1 ⊣ Γ2
| Snd_typed Δ Γ1 e ρ τ1 τ2 Γ2 :
  Δ .| Γ1 ⊢ₜ e : ρ : τ1 * τ2  ⊣ Γ2 →
                    Δ .| Γ1 ⊢ₜ Snd e : ρ : τ2 ⊣ Γ2

| InjL_typed Δ Γ1 e ρ τ1 τ2 Γ2 :
  Δ .| Γ1 ⊢ₜ e : ρ : τ1 ⊣ Γ2 →
                    Δ .| Γ1 ⊢ₜ InjL e : ρ : τ1 + τ2 ⊣ Γ2
| InjR_typed Δ Γ1 e ρ τ1 τ2 Γ2 :
  Δ .| Γ1 ⊢ₜ e : ρ : τ2 ⊣ Γ2 →
                    Δ .| Γ1 ⊢ₜ InjR e : ρ : τ1 + τ2 ⊣ Γ2
| Case_typed Δ Γ1 Γ2 Γ3 e0 e1 e2 ρ τ1 τ2 τ3 :
  Δ .| Γ1 ⊢ₜ e0 : ρ : τ1 + τ2 ⊣ Γ2 →
                     Δ .| Γ2 ⊢ₜ e1 : ρ : τ1 -{ ρ }-∘ τ3 ⊣ Γ3 →
                                        Δ .| Γ2 ⊢ₜ e2 : ρ : τ2 -{ ρ }-∘ τ3 ⊣ Γ3 →
                                                           Δ .| Γ1 ⊢ₜ Case e0 e1 e2 : ρ : τ3 ⊣ Γ3

| If_typed Δ Γ1 Γ2 Γ3 e0 e1 e2 ρ τ :
  Δ .| Γ1 ⊢ₜ e0 : ρ : 𝔹 ⊣ Γ2 →
                     Δ .| Γ2 ⊢ₜ e1 : ρ : τ ⊣ Γ3 →
                                        Δ .| Γ2 ⊢ₜ e2 : ρ : τ ⊣ Γ3 →
                                                           Δ .| Γ1 ⊢ₜ If e0 e1 e2 : ρ : τ ⊣ Γ3
(* TODO: consider other rules for affine function types *)
| Rec_typed Δ Γ f x e ρ τ κ :
  Δ .| <[ f :=c (τ -{ ρ }-> κ)%ty ]> <[ x :=c τ ]> Γ ⊢ₜ e : ρ : κ ⊣ ∅ →
                                                             Δ .| Γ ⊢ₜ Rec f x e : RNil : τ -{ ρ }-> κ ⊣ ∅
(* TODO: generalize according to Fig. 5 in Affect *)
| App_typed Δ Γ1 Γ2 Γ3 e1 e2 ρ τ κ :
  Δ .| Γ1 ⊢ₜ e2 : ρ : τ ⊣ Γ2 →
                     Δ .| Γ2 ⊢ₜ e1 : ρ : τ -{ ρ }-∘ κ ⊣ Γ3 →
                                        Δ .| Γ1 ⊢ₜ App e1 e2 : ρ : κ ⊣ Γ3

| TAlloc Δ Γ1 e ρ τ Γ2 : Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2  → Δ .| Γ1 ⊢ₜ AllocN (Val $ LitV $ LitInt 1) e : ρ : ref τ ⊣ Γ2
| TLoad Δ Γ1 e ρ τ Γ2 : Δ .| Γ1 ⊢ₜ e : ρ : ref τ ⊣ Γ2 → Δ .| Γ1 ⊢ₜ Load e : ρ : τ ⊣ Γ2
| TStore Δ Γ1 Γ2 Γ3 e e' ρ τ :
  Δ .| Γ1 ⊢ₜ e' : ρ : τ ⊣ Γ2 → 
                     Δ .| Γ2 ⊢ₜ e : ρ : ref τ ⊣ Γ3 → 
                                       Δ .| Γ1 ⊢ₜ Store e e' : ρ : () ⊣ Γ3
| TAllocTape Δ Γ1 e ρ Γ2 : Δ .| Γ1 ⊢ₜ e : ρ : ℕ ⊣ Γ2 →  Δ .| Γ1 ⊢ₜ AllocTape e : ρ : TTape ⊣ Γ2
| TRand Δ Γ1 Γ2 Γ3 e1 e2 ρ : Δ .| Γ2 ⊢ₜ e1 : ρ : ℕ ⊣ Γ3 → Δ .| Γ1 ⊢ₜ e2 : ρ : TTape ⊣ Γ2 → Δ .| Γ1 ⊢ₜ Rand e1 e2 : ρ : ℕ ⊣ Γ3
| TRandU Δ Γ1 Γ2 Γ3 e1 e2 ρ : Δ .| Γ2 ⊢ₜ e1 : ρ : ℕ ⊣ Γ3 → Δ .| Γ1 ⊢ₜ e2 : ρ : () ⊣ Γ2 → Δ .| Γ1 ⊢ₜ Rand e1 e2 : ρ : ℕ ⊣ Γ3
(* TODO: add to subsumption rules
   | Subsume_int_nat Γ e : Γ ⊢ₜ e : TNat → Γ ⊢ₜ e : TInt *)

| Effect_typed Δ Γ1 e s ρ τ Γ2 :
  let Abs_ρ := RCons (SAbs s) ρ in

  vars._fresh s Γ1 ρ τ →
  (<[ s := () ]> Δ) .| Γ1 ⊢ₜ e : Abs_ρ : τ ⊣ Γ2 →
  Δ .| Γ1 ⊢ₜ Effect s e : ρ : τ ⊣ Γ2
| Do_typed Δ Γ1 s e ρ' τ ι κ m Γ2 :
  m m⪯C Γ2 →
  Δ !! s = Some () →
  let ρ := RCons (SFlip m (SSig s ι κ)) ρ' in
  Δ .| Γ1 ⊢ₜ e : ρ : ι.[τ/] ⊣ Γ2 →
                    Δ .| Γ1 ⊢ₜ Do (EffName s) e : ρ : κ.[τ/] ⊣ Γ2
| DeepHandle_typed Δ Γ1 Γ2 Γ (m : mode) s e x k h y r ρ0 σ τ τ' ι κ :
  le.MultiC Γ →
  Δ !! s = Some () →
  le.eff_name_from_sig σ = s →
  let ρ := RCons σ ρ0 in
  let ρ' := RCons (SFlip m (SSig s ι κ)) ρ0 in
  Δ .| Γ1 ⊢ₜ e : ρ' : τ ⊣ Γ2 →
  Δ .| <[ y :=c τ ]> (Γ2 ;; Γ) ⊢ₜ r : ρ : τ' ⊣ Γ →
  Δ .| <[ x :=c ι ]> <[ k :=c ![m] (κ -{ ρ }-∘ τ') ]> Γ ⊢ₜ h : ρ : τ' ⊣ Γ →
  Δ .| (Γ1 ;; Γ) ⊢ₜ (Handle Deep m s e (Lam x (Lam k h)) (Lam y r)) : ρ : τ' ⊣ Γ
with val_typed : val → type → Prop :=
| Unit_val_typed : ⊢ᵥ LitV LitUnit : ()
where "Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2" := (typed Δ Γ1 e ρ τ Γ2)
and "⊢ᵥ e : τ" := (val_typed e τ).                   



(* (** * Manipulation of de Bruijn Indices. *)
   
   (* We define the lifting and substitution of both row and type variables.
      The definitions are standard.
   *)
   
   (** Lifting of row variables. *)
   
   Module rvar_lift.
   
     Fixpoint _eff_sig_pre
       (f : nat → type → type)
       (n : nat) (σ : eff_sig) : eff_sig :=
       match σ with
       | EFlip m σ => EFlip m (_eff_sig_pre f n σ)
       | ESig s α β => ESig s (f n α) (f n β)
       end. 
   
     Fixpoint _row_pre
       (f : nat → type → type)
       (n : nat) (ρ : row) : row :=
       match ρ with
       | RNil => ρ
       | RCons σ ρ => RCons (_eff_sig_pre f n σ) (_row_pre f n ρ)
       | RVar m => let m' := if (decide (m < n)) then m else (S m) in RVar m'
       | RFlip m ρ => RFlip m (_row_pre f n ρ)
       | RRec ρ => RRec (_row_pre f n ρ)
       end.
              
     Fixpoint _ty (n : nat) (α : type) : type :=
       match α with
       | TUnit
       | TBool
       | TInt
       | TTop
       | TBot
       | TTape
       | TVar _ =>
           α
       | TRef α =>
           TRef (_ty n α)
       | TProd α β =>
           TProd (_ty n α) (_ty n β)
       | TSum α β =>
           TSum (_ty n α) (_ty n β)
       | TArrow α ρ β =>
           TArrow (_ty n α)
                (_row_pre _ty n ρ)
                (_ty n β)
       | TForall R α =>
           TForall R (_ty (S n) α)
       | TForall m α =>
           TForall m (_ty n α)
       | TExists α =>
           TExists (_ty n α)
       | TRec α =>
           TRec (_ty n α)
       | TBang m α =>
           TBang m (_ty n α)
       end.
   
     Definition _eff_sig : nat → eff_sig → eff_sig :=
       _eff_sig_pre _ty.
   
     Definition _row : nat → row → row :=
       _row_pre _ty.
   
   End rvar_lift.
   
   (** Lifting of type variables *)
   
   Module tvar_lift.
     
     Fixpoint _eff_sig_pre
       (f : nat → type → type)
       (n : nat) (σ : eff_sig) : eff_sig :=
       match σ with
       | EFlip m σ => EFlip m (_eff_sig_pre f n σ)
       | ESig s α β => ESig s (f n α) (f n β)
       end. 
   
     Fixpoint _row_pre
       (f : nat → type → type)
       (n : nat) (ρ : row) : row :=
       match ρ with
       | RNil 
       | RVar _ => ρ
       | RCons σ ρ => RCons (_eff_sig_pre f n σ) (_row_pre f n ρ)
       | RFlip m ρ => RFlip m (_row_pre f n ρ)
       | RRec ρ => RRec (_row_pre f n ρ)
       end.
   
      Fixpoint _ty (n : nat) (α : type) : type :=
       match α with
       | TUnit
       | TBool
       | TInt
       | TTop
       | TBot
       | TTape =>
           α
       | TRef α =>
           TRef (_ty n α)
       | TProd α β =>
           TProd (_ty n α) (_ty n β)
       | TSum α β =>
           TSum (_ty n α) (_ty n β)
       | TArrow α ρ β =>
           TArrow (_ty n α)
                (_row_pre _ty n ρ)
                (_ty n β)
       | TForall T α =>
           TForall T (_ty (S n) α)
       | TForall m α =>
           TForall m (_ty n α)
       | TExists α =>
           TExists (_ty (S n) α)
       | TRec α =>
           TRec (_ty (S n) α)
       | TBang m α =>
           TBang m (_ty n α)
       | TVar m => let m' := if (decide (m < n)) then m else (S m) in TVar m'
       end.
   
     Definition _eff_sig : nat → eff_sig → eff_sig :=
       _eff_sig_pre _ty.
   
     Definition _row : nat → row → row :=
       _row_pre _ty.
   
   End tvar_lift.
   
   (** Lifting of mode variables *)
   
   Module mvar_lift.
   
       Fixpoint _eff_sig_pre
       (f : nat → type → type)
       (n : nat) (σ : eff_sig) : eff_sig :=
       match σ with
       | EFlip (MVar m) σ => let m' := if (decide (m < n)) then m else (S m) in EFlip (MVar m') (_eff_sig_pre f n σ)
       | EFlip m σ => EFlip m (_eff_sig_pre f n σ)
       | ESig s α β => ESig s (f n α) (f n β)
       end. 
   
     Fixpoint _row_pre
       (f : nat → type → type)
       (n : nat) (ρ : row) : row :=
       match ρ with
       | RNil 
       | RVar _ => ρ
       | RCons σ ρ => RCons (_eff_sig_pre f n σ) (_row_pre f n ρ)
       | RFlip (MVar m) ρ => let m' := if (decide (m < n)) then m else (S m) in RFlip (MVar m') (_row_pre f n ρ)
       | RFlip m ρ => RFlip m (_row_pre f n ρ)
       | RRec ρ => RRec (_row_pre f n ρ)
       end.
   
      Fixpoint _ty (n : nat) (α : type) : type :=
       match α with
       | TUnit
       | TBool
       | TInt
       | TTop
       | TBot
       | TTape
       | TVar _ =>
           α
       | TRef α =>
           TRef (_ty n α)
       | TProd α β =>
           TProd (_ty n α) (_ty n β)
       | TSum α β =>
           TSum (_ty n α) (_ty n β)
       | TArrow α ρ β =>
           TArrow (_ty n α)
                (_row_pre _ty n ρ)
                (_ty n β)
       | TForall T α =>
           TForall T (_ty (S n) α)
       | TForall m α =>
           TForall m (_ty n α)
       | TExists α =>
           TExists (_ty (S n) α)
       | TRec α =>
           TRec (_ty (S n) α)
       | TBang (MVar m) α => let m' := if (decide (m < n)) then m else (S m) in
                                            TBang (MVar m') (_ty n α)
       | TBang m α => TBang m (_ty n α)
       end.
   
     Definition _eff_sig : nat → eff_sig → eff_sig :=
       _eff_sig_pre _ty.
   
     Definition _row : nat → row → row :=
       _row_pre _ty.
   
   End mvar_lift.
   
   (* Substitution of row variables *)
   
   Module rvar_subst. *)

  
