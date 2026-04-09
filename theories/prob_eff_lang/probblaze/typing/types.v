From Autosubst Require Import Autosubst.
From stdpp Require Export strings gmultiset gmap stringmap.
From clutch.prob_eff_lang.probblaze Require Import syntax.
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
  | RErase_le D s ρ ss js :
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

  .
         
      



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

  
