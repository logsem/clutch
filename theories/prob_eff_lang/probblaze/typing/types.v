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

  Global Instance Ids_vmode : Ids vmode. derive. Defined.
  Global Instance Rename_vmode : Rename vmode. derive. Defined.
  Global Instance Subst_vmode : Subst vmode. derive. Defined.
  Global Instance SubstLemmas_vmode : SubstLemmas vmode. derive. Qed.

  Global Instance Ids_row : Ids row. derive. Defined.
  Global Instance Ids_type : Ids type. derive. Defined.

  Fixpoint hsubst_vmode_type (σ : var → vmode) (τ : type) : type :=
    let _ := hsubst_vmode_type : HSubst vmode type in
    let _ := hsubst_vmode_row : HSubst vmode row in
    match τ with
    | TBot
    | TTop
    | TUnit
    | TBool
    | TInt 
    | TNat
    | TTape
    | TVar _ => τ
    | TRef α => TRef α.|[σ]
    | TProd α β => TProd α.|[σ] β.|[σ]
    | TSum α β => TSum α.|[σ] β.|[σ]
    | TArrow α ρ β => TArrow α.|[σ] ρ.|[σ] β.|[σ]
    | TForallT τ => TForallT τ.|[σ]
    | TForallR τ => TForallR τ.|[σ]
    | TExists τ => TExists τ.|[σ] 
    | TRec τ => TRec τ.|[σ]
    | TBang m τ => TBang m.[σ] τ
    | TForallM τ => TForallM τ.|[up σ]
    end
  with hsubst_vmode_row (σ : var → vmode) (ρ : row) : row :=
         let _ := hsubst_vmode_row : HSubst vmode row in
         let _ := hsubst_vmode_eff_sig : HSubst vmode eff_sig in
         match ρ with
         | RFlip m ρ => RFlip m.[σ] ρ.|[σ]
         | RNil
         | RVar _ => ρ
         | RRec ρ => RRec ρ.|[σ]
         | RCons s ρ => RCons s.|[σ] ρ.|[σ]
         end
  with hsubst_vmode_eff_sig (σ : var → vmode) (s : eff_sig) : eff_sig :=
         let _ := hsubst_vmode_eff_sig : HSubst vmode eff_sig in
         let _ := hsubst_vmode_type : HSubst vmode type in
         match s with
         | SSig e α β => SSig e α.|[σ] β.|[σ] 
         | SFlip m s => SFlip m.[σ] s.|[σ]
         end.

  Global Instance HSubst_vmode_type : HSubst vmode type := hsubst_vmode_type.
  Global Instance HSubst_vmode_row : HSubst vmode row := hsubst_vmode_row.
  Global Instance HSubst_vmode_eff_sig : HSubst vmode eff_sig := hsubst_vmode_eff_sig.

  Local Lemma hsubst_vmode_type_id (τ : type) : τ.|[ids : var → vmode] = τ
  with hsubst_vmode_row_id (ρ : row) : ρ.|[ids : var → vmode] = ρ
    with hsubst_vmode_eff_sig_id (e : eff_sig) : e.|[ids : var → vmode] = e.
  Proof.
    - destruct τ; rewrite /= ?up_id ?hsubst_vmode_type_id ?hsubst_vmode_row_id ?subst_id//.
    - destruct ρ; rewrite /= ?hsubst_vmode_row_id ?subst_id ?hsubst_vmode_eff_sig_id //.
    - destruct e; rewrite /= ?hsubst_vmode_type_id ?hsubst_vmode_row_id ?hsubst_vmode_eff_sig_id ?subst_id //.
  Qed. 

  (* Local Lemma rename_hsubst_hsubst_vmode_type_comp (ξ : var → var) (σ : var → vmode) (τ : type) :
       (rename ξ τ).[σ] = τ.|[σ >>> rename ξ]. *)
                                                           

  Local Lemma hsubst_vmode_type_comp (σ σ' : var → vmode) (τ : type) : τ.|[σ].|[σ'] = τ.|[σ >> σ']
    with hsubst_vmode_row_comp (σ σ' : var → vmode) (ρ : row) : ρ.|[σ].|[σ'] = ρ.|[σ >> σ']
      with hsubst_vmode_eff_sig_comp (σ σ' : var → vmode) (e : eff_sig) : e.|[σ].|[σ'] = e.|[σ >> σ'].
  Proof.
    - destruct τ; rewrite /= ?hsubst_vmode_type_comp ?hsubst_vmode_row_comp ?subst_comp //. rewrite up_comp //.
    - destruct ρ; rewrite /= ?hsubst_vmode_row_comp ?hsubst_vmode_eff_sig_comp ?subst_comp//.
    - destruct e; rewrite /= ?hsubst_vmode_eff_sig_comp ?hsubst_vmode_type_comp ?hsubst_vmode_row_comp ?subst_comp //.
  Qed.
  
  Global Instance HSubstLemmas_vmode_type : HSubstLemmas vmode type.
  Proof.
    constructor; try done.
    - apply hsubst_vmode_type_id.
    - apply hsubst_vmode_type_comp.
  Qed. 

  Global Instance HSubstLemmas_vmode_row : HSubstLemmas vmode row.
  Proof.
    constructor; try done.
    - apply hsubst_vmode_row_id.
    - apply hsubst_vmode_row_comp.
  Qed. 

  Fixpoint rename_type (ξ : var → var) (τ : type) : type :=
    let _ := rename_type : Rename type in 
    match τ with
    | TBot
    | TTop
    | TUnit
    | TBool
    | TInt 
    | TNat
    | TTape => τ
    | TVar i => TVar (ξ i)
    | TRef α => TRef (rename ξ α)
    | TProd α β => TProd (rename ξ α) (rename ξ β)
    | TSum α β => TSum (rename ξ α) (rename ξ β)
    | TArrow α ρ β => TArrow (rename ξ α) (rename_type_row ξ ρ) (rename ξ β)
    | TForallT τ => TForallT (rename (upren ξ) τ)
    | TForallR τ => TForallR (rename ξ τ)
    | TForallM τ => TForallM (rename ξ τ)
    | TExists τ => TExists (rename (upren ξ) τ)
    | TRec τ => TRec (rename (upren ξ) τ)
    | TBang m τ => TBang m (rename ξ τ)
    end
  with rename_type_row (ξ : var → var) (ρ : row) : row :=
         match ρ with
         | RNil
         | RVar _ => ρ
         | RFlip m ρ => RFlip m (rename_type_row ξ ρ)
         | RRec ρ => RRec (rename_type_row ξ ρ)
         | RCons s ρ => RCons (rename_type_eff_sig ξ s) (rename_type_row ξ ρ)
         end
  with rename_type_eff_sig (ξ : var → var) (s : eff_sig) : eff_sig :=
         let _ := rename_type : Rename type in
         match s with
         | SSig e α β => SSig e (rename (upren ξ) α) (rename (upren ξ) β)
         | SFlip m s => SFlip m (rename_type_eff_sig ξ s)
         end.
  
  Global Instance Rename_type : Rename type := rename_type.

  Fixpoint rename_row (ξ : var → var) (ρ : row) : row :=
    let _ := rename_row : Rename row in
    match ρ with
    | RFlip m ρ => RFlip m (rename ξ ρ)
    | RNil => ρ
    | RVar i => RVar (ξ i)
    | RRec ρ => RRec (rename ξ ρ)
    | RCons s ρ => RCons (rename_row_eff_sig ξ s) (rename ξ ρ)
    end
  with rename_row_type (ξ : var → var) (τ : type) : type :=
         let _ := rename_row : Rename row in
         match τ with
         | TBot
         | TTop
         | TUnit
         | TBool
         | TInt 
         | TNat
         | TTape
         | TVar _ => τ
         | TProd α β => TProd (rename_row_type ξ α) (rename_row_type ξ β)
         | TSum α β => TSum (rename_row_type ξ α) (rename_row_type ξ β)
         | TArrow α ρ β => TArrow (rename_row_type ξ α) (rename ξ ρ) (rename_row_type ξ β)
         | TForallT α => TForallT (rename_row_type ξ α)
         | TForallM α => TForallM (rename_row_type ξ α)
         | TForallR α => TForallR (rename_row_type (upren ξ) α)
         | TExists α => TExists (rename_row_type ξ α)
         | TRec α => TRec (rename_row_type ξ α)
         | TBang m α => TBang m (rename_row_type ξ α)
         | TRef α => TRef (rename_row_type ξ α)
         end
  with rename_row_eff_sig (ξ : var → var) (s : eff_sig) : eff_sig :=
         match s with
         | SSig e α β => SSig e (rename_row_type ξ α) (rename_row_type ξ β)
         | SFlip m s => SFlip m (rename_row_eff_sig ξ s)
         end.

  Global Instance Rename_row : Rename row := rename_row.
  
  Fixpoint subst_type (σ : var → type) (τ : type) : type :=
    let _ := subst_type : Subst type in
    let _ := hsubst_type_row : HSubst type row in
    match τ with
    | TBot
    | TTop
    | TUnit
    | TBool
    | TInt
    | TNat
    | TTape => τ
    | TVar i => σ i
    | TRef α => TRef α.[σ]
    | TProd α β => TProd α.[σ] β.[σ]
    | TSum α β =>  TSum α.[σ] β.[σ]
    | TArrow α ρ β => TArrow α.[σ] ρ.|[σ] β.[σ]
    | TExists α => TExists α.[up σ]
    | TRec α => TRec α.[up σ]
    | TBang m α => TBang m α.[σ]
    | TForallM α => TForallM α.[σ]
    | TForallT α => TForallT α.[up σ]
    | TForallR α => TForallR α.[σ]
    end
  with hsubst_type_row (σ : var → type) (ρ : row) : row :=
         let _ := hsubst_type_row : HSubst type row in
         let _ := hsubst_type_eff_sig : HSubst type eff_sig in
         match ρ with
         | RFlip m ρ => RFlip m ρ.|[σ]
         | RNil
         | RVar _ => ρ
         | RRec ρ => RRec ρ.|[σ]
         | RCons s ρ => RCons s.|[σ] ρ.|[σ]
         end
  with hsubst_type_eff_sig (σ : var → type) (s : eff_sig) : eff_sig :=
         let _ := hsubst_type_eff_sig : HSubst type eff_sig in
         let _ := subst_type : Subst type in
         match s with
         | SSig e α β => SSig e α.[up σ] β.[up σ]
         | SFlip m s => SFlip m s.|[σ]
         end.

  Fixpoint subst_row (σ : var → row) (ρ : row) : row :=
    let _ := subst_row : Subst row in
    let _ := hsubst_row_eff_sig : HSubst row eff_sig in 
    match ρ with
    | RNil => ρ
    | RVar i => σ i
    | RFlip m ρ => RFlip m ρ.[σ]
    | RRec ρ => RRec ρ.[σ]
    | RCons s ρ => RCons s.|[σ] ρ.[σ]
    end
  with hsubst_row_type (σ : var → row) (τ : type) : type :=
         let _ := subst_row : Subst row in
         let _ := hsubst_row_type : HSubst row type in
         match τ with
         | TBot
         | TTop
         | TUnit
         | TBool
         | TInt
         | TNat
         | TTape
         | TVar _ => τ
         | TRef α => TRef α.|[σ]
         | TProd α β => TProd α.|[σ] β.|[σ]
         | TSum α β =>  TSum α.|[σ] β.|[σ]
         | TArrow α ρ β => TArrow α.|[σ] ρ.[σ] β.|[σ]
         | TExists α => TExists α.|[σ]
         | TRec α => TRec α.|[σ]
         | TBang m α => TBang m α.|[σ]
         | TForallM α => TForallM α.|[σ]
         | TForallT α => TForallT α.|[σ]
         | TForallR α => TForallR α.|[up σ]
         end
  with hsubst_row_eff_sig (σ : var → row) (s : eff_sig) : eff_sig :=
         let _ := hsubst_row_type : HSubst row type in
         let _ := hsubst_row_eff_sig : HSubst row eff_sig in
         match s with
         | SSig e α β => SSig e α.|[σ] β.|[σ]
         | SFlip m α => SFlip m α.|[σ]
         end.

  Global Instance Subst_type : Subst type := subst_type.
  Global Instance HSubst_row_type : HSubst row type := hsubst_row_type.

  Global Instance Subst_row : Subst row := subst_row.
  Global Instance HSubst_type_row : HSubst type row := hsubst_type_row.

  Global Instance HSubst_row_eff_sig : HSubst row eff_sig := hsubst_row_eff_sig.
  Global Instance HSubst_type_eff_sig : HSubst type eff_sig := hsubst_type_eff_sig.

  Local Lemma rename_type_row_hsubst_ren (ξ : var → var) ρ :
    rename_type_row ξ ρ = ρ.|[ren ξ]
    with rename_type_eff_sig_hsubst_ren (ξ : var → var) s :
      rename_type_eff_sig ξ s = s.|[ren ξ]
    with rename_subst_type (ξ : var → var) (τ : type) :
      rename ξ τ = τ.[ren ξ].
  Proof.
    - destruct ρ; rewrite /= ?rename_type_row_hsubst_ren ?rename_type_eff_sig_hsubst_ren //.
    - destruct s; rewrite /= ?rename_type_eff_sig_hsubst_ren ?rename_subst_type ?up_upren_internal //.
    - destruct τ; rewrite /= ?rename_subst_type ?rename_type_row_hsubst_ren ?up_upren_internal //.
  Qed. 

  Local Lemma rename_row_eff_sig_hsubst_ren (ξ : var → var) (s : eff_sig) :
    rename_row_eff_sig ξ s = hsubst_row_eff_sig (ren ξ) s
  with rename_row_type_hsubst_ren (ξ : var → var) (τ : type) :
    rename_row_type ξ τ = τ.|[ren ξ]
  with rename_subst_row (ξ : var → var) (ρ : row) :
    rename ξ ρ = ρ.[ren ξ].
  Proof.
    - destruct s; rewrite /= ?rename_row_eff_sig_hsubst_ren ?rename_row_type_hsubst_ren //.
    - destruct τ; rewrite /= ?rename_row_type_hsubst_ren ?up_upren_internal //.
      rewrite rename_subst_row //.
    - destruct ρ; rewrite /= ?rename_subst_row ?rename_row_eff_sig_hsubst_ren //.
  Qed. 

  Local Lemma subst_row_id (ρ : row) : ρ.[ids] = ρ
    with hsubst_row_eff_sig_id (e : eff_sig) : e.|[ids : var → row] = e
      with hsubst_row_type_id (τ : type) : τ.|[ids : var → row] = τ.
  Proof.
    - destruct ρ; rewrite /= ?subst_row_id ?hsubst_row_eff_sig_id //.
    - destruct e; rewrite /= ?up_id ?hsubst_row_eff_sig_id ?hsubst_row_type_id //.
    - destruct τ; rewrite /= ?up_id_internal ?hsubst_row_type_id ?subst_row_id //.
  Qed.   

  Local Lemma subst_type_id (τ : type) : τ.[ids] = τ
    with hsubst_type_eff_sig_id (e : eff_sig) : e.|[ids : var → type] = e
      with hsubst_type_row_id (ρ : row) : ρ.|[ids : var → type] = ρ.
  Proof.
    - destruct τ; rewrite /= ?up_id_internal ?subst_type_id ?hsubst_type_row_id //.
    - destruct e; rewrite /= ?hsubst_type_eff_sig_id ?up_id_internal ?subst_type_id //.
    - destruct ρ; rewrite /= ?hsubst_type_eff_sig_id ?hsubst_type_row_id //.
  Qed.
  
  Local Lemma rename_subst_subst_comp_type (ξ : var → var) (σ : var → type) (τ : type) :
    (rename ξ τ).[σ] = τ.[ξ >>> σ]
    with rename_hsubst_hsubst_comp_type_row  (ξ : var → var) (σ : var → type) (ρ : row) :
      (rename_type_row ξ ρ).|[σ] = ρ.|[ξ >>> σ]
      with rename_hsubst_hsubst_comp_type_eff_sig  (ξ : var → var) (σ : var → type) (e : eff_sig) :
    (rename_type_eff_sig ξ e).|[σ] = e.|[ξ >>> σ].
  Proof. 
    - destruct τ; rewrite /= ?rename_subst_subst_comp_type ?rename_hsubst_hsubst_comp_type_row  //; rewrite up_comp_ren_subst //.
    - destruct ρ; rewrite /= ?rename_hsubst_hsubst_comp_type_row ?rename_hsubst_hsubst_comp_type_eff_sig //.
    - destruct e; rewrite /= ?rename_hsubst_hsubst_comp_type_eff_sig ?rename_subst_subst_comp_type //; rewrite up_comp_ren_subst //.
  Qed. 

  Local Lemma rename_subst_comp_type_rename (ξ : var → var) (σ : var → type) (τ : type) :
    rename ξ τ.[σ] = τ.[σ >>> rename ξ]
    with rename_hsubst_comp_type_row_rename  (ξ : var → var) (σ : var → type) (ρ : row) :
      rename_type_row ξ ρ.|[σ] = ρ.|[σ >>> rename ξ]
      with rename_hsubst_comp_type_eff_sig_rename  (ξ : var → var) (σ : var → type) (e : eff_sig) :
    rename_type_eff_sig ξ e.|[σ] = e.|[σ >>> rename ξ].
  Proof with auto using rename_subst_subst_comp_type, rename_subst_type. 
    - destruct τ; rewrite /= ?rename_subst_comp_type_rename ?rename_hsubst_comp_type_row_rename //; rewrite up_comp_subst_ren_internal //...
    - destruct ρ; rewrite /= ?rename_hsubst_comp_type_row_rename ?rename_hsubst_comp_type_eff_sig_rename //.
    - destruct e; rewrite /= ?rename_hsubst_comp_type_eff_sig_rename ?rename_subst_comp_type_rename //; rewrite up_comp_subst_ren_internal //...
  Qed.
  
  Local Lemma subst_type_comp (σ σ' : var → type) (τ : type) : τ.[σ].[σ'] = τ.[σ >> σ']
    with hsubst_type_eff_sig_comp (σ σ' : var → type) (e : eff_sig) : e.|[σ].|[σ'] = e.|[σ >> σ']
      with hsubst_type_row_comp (σ σ' : var → type) (ρ : row) : ρ.|[σ].|[σ'] = ρ.|[σ >> σ'].
  Proof with auto using rename_subst_subst_comp_type, rename_subst_comp_type_rename. 
    - destruct τ; rewrite /= ?subst_type_comp ?hsubst_type_row_comp ?up_comp_internal //...
    - destruct e; rewrite /= ?hsubst_type_eff_sig_comp ?subst_type_comp ?up_comp_internal //...
    - destruct ρ; rewrite /= ?hsubst_type_row_comp ?hsubst_type_eff_sig_comp  //.
  Qed. 

  Global Instance SubstLemmas_type : SubstLemmas type.
  Proof.
    constructor; [| |done|].
    - apply rename_subst_type.
    - apply subst_type_id.
    - apply subst_type_comp. 
  Qed. 

  Global Instance HSubstLemmas_type_row : HSubstLemmas type row.
  Proof. 
    constructor; try done.
    - apply hsubst_type_row_id.
    - apply hsubst_type_row_comp. 
  Qed. 

  Local Lemma rename_subst_subst_comp_row (ξ : var → var) (σ : var → row) (ρ : row) :
    (rename ξ ρ).[σ] = ρ.[ξ >>> σ]
    with rename_hsubst_hsubst_comp_row_type (ξ : var → var) (σ : var → row) (τ : type) :
      (rename_row_type ξ τ).|[σ] = τ.|[ξ >>> σ]
      with rename_hsubst_hsubst_comp_row_eff_sig (ξ : var → var) (σ : var → row) (e : eff_sig) :
        (rename_row_eff_sig ξ e).|[σ] = e.|[ξ >>> σ].
  Proof.
    - destruct ρ; rewrite /= ?rename_subst_subst_comp_row ?rename_hsubst_hsubst_comp_row_eff_sig//.
    - destruct τ; rewrite /= ?rename_hsubst_hsubst_comp_row_type ?rename_subst_subst_comp_row //; rewrite up_comp_ren_subst //.
    - destruct e; rewrite /= ?rename_hsubst_hsubst_comp_row_eff_sig ?rename_hsubst_hsubst_comp_row_type //.
  Qed. 

  Local Lemma rename_subst_comp_row_rename (ξ : var → var) (σ : var → row) (ρ : row) :
    rename ξ ρ.[σ] = ρ.[σ >>> rename ξ]
    with rename_hsubst_comp_row_type_rename (ξ : var → var) (σ : var → row) (τ : type) :
      rename_row_type ξ τ.|[σ] = τ.|[σ >>> rename ξ]
      with rename_hsubst_comp_row_eff_sig_rename (ξ : var → var) (σ : var → row) (e : eff_sig) :
        rename_row_eff_sig ξ e.|[σ] = e.|[σ >>> rename ξ].
  Proof with auto using rename_subst_subst_comp_row, rename_subst_row. 
    - destruct ρ; rewrite /= ?rename_subst_comp_row_rename ?rename_hsubst_comp_row_eff_sig_rename //.
    - destruct τ; rewrite /= ?rename_hsubst_comp_row_type_rename ?rename_subst_comp_row_rename //; rewrite up_comp_subst_ren_internal //...
    - destruct e; rewrite /= ?rename_hsubst_comp_row_eff_sig_rename ?rename_hsubst_comp_row_type_rename //.
  Qed. 

  Local Lemma subst_row_comp (σ σ' : var → row) (ρ : row) : ρ.[σ].[σ'] = ρ.[σ >> σ']
    with hsubst_row_eff_sig_comp (σ σ' : var → row) (e : eff_sig) : e.|[σ].|[σ'] = e.|[σ >> σ']
      with hsubst_row_type_comp (σ σ' : var → row) (τ : type) : τ.|[σ].|[σ'] = τ.|[σ >> σ'].
  Proof with auto using rename_subst_subst_comp_row, rename_subst_comp_row_rename. 
    - destruct ρ; rewrite /= ?subst_row_comp ?hsubst_row_eff_sig_comp //.
    - destruct e; rewrite /= ?hsubst_row_eff_sig_comp ?hsubst_row_type_comp //.
    - destruct τ; rewrite /= ?hsubst_row_type_comp ?subst_row_comp ?up_comp_internal //...
  Qed.   

  Global Instance SubstLemmas_row : SubstLemmas row.
  Proof. 
    constructor; [| |done|].
    - apply rename_subst_row.
    - apply subst_row_id.
    - apply subst_row_comp.
  Qed. 

  Global Instance HSubstLemmas_row_type : HSubstLemmas row type.
  Proof.
    constructor; try done.   
    - apply hsubst_row_type_id.
    - apply hsubst_row_type_comp.
  Qed. 

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
Notation "α '-{' ρ '}-[' m ']->' β" := (TBang m (TArrow α ρ β))
                                         (at level 100, ρ, m, β at level 200) : FType_scope.
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

  (* (* A ctx is a multiset of key-value pairs restricting the value to be the same for each instance of the key *)
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
     Definition ctx_append (Γ1 Γ2 : ctx) : ctx := gmap_merge _ _ _ merge_aux Γ1 Γ2. *)

  Definition ctx := list (string * type).
  
  Definition ctx_insert (x : binder) (t : type) (Γ : ctx) := match x with 
                                                             | BAnon => Γ 
                                                             | BNamed s => (s, t) :: Γ
                                                             end.
  
  Definition ctx_append (Γ1 Γ2 : ctx) := Γ1 ++ Γ2.
  
  Global Instance empty_ctx : Empty ctx := [].
  
  Definition ctx_dom (Γ : ctx) : gset string := ⋃ ((λ '(s, _), {[s]}) <$> Γ).

  (* Definition ctx := gmap string (list type).
     
     Definition ctx_insert (x : string) (τ : type) (Γ : ctx) :=
       match Γ !! x with
       | None => <[ x := [τ] ]> Γ
       | Some ls => <[ x := τ :: ls ]> Γ
       end.
     
     Definition ctx_overwrite (x : string) (τ : type) (Γ : ctx) := <[ x := [τ] ]> Γ.
     
     Definition merge_aux : option (list type) → option (list type) → option (list type) :=
       λ xs ys, match xs, ys with
                | x, None
                | None, x => x
                | Some x, Some y => Some (x ++ y)
                end.
     Definition ctx_append (Γ1 Γ2 : ctx) : ctx := gmap_merge _ _ _ merge_aux Γ1 Γ2.
     
     Definition ctx_dom (Γ : ctx) := dom Γ. *)

  Global Instance elem_binder_string : (ElemOf binder stringset) | 10 := 
    (λ b xs, match b with
               BAnon => False%type
             | BNamed x => x ∈ xs
             end).

  
End ctx.

Notation "'<[' x ':=c' t ']>' Γ" := (ctx_insert x t Γ).
(* Notation "'<[' x ':=o' t ']>' Γ" := (ctx_overwrite x t Γ). *)
(* Notation "Γ '!!c' x" := (ctx_lookup x Γ) (at level 100, x at next level). *)
(* Notation "'<[' x ':=c + ]>' Γ" := (ctx_contraction x Γ).
   Notation "'<[' x ':=c - ]>' Γ" := (ctx_remove x Γ). *)
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
  | RFold_le D b ρ : _row D b (ρ.[RRec ρ/]) (RRec ρ)

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

  (* Definition list_type_le D (ts rs : list type) : Prop :=
       ∃ l, l ⊆+ rs → Forall2 (_type D) ts l.  
     
     Definition _ctx (D : disj_ctx) (Γ1 Γ2 : ctx) : Prop := Forall (λ (y : (string * list type)), let (x, ts) := y in
                                                                      match Γ1 !! x with
                                                                              | None => False 
                                                                              | Some rs => list_type_le D rs ts
                                                                              end) (map_to_list Γ2). *)

  Fixpoint _ctx (D : disj_ctx) (Γ Γ' : ctx) : Prop := 
    match Γ with
    | [] => True
    | (x,t) :: Γ_tail => 
        ∃ t' pre post, Γ' = pre ++ (x, t') :: post ∧ _type D t t' ∧ _ctx D Γ_tail (pre ++ post)
  end.

  (* Fixpoint _ctx D (Γ Γ' : ctx) : Prop := 
       match Γ, Γ' with
       | (x,t) :: Γ, [] => False
       | (x,t) :: Γ, (x',t') :: Γ' => x = x' ∧ _type D t t' ∧ _ctx D Γ Γ'
       | [], _ => True
       end.  *)

  Definition MultiT (τ : type) : Prop := _type ∅ τ (![MS] τ).

  Definition OnceR (ρ : row) : Prop := ∃ b, _row ∅ b (RFlip MS ρ) ρ. 

  (* Lifting Multi from types to ctx *)
  (* for multiset map *)
  (* Definition MultiC (Γ : ctx) : Prop := Forall MultiT (fmap fst (fmap snd (map_to_list Γ))). *)
  (* for lists *)
  Definition MultiC (Γ : ctx) : Prop := Forall MultiT (snd <$> Γ).

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
Notation "D ⊢ Γ ≤C Γ'" := (le._ctx D Γ Γ')
  (at level 74, Γ, Γ' at next level).
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
  
  (* Definition _ctx (Γ : ctx) : gset eff_name :=
       ⋃ ((λ '(_, (α, _)), _ty α) <$> (map_to_list Γ)). *)
  (* Definition _ctx (Γ : ctx) : gset eff_name :=
         ⋃ ((λ '(_, α), _ty α) <$> Γ). *)
  (* Definition _ctx (Γ : ctx) : gset eff_name :=
        ⋃ ((λ '(_, αs), ⋃ (_ty <$> αs)) <$> (map_to_list Γ)). *)
  Definition _ctx (Γ : ctx) : gset eff_name :=
    ⋃ ((λ '(_, α), _ty α) <$> Γ).


  (* REMARK : unsure if we need to make the check that s is free in dom Γ *)
  (* since this is probably dependent on the implementation of subst *)
  (* the reason is that we can tell eff_names and variables apart *)
  
  (* The assertion [fresh s Γ ρ α] holds if the string [s] is free in
     [ρ], [α], and [Γ], when seen as an effect name, and it must also not
     appear in the domain of [Γ]. *)
  Definition _fresh s Γ ρ α :=
    s ∉ vars._ctx Γ ∧
    s ∉ vars._row ρ ∧
    s ∉ vars._ty α.

End vars.

(* Shift all the indices in the context by one, *)
(*    used when inserting a new type interpretation in Δ. *)
(* Definition up_list_type (ts : list type) : list type := subst (ren (+1)) <$> ts. *)
Notation "⤉ Γ" := ((λ '(x, α), (x, α.[ren (+1)])) <$> (Γ : ctx)) (at level 10, format "⤉ Γ").

Reserved Notation "Δ '.|' Γ1 '⊢ₜ' e ':' ρ ':' τ '⊣' Γ2"
  (at level 74, Γ1, e, ρ, τ, Γ2 at next level).
Reserved Notation "'⊢ᵥ' v ':' τ"  (at level 20, v, τ at next level).
Reserved Notation "Γ '⊢ₚ' e ':' τ" (at level 20, e, τ at next level). 


Inductive typed :
  stringmap unit → ctx → expr → row → type → ctx → Prop :=

| Var_typed Δ Γ (x : string) τ :
  Δ .| <[ x :=c τ ]> Γ ⊢ₜ Var x : RNil : τ ⊣ Γ

| Val_typed Δ Γ v τ :
  ⊢ᵥ v : τ →
  Δ .| Γ ⊢ₜ Val v : RNil : τ ⊣ Γ

| Pure_typed Δ Γ1 Γ2 e τ :
  Γ1 ⊢ₚ e : τ → Δ .| Γ2 ;; Γ1 ⊢ₜ e : RNil : τ ⊣ Γ2

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
| Rec_typed Δ Γ Γ' f x e m ρ τ κ :
  match f with BNamed f => BNamed f ≠ x | BAnon => True end →
  (* TODO: for now we have to have this restriction *)
  f ∉ ctx_dom Γ → x ∉ ctx_dom Γ →  m m⪯C Γ →
  Δ .| <[ f :=c (τ -{ ρ }-[m]-> κ)%ty ]> <[ x :=c τ ]> Γ ⊢ₜ e : ρ : κ ⊣ ∅ →
                                                                Δ .| Γ ;; Γ' ⊢ₜ Rec f x e : RNil : τ -{ ρ }-[m]-> κ ⊣ Γ'

(* TODO: generalize according to Fig. 5 in Affect *)
| App_typed Δ Γ1 Γ2 Γ3 e1 e2 ρ ρ' ρ'' b τ κ :
  let D := le.row_to_disj_ctx ρ in 
  D ⊢ ρ' ≤R ρ @ b → D ⊢ ρ'' ≤R ρ @ b →
  ρ' R⪯T τ → ρ'' R⪯C Γ3 →
  Δ .| Γ1 ⊢ₜ e2 : ρ : τ ⊣ Γ2 →
                     Δ .| Γ2 ⊢ₜ e1 : ρ' : τ -{ ρ'' }-∘ κ ⊣ Γ3 →
                                        Δ .| Γ1 ⊢ₜ App e1 e2 : ρ : κ ⊣ Γ3

| TAbsElim_typed Δ Γ1 Γ2 e ρ τ τ' :
  Δ .| Γ1 ⊢ₜ e : ρ : ∀T: τ ⊣ Γ2 →
                     Δ .| Γ1 ⊢ₜ e : ρ : τ.[τ'/] ⊣ Γ2
| RAbsElim_typed Δ Γ1 Γ2 e (ρ ρ' : row) τ :
  Δ .| Γ1 ⊢ₜ e : ρ : ∀R: τ ⊣ Γ2 →
                     Δ .| Γ1 ⊢ₜ e : ρ : τ.|[ρ'/] ⊣ Γ2
| MAbsElim_typed Δ Γ1 Γ2 e ρ τ m :
  Δ .| Γ1 ⊢ₜ e : ρ : ∀M: τ ⊣ Γ2 →
                     Δ .| Γ1 ⊢ₜ e : ρ : τ.|[m/] ⊣ Γ2
                    

| TAlloc Δ Γ1 e ρ τ Γ2 : Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2  → Δ .| Γ1 ⊢ₜ AllocN (Val $ LitV $ LitInt 1) e : ρ : ref τ ⊣ Γ2
| TLoad Δ Γ1 e ρ τ Γ2 : Δ .| Γ1 ⊢ₜ e : ρ : ref τ ⊣ Γ2 → Δ .| Γ1 ⊢ₜ Load e : ρ : τ ⊣ Γ2
| TStore Δ Γ1 Γ2 Γ3 e e' ρ τ :
  Δ .| Γ1 ⊢ₜ e' : ρ : τ ⊣ Γ2 → 
                     Δ .| Γ2 ⊢ₜ e : ρ : ref τ ⊣ Γ3 → 
                                       Δ .| Γ1 ⊢ₜ Store e e' : ρ : () ⊣ Γ3
| TAllocTape Δ Γ1 e ρ Γ2 : Δ .| Γ1 ⊢ₜ e : ρ : ℕ ⊣ Γ2 →  Δ .| Γ1 ⊢ₜ AllocTape e : ρ : TTape ⊣ Γ2
| TRand Δ Γ1 Γ2 Γ3 e1 e2 ρ : Δ .| Γ2 ⊢ₜ e1 : ρ : ℕ ⊣ Γ3 → Δ .| Γ1 ⊢ₜ e2 : ρ : TTape ⊣ Γ2 → Δ .| Γ1 ⊢ₜ Rand e1 e2 : ρ : ℕ ⊣ Γ3
| TRandU Δ Γ1 Γ2 Γ3 e1 e2 ρ : Δ .| Γ2 ⊢ₜ e1 : ρ : ℕ ⊣ Γ3 → Δ .| Γ1 ⊢ₜ e2 : ρ : () ⊣ Γ2 → Δ .| Γ1 ⊢ₜ Rand e1 e2 : ρ : ℕ ⊣ Γ3
| TFold Δ Γ1 e ρ τ Γ2 :
     Δ .| Γ1 ⊢ₜ e : ρ : τ.[(μ: τ)%ty/] ⊣ Γ2 →
     Δ .| Γ1 ⊢ₜ e : ρ : (μ: τ) ⊣ Γ2
| TUnfold Δ Γ1 e ρ τ Γ2 :
     Δ .| Γ1 ⊢ₜ e : ρ : (μ: τ)%ty ⊣ Γ2 →
     Δ .| Γ1 ⊢ₜ rec_unfold e : ρ : τ.[(μ: τ)%ty/] ⊣ Γ2
| TPack Δ Γ1 e ρ τ τ' Γ2 :
     Δ .| Γ1 ⊢ₜ e : ρ : τ.[τ'/] ⊣ Γ2 →
     Δ .| Γ1 ⊢ₜ e : ρ : (∃: τ) ⊣ Γ2
| TUnpack Δ Γ1 Γ2 Γ3 e1 x e2 ρ τ τ2 :
     Δ .| Γ1 ⊢ₜ e1 : ρ : (∃: τ) ⊣ Γ2 →
     Δ .| <[x:=c τ]> (⤉ Γ2) ⊢ₜ e2 : ρ : τ2.[ren (+1)] ⊣ Γ3 →
     Δ .| Γ1 ⊢ₜ (unpack: x := e1 in e2) : ρ : τ2 ⊣ Γ3
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

| DeepHandle_typed Δ Γ1 Γ2 Γ3 Γ (m : mode) s e x k h y r ρ0 σ τ τ' ι κ :
  le.MultiC Γ →
  Δ !! s = Some () →
  le.eff_name_from_sig σ = s →
  let ρ := RCons σ ρ0 in
  let ρ' := RCons (SFlip m (SSig s ι κ)) ρ0 in
  Δ .| Γ1 ⊢ₜ e : ρ' : τ ⊣ Γ2 →
  Δ .| <[ y :=c τ ]> (Γ2 ;; Γ) ⊢ₜ r : ρ : τ' ⊣ Γ3 →
  Δ .| <[ x :=c ι ]> <[ k :=c ![m] (κ -{ ρ }-∘ τ') ]> Γ ⊢ₜ h : ρ : τ' ⊣ Γ3 →
  Δ .| (Γ1 ;; Γ) ⊢ₜ (Handle Deep m s e (Lam x (Lam k h)) (Lam y r)) : ρ : τ' ⊣ Γ3

| ShallowHandle_typed Δ Γ1 Γ2 Γ3 Γ (m : mode) s e x k h y r ρ0 σ τ τ' ι κ :
  Δ !! s = Some () →
  le.eff_name_from_sig σ = s →
  let ρ := RCons σ ρ0 in
  ρ R⪯C Γ →
  let ρ' := RCons (SFlip m (SSig s ι κ)) ρ0 in
  Δ .| Γ1 ⊢ₜ e : ρ' : τ ⊣ Γ2 →
  Δ .| <[ y :=c τ ]> (Γ2 ;; Γ) ⊢ₜ r : ρ : τ' ⊣ Γ3 →
  Δ .| <[ x :=c ι ]> <[ k :=c ![m] (κ -{ ρ' }-∘ τ) ]> Γ ⊢ₜ h : ρ : τ' ⊣ Γ3 →
  Δ .| (Γ1 ;; Γ) ⊢ₜ Handle Shallow m s e (Lam x (Lam k h)) (Lam y r) : ρ : τ' ⊣ Γ3
    
| Sub_typed Δ Γ1 Γ1' Γ2 Γ2' ρ ρ' b τ τ' e : 
  let D := le.row_to_disj_ctx ρ in
  D ⊢ Γ1 ≤C Γ1' → D ⊢ Γ2' ≤C Γ2 →
  D ⊢ ρ' ≤R ρ @ b → D ⊢ τ' ≤T τ →
  Δ .| Γ1' ⊢ₜ e : ρ' : τ' ⊣ Γ2' →
                       Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2

| Contraction_typed Δ Γ1 Γ2 e ρ τ x κ :
  le.MultiT κ →
  Δ .| <[ x :=c κ ]> <[ x :=c κ ]> Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2 →
  Δ .| <[ x :=c κ ]> Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2
                           
| Weakening_typed Δ Γ1 Γ2 e ρ τ x κ :
  Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2 →
  Δ .| <[ x :=c κ ]> Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2

(* Pure_typed is used for value restriction, but allowing a bit more freedom. Can be extended later to cover all pure expressions *)
with pure_typed  : ctx → expr → type → Prop :=
| Val_pure_typed v τ : 
  ⊢ᵥ v : τ → [] ⊢ₚ v : τ

| Rec_pure_typed Γ1 f x e m τ ρ κ : 
  match f with BNamed f => BNamed f ≠ x | BAnon => True end →
  (* TODO: for now we have to have this restriction *)
  f ∉ ctx_dom Γ1 → x ∉ ctx_dom Γ1 →
  m m⪯C Γ1 → 
  ∅ .| <[ x :=c τ ]> <[ f :=c (τ -{ ρ }-[m]-> κ)%ty ]> Γ1 ⊢ₜ e : ρ : κ ⊣ [] → Γ1 ⊢ₚ Rec f x e : (τ -{ ρ }-[m]-> κ)%ty


| Pair_pure_typed Γ e1 e2 τ1 τ2 : 
  Γ ⊢ₚ e1 : τ1 → Γ ⊢ₚ e2 : τ2 → Γ ⊢ₚ Pair e1 e2 : (τ1 * τ2)%ty

| InjL_pure_typed Γ e τ1 τ2 : 
  Γ ⊢ₚ e : τ1 → Γ ⊢ₚ InjL e : (τ1 + τ2)%ty
| InjR_pure_typed Γ e τ1 τ2 : 
  Γ ⊢ₚ e : τ2 → Γ ⊢ₚ InjR e : (τ1 + τ2)%ty

| Var_pure_typed Γ (x : string) τ : 
   <[ x :=c τ ]> Γ ⊢ₚ Var x : τ 

| BangIntro_pure_typed Γ e m τ :
  m m⪯C Γ → Γ ⊢ₚ e : τ → Γ ⊢ₚ e : (![m] τ)%ty

| TAbs_pure_typed Γ e τ :
  Γ ⊢ₚ e : τ → Γ ⊢ₚ e : (∀T: τ)
| RAbs_pure_typed Γ e τ :
  Γ ⊢ₚ e : τ → Γ ⊢ₚ e : (∀R: τ)
| MAbs_pure_typed Γ e τ :
  Γ ⊢ₚ e : τ → Γ ⊢ₚ e : (∀M: τ)



with val_typed : val → type → Prop :=
| Unit_val_typed : ⊢ᵥ LitV LitUnit : ()
| Int_val_typed (n : Z) : ⊢ᵥ LitV (LitInt n) : ℤ
| Nat_val_typed (n : nat) : ⊢ᵥ LitV (LitInt n) : ℕ
| Bool_val_typed (b : bool) : ⊢ᵥ LitV (LitBool b) : 𝔹
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
| Rec_val_typed f x e τ1 ρ τ2 :
  ∅ .| <[f:=c τ1 -{ ρ }-> τ2]>(<[x:=c τ1]> ∅) ⊢ₜ e : ρ : τ2 ⊣ ∅ →
                                         ⊢ᵥ RecV f x e : (τ1 -{ ρ }-> τ2)
| TAbs_val_typed v τ :
  ⊢ᵥ v : τ →
           ⊢ᵥ v : (∀T: τ)
| RAbs_val_typed v τ :
  ⊢ᵥ v : τ →
           ⊢ᵥ v : (∀R: τ)
| MAbs_val_typed v τ :
  ⊢ᵥ v : τ →
           ⊢ᵥ v : (∀M: τ)

where "Δ .| Γ1 ⊢ₜ e : ρ : τ ⊣ Γ2" := (typed Δ Γ1 e%E ρ τ%ty Γ2)
and "⊢ᵥ e : τ" := (val_typed e τ%ty)
and "Γ ⊢ₚ e : τ" := (pure_typed Γ e%E τ%ty).                   
 
Section derived_rules. 

  Lemma CRefl_le D Γ :
      D ⊢  Γ ≤C Γ.
  Proof.
    induction Γ as [| [x t] Γ_tail IH].
    - simpl. exact I.
    - simpl.
      (* We need to provide t', pre, and post *)
      exists t, [], Γ_tail.
      split; [reflexivity |].
      split; [apply le.TRefl_le |].
      apply IH.
  Qed.

  (* Lemma: If Γ' is a permutation of Γ'', and we can match Γ into Γ', 
   we can also match it into Γ''. *)
  Lemma _ctx_perm_right : forall D Γ Γ' Γ'',
      le._ctx D Γ Γ' ->
      Permutation Γ' Γ'' ->
      le._ctx D Γ Γ''.
  Proof.
    intros D Γ. induction Γ as [| [x t] Γ_tail IH].
    - simpl. auto.
    - intros Γ' Γ'' Hctx Hperm. simpl in *.
      destruct Hctx as [t' [pre [post [Heq [Htype Hrest]]]]].
      subst Γ'.
      (* Since (pre ++ (x, t') :: post) is permuted to Γ'', 
       (x, t') must exist somewhere in Γ'' *)
      assert (H_in: In (x, t') Γ''). {
        apply Permutation_in with (l := pre ++ (x, t') :: post); first done.
        apply in_elt.
      }
      (* Decompose Γ'' around (x, t') *)
      apply in_split in H_in. destruct H_in as [pre' [post' Heq'']].
      exists t', pre', post'.
      split. { assumption. }
      split. { assumption. }
      (* The key: the remainders are also permutations *)
      apply IH with (Γ' := pre ++ post).
      + assumption.
      + eapply Permutation_cons_inv. 
        rewrite !Permutation_middle. 
        erewrite Hperm. by rewrite Heq''.
  Qed. 

  Lemma _ctx_perm_left D Γ1 Γ2 Γ3 : 
    D ⊢ Γ1 ≤C Γ2 → 
    Permutation Γ1 Γ3 →
    D ⊢ Γ3 ≤C Γ2. 
  Proof. 
    intros Hle1 Hperm.
    generalize dependent Γ2.
    induction Hperm; intros Γ3 Hle1.
    - exact Hle1.
    - simpl in *. destruct x as (x, t).
      destruct Hle1 as [t' [pre [post [Heq [Htyp Htail]]]]].
      exists t', pre, post.
      split; [assumption | split; [assumption |]].
      apply IHHperm. exact Htail.
    - destruct x as (x,t).
      destruct y as (y, t').
      destruct Hle1 as (t''&pre&post&->&Ht''&Hle).
      destruct Hle as (r&pre'&post'&Heq&Ht&Hle).
      eapply _ctx_perm_right; last apply Permutation_middle.
      exists r, ((y,t'')::pre'), post'.
      split. { rewrite -app_comm_cons. by rewrite -Heq. }
      split; first done.
      exists t'', [], (pre' ++ post'). split; first done.
      split; done.
    - apply IHHperm2, IHHperm1, Hle1.
  Qed.
    
  Lemma CTrans_le D Γ1 Γ2 Γ3 :
    D ⊢ Γ1 ≤C Γ2 → D ⊢ Γ2 ≤C Γ3 → D ⊢ Γ1 ≤C Γ3.
  Proof. 
    generalize Γ2 Γ3. induction Γ1 as [| [x t1] Γ1_tail IH]; [done|].
    intros Γ2' Γ3' (τ&pre&post&->&Hτ&Hle1) Hle2.
    eapply _ctx_perm_left in Hle2; last by rewrite -Permutation_middle.
    destruct Hle2 as (τ'&pre'&post'&->&Hτ'&Hle3).
    exists τ', pre', post'.
    split; first done. split; first by eapply le.TTrans_le.
    by eapply IH.
  Qed. 

  Lemma SRefl_le D e : D ⊢ e ≤S e.
  Proof. 
    induction e; by repeat constructor.
  Qed. 

  Lemma RRefl_le D ρ b : D ⊢ ρ ≤R ρ @ b.
  Proof.
    generalize dependent b. revert ρ. induction ρ; intros b; repeat constructor.
    - apply SRefl_le.
    - apply IHρ.
    - apply IHρ.
    - eapply le.RTrans_le.
      + apply le.RUnfold_le.
      + apply le.RFold_le.
  Qed. 

End derived_rules.
