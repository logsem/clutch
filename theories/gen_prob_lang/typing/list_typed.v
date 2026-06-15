(** Syntactic typing of the polymorphic list map [list_map_poly].

    [list_map_poly] (defined in [gwp.list]) is the type-abstracted version of the
    monomorphic [list_map]: it is typeable at the polymorphic type

        ∀α. ∀β. (α → β) → list α → list β

    so the fundamental theorem yields its relational free theorem.  [list_map]
    is the eta-expanded monomorphization [λ "f" "l", list_map_poly #() #() "f"
    "l"], so it behaves identically up to a few head beta-steps. *)
From clutch.gen_prob_lang.typing Require Import types.
From clutch.gen_prob_lang Require Import lang notation.
From clutch.gen_prob_lang Require Import gwp.list.

(** Unfolding the list type body at [TList τ] computes (definitionally, via
    [asimpl]) to [() + (τ × TList τ)].  The [τ.[ren (+1)]] shift in [TList] is
    exactly what makes this clean. *)
Lemma type_unfold_compute (τ : type) :
  (TSum TUnit (TProd τ.[ren (+1)] (TVar 0))).[(TList τ)/]
  = (TSum TUnit (TProd τ (TList τ))).
Proof. rewrite /TList. asimpl. reflexivity. Qed.

(** [list_cons] (the [::] constructor) is typeable at every element type
    [τ → TList τ → TList τ]. *)
Lemma list_cons_typed Sg (τ : type) Γ :
  typed Sg Γ (Val list_cons) (τ → TList τ → TList τ)%ty.
Proof.
  apply Val_typed.
  rewrite /list_cons.
  apply Rec_val_typed.
  apply Rec_typed.
  rewrite {1}/TList.
  apply (TFold _ _ _ (TSum TUnit (TProd τ.[ren (+1)] (TVar 0)))).
  rewrite (type_unfold_compute τ).
  apply InjR_typed.
  apply Pair_typed.
  - apply Var_typed. by rewrite lookup_insert_ne // lookup_insert.
  - apply Var_typed. by rewrite lookup_insert.
Qed.

(** [list_init_poly] is well-typed at the polymorphic list-init type
    [∀α. int → (int → α) → list α].  The index is [TInt] (matching its
    callers, which apply the per-index function to an integer index).  The
    loop only builds a list — [NONE]/[::] fold implicitly — so no
    [rec_unfold] appears. *)
Lemma list_init_poly_typed Sg :
  val_typed Sg list_init_poly
    (TForall (TInt → (TInt → TVar 0) → TList (TVar 0)))%ty.
Proof.
  rewrite /list_init_poly.
  apply TLam_val_typed.
  apply Rec_typed. apply Rec_typed.
  eapply App_typed; last (apply Val_typed; apply Int_val_typed).
  apply Rec_typed.
  apply If_typed.
  - (* [ "i" = "len" : bool ] *)
    eapply BinOp_typed_int; [ | | reflexivity ].
    + apply Var_typed. by rewrite lookup_insert_ne // lookup_insert.
    + apply Var_typed.
      by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_ne // lookup_insert.
  - (* [ [] = NONE : list α ] *)
    rewrite /list_nil {1}/TList.
    apply (TFold _ _ _ (TSum TUnit (TProd (TVar 0).[ren (+1)] (TVar 0)))).
    rewrite (type_unfold_compute (TVar 0)).
    apply InjL_typed. apply Val_typed. apply Unit_val_typed.
  - (* [ let: "h" := "f" "i" in let: "t" := "aux" ("i"+1) in "h" :: "t" ] *)
    eapply App_typed.
    + apply Rec_typed.
      eapply App_typed.
      * apply Rec_typed.
        (* [ "h" :: "t" = list_cons "h" "t" : list α ] *)
        eapply App_typed; [ eapply App_typed | ].
        -- apply (list_cons_typed _ (TVar 0)).
        -- apply Var_typed.
           by rewrite lookup_insert_ne // lookup_insert.
        -- apply Var_typed. by rewrite lookup_insert.
      * (* [ "aux" ("i" + #1) : list α ] *)
        eapply App_typed.
        -- apply Var_typed.
           by rewrite lookup_insert_ne // lookup_insert.
        -- eapply BinOp_typed_int; [ | apply Val_typed; apply Int_val_typed | reflexivity ].
           apply Var_typed.
           by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert.
    + (* [ "f" "i" : α ] *)
      eapply App_typed.
      * apply Var_typed.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert.
      * apply Var_typed. by rewrite lookup_insert_ne // lookup_insert.
Qed.

(** [list_map_poly] is well-typed at the polymorphic list-map type. *)
Lemma list_map_poly_typed Sg :
  val_typed Sg list_map_poly
    (TForall (TForall ((TVar 1 → TVar 0) → TList (TVar 1) → TList (TVar 0))))%ty.
Proof.
  rewrite /list_map_poly /list_map_go.
  apply TLam_val_typed.
  apply TLam_typed.
  apply Val_typed.
  apply Rec_val_typed.
  apply Rec_typed.
  eapply (Case_typed _ _ _ _ _ TUnit (TProd (TVar 1) (TList (TVar 1))) (TList (TVar 0))).
  - change ((λ: "x", "x")%V "l")%E with (rec_unfold "l").
    rewrite -(type_unfold_compute (TVar 1)).
    apply TUnfold. apply Var_typed. by rewrite lookup_insert.
  - apply Rec_typed.
    rewrite {1}/TList.
    apply (TFold _ _ _ (TSum TUnit (TProd (TVar 0).[ren (+1)] (TVar 0)))).
    rewrite (type_unfold_compute (TVar 0)).
    apply InjL_typed. apply Val_typed. apply Unit_val_typed.
  - apply Rec_typed.
    eapply App_typed.
    + eapply App_typed.
      * apply (list_cons_typed _ (TVar 0)).
      * eapply App_typed.
        -- apply Var_typed. by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert.
        -- eapply Fst_typed. apply Var_typed. by rewrite lookup_insert.
    + eapply App_typed.
      * eapply App_typed.
        -- apply Var_typed. by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_ne // lookup_insert.
        -- apply Var_typed. by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_ne // lookup_insert.
      * eapply Snd_typed. apply Var_typed. by rewrite lookup_insert.
Qed.
