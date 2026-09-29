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

(** [list_fold_poly] is well-typed at the polymorphic list-fold type
    [∀α. ∀β. (β → α → β) → β → list α → β].  The outer binder is the element
    type [α] ([TVar 1] inside), the inner binder the accumulator type [β]
    ([TVar 0]); this matches the instantiation in [list_max_index_aux], which
    folds an [α = TInt] list with a [β = TInt*TInt*TInt] accumulator.  The
    [rec_unfold] coercion before the [match] is handled by [TUnfold] (cf.
    [list_map_poly_typed]). *)
Lemma list_fold_poly_typed Sg :
  val_typed Sg list_fold_poly
    (TForall (TForall ((TVar 0 → TVar 1 → TVar 0) → TVar 0 → TList (TVar 1) → TVar 0)))%ty.
Proof.
  rewrite /list_fold_poly /list_fold_go.
  apply TLam_val_typed.
  apply TLam_typed.
  apply Val_typed.
  apply Rec_val_typed.
  do 2 apply Rec_typed.
  eapply (Case_typed _ _ _ _ _ TUnit (TProd (TVar 1) (TList (TVar 1))) (TVar 0)).
  - change ((λ: "x", "x")%V "l")%E with (rec_unfold "l").
    rewrite -(type_unfold_compute (TVar 1)).
    apply TUnfold. apply Var_typed. by rewrite lookup_insert.
  - (* [NONE => "acc"] : the [λ <> "acc"] branch returns the accumulator *)
    apply Rec_typed. apply Var_typed.
    by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert.
  - (* [SOME "a" => let "f" := Fst "a" in let "s" := Snd "a" in
                    let "acc" := "handler" "acc" "f" in "go" "handler" "acc" "s"] *)
    apply Rec_typed.
    (* let: "f" := Fst "a" : TVar 1 *)
    eapply App_typed; last (eapply Fst_typed; apply Var_typed; by rewrite lookup_insert).
    apply Rec_typed.
    (* let: "s" := Snd "a" : TList (TVar 1) *)
    eapply App_typed; last (eapply Snd_typed; apply Var_typed;
      by rewrite lookup_insert_ne // lookup_insert).
    apply Rec_typed.
    (* let: "acc" := "handler" "acc" "f" : TVar 0 *)
    eapply App_typed.
    + apply Rec_typed.
      (* "go" "handler" "acc" "s" : TVar 0 *)
      eapply App_typed; [ eapply App_typed | ].
      * (* "go" "handler" : TVar 0 → TList (TVar 1) → TVar 0 *)
        eapply App_typed.
        -- apply Var_typed.
           by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_ne //
                      lookup_insert_ne // lookup_insert_ne // lookup_insert.
        -- apply Var_typed.
           by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_ne //
                      lookup_insert_ne // lookup_insert.
      * (* "acc" : TVar 0 *)
        apply Var_typed. by rewrite lookup_insert.
      * (* "s" : TList (TVar 1) *)
        apply Var_typed.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert.
    + (* "handler" "acc" "f" : TVar 0 *)
      eapply App_typed; [ eapply App_typed | ].
      * (* "handler" : TVar 0 → TVar 1 → TVar 0 *)
        apply Var_typed.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_ne //
                   lookup_insert_ne // lookup_insert.
      * (* "acc" : TVar 0 *)
        apply Var_typed. by rewrite lookup_insert_ne // lookup_insert.
      * (* "f" : TVar 1 *)
        apply Var_typed. by rewrite lookup_insert_ne // lookup_insert.
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

(** [list_max_index_aux] is well-typed (monomorphically) at
    [int → list int → (int * int * int)].  It folds the list with
    [list_fold_poly] instantiated at element type [int] and accumulator type
    [int * int * int]; the per-element handler destructures the accumulator
    triple (nested [Fst]/[Snd] via the [let,] notation) and rebuilds it, with
    every component forced to [TInt] by the [+ #1] increments. *)
Lemma list_max_index_aux_typed Sg :
  val_typed Sg list_max_index_aux (TInt → TList TInt → (TInt * TInt * TInt))%ty.
Proof.
  rewrite /list_max_index_aux.
  apply Rec_val_typed.
  apply Rec_typed.
  (* list_fold_poly #() #() handler acc xs : β  with α=TInt, β=TInt*TInt*TInt *)
  eapply (App_typed _ _ _ _ (TList TInt));
    [| apply Var_typed; by rewrite lookup_insert].
  eapply (App_typed _ _ _ _ (TInt * TInt * TInt)%ty).
  - (* list_fold_poly #() #() handler : β → TList TInt → β *)
    eapply (App_typed _ _ _ _
              ((TInt * TInt * TInt) → TInt → (TInt * TInt * TInt))%ty).
    + (* list_fold_poly #() #() : (β→α→β) → β → list α → β, instantiated at α/β *)
      eapply (TApp_typed _ _ _
                ((TVar 0 → TInt → TVar 0) → TVar 0 → TList TInt → TVar 0)%ty
                (TInt * TInt * TInt)%ty).
      change (list_fold_poly #()) with (TApp list_fold_poly).
      eapply (TApp_typed _ _ _
                (TForall ((TVar 0 → TVar 1 → TVar 0) → TVar 0 → TList (TVar 1) → TVar 0))%ty
                TInt).
      apply Val_typed. apply list_fold_poly_typed.
    + (* handler : β → α → β *)
      apply Rec_typed. apply Rec_typed.
      (* let: "y" := "(y, iy, ix)" : β *)
      eapply App_typed;
        [| apply Var_typed; by rewrite lookup_insert_ne // lookup_insert].
      apply Rec_typed.
      (* let: "iy" := Snd (Fst "y") : TInt *)
      eapply (App_typed _ _ _ _ TInt).
      * apply Rec_typed.
        (* let: "ix" := Snd "y" : TInt *)
        eapply (App_typed _ _ _ _ TInt).
        -- apply Rec_typed.
           (* let: "y" := Fst (Fst "y") : TInt *)
           eapply (App_typed _ _ _ _ TInt).
           ++ apply Rec_typed.
              (* if: "y" < "x" then (...) else (...) : β *)
              apply If_typed.
              ** eapply BinOp_typed_int; [ | | reflexivity ].
                 { apply Var_typed. by rewrite lookup_insert. }
                 { apply Var_typed.
                   by rewrite lookup_insert_ne // lookup_insert_ne //
                              lookup_insert_ne // lookup_insert_ne //
                              lookup_insert_ne // lookup_insert. }
              ** (* ("x", "ix", "ix"+#1) : (TInt*TInt)*TInt *)
                 apply Pair_typed; [apply Pair_typed|].
                 { apply Var_typed.
                   by rewrite lookup_insert_ne // lookup_insert_ne //
                              lookup_insert_ne // lookup_insert_ne //
                              lookup_insert_ne // lookup_insert. }
                 { apply Var_typed.
                   by rewrite lookup_insert_ne // lookup_insert. }
                 { eapply BinOp_typed_int; [ | apply Val_typed; apply Int_val_typed | reflexivity ].
                   apply Var_typed. by rewrite lookup_insert_ne // lookup_insert. }
              ** (* ("y", "iy", "ix"+#1) : (TInt*TInt)*TInt *)
                 apply Pair_typed; [apply Pair_typed|].
                 { apply Var_typed. by rewrite lookup_insert. }
                 { apply Var_typed.
                   by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert. }
                 { eapply BinOp_typed_int; [ | apply Val_typed; apply Int_val_typed | reflexivity ].
                   apply Var_typed. by rewrite lookup_insert_ne // lookup_insert. }
           ++ (* Fst (Fst "y") : TInt *)
              eapply Fst_typed. eapply Fst_typed. apply Var_typed.
              by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert.
        -- (* Snd "y" : TInt *)
           eapply Snd_typed. apply Var_typed.
           by rewrite lookup_insert_ne // lookup_insert.
      * (* Snd (Fst "y") : TInt *)
        eapply Snd_typed. eapply Fst_typed. apply Var_typed.
        by rewrite lookup_insert.
  - (* acc = ("y", #0, #1) : (TInt*TInt)*TInt *)
    apply Pair_typed; [apply Pair_typed|].
    + apply Var_typed. by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert.
    + apply Val_typed. apply Int_val_typed.
    + apply Val_typed. apply Int_val_typed.
Qed.

(** [list_max_index] is well-typed at [list int → int]: the outer match
    ([rec_unfold] on the scrutinee, handled by [TUnfold]) returns [#0 : int] on
    the empty list, and otherwise destructures the head/tail, runs
    [list_max_index_aux], and projects the middle component [iy : int]. *)
Lemma list_max_index_typed Sg :
  val_typed Sg list_max_index (TList TInt → TInt)%ty.
Proof.
  rewrite /list_max_index.
  apply Rec_val_typed.
  eapply (Case_typed _ _ _ _ _ TUnit (TProd TInt (TList TInt)) TInt).
  - (* scrutinee: rec_unfold "xs" : () + (TInt * TList TInt) *)
    change ((λ: "x", "x")%V "xs")%E with (rec_unfold "xs").
    rewrite -(type_unfold_compute TInt).
    apply TUnfold. apply Var_typed. by rewrite lookup_insert.
  - (* InjL: λ <>, #0 : () → TInt *)
    apply Rec_typed. apply Val_typed. apply Int_val_typed.
  - (* InjR: λ "y_xs", … : (TInt * TList TInt) → TInt *)
    apply Rec_typed.
    (* let: "xs" := "y_xs" : TInt * TList TInt *)
    eapply App_typed;
      [| apply Var_typed; by rewrite lookup_insert].
    apply Rec_typed.
    (* let: "y" := Fst "xs" : TInt *)
    eapply App_typed;
      [| eapply Fst_typed; apply Var_typed; by rewrite lookup_insert].
    apply Rec_typed.
    (* let: "xs" := Snd "xs" : TList TInt *)
    eapply App_typed;
      [| eapply Snd_typed; apply Var_typed;
         by rewrite lookup_insert_ne // lookup_insert].
    apply Rec_typed.
    (* let: "_y" := list_max_index_aux "y" "xs" : (TInt*TInt)*TInt *)
    eapply App_typed.
    + apply Rec_typed.
      (* let: "iy" := Snd (Fst "_y") : TInt *)
      eapply (App_typed _ _ _ _ TInt).
      * apply Rec_typed.
        (* let: "_ix" := Snd "_y" : TInt *)
        eapply (App_typed _ _ _ _ TInt).
        -- apply Rec_typed.
           (* let: "_y" := Fst (Fst "_y") : TInt *)
           eapply (App_typed _ _ _ _ TInt).
           ++ apply Rec_typed.
              (* "iy" : TInt *)
              apply Var_typed.
              by rewrite lookup_insert_ne // lookup_insert.
           ++ (* Fst (Fst "_y") : TInt *)
              eapply Fst_typed. eapply Fst_typed. apply Var_typed.
              by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert.
        -- (* Snd "_y" : TInt *)
           eapply Snd_typed. apply Var_typed.
           by rewrite lookup_insert_ne // lookup_insert.
      * (* Snd (Fst "_y") : TInt *)
        eapply Snd_typed. eapply Fst_typed. apply Var_typed.
        by rewrite lookup_insert.
    + (* list_max_index_aux "y" "xs" : (TInt*TInt)*TInt *)
      eapply App_typed; [ eapply App_typed | ].
      * apply Val_typed. apply list_max_index_aux_typed.
      * apply Var_typed.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert.
      * apply Var_typed. by rewrite lookup_insert.
Qed.
