From clutch.con_prob_lang Require Import lang notation.
From clutch.con_prob_lang.typing Require Import types contextual_refinement.

(* Simple-minded syntax-directed type checker. The econstructor tactic can go
   wrong by applying non-syntax directed (insufficiently constrained)
   constructors, and get stuck, so we explicitly select constructors where it's
   unambiguous instead.

   The definition is recursive since it uses a very small amount of
   backtracking. Thus, invoking `type_expr N` is not quite equivalent to
   calling `do N type_expr 1`. *)
Ltac type_expr n :=
  lazymatch eval compute in n with
  | O => idtac
  | _ =>
      lazymatch goal with
      | |- _ ⊢ₜ Var _ : _ => eapply Var_typed ; (try by eauto)
      | |- _ ⊢ₜ Val _ : _ => eapply Val_typed ; type_val n
      | |- _ ⊢ₜ BinOp ?op _ _ : _ =>
          match eval compute in (binop_int_res_type op) with
          | Some _ => eapply BinOp_typed_int ; [type_expr (n-1) | type_expr (n-1) | try by eauto]
          | _ => match eval compute in (binop_bool_res_type op) with
                 | Some _ => eapply BinOp_typed_bool ; [type_expr (n-1) | type_expr (n-1) | try by eauto]
                 end
          end
      | |- _ ⊢ₜ UnOp ?op _ : _ =>
          match eval compute in (unop_int_res_type op) with
          | Some _ => eapply UnOp_typed_int ; [type_expr (n-1) | try by eauto]
          | _ => match eval compute in (unop_bool_res_type op) with
                 | Some _ => eapply UnOp_typed_bool ; [type_expr (n-1) | try by eauto]
                 end
          end
      | |- _ ⊢ₜ BinOp EqOp _ _ : _ => eapply UnboxedEq_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Pair _ _ : _ => eapply Pair_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Fst _ : _ => eapply Fst_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Snd _ : _ => eapply Snd_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ InjL _ : _ => eapply InjL_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ InjR _ : _ => eapply InjR_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Case _ _ _ : _ => eapply Case_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ If _ _ _ : _ => eapply If_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ (Rec _ _ _) : _ =>
          (* could also try TLam_typed here *)
          eapply Rec_typed ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ App _ _ : _ =>
          (* could also try TApp_typed here *)
          eapply App_typed ; (try by eauto) ; type_expr (n-1)
      (* | TLam_typed Γ e τ : *)
      (*     ⤉ Γ ⊢ₜ e : τ → *)
      (*     Γ ⊢ₜ (Λ: e) : ∀: τ *)
      (*  | TApp_typed Γ e τ τ' : *)
      (*     Γ ⊢ₜ e : (∀: τ) → *)
      (*     Γ ⊢ₜ e #() : τ.[τ'/] *)
      (*  | TFold Γ e τ : *)
      (*     Γ ⊢ₜ e : τ.[(μ: τ)%ty/] → *)
      (*     Γ ⊢ₜ e : (μ: τ) *)
      (*  | TUnfold Γ e τ : *)
      (*     Γ ⊢ₜ e : (μ: τ)%ty → *)
      (*     Γ ⊢ₜ rec_unfold e : τ.[(μ: τ)%ty/] *)
      (*  | TPack Γ e τ τ' : *)
      (*     Γ ⊢ₜ e : τ.[τ'/] → *)
      (*     Γ ⊢ₜ e : (∃: τ) *)
      (*  | TUnpack Γ e1 x e2 τ τ2 : *)
      (*     Γ ⊢ₜ e1 : (∃: τ) → *)
      (*     <[x:=τ]>(⤉ Γ) ⊢ₜ e2 : (Autosubst_Classes.subst (ren (+1)) τ2) → *)
      (*     Γ ⊢ₜ (unpack: x := e1 in e2) : τ2 *)
      | |- _ ⊢ₜ Alloc _ : _ => eapply TAlloc ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Load _ : _ => eapply TLoad ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Store _ _ : _ => eapply TStore ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ AllocTape _ : _ => eapply TAllocTape ; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Rand _ _ : _ =>
          first [ eapply TRand ; (try by eauto) ; [ type_expr (n-1) | by type_expr (n-1) ]
                | eapply TRandU ; (try by eauto) ; type_expr (n-1)]
      | |- _ ⊢ₜ Fork _ : _ => eapply Fork_typed; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ CmpXchg _ _ _ : _ => eapply CmpXchg_typed; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ Xchg _ _: _ => eapply Xchg_typed; (try by eauto) ; type_expr (n-1)
      | |- _ ⊢ₜ FAA _ _: _ => eapply Faa_typed; (try by eauto) ; type_expr (n-1)
      | |- _ => idtac
      end
  end

    with type_val n :=
    lazymatch eval compute in n with
    | O => idtac
    | _ =>
        lazymatch goal with
        | |- ⊢ᵥ LitV LitUnit : _ => eapply Unit_val_typed
        | |- ⊢ᵥ _ : TNat => eapply Nat_val_typed
        | |- ⊢ᵥ LitV (LitInt _) : _ => eapply Int_val_typed
        (* | |- ⊢ᵥ LitV (LitInt _) : _ => eapply Nat_val_typed *)
        | |- ⊢ᵥ LitV (LitBool _) : _ => eapply Bool_val_typed
        | |- ⊢ᵥ PairV _ _ : _ => eapply Pair_val_typed ; type_val (n-1)
        | |- ⊢ᵥ InjLV _ : _ => eapply InjL_val_typed ; type_val (n-1)
        | |- ⊢ᵥ InjRV _ : _ => eapply InjR_val_typed ; type_val (n-1)
        | |- ⊢ᵥ RecV _ _ _ : _ => eapply Rec_val_typed ; type_expr (n-1)
        | |- ⊢ᵥ (Λ: _) : (∀: _) => idtac
        (* TODO does this overlap with the RecV case? Does the below work for
        Λ: λ:"x","x"? *)
        (* eapply TLam_val_typed ; type_expr (n-1) *)
        | _ => idtac
        end
    end.

Ltac type_ctx :=
  match goal with
  | |- typed_ctx nil ?ctx_in ?ty_in ?ctx_out ?ty_out =>
      apply TPCTX_nil
  | |- typed_ctx (?k :: ?K) ?ctx_in ?ty_in ?ctx_out ?ty_out =>
      econstructor ; last first ; [type_ctx | econstructor]
  | _ => idtac
  end.

Ltac tychk := try type_ctx ; try type_expr 100 ; try type_val 100.
