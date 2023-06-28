(** Notion of contextual refinement & proof that it is a precongruence wrt the logical relation *)
From Coq Require Import Reals.
From clutch.program_logic Require Import exec.
From clutch.prob_lang Require Export lang notation.
From iris.proofmode Require Import proofmode.
From clutch.rel_logic Require Import primitive_laws model.
From clutch.typing Require Export types interp fundamental.

Inductive ctx_item :=
  (* Base lambda calculus *)
  | CTX_Rec (f x : binder)
  | CTX_AppL (e2 : expr)
  | CTX_AppR (e1 : expr)
  (* Base types and their operations *)
  | CTX_UnOp (op : un_op)
  | CTX_BinOpL (op : bin_op) (e2 : expr)
  | CTX_BinOpR (op : bin_op) (e1 : expr)
  | CTX_IfL (e1 : expr) (e2 : expr)
  | CTX_IfM (e0 : expr) (e2 : expr)
  | CTX_IfR (e0 : expr) (e1 : expr)
  (* Products *)
  | CTX_PairL (e2 : expr)
  | CTX_PairR (e1 : expr)
  | CTX_Fst
  | CTX_Snd
  (* Sums *)
  | CTX_InjL
  | CTX_InjR
  | CTX_CaseL (e1 : expr) (e2 : expr)
  | CTX_CaseM (e0 : expr) (e2 : expr)
  | CTX_CaseR (e0 : expr) (e1 : expr)
  (* Heap *)
  | CTX_Alloc
  | CTX_Load
  | CTX_StoreL (e2 : expr)
  | CTX_StoreR (e1 : expr)
  (* Recursive Types *)
  | CTX_Fold
  | CTX_Unfold
  (* Polymorphic Types *)
  | CTX_TLam
  | CTX_TApp
  (* Existential types *)
    (* Nb: we do not have an explicit PACK operation *)
  | CTX_UnpackL (x : binder) (e2 : expr)
  | CTX_UnpackR (x : binder) (e1 : expr)
  | CTX_AllocTape
  | CTX_RandL (e2 : expr)
  | CTX_RandR (e1 : expr)
.

Definition fill_ctx_item (ctx : ctx_item) (e : expr) : expr :=
  match ctx with
  (* Base lambda calculus *)
  | CTX_Rec f x => Rec f x e
  | CTX_AppL e2 => App e e2
  | CTX_AppR e1 => App e1 e
  (* Base types and operations *)
  | CTX_UnOp op => UnOp op e
  | CTX_BinOpL op e2 => BinOp op e e2
  | CTX_BinOpR op e1 => BinOp op e1 e
  | CTX_IfL e1 e2 => If e e1 e2
  | CTX_IfM e0 e2 => If e0 e e2
  | CTX_IfR e0 e1 => If e0 e1 e
  (* Products *)
  | CTX_PairL e2 => Pair e e2
  | CTX_PairR e1 => Pair e1 e
  | CTX_Fst => Fst e
  | CTX_Snd => Snd e
  (* Sums *)
  | CTX_InjL => InjL e
  | CTX_InjR => InjR e
  | CTX_CaseL e1 e2 => Case e e1 e2
  | CTX_CaseM e0 e2 => Case e0 e e2
  | CTX_CaseR e0 e1 => Case e0 e1 e
  (* Concurrency *)
  (* Heap & atomic CAS/FAA *)
  | CTX_Alloc => Alloc e
  | CTX_Load => Load e
  | CTX_StoreL e2 => Store e e2
  | CTX_StoreR e1 => Store e1 e
  (* Recursive & polymorphic types *)
  | CTX_Fold => e
  | CTX_Unfold => rec_unfold e
  | CTX_TLam => Λ: e
  | CTX_TApp => TApp e
  | CTX_UnpackL x e1 => unpack: x:=e in e1
  | CTX_UnpackR x e0 => unpack: x:=e0 in e
  | CTX_AllocTape => AllocTape e
  | CTX_RandL e2 => Rand e e2
  | CTX_RandR e1 => Rand e1 e
  end.

Definition ctx := list ctx_item.

(* TODO: consider using foldl here *)
Definition fill_ctx (K : ctx) (e : expr) : expr := foldr fill_ctx_item e K.

(** typed ctx *)
Inductive typed_ctx_item :
    ctx_item → stringmap type → type → stringmap type → type → Prop :=
  (* Base lambda calculus *)
  | TP_CTX_Rec Γ τ τ' f x :
     typed_ctx_item (CTX_Rec f x) (<[f:=TArrow τ τ']>(<[x:=τ]>Γ)) τ' Γ (TArrow τ τ')
  | TP_CTX_AppL Γ e2 τ τ' :
     typed Γ e2 τ →
     typed_ctx_item (CTX_AppL e2) Γ (TArrow τ τ') Γ τ'
  | TP_CTX_AppR Γ e1 τ τ' :
     typed Γ e1 (TArrow τ τ') →
     typed_ctx_item (CTX_AppR e1) Γ τ Γ τ'
  (* Base types and operations *)
  | TP_CTX_UnOp_Nat op Γ τ :
     unop_int_res_type op = Some τ →
     typed_ctx_item (CTX_UnOp op) Γ TInt Γ τ
  | TP_CTX_UnOp_Bool op Γ τ :
     unop_bool_res_type op = Some τ →
     typed_ctx_item (CTX_UnOp op) Γ TBool Γ τ
  | TP_CTX_BinOpL_Nat op Γ e2 τ :
     typed Γ e2 TInt →
     binop_int_res_type op = Some τ →
     typed_ctx_item (CTX_BinOpL op e2) Γ TInt Γ τ
  | TP_CTX_BinOpR_Nat op e1 Γ τ :
     typed Γ e1 TInt →
     binop_int_res_type op = Some τ →
     typed_ctx_item (CTX_BinOpR op e1) Γ TInt Γ τ
  | TP_CTX_BinOpL_Bool op Γ e2 τ :
     typed Γ e2 TBool →
     binop_bool_res_type op = Some τ →
     typed_ctx_item (CTX_BinOpL op e2) Γ TBool Γ τ
  | TP_CTX_BinOpR_Bool op e1 Γ τ :
     typed Γ e1 TBool →
     binop_bool_res_type op = Some τ →
     typed_ctx_item (CTX_BinOpR op e1) Γ TBool Γ τ
  | TP_CTX_BinOpL_UnboxedEq e2 Γ τ :
     UnboxedType τ →
     typed Γ e2 τ →
     typed_ctx_item (CTX_BinOpL EqOp e2) Γ τ Γ TBool
  | TP_CTX_BinOpR_UnboxedEq e1 Γ τ :
     UnboxedType τ →
     typed Γ e1 τ →
     typed_ctx_item (CTX_BinOpR EqOp e1) Γ τ Γ TBool
  | TP_CTX_IfL Γ e1 e2 τ :
     typed Γ e1 τ → typed Γ e2 τ →
     typed_ctx_item (CTX_IfL e1 e2) Γ (TBool) Γ τ
  | TP_CTX_IfM Γ e0 e2 τ :
     typed Γ e0 (TBool) → typed Γ e2 τ →
     typed_ctx_item (CTX_IfM e0 e2) Γ τ Γ τ
  | TP_CTX_IfR Γ e0 e1 τ :
     typed Γ e0 (TBool) → typed Γ e1 τ →
     typed_ctx_item (CTX_IfR e0 e1) Γ τ Γ τ
  (* Products *)
  | TP_CTX_PairL Γ e2 τ τ' :
     typed Γ e2 τ' →
     typed_ctx_item (CTX_PairL e2) Γ τ Γ (TProd τ τ')
  | TP_CTX_PairR Γ e1 τ τ' :
     typed Γ e1 τ →
     typed_ctx_item (CTX_PairR e1) Γ τ' Γ (TProd τ τ')
  | TP_CTX_Fst Γ τ τ' :
     typed_ctx_item CTX_Fst Γ (TProd τ τ') Γ τ
  | TP_CTX_Snd Γ τ τ' :
     typed_ctx_item CTX_Snd Γ (TProd τ τ') Γ τ'
  (* Sums *)
  | TP_CTX_InjL Γ τ τ' :
     typed_ctx_item CTX_InjL Γ τ Γ (TSum τ τ')
  | TP_CTX_InjR Γ τ τ' :
     typed_ctx_item CTX_InjR Γ τ' Γ (TSum τ τ')
  | TP_CTX_CaseL Γ e1 e2 τ1 τ2 τ' :
     typed Γ e1 (TArrow τ1 τ') → typed Γ e2 (TArrow τ2 τ') →
     typed_ctx_item (CTX_CaseL e1 e2) Γ (TSum τ1 τ2) Γ τ'
  | TP_CTX_CaseM Γ e0 e2 τ1 τ2 τ' :
     typed Γ e0 (TSum τ1 τ2) → typed Γ e2 (TArrow τ2 τ') →
     typed_ctx_item (CTX_CaseM e0 e2) Γ (TArrow τ1 τ') Γ τ'
  | TP_CTX_CaseR Γ e0 e1 τ1 τ2 τ' :
     typed Γ e0 (TSum τ1 τ2) → typed Γ e1 (TArrow τ1 τ') →
     typed_ctx_item (CTX_CaseR e0 e1) Γ (TArrow τ2 τ') Γ τ'
  (* Heap *)
  | TPCTX_Alloc Γ τ :
     typed_ctx_item CTX_Alloc Γ τ Γ (TRef τ)
  | TP_CTX_Load Γ τ :
     typed_ctx_item CTX_Load Γ (TRef τ) Γ τ
  | TP_CTX_StoreL Γ e2 τ :
     typed Γ e2 τ → typed_ctx_item (CTX_StoreL e2) Γ (TRef τ) Γ ()
  | TP_CTX_StoreR Γ e1 τ :
     typed Γ e1 (TRef τ) →
     typed_ctx_item (CTX_StoreR e1) Γ τ Γ ()
  (* Polymorphic & recursive types *)
  | TP_CTX_Fold Γ τ :
     typed_ctx_item CTX_Fold Γ τ.[(TRec τ)/] Γ (TRec τ)
  | TP_CTX_Unfold Γ τ :
     typed_ctx_item CTX_Unfold Γ (TRec τ) Γ τ.[(TRec τ)/]
  | TP_CTX_TLam Γ τ :
     typed_ctx_item CTX_TLam (Autosubst_Classes.subst (ren (+1)) <$> Γ) τ Γ (TForall τ)
  | TP_CTX_TApp Γ τ τ' :
     typed_ctx_item CTX_TApp Γ (TForall τ) Γ τ.[τ'/]
  (* | TP_CTX_Pack Γ τ τ' : *)
  (*    typed_ctx_item CTX_Pack Γ τ.[τ'/] Γ (TExists τ) *)
  | TP_CTX_UnpackL x e2 Γ τ τ2 :
     <[x:=τ]>(⤉ Γ) ⊢ₜ e2 : (Autosubst_Classes.subst (ren (+1)) τ2) →
     typed_ctx_item (CTX_UnpackL x e2) Γ (TExists τ) Γ τ2
  | TP_CTX_UnpackR x e1 Γ τ τ2 :
      Γ ⊢ₜ e1 : TExists τ →
     typed_ctx_item (CTX_UnpackR x e1)
                    (<[x:=τ]>(⤉ Γ)) (Autosubst_Classes.subst (ren (+1)) τ2)
                    Γ τ2
  | TP_CTX_AllocTape Γ :
     typed_ctx_item CTX_AllocTape Γ TNat Γ (TTape)
  | TP_CTX_RandUnitL Γ e2 :
    typed Γ e2 TUnit → typed_ctx_item (CTX_RandL e2) Γ TNat Γ TNat
  | TP_CTX_RandTapeL Γ e2 :
     typed Γ e2 TTape → typed_ctx_item (CTX_RandL e2) Γ TNat Γ TNat
  | TP_CTX_RandUnitR Γ e1 :
    typed Γ e1 TNat → typed_ctx_item (CTX_RandR e1) Γ TUnit Γ TNat
  | TP_CTX_RandTapeR Γ e1 :
     typed Γ e1 TNat → typed_ctx_item (CTX_RandR e1) Γ TTape Γ TNat
.

Inductive typed_ctx: ctx → stringmap type → type → stringmap type → type → Prop :=
  | TPCTX_nil Γ τ :
     typed_ctx nil Γ τ Γ τ
  | TPCTX_cons Γ1 τ1 Γ2 τ2 Γ3 τ3 k K :
     typed_ctx_item k Γ2 τ2 Γ3 τ3 →
     typed_ctx K Γ1 τ1 Γ2 τ2 →
     typed_ctx (k :: K) Γ1 τ1 Γ3 τ3.

(** The main definition of contextual refinement that we use. An
    alternative (equivalent) formulation which observes only
    termination can be found in [contextual_refinement_alt.v] *)
(* Can we avoid exposing validity of the initial tapes in this definition? *)
Definition ctx_refines (Γ : stringmap type)
    (e e' : expr) (τ : type) : Prop := ∀ K σ₀ (b : bool),
  typed_ctx K Γ τ ∅ TBool →
  (lim_exec_val (fill_ctx K e, σ₀) #b <= lim_exec_val (fill_ctx K e', σ₀) #b)%R.

Notation "Γ ⊨ e '≤ctx≤' e' : τ" :=
  (ctx_refines Γ e e' τ) (at level 100, e, e' at next level, τ at level 200).

Lemma typed_ctx_item_typed k Γ τ Γ' τ' e :
  typed Γ e τ → typed_ctx_item k Γ τ Γ' τ' →
  typed Γ' (fill_ctx_item k e) τ'.
Proof. induction 2; simpl; eauto using typed. Qed.

Lemma typed_ctx_typed K Γ τ Γ' τ' e :
  typed Γ e τ → typed_ctx K Γ τ Γ' τ' → typed Γ' (fill_ctx K e) τ'.
Proof. induction 2; simpl; eauto using typed_ctx_item_typed. Qed.

Global Instance ctx_refines_reflexive Γ τ :
  Reflexive (fun e1 e2 => ctx_refines Γ e1 e2 τ).
Proof. intros ?????. done. Qed.

Global Instance ctx_refines_transitive Γ τ :
  Transitive (fun e1 e2 => ctx_refines Γ e1 e2 τ).
Proof.
  intros e1 e2 e3 Hctx1 Hctx2 K σ₀ b Hty.
  pose proof (Hctx1 K σ₀ b Hty) as H1.
  pose proof (Hctx2 K σ₀ b Hty) as H2.
  by etrans.
Qed.

Lemma fill_ctx_app (K K' : ctx) (e : expr) :
  fill_ctx K' (fill_ctx K e) = fill_ctx (K' ++ K) e.
Proof. by rewrite /fill_ctx foldr_app. Qed.

Lemma typed_ctx_compose (K K' : ctx) (Γ1 Γ2 Γ3 : stringmap type) (τ1 τ2 τ3 : type) :
  typed_ctx K Γ1 τ1 Γ2 τ2 →
  typed_ctx K' Γ2 τ2 Γ3 τ3 →
  typed_ctx (K' ++ K) Γ1 τ1 Γ3 τ3.
Proof.
  revert Γ1 Γ2 Γ3 τ1 τ2 τ3.
  induction K' as [|k K'] => Γ1 Γ2 Γ3 τ1 τ2 τ3.
  - by inversion 2; simplify_eq/=.
  - intros HK.
    inversion 1 as [|? ? ? ? ? ? ? ? Hx1 Hx2]; simplify_eq/=.
    specialize (IHK' _ _ _ _ _ _ HK Hx2).
    econstructor; eauto.
Qed.

Lemma ctx_refines_congruence Γ e1 e2 τ Γ' τ' K :
  typed_ctx K Γ τ Γ' τ' →
  (Γ ⊨ e1 ≤ctx≤ e2 : τ) →
  Γ' ⊨ fill_ctx K e1 ≤ctx≤ fill_ctx K e2 : τ'.
Proof.
  intros HK Hctx K' σ₀ b Hty.
  rewrite !fill_ctx_app.
  apply (Hctx (K' ++ K) σ₀); auto.
  eapply typed_ctx_compose; eauto.
Qed.

Definition ctx_equiv Γ e1 e2 τ :=
  (Γ ⊨ e1 ≤ctx≤ e2 : τ) ∧ (Γ ⊨ e2 ≤ctx≤ e1 : τ).

Notation "Γ ⊨ e '=ctx=' e' : τ" :=
  (ctx_equiv Γ e e' τ) (at level 100, e, e' at next level, τ at level 200).

Global Instance ctx_equiv_transitive Γ τ :
  Transitive (fun e1 e2 => ctx_equiv Γ e1 e2 τ).
Proof.
  intros e1 e2 e3 [Hctx11 Hctx12] [Hctx21 Hctx22].
  split ; eapply ctx_refines_transitive ;eauto.
Qed.

Section bin_log_related_under_typed_ctx.
  Context `{!clutchRGS Σ}.

  (* Precongruence *)
  Lemma bin_log_related_under_typed_ctx Γ e e' τ Γ' τ' K :
    (typed_ctx K Γ τ Γ' τ') →
    (□ ∀ Δ, (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ)) -∗
      (∀ Δ, 〈Δ;Γ'〉 ⊨ fill_ctx K e ≤log≤ fill_ctx K e' : τ')%I.
  Proof.
    revert Γ τ Γ' τ' e e'.
    induction K as [|k K]=> Γ τ Γ' τ' e e'; simpl.
    - inversion_clear 1; trivial. iIntros "#H".
      iIntros (Δ). by iApply "H".
    - inversion_clear 1 as [|? ? ? ? ? ? ? ? Hx1 Hx2].
      specialize (IHK _ _ _ _ e e' Hx2).
      inversion Hx1; subst; simpl; iIntros "#Hrel";
        iIntros (Δ).
      + iApply (bin_log_related_rec with "[-]"); auto.
        iModIntro. iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_app with "[]").
        { iApply (IHK with "[Hrel]"); auto. }
        by iApply fundamental.
      + iApply (bin_log_related_app _ _ _ _ _ _ τ2 with "[]").
        { by iApply fundamental. }
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_int_unop; eauto.
        by iApply (IHK with "Hrel").
      + iApply bin_log_related_bool_unop; eauto.
        by iApply (IHK with "Hrel").
      + iApply bin_log_related_int_binop;
          try (by iApply fundamental); eauto.
        by iApply (IHK with "Hrel").
      + iApply bin_log_related_int_binop;
          try (by iApply fundamental); eauto.
        by iApply (IHK with "Hrel"); auto.
      + iApply bin_log_related_bool_binop;
          try (by iApply fundamental); eauto.
        by iApply (IHK with "Hrel").
      + iApply bin_log_related_bool_binop;
          try (by iApply fundamental); eauto.
        by iApply (IHK with "Hrel").
      + iApply bin_log_related_unboxed_eq; try (eassumption || by iApply fundamental).
        by iApply (IHK with "Hrel").
      + iApply bin_log_related_unboxed_eq; try (eassumption || by iApply fundamental).
        by iApply (IHK with "Hrel").
      + iApply (bin_log_related_if with "[] []");
          try by iApply fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_if with "[] []");
          try by iApply fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_if with "[] []");
          try by iApply fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_pair with "[]").
        { iApply (IHK with "[Hrel]"); auto. }
        by iApply fundamental.
      + iApply (bin_log_related_pair with "[]").
        { by iApply fundamental. }
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_fst.
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_snd.
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_injl.
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_injr.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_case with "[] []").
        { iApply (IHK with "[Hrel]"); auto. }
        { by iApply fundamental. }
        by iApply fundamental.
      + iApply (bin_log_related_case with "[] []").
        { by iApply fundamental. }
        { iApply (IHK with "[Hrel]"); auto. }
        by iApply fundamental.
      + iApply (bin_log_related_case with "[] []").
        { by iApply fundamental. }
        { by iApply fundamental. }
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_alloc with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_load with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_store with "[]");
          try by iApply fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_store with "[]");
          try by iApply fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_fold with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_unfold with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_tlam with "[]").
        iIntros (τi). iModIntro.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_tapp' with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_unpack.
        * iApply (IHK with "[Hrel]"); auto.
        * iIntros (A). by iApply fundamental.
      + iApply bin_log_related_unpack.
        * by iApply fundamental.
        * iIntros (A). iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_alloctape.
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_rand_unit.
        * iApply (IHK with "[Hrel]"); auto.
        * by iApply fundamental.
      + iApply bin_log_related_rand_tape.
        * iApply (IHK with "[Hrel]"); auto.
        * by iApply fundamental.
      + iApply bin_log_related_rand_unit.
        * by iApply fundamental.
        * iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_rand_tape.
        * by iApply fundamental.
        * iApply (IHK with "[Hrel]"); auto.
  Qed.
End bin_log_related_under_typed_ctx.


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
          first [ eapply TRand ; (try by eauto) ; type_expr (n-1)
                | eapply TRandU ; (try by eauto) ; type_expr (n-1)]
      | |- _ => idtac
      end
  end

    with type_val n :=
    lazymatch eval compute in n with
    | O => idtac
    | _ =>
        lazymatch goal with
        | |- ⊢ᵥ LitV LitUnit : _ => eapply Unit_val_typed
        | |- ⊢ᵥ LitV (LitInt _) : _ => eapply Int_val_typed
        | |- ⊢ᵥ LitV (LitInt _) : _ => eapply Nat_val_typed
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
