From Stdlib Require Import Reals Psatz Btauto. 
From stdpp Require Import countable gmap stringmap fin_sets.
From clutch.prelude Require Import stdpp_ext.
From clutch.delay_prob_lang Require Import tactics notation.
From clutch.delay_prob_lang Require Export lang.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".

Section urn_subst.
  (** support set*)
  
  Fixpoint expr_support_set e : gset loc :=
    match e with
    | Val v => val_support_set v
    | Var x => ∅
    | Rec f x e => expr_support_set e
    | App e1 e2 => expr_support_set e1 ∪ expr_support_set e2
    | UnOp op e => expr_support_set e
    | BinOp op e1 e2 => expr_support_set e1 ∪ expr_support_set e2
    | If e0 e1 e2 => expr_support_set e0 ∪ expr_support_set e1 ∪ expr_support_set e2
    | Pair e1 e2 => expr_support_set e1 ∪ expr_support_set e2
    | Fst e => expr_support_set e
    | Snd e => expr_support_set e
    | InjL e => expr_support_set e
    | InjR e => expr_support_set e
    | Case e0 e1 e2 => expr_support_set e0 ∪ expr_support_set e1 ∪ expr_support_set e2
    | AllocN e1 e2 => expr_support_set e1 ∪ expr_support_set e2
    | Load e => expr_support_set e
    | Store e1 e2 => expr_support_set e1 ∪ expr_support_set e2
    | Rand e => expr_support_set e
    | DRand e => expr_support_set e
    | Laplace e0 e1 e2 => expr_support_set e0 ∪ expr_support_set e1 ∪ expr_support_set e2
    | DLaplace e0 e1 e2 => expr_support_set e0 ∪ expr_support_set e1 ∪ expr_support_set e2
    end
  with val_support_set v :=
         match v with
         | LitV l =>
             base_lit_support_set l
         | RecV f x e => expr_support_set e
         | PairV v1 v2 => val_support_set v1 ∪ val_support_set v2
         | InjLV v => val_support_set v
         | InjRV v => val_support_set v
         end.

  Definition ectx_item_support_set K : gset loc :=
    match K with
    | AppLCtx v2 => val_support_set v2
    | AppRCtx e1 => expr_support_set e1
    | UnOpCtx op => ∅
    | BinOpLCtx op v2 => val_support_set v2
    | BinOpRCtx op e1 => expr_support_set e1
    | IfCtx e1 e2 => expr_support_set e1 ∪ expr_support_set e2
    | PairLCtx v2 => val_support_set v2
    | PairRCtx e1 => expr_support_set e1
    | FstCtx => ∅
    | SndCtx => ∅
    | InjLCtx => ∅
    | InjRCtx => ∅
    | CaseCtx e1 e2 => expr_support_set e1 ∪ expr_support_set e2
    | AllocNLCtx v2 => val_support_set v2
    | AllocNRCtx e1 => expr_support_set e1
    | LoadCtx => ∅
    | StoreLCtx v2 => val_support_set v2
    | StoreRCtx e1 => expr_support_set e1
    | RandCtx => ∅
    | DRandCtx => ∅
    | LaplaceNumCtx v2 v3 => val_support_set v2 ∪ val_support_set v3
    | LaplaceDenCtx e1 v3 => expr_support_set e1 ∪ val_support_set v3
    | LaplaceLocCtx e1 e2 => expr_support_set e1 ∪ expr_support_set e2
    | DLaplaceNumCtx v2 v3 => val_support_set v2 ∪ val_support_set v3
    | DLaplaceDenCtx e1 v3 => expr_support_set e1 ∪ val_support_set v3
    | DLaplaceLocCtx e1 e2 => expr_support_set e1 ∪ expr_support_set e2
    end.

  Lemma support_set_fill_item Ki e:
    expr_support_set (fill_item Ki e) = ectx_item_support_set Ki ∪ expr_support_set e.
  Proof.
    destruct Ki; set_solver.
  Qed. 

  Lemma support_set_fill K e:
    expr_support_set (fill K e) =
    (union_list (ectx_item_support_set <$> K)) ∪ expr_support_set e.
  Proof.
    revert e.
    induction K as [|Ki K' IH]; first set_solver.
    intros.
    simpl.
    rewrite IH.
    rewrite support_set_fill_item.
    set_solver.
  Qed.

  Lemma val_support_set_un_op v v' op:
    un_op_eval op v = Some v' ->
    val_support_set v = val_support_set v'.
  Proof.
    rewrite /un_op_eval.
    case_match; try done.
    repeat case_match; try done;
      intros; by simplify_eq.
  Qed.
  
  Lemma val_support_set_bin_op v1 v2 v' op:
    bin_op_eval op v1 v2 = Some v' ->
    val_support_set v1 ∪ val_support_set v2= val_support_set v'.
  Proof.
    rewrite /bin_op_eval.
    case_match; try done.
    case_match; try done.
    subst.
    rewrite bind_Some.
    rewrite /bin_op_eval_bl.
    intros; destruct!/=.
    repeat case_match; try done;
      intros; by simplify_eq.
  Qed.

  Lemma expr_support_set_subst f v e:
    expr_support_set (subst f v e) ⊆ expr_support_set e ∪ val_support_set v.
  Proof.
    induction e; simpl; try case_match; set_solver.
  Qed. 
    
  Lemma expr_support_set_subst' f v e:
    expr_support_set (subst' f v e) ⊆ expr_support_set e ∪ val_support_set v.
  Proof.
    rewrite /subst'.
    case_match; first set_solver.
    subst.
    apply expr_support_set_subst.
  Qed. 
  
(** In lang.v, we defined functions and lemmas for substituing for baselits, 
   now we do it for expressions and values*)
(** We also replace DRands with Rands *)

  Fixpoint urn_subst_expr (f: gmap loc Z) (e : expr) : option expr :=
    match e with
    | Val v => v' ← urn_subst_val f v; Some (Val v') 
| Var x => Some $ Var x
| Rec f' x e => e' ← urn_subst_expr f e; Some (Rec f' x e')
| App e1 e2 => e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some (App e1' e2')
| UnOp op e => e' ← urn_subst_expr f e; Some (UnOp op e')
| BinOp op e1 e2 => e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some (BinOp op e1' e2')
| If e0 e1 e2 => e0' ← urn_subst_expr f e0; e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some (If e0' e1' e2')
| Pair e1 e2 => e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some (Pair e1' e2')
| Fst e => e' ← urn_subst_expr f e; Some (Fst e')
| Snd e => e' ← urn_subst_expr f e; Some (Snd e')
| InjL e => e' ← urn_subst_expr f e; Some (InjL e')
| InjR e => e' ← urn_subst_expr f e; Some (InjR e')
| Case e0 e1 e2 => e0' ← urn_subst_expr f e0; e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some (Case e0' e1' e2')
| AllocN e1 e2 => e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some (AllocN e1' e2')
| Load e => e' ← urn_subst_expr f e; Some (Load e')
| Store e1 e2 => e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some (Store e1' e2')
| Rand e => e' ← urn_subst_expr f e; Some (Rand e')
| DRand e => e' ← urn_subst_expr f e; Some (Rand e')
| Laplace e0 e1 e2 => e0' ← urn_subst_expr f e0; e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some (Laplace e0' e1' e2')
| DLaplace e0 e1 e2 => e0' ← urn_subst_expr f e0; e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some (Laplace e0' e1' e2')
  end
  with urn_subst_val f v : option val :=
         match v with
         | LitV l => l' ← urn_subst f l; Some $ LitV l'
| RecV f' x e => e' ← urn_subst_expr f e; Some $ RecV f' x e'
| PairV v1 v2 => v1' ← urn_subst_val f v1; v2' ← urn_subst_val f v2; Some $ PairV v1' v2'
| InjLV v =>  v' ← urn_subst_val f v; Some $ InjLV v'
| InjRV v => v' ← urn_subst_val f v; Some $ InjRV v'
  end
  .

  
  Fixpoint is_simple_expr (e : expr) : bool :=
    match e with
    | Val v => is_simple_val v
    | Var x => true
    | Rec f x e => is_simple_expr e
    | App e1 e2 => is_simple_expr e1 && is_simple_expr e2
    | UnOp op e => is_simple_expr e
    | BinOp op e1 e2 => is_simple_expr e1 && is_simple_expr e2
    | If e0 e1 e2 => is_simple_expr e0 && is_simple_expr e1 && is_simple_expr e2
    | Pair e1 e2 => is_simple_expr e1 && is_simple_expr e2
    | Fst e => is_simple_expr e
    | Snd e => is_simple_expr e
    | InjL e => is_simple_expr e
    | InjR e => is_simple_expr e
    | Case e0 e1 e2 => is_simple_expr e0 && is_simple_expr e1 && is_simple_expr e2
    | AllocN e1 e2 => is_simple_expr e1 && is_simple_expr e2
    | Load e => is_simple_expr e
    | Store e1 e2 => is_simple_expr e1 && is_simple_expr e2
    | Rand e => is_simple_expr e
    | DRand e => false
    | Laplace e1 e2 e3 => is_simple_expr e1 && is_simple_expr e2 && is_simple_expr e3
    | DLaplace e1 e2 e3 => false
    end
  with is_simple_val v : bool :=
         match v with
         | LitV l => is_simple_base_lit l
         | RecV f x e => is_simple_expr e
         | PairV v1 v2 => is_simple_val v1 && is_simple_val v2
         | InjLV v => is_simple_val v
         | InjRV v => is_simple_val v
         end
  .

  Definition urn_subst_ectx_item (f:gmap loc Z) K : option ectx_item :=
    match K with
    | AppLCtx v2 => v2' ← urn_subst_val f v2; Some $ AppLCtx v2'
    | AppRCtx e1 => e1' ← urn_subst_expr f e1; Some $ AppRCtx e1'
    | UnOpCtx op => Some $ UnOpCtx op
    | BinOpLCtx op v2 => v2' ← urn_subst_val f v2; Some $ BinOpLCtx op v2'
    | BinOpRCtx op e1 => e1' ← urn_subst_expr f e1; Some $ BinOpRCtx op e1'
    | IfCtx e1 e2 => e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some $ IfCtx e1' e2'
    | PairLCtx v2 => v2' ← urn_subst_val f v2; Some $ PairLCtx v2'
    | PairRCtx e1 => e1' ← urn_subst_expr f e1; Some $ PairRCtx e1'
    | FstCtx => Some FstCtx
    | SndCtx => Some SndCtx
    | InjLCtx => Some InjLCtx
    | InjRCtx => Some InjRCtx
    | CaseCtx e1 e2 => e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some $ CaseCtx e1' e2'
    | AllocNLCtx v2 => v2' ← urn_subst_val f v2; Some $ AllocNLCtx v2'
    | AllocNRCtx e1 => e1' ← urn_subst_expr f e1; Some $ AllocNRCtx e1'
    | LoadCtx => Some LoadCtx
    | StoreLCtx v2 => v2' ← urn_subst_val f v2; Some $ StoreLCtx v2'
    | StoreRCtx e1 => e1' ← urn_subst_expr f e1; Some $ StoreRCtx e1'
    | RandCtx => Some RandCtx
    | DRandCtx => Some RandCtx
    | LaplaceNumCtx v2 v3 => v2' ← urn_subst_val f v2; v3' ← urn_subst_val f v3; Some $ LaplaceNumCtx v2' v3'
    | LaplaceDenCtx e1 v3 => e1' ← urn_subst_expr f e1; v3' ← urn_subst_val f v3; Some $ LaplaceDenCtx e1' v3'
    | LaplaceLocCtx e1 e2 => e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some $ LaplaceLocCtx e1' e2'
    | DLaplaceNumCtx v2 v3 => v2' ← urn_subst_val f v2; v3' ← urn_subst_val f v3; Some $ LaplaceNumCtx v2' v3'
    | DLaplaceDenCtx e1 v3 => e1' ← urn_subst_expr f e1; v3' ← urn_subst_val f v3; Some $ LaplaceDenCtx e1' v3'
    | DLaplaceLocCtx e1 e2 => e1' ← urn_subst_expr f e1; e2' ← urn_subst_expr f e2; Some $ LaplaceLocCtx e1' e2'
  end.

  Lemma urn_subst_expr_is_simple f e e':
    urn_subst_expr f e = Some e' -> is_simple_expr e' = true.
  Proof.
    revert e e'.
    apply (expr_mut (λ e, ∀ e', urn_subst_expr f e = Some e' → is_simple_expr e' = true)
             (λ v, ∀ v', urn_subst_val f v = Some v' -> is_simple_val v' = true)); pose proof urn_subst_is_simple.
    all: simpl; repeat setoid_rewrite bind_Some; intros; destruct!/=; simpl in *; repeat rewrite andb_true_iff; repeat split; naive_solver.
  Qed.
  
  Lemma urn_subst_val_is_simple f v v':
    urn_subst_val f v = Some v' -> is_simple_val v' = true.
  Proof.
    revert v v'.
    fix FIX 1.
    intros []; simpl; repeat setoid_rewrite bind_Some; intros; destruct!/=; simpl.
    - by eapply urn_subst_is_simple.
    - by eapply urn_subst_expr_is_simple.
    - repeat erewrite FIX; naive_solver.
    - erewrite FIX; naive_solver.
    - erewrite FIX; naive_solver.
  Qed.
  
  Lemma base_lit_support_set_not_support bl f:
    base_lit_support_set bl ⊈ dom f → urn_subst f bl = None.
  Proof.
    induction bl; simpl; repeat setoid_rewrite bind_None.
    1, 2, 3, 4: set_solver.
    1:  intros; left; apply not_elem_of_dom_1; set_solver.
    1, 2: naive_solver.
    all: rewrite union_subseteq;
      intros ?%not_and_or_not;
      destruct!/=; repeat setoid_rewrite bind_None; first naive_solver;
      destruct (urn_subst _ _); naive_solver.
  Qed. 
  
  Lemma expr_support_set_not_support e f:
    ¬ (expr_support_set e ⊆ dom f)-> urn_subst_expr f e = None.
  Proof.
    revert e.
    apply (expr_mut (λ e, ¬ (expr_support_set e ⊆ dom f)-> urn_subst_expr f e = None)
             (λ v, ¬ (val_support_set v ⊆ dom f)-> urn_subst_val f v = None)).
    all: simpl; repeat setoid_rewrite bind_None.
    1: naive_solver.
    1: set_solver.
    1, 3, 7, 8, 9, 10, 13, 15, 16: naive_solver.
    1, 4, 6, 7:  setoid_rewrite union_subseteq;
         intros ???? ?%not_and_or_not;
         destruct (urn_subst_expr _ _); last naive_solver;
         destruct!/=; first naive_solver;
             right; naive_solver.
    1: setoid_rewrite union_subseteq;
         intros ????? ?%not_and_or_not;
         destruct (urn_subst_expr _ _); last naive_solver;
         destruct!/=; first naive_solver;
    right; naive_solver.
    1:{ repeat setoid_rewrite union_subseteq.
        intros ?????? H.
        apply not_and_or_not in H.
        destruct!/=; last first.
        - destruct (urn_subst_expr _ _); last naive_solver.
          right.
          eexists _; split; first done.
          destruct (urn_subst_expr _ _); last naive_solver.
          right.
          naive_solver.
        - apply not_and_or_not in H.
         destruct (urn_subst_expr _ _); last naive_solver;
           destruct!/=; first naive_solver.
         right. naive_solver.
    } 
    1:{ repeat setoid_rewrite union_subseteq.
        intros ?????? H.
        apply not_and_or_not in H.
        destruct!/=; last first.
        - destruct (urn_subst_expr _ _); last naive_solver.
          right.
          eexists _; split; first done.
          destruct (urn_subst_expr _ _); last naive_solver.
          right.
          naive_solver.
        - apply not_and_or_not in H.
         destruct (urn_subst_expr _ _); last naive_solver;
           destruct!/=; first naive_solver.
         right. naive_solver.
    }
    1:{ repeat setoid_rewrite union_subseteq.
        intros ?????? H.
        apply not_and_or_not in H.
        destruct!/=; last first.
        - destruct (urn_subst_expr _ _); last naive_solver.
          right.
          eexists _; split; first done.
          destruct (urn_subst_expr _ _); last naive_solver.
          right.
          naive_solver.
        - apply not_and_or_not in H.
         destruct (urn_subst_expr _ _); last naive_solver;
           destruct!/=; first naive_solver.
         right. naive_solver.
    }
    1:{ repeat setoid_rewrite union_subseteq.
        intros ?????? H.
        apply not_and_or_not in H.
        destruct!/=; last first.
        - destruct (urn_subst_expr _ _); last naive_solver.
          right.
          eexists _; split; first done.
          destruct (urn_subst_expr _ _); last naive_solver.
          right.
          naive_solver.
        - apply not_and_or_not in H.
         destruct (urn_subst_expr _ _); last naive_solver;
           destruct!/=; first naive_solver.
         right. naive_solver.
    }
    - intros. left. by apply base_lit_support_set_not_support.
    - intros. naive_solver.
    - setoid_rewrite union_subseteq;
         intros ???? ?%not_and_or_not;
         destruct (urn_subst_val _ _); last naive_solver;
         destruct!/=; first naive_solver;
        right; naive_solver.
    - naive_solver.
    - naive_solver.
  Qed.
  
  Lemma val_support_set_not_support v f:
    ¬ (val_support_set v ⊆ dom f)-> urn_subst_val f v = None.
  Proof.
    revert v.
    fix FIX 1.
    intros []; simpl.
    - rewrite bind_None; left.
      by apply base_lit_support_set_not_support.
    - rewrite bind_None; left.
      by apply expr_support_set_not_support.
    - rewrite union_subseteq.
      intros ?%not_and_or_not.
      destruct!/=; repeat setoid_rewrite bind_None.
      + naive_solver.
      + destruct (urn_subst_val _ _); last naive_solver.
        naive_solver.
    - rewrite bind_None. naive_solver.
    - rewrite bind_None. naive_solver.
  Qed. 

  Lemma urn_subst_expr_not_val e f e':
    to_val e = None -> urn_subst_expr f e = Some e' -> to_val e' = None.
  Proof.
    destruct e; simpl; repeat setoid_rewrite bind_Some; intros; by destruct!/=.
  Qed.
  
  Definition urn_subst_heap f (h:gmap loc val): option (gmap loc val) :=
    list_to_map <$> (mapM (λ '(k, v), v' ← urn_subst_val f v; Some (k, v'))
                       (map_to_list h)).

  Lemma heap_support_set_not_support f h:
    ¬ (map_Forall (λ _ v, val_support_set v ⊆ dom f) h) -> urn_subst_heap f h = None.
  Proof.
    intros H%map_not_Forall; last apply _.
    destruct H as (i&x&Hsome &H).
    rewrite /urn_subst_heap.
    rewrite fmap_None.
    apply mapM_None_2.
    rewrite Exists_exists.
    eexists (_,_).
    split; first by rewrite elem_of_map_to_list.
    rewrite bind_None.
    left.
    by apply val_support_set_not_support.
  Qed.

  Lemma urn_subst_expr_fill_item f Ki e:
    urn_subst_expr f (fill_item Ki e) =
    Ki' ← urn_subst_ectx_item f Ki;
  e' ← urn_subst_expr f e;
  Some $ fill_item Ki' e'.
  Proof.
    destruct Ki; simpl; try done;
      repeat (done||intros; simpl||apply option_bind_ext_fun||rewrite !option_bind_assoc||rewrite option_bind_comm).
  Qed.
  
  Lemma urn_subst_expr_fill f (K : list _) e:
    urn_subst_expr f (fill K e) =
    K' ← mapM (urn_subst_ectx_item f) K;
  e' ← urn_subst_expr f e;
  Some $ fill K' e'.
  Proof.
    revert e.
    induction K as [|Ki K' IH]; simpl; first (intros; by rewrite bind_with_Some).
    intros e.
    rewrite IH.
    rewrite urn_subst_expr_fill_item.
    rewrite option_bind_comm.
    rewrite !option_bind_assoc.
    apply option_bind_ext_fun.
    intros.
    simpl.
    rewrite option_bind_comm !option_bind_assoc.
    apply option_bind_ext_fun; intros; simpl.
    by rewrite option_bind_assoc.
  Qed. 

  (** * Well constructed expressions and values *)
Fixpoint is_well_constructed_expr e:=
  match e with
  | Val v => is_well_constructed_val v
  | Var x => true 
  | Rec f x e => is_well_constructed_expr e
  | App e1 e2 => is_well_constructed_expr e1 && is_well_constructed_expr e2
  | UnOp op e => is_well_constructed_expr e
  | BinOp op e1 e2 => is_well_constructed_expr e1 && is_well_constructed_expr e2
  | If e0 e1 e2 => is_well_constructed_expr e0 && is_well_constructed_expr e1 && is_well_constructed_expr e2
  | Pair e1 e2 => is_well_constructed_expr e1 && is_well_constructed_expr e2
  | Fst e => is_well_constructed_expr e
  | Snd e => is_well_constructed_expr e
  | InjL e => is_well_constructed_expr e
  | InjR e => is_well_constructed_expr e
  | Case e0 e1 e2 => is_well_constructed_expr e0 && is_well_constructed_expr e1 && is_well_constructed_expr e2
  | AllocN e1 e2 => is_well_constructed_expr e1 && is_well_constructed_expr e2
  | Load e => is_well_constructed_expr e
  | Store e1 e2 => is_well_constructed_expr e1 && is_well_constructed_expr e2
  | Rand e => is_well_constructed_expr e
  | DRand e => is_well_constructed_expr e
  | Laplace e0 e1 e2 => is_well_constructed_expr e0 && is_well_constructed_expr e1 && is_well_constructed_expr e2
  | DLaplace e0 e1 e2 => is_well_constructed_expr e0 && is_well_constructed_expr e1 && is_well_constructed_expr e2
  end
with is_well_constructed_val v :=
  match v with
  | LitV l => match base_lit_type_check l with | Some _ => true | _ => false end
  | RecV f x e => is_well_constructed_expr e
  | PairV v1 v2 => is_well_constructed_val v1 && is_well_constructed_val v2
  | InjLV v => is_well_constructed_val v
  | InjRV v => is_well_constructed_val v
  end
.

Definition is_well_constructed_ectx_item K :=
  match K with
  | AppLCtx v2 => is_well_constructed_val v2
  | AppRCtx e1 => is_well_constructed_expr e1
  | UnOpCtx op => true
  | BinOpLCtx op v2 => is_well_constructed_val v2
  | BinOpRCtx op e1 => is_well_constructed_expr e1
  | IfCtx e1 e2 => is_well_constructed_expr e1 && is_well_constructed_expr e2
  | PairLCtx v2 => is_well_constructed_val v2
  | PairRCtx e1 => is_well_constructed_expr e1
  | FstCtx => true
  | SndCtx => true
  | InjLCtx => true
  | InjRCtx => true
  | CaseCtx e1 e2 => is_well_constructed_expr e1 && is_well_constructed_expr e2
  | AllocNLCtx v2 => is_well_constructed_val v2
  | AllocNRCtx e1 => is_well_constructed_expr e1
  | LoadCtx => true
  | StoreLCtx v2 => is_well_constructed_val v2
  | StoreRCtx e1 => is_well_constructed_expr e1
  | RandCtx => true
  | DRandCtx => true
  | LaplaceNumCtx v2 v3 => is_well_constructed_val v2 && is_well_constructed_val v3
  | LaplaceDenCtx e1 v3 => is_well_constructed_expr e1 && is_well_constructed_val v3
  | LaplaceLocCtx e1 e2 => is_well_constructed_expr e1 && is_well_constructed_expr e2
  | DLaplaceNumCtx v2 v3 => is_well_constructed_val v2 && is_well_constructed_val v3
  | DLaplaceDenCtx e1 v3 => is_well_constructed_expr e1 && is_well_constructed_val v3
  | DLaplaceLocCtx e1 e2 => is_well_constructed_expr e1 && is_well_constructed_expr e2
  end.

Lemma is_well_constructed_expr_false e f:
  is_well_constructed_expr e = false -> urn_subst_expr f e = None.
Proof.
  revert e.
  apply (expr_mut (λ e, is_well_constructed_expr e = false -> urn_subst_expr f e = None) (λ v, is_well_constructed_val v = false -> urn_subst_val f v = None)); simpl; repeat setoid_rewrite bind_None; repeat setoid_rewrite andb_false_iff.
  1, 2, 3, 5, 9, 10, 11, 12, 15, 17, 18, 22, 24, 25: naive_solver.
  1, 2, 4, 6, 7: intros; destruct!/=; first naive_solver;
              destruct (urn_subst_expr _ _); naive_solver.
  1, 2, 3, 4: intros; destruct!/=; first naive_solver;
     first (destruct (urn_subst_expr _ _); naive_solver);
     destruct (urn_subst_expr _ _); last naive_solver; right; eexists _; split; first done;
     destruct (urn_subst_expr _ _); naive_solver.
  1:{ intros. case_match; simplify_eq. left. by apply base_lit_type_check_None. }
  intros; destruct!/=; first naive_solver.
  destruct (urn_subst_val _ _); naive_solver.
Qed.

Lemma is_well_constructed_val_false v f:
  is_well_constructed_val v = false -> urn_subst_val f v = None.
Proof.
  induction v; simpl; repeat setoid_rewrite bind_None.
  - case_match; first done.
    intros. 
    left.
    by apply base_lit_type_check_None.
  - intros.
    left.
    by apply is_well_constructed_expr_false.
  - rewrite andb_false_iff.
    intros.
    destruct!/=; first naive_solver.
    destruct (urn_subst_val _ _); naive_solver.
  - naive_solver.
  - naive_solver.
Qed. 

  Lemma heap_not_well_constructed f h:
    ¬ (map_Forall (λ _ v, is_well_constructed_val v = true) h) -> urn_subst_heap f h = None.
  Proof.
    intros H%map_not_Forall; last apply _.
    destruct H as (i&x&Hsome &H%not_true_is_false).
    rewrite /urn_subst_heap.
    rewrite fmap_None.
    apply mapM_None_2.
    rewrite Exists_exists.
    eexists (_,_).
    split; first by rewrite elem_of_map_to_list.
    rewrite bind_None.
    left.
    by apply is_well_constructed_val_false.
  Qed.

  Lemma is_well_constructed_fill_item Ki e:
    is_well_constructed_expr (fill_item Ki e) =
    is_well_constructed_expr e && is_well_constructed_ectx_item Ki.
  Proof.
    destruct Ki; simpl; btauto.
  Qed. 
  
  Lemma is_well_constructed_fill K e:
    is_well_constructed_expr (fill K e) =
    is_well_constructed_expr e && forallb (λ Ki, is_well_constructed_ectx_item Ki) K.
  Proof.
    revert e.
    induction K as [|Ki K' IH].
    { intros. by rewrite andb_true_r. }
    simpl.
    intros.
    rewrite IH.
    rewrite andb_assoc.
    f_equal.
    by rewrite is_well_constructed_fill_item.
  Qed.
  
  Lemma is_well_constructed_un_op_eval op v v':
    un_op_eval op v = Some v' ->
    is_well_constructed_val v = true ->
    is_well_constructed_val v' = true.
  Proof.
    intros H1 H2.
    rewrite /un_op_eval in H1.
    by repeat (case_match; simplify_eq; simpl in *; simpl).
  Qed. 

  Lemma is_well_constructed_bin_op_eval op v1 v2 v':
    bin_op_eval op v1 v2 = Some v' ->
    is_well_constructed_val v1 = true ->
    is_well_constructed_val v2 = true ->
    is_well_constructed_val v' = true.
  Proof.
    intros H1 H2 H3.
    rewrite /bin_op_eval in H1.
    repeat (case_match; simplify_eq; simpl in *; simpl).
    rewrite bind_Some in H1.
    rewrite /bin_op_eval_bl in H1.
    destruct!/=.
    by repeat (case_match; simplify_eq; simpl in *; simpl).
  Qed.

  Lemma is_well_constructed_subst f e v:
    is_well_constructed_expr e = true->
    is_well_constructed_val v = true->
    is_well_constructed_expr (subst f v e) = true.
  Proof.
    intros H1 H2.
    revert H1.
    induction e; simpl; andb_solver; intros; destruct!/=; try case_match; naive_solver.
  Qed. 
  
  Lemma is_well_constructed_subst' f e v:
    is_well_constructed_expr e = true->
    is_well_constructed_val v = true->
    is_well_constructed_expr (subst' f v e) = true.
  Proof.
    rewrite /subst'.
    case_match; first done.
    eapply is_well_constructed_subst.
  Qed. 

  Local Ltac smash :=
  repeat
    match goal with
    | H : _ ∪ _ ⊆ _ |- _ => rewrite union_subseteq in H; destruct H
    end.
  
  Lemma urn_subst_base_lit_exists bl f b:
    base_lit_type_check bl = Some b ->
    base_lit_support_set bl ⊆ dom f ->
    (∃ bl', urn_subst f bl = Some bl').
  Proof.
    revert b.
    induction bl as [| | | | |bl IH|bl IH |bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2|bl1 IH1 bl2 IH2]; simpl; repeat setoid_rewrite bind_Some; intros; repeat (destruct!/= || case_match); simplify_eq.
    1,2,3,4: naive_solver.
    1:{ rename select (_⊆_) into H. rewrite singleton_subseteq_l elem_of_dom in H.
      destruct H.
      naive_solver. }
    1, 2: eassert (∃ bl' : base_lit, urn_subst f _ = Some bl') as [x H]; first naive_solver;
      apply urn_subst_well_typed in H as H';
      apply urn_subst_is_simple in H as H'';
      destruct!/=;
      destruct x; simplify_eq;
      naive_solver.
    all: smash;
      eassert (∃ bl' : base_lit, urn_subst f bl1 = Some bl') as [x1 K1]; first naive_solver;
      eassert (∃ bl' : base_lit, urn_subst f bl2 = Some bl') as [x2 K2]; first naive_solver;
      apply urn_subst_well_typed in K1 as K1';
      apply urn_subst_is_simple in K1 as K1'';
      apply urn_subst_well_typed in K2 as K2';
      apply urn_subst_is_simple in K2 as K2''; destruct!/=; destruct x1, x2; simplify_eq; naive_solver.
  Qed. 
  
  Lemma urn_subst_expr_exists e f:
    is_well_constructed_expr e = true ->
    expr_support_set e ⊆ dom f ->
    (∃ e', urn_subst_expr f e = Some e').
  Proof.
    revert e.
    apply (expr_mut (λ e, 
    is_well_constructed_expr e = true ->
    expr_support_set e ⊆ dom f ->
    (∃ e', urn_subst_expr f e = Some e')) (λ v, 
    is_well_constructed_val v = true ->
    val_support_set v ⊆ dom f ->
    (∃ v', urn_subst_expr f v = Some v'))); simpl; repeat setoid_rewrite bind_Some; intros; andb_solver; smash.
    21: { repeat case_match; simplify_eq.
      rename select (base_lit_type_check _ = _) into H.
      eapply urn_subst_base_lit_exists in H; last done.
      destruct!/=. naive_solver. }
    all: naive_solver.
  Qed. 

  Local Ltac bind_solver :=
  repeat
    match goal with
    | H : _ ≫= _ = Some _ |- _ => rewrite bind_Some in H; destruct H as [?[]]; simplify_eq
    end.
  
  Lemma urn_subst_val_exists v f:
    is_well_constructed_val v = true ->
    val_support_set v ⊆ dom f ->
    (∃ v', urn_subst_val f v = Some v').
  Proof.
    induction v as [| |v1 ? v2 |v|v]; simpl; repeat setoid_rewrite bind_Some; intros; smash; andb_solver.
    - repeat case_match; simplify_eq.
      rename select (base_lit_type_check _ = _) into H.
      eapply urn_subst_base_lit_exists in H; last done.
      destruct!/=. naive_solver.
    - unshelve epose proof urn_subst_expr_exists _ _ _ _; [| |done|done|].
      destruct!/=.
      naive_solver.
    - eassert (∃ v' , urn_subst_val f v1 = Some v') as [v1' K1]; first naive_solver.
      eassert (∃ v' , urn_subst_val f v2 = Some v') as [v2' K2]; first naive_solver.
      simpl in *.
      bind_solver. naive_solver.
    - eassert (∃ v' , urn_subst_val f v = Some v') as [v' K]; first naive_solver.
      simpl in *.
      bind_solver. naive_solver.
    - eassert (∃ v' , urn_subst_val f v = Some v') as [v' K]; first naive_solver.
      simpl in *.
      bind_solver. naive_solver.
  Qed.
  
  Lemma urn_subst_ectx_item_exists Ki f:
    is_well_constructed_ectx_item Ki = true ->
    ectx_item_support_set Ki ⊆ dom f ->
    (∃ Ki', urn_subst_ectx_item f Ki = Some Ki').
  Proof.
    destruct Ki; simpl; repeat setoid_rewrite bind_Some.
    all: try (intros H1 H2;
      eapply urn_subst_val_exists in H1; last done; destruct!/=;
                                                      bind_solver; naive_solver).
    all: try (intros H1 H2;
      eapply urn_subst_expr_exists in H1; last done; destruct!/=;
                                                       bind_solver; naive_solver).
    all: try (intros H1 H2;
        smash;
              rewrite andb_true_iff in H1; destruct H1 as [K1 K2];
              (eapply urn_subst_val_exists in K1||eapply urn_subst_expr_exists in K1);
              (eapply urn_subst_val_exists in K2||eapply urn_subst_expr_exists in K2); last done; destruct!/=;
                                                                                                   bind_solver; naive_solver).
    all: naive_solver.
  Qed.
  
  Lemma urn_subst_heap_exists m f:
  map_Forall (λ _ v, is_well_constructed_val v = true) m ->
  map_Forall (λ _ v, val_support_set v ⊆ dom f) m ->
  (∃ m', urn_subst_heap f m = Some m').
  Proof.
    intros H1 H2.
    destruct (urn_subst_heap f m) eqn :H; first naive_solver.
    exfalso.
    rewrite /urn_subst_heap in H.
    setoid_rewrite fmap_None in H.
    setoid_rewrite mapM_None in H.
    revert H.
    apply Forall_Exists_neg.
    rewrite Forall_forall.
    intros [??].
    rewrite elem_of_map_to_list.
    intros ?.
    destruct (mbind _ _) eqn:H'; first done.
    rewrite bind_None in H'.
    destruct!/=.
    eapply map_Forall_lookup_1 in H1; last done.
    eapply (map_Forall_lookup_1 (λ (_ : loc) (v : val), val_support_set v ⊆ dom f)) in H2; last done.
    eapply urn_subst_val_exists in H1; last done.
    destruct!/=.
  Qed.

  Lemma urn_subst_subset f f' bl bl':
    f ⊆  f'->
    urn_subst f bl = Some bl' ->
    urn_subst f' bl = Some bl'.
  Proof.
    intros H.
    revert bl'.
    induction bl; simpl; repeat setoid_rewrite bind_Some; intros; destruct!/=.
    5:{ eexists _; split; last done.
        by eapply lookup_weaken. }
    all: naive_solver.
  Qed. 

  Lemma urn_subst_expr_subset f f' e e':
    f ⊆  f'->
    urn_subst_expr f e = Some e' ->
    urn_subst_expr f' e = Some e'.
  Proof.
    intros H.
    revert e e'.
    eapply (expr_mut (λ e, ∀ e', 
    urn_subst_expr f e = Some e' ->
    urn_subst_expr f' e = Some e') (λ v, ∀ v', urn_subst_val f v = Some v' ->
                                                urn_subst_val f' v = Some v')); simpl; repeat setoid_rewrite bind_Some; intros; destruct!/=.
    21:{ eapply urn_subst_subset in H; last done.
         naive_solver. }
    all: naive_solver.
  Qed. 
  
  Lemma urn_subst_val_subset f f' v v':
    f ⊆  f'->
    urn_subst_val f v = Some v' ->
    urn_subst_val f' v = Some v'.
  Proof.
    intros H.
    revert v v'.
    induction v; simpl; repeat setoid_rewrite bind_Some; simpl; intros; destruct!/=.
    - eapply urn_subst_subset in H; last done.
      naive_solver.
    - eapply urn_subst_expr_subset in H; last done.
      naive_solver.
    - naive_solver.
    - naive_solver.
    - naive_solver.
  Qed. 
    
  Lemma urn_subst_ectx_item_subset f f' Ki Ki':
    f ⊆ f'->
    urn_subst_ectx_item f Ki = Some Ki' ->
    urn_subst_ectx_item f' Ki = Some Ki'.
  Proof.
    pose proof urn_subst_val_subset.
    pose proof urn_subst_expr_subset.
    intros H1.
    destruct Ki; simpl; repeat setoid_rewrite bind_Some; intros; destruct!/=.
    all: naive_solver.
  Qed. 
    
  Lemma urn_subst_ectx_subset f f' K K':
    f ⊆ f'->
    mapM (urn_subst_ectx_item f) K = Some K' ->
    mapM (urn_subst_ectx_item f') K = Some K'.
  Proof.
    intros H.
    revert K'.
    induction K; simpl; first (cbv; naive_solver).
    repeat setoid_rewrite bind_Some.
    intros. destruct!/=.
    rename select (mret _ = _) into Heq. cbv in Heq. simplify_eq.
    eapply urn_subst_ectx_item_subset in H as H'; last done.
    eexists _; split; first done.
    naive_solver.
  Qed. 
  
  Lemma urn_subst_expr_subst x v v' e e' f:
    urn_subst_expr f e = Some e'->
    urn_subst_val f v = Some v' ->
    urn_subst_expr f (subst x v e) =
    Some (subst x v' e').
  Proof.
    revert v v' e'.
    induction e; simpl; intros; bind_solver; repeat (setoid_rewrite bind_Some || case_match||simplify_eq||simpl); naive_solver.
  Qed. 
    
  Lemma urn_subst_expr_subst' x v v' e e' f:
    urn_subst_expr f e = Some e'->
    urn_subst_val f v = Some v' ->
    urn_subst_expr f (subst' x v e) =
    Some (subst' x v' e').
  Proof.
    destruct x; simpl; first naive_solver.
    apply urn_subst_expr_subst.
  Qed.

  Local Ltac match_solver :=
  repeat
    match goal with
    | H : match _ with _ => _  end = Some _  |- _ => case_match; simplify_eq
    end.

  Lemma urn_subst_val_un_op op f v v' v'':
    un_op_eval op v = Some v' ->
    urn_subst_val f v = Some v'' ->
    ∃ v_final, urn_subst_val f v' = Some v_final /\ un_op_eval op v'' = Some v_final.
  Proof.
    rewrite {1}/un_op_eval; intros; match_solver;destruct!/=; repeat setoid_rewrite bind_Some; match_solver; bind_solver; match_solver; simpl; naive_solver.
  Qed.

  Local Ltac bin_op_smash:= intros K1 K2 K3; rewrite !bind_Some in K2 K3;
      destruct K2 as [x1[K2 ?]]; destruct K3 as [x2[K3 ?]]; simplify_eq;
        apply urn_subst_well_typed in K2 as K2';
        destruct K2' as [? [? Hrewrite1]];
        apply urn_subst_well_typed in K3 as K3';
        destruct K3' as [? [? Hrewrite2]]; simplify_eq;
        rewrite Hrewrite1 Hrewrite2;
      apply urn_subst_is_simple in K2 as K2'';
        apply urn_subst_is_simple in K3 as K3'';
        destruct x1, x2; simplify_eq;
                     setoid_rewrite bind_Some;
                     eexists _; split;  [|naive_solver];
                     apply bind_Some in K1 as [? [? ?]]; simplify_eq;
    bind_solver; match_solver;
    simpl in *; simplify_eq; try rewrite K2; try rewrite K3; done.
  
  Lemma urn_subst_val_bin_op op f v1 v2 v v1' v2':
    bin_op_eval op v1 v2 = Some v ->
    urn_subst_val f v1 = Some v1' ->
    urn_subst_val f v2 = Some v2' ->
    ∃ v', urn_subst_val f v = Some v' /\ bin_op_eval op v1' v2' = Some v'.
  Proof.
    rewrite /bin_op_eval/bin_op_eval_bl.
    destruct v1 as [l1| | | |]; 
      destruct v2 as [l2| | | |]; simpl; [|done..].
    destruct (base_lit_type_check l1) as [b1|] eqn:H1; 
      destruct (base_lit_type_check l2) as [b2|] eqn:H2; [|repeat (done||case_match)..].
    destruct op, b1, b2; simplify_eq; try done.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
    - bin_op_smash.
  Qed.

  Lemma urn_subst_heap_nodup (l:list (loc * _)) l' f:
    NoDup l.*1 -> 
    (mapM (λ '(k, v), urn_subst_val f v ≫= λ v' : val, Some (k, v')) l) = Some l' ->
    NoDup l'.*1.
  Proof.
    revert l'.
    induction l; simpl.
    - cbv. intros. by simplify_eq.
    - intros ?. rewrite NoDup_cons.
      intros [].
      case_match. simplify_eq.
      rewrite bind_Some.
      intros [[][H1 H2]].
      rewrite !bind_Some in H1 H2.
      destruct!/=.
      unfold mret, option_ret in *. simplify_eq.
      simpl.
      rewrite NoDup_cons.
      split; last eapply IHl; try done.
      rename select (mapM _ _ = _) into H'.
      rewrite mapM_Some in H'.
      assert (Forall2
                (λ x y, x=y) l.*1 x.*1) as Hforall.
      + apply Forall2_fmap.
        eapply Forall2_impl; first done.
        simpl. intros [][]. rewrite bind_Some.
        intros. by destruct!/=.
      + apply list_eq_Forall2 in Hforall.
        by rewrite Hforall in H.
  Qed. 

  Lemma urn_subst_heap_permutate_lemma (l1:list (loc * _)) l2 l1' l2' f:
    l1≡ₚ l2->
    mapM (λ '(k, v), urn_subst_val f v ≫= λ v' : val, Some (k, v')) l1 = Some l1' ->
    mapM (λ '(k, v), urn_subst_val f v ≫= λ v' : val, Some (k, v')) l2 = Some l2' ->
    l1'≡ₚ l2'.
  Proof.
    intros H.
    revert l1' l2'.
    induction H.
    - simpl. cbv.
      intros. by simplify_eq.
    - simpl.
      intros l1' l2'.
      case_match.
      rewrite !bind_Some.
      subst.
      intros [[][H1 H2]][[][H3 H4]].
      rewrite !bind_Some in H1 H2 H3 H4.
      destruct H1 as [?[H1 ?]].
      destruct H2 as [?[H2 H2']].
      destruct H3 as [?[H3 ?]].
      destruct H4 as [?[H4 H4']].
      cbv in H2'.
      cbv in H4'.
      simplify_eq.
      apply Permutation_skip.
      by eapply IHPermutation.
    - intros l1' l2'.
      simpl.
      case_match; subst.
      case_match; subst.
      repeat setoid_rewrite bind_Some.
      intros. destruct!/=.
      repeat (rename select (mret _ = Some _) into H'; cbv in H'; simplify_eq).
      apply Permutation_swap.
    - intros l1' l2' H1 H2.
      assert (∃ l1', mapM (λ '(k, v), urn_subst_val f v ≫= λ v' : val, Some (k, v')) l' = Some l1') as []; last first.
      + etrans; first eapply IHPermutation1; try done.
        by eapply IHPermutation2.
      + apply mapM_is_Some_2.
        rewrite Forall_forall.
        intros [] Hin.
        simpl.
        rewrite /is_Some.
        setoid_rewrite bind_Some. subst.
        rewrite elem_of_Permutation in Hin.
        setoid_rewrite <-H in Hin.
        rewrite -elem_of_Permutation in Hin.
        rewrite mapM_Some in H1.
        rewrite elem_of_list_lookup in Hin.
        destruct!/=.
        eapply Forall2_lookup_l in H1; last done.
        destruct H1 as [[][? H1]].
        rewrite bind_Some in H1.
        destruct!/=.
        naive_solver.
  Qed. 
                                                                             
  Lemma urn_subst_heap_permutate f (l: list (loc * val)) l':
    NoDup l.*1->
    l≡ₚ l'->
    ((list_to_map <$> mapM (λ '(k, v), urn_subst_val f v ≫= λ v' : val, Some (k, v')) l):option (gmap loc val)) =
    ((list_to_map <$> mapM (λ '(k, v), urn_subst_val f v ≫= λ v' : val, Some (k, v')) l')).
  Proof.
    simpl.
    intros Hnodup H.
    destruct (list_to_map<$>_) eqn:Heqn; last first.
    { symmetry.
      rewrite !fmap_None !mapM_None !Exists_exists in Heqn *.
      destruct Heqn as [?[H0]].
      destruct!/=.
      eexists (_,_); split; last done.
      rewrite elem_of_Permutation.
      setoid_rewrite <-H.
      by rewrite elem_of_Permutation in H0.
    }
    symmetry.
    rewrite /fmap/option_fmap/option_map in Heqn *.
    destruct (mapM _ _) as [l0|] eqn:Heqn1; simplify_eq.
    destruct (mapM _ l') as [l1|] eqn:Heqn2; simplify_eq.
    - f_equal.
      symmetry.
      apply list_to_map_proper.
      + by eapply urn_subst_heap_nodup. 
      + eapply urn_subst_heap_permutate_lemma; last first; done.
    - rewrite mapM_Some in Heqn1.
      rewrite mapM_None in Heqn2.
      exfalso.
      rewrite Exists_exists in Heqn2.
      destruct Heqn2 as [[l1 v][H1 H2]].
      rewrite bind_None in H2.
      destruct!/=.
      rewrite elem_of_Permutation in H1.
      setoid_rewrite <-H in H1.
      rewrite -elem_of_Permutation in H1.
      rewrite elem_of_list_lookup in H1.
      destruct!/=.
      eapply Forall2_lookup_l in Heqn1; last done.
      setoid_rewrite bind_Some in Heqn1.
      destruct!/=.
  Qed. 
  
  Lemma urn_subst_heap_insert f i x x' m m':
    i ∉ dom m ->
    urn_subst_val f x = Some x' ->
    urn_subst_heap f m = Some m' ->
    urn_subst_heap f (<[i:=x]> m) = Some (<[i:=x']> m').
  Proof.
    rewrite /urn_subst_heap.
    intros Hdom Hsome H.
    erewrite urn_subst_heap_permutate; last first.
    - apply map_to_list_insert.
      by rewrite not_elem_of_dom in Hdom.
    - apply NoDup_fst_map_to_list.
    - simpl.
      rewrite Hsome.
      simpl.
      apply fmap_Some in H.
      destruct H as [?[? ->]].
      apply fmap_Some.
      setoid_rewrite bind_Some.
      eexists _. split; first naive_solver.
      by rewrite list_to_map_cons.
  Qed.
  
  Lemma urn_subst_heap_union m1 m2 m1' m2' f:
    dom m1 ## dom m2 ->
    urn_subst_heap f m1 = Some m1' ->
    urn_subst_heap f m2 = Some m2' ->
    (urn_subst_heap f (m1 ∪ m2)) = Some (m1' ∪ m2').
  Proof.
    revert m2 m1' m2'.
    revert m1.
    apply (map_ind (λ m1, ∀ m2 m1' m2', dom m1 ## dom m2
    → urn_subst_heap f m1 = Some m1'
    → urn_subst_heap f m2 = Some m2' → urn_subst_heap f (m1 ∪ m2) = Some (m1' ∪ m2'))).
    { intros m2 m1' m2' Hdom.
      rewrite {1}/urn_subst_heap.
      rewrite map_to_list_empty/=.
      intros. simplify_eq.
      by rewrite !map_empty_union. }
    intros i x m Hnone IH.
    intros m2 m1' m2'.
    rewrite dom_insert.
    rewrite disjoint_union_l.
    intros [Hdom1 Hdom2].
    destruct (urn_subst_val f x) eqn:Heqn; last first.
    { intros Hcontra.
      assert (urn_subst_heap f (<[i:=x]> m) = None); last naive_solver.
      rewrite /urn_subst_heap.
      rewrite fmap_None.
      apply mapM_None_2.
      rewrite Exists_exists.
      eexists (i, _).
      rewrite elem_of_map_to_list.
      rewrite lookup_insert.
      split; first done.
      rewrite bind_None.
      naive_solver.
    }
    intros H.
    destruct (urn_subst_heap f m) eqn:Heqn'; last first.
    {
      assert (urn_subst_heap f (<[i:=x]> m) = None); last naive_solver.
      rewrite /urn_subst_heap in Heqn' *.
      rewrite !fmap_None !mapM_None !Exists_exists in Heqn' *.
      destruct Heqn' as [[l ][H1 H2]].
      rewrite elem_of_map_to_list in H1.
      rewrite bind_None in H2.
      destruct!/=.
      eexists (_,_).
      rewrite elem_of_map_to_list.
      erewrite (lookup_insert_ne _ _ l).
      - split; first done.
        rewrite bind_None. naive_solver.
      - intros ->. naive_solver.
    }
    erewrite urn_subst_heap_insert in H; try done; last by rewrite not_elem_of_dom.
    simplify_eq.
    intros.
    eapply IH in Hdom2; try done.
    rewrite -insert_union_l.
    erewrite urn_subst_heap_insert; try done; first by rewrite -insert_union_l.
    rewrite not_elem_of_dom.
    apply lookup_union_None_2; try done.
    by apply disjoint_singleton_l, not_elem_of_dom in Hdom1.
  Qed.

  Lemma urn_subst_heap_empty f:
    urn_subst_heap f ∅ = Some ∅.
  Proof.
    rewrite /urn_subst_heap.
    by rewrite map_to_list_empty.
  Qed.

  Lemma urn_subst_heap_forall f m m':
    urn_subst_heap f m = Some m' ->
    map_Forall (λ _ v, ∃ v', urn_subst_val f v = Some v') m.
  Proof.
    rewrite /urn_subst_heap.
    rewrite fmap_Some.
    setoid_rewrite mapM_Some.
    intros.
    destruct!/=.
    rewrite map_Forall_to_list.
    eapply Forall2_Forall_l; first done.
    simpl.
    apply Forall_true.
    intros [][].
    rewrite bind_Some.
    intros. destruct!/=.
    naive_solver.
  Qed.

  Lemma urn_subst_heap_forall' f m:
    map_Forall (λ _ v, ∃ v', urn_subst_val f v = Some v') m ->
    is_Some (urn_subst_heap f m).
  Proof.
    intros Hforall.
    destruct (urn_subst_heap f m) eqn :H; first naive_solver.
    exfalso.
    rewrite /urn_subst_heap in H.
    setoid_rewrite fmap_None in H.
    setoid_rewrite mapM_None in H.
    revert H.
    apply Forall_Exists_neg.
    rewrite Forall_forall.
    intros [??].
    rewrite elem_of_map_to_list.
    intros ?.
    destruct (mbind _ _) eqn:H'; first done.
    rewrite bind_None in H'.
    destruct!/=.
    rewrite map_Forall_lookup in Hforall.
    apply Hforall in H.
    naive_solver.
  Qed.
  
  
  Lemma urn_subst_heap_dom f m m':
    urn_subst_heap f m = Some m' ->
    dom m = dom m'.
  Proof.
    revert m'.
    revert m.
    apply (map_ind (λ m, ∀ m', urn_subst_heap _ _ = _ -> _)).
    - intros ?. rewrite urn_subst_heap_empty.
      intros. by simplify_eq.
    - intros ?????.
      intros ?.
      intros H'.
      apply urn_subst_heap_forall in H' as H''.
      eapply map_Forall_lookup_1 in H'' as K; last apply lookup_insert.
      destruct!/=.
      unshelve epose proof urn_subst_heap_forall' f m _ as []; first by eapply map_Forall_insert_1_2.
      erewrite urn_subst_heap_insert in H'; [| |done|done].
      + simplify_eq.
        rewrite !dom_insert_L.
        f_equal.
        naive_solver.
      + by rewrite not_elem_of_dom.
  Qed. 

  Lemma urn_subst_heap_replicate f l v v' n m:
    urn_subst_val f v = Some v' ->
    urn_subst_heap f (heap_array l (replicate n v)) =
    Some m ->
    (heap_array l (replicate n v')) = m.
  Proof.
    intros Hv.
    revert l m.
    induction n; simpl.
    - setoid_rewrite urn_subst_heap_empty.
      naive_solver.
    - intros ??.
      assert (∃ m', urn_subst_heap f (heap_array (l +ₗ 1) (replicate n v)) = Some m').
      { apply urn_subst_heap_forall'.
        apply map_Forall_lookup_2.
        intros ??.
        rewrite heap_array_lookup.
        intros H.
        destruct H as [?[?[? K]]].
        rewrite lookup_replicate in K.
        destruct!/=. naive_solver.
      }
      destruct!/=.
      erewrite urn_subst_heap_union; last first.
      + done.
      + rewrite /urn_subst_heap.
        rewrite fmap_Some.
        setoid_rewrite mapM_Some.
        eexists _.
        rewrite map_to_list_singleton.
        erewrite Forall2_cons_iff.
        rewrite Hv. naive_solver.
      + symmetry.
        set_unfold.
        intros ?.
        intros [K]%dom_heap_array.
        intros ->.
        revert K.
        rewrite /loc_add/loc_le.
        simpl. lia. 
      + simpl. rewrite insert_empty.
        intros. simplify_eq.
        f_equal.
        naive_solver.
  Qed.
  
  Lemma urn_subst_heap_delete f i m m':
    i ∈ dom m ->
    urn_subst_heap f m = Some m' ->
    urn_subst_heap f (delete i m) = Some (delete i m').
  Proof.
    intros Hdom H1.
    apply urn_subst_heap_forall in H1 as H2.
    assert (∃ m', urn_subst_heap f (delete i m) = Some m') as H.
    { eapply urn_subst_heap_forall'. by apply map_Forall_delete. }
    destruct!/=.
    rewrite H.
    f_equal.
    rewrite elem_of_dom in Hdom.
    destruct Hdom as [? Hdom].
    eapply map_Forall_lookup_1 in H2; last done.
    destruct H2 as [? H2].
    unshelve epose proof urn_subst_heap_insert _ _ _ _ _ _ _ H2 H as H'.
    2:{ rewrite not_elem_of_dom. apply lookup_delete. }
    rewrite insert_delete in H'; last done.
    rewrite H1 in H'. simplify_eq.
    rewrite delete_insert; first done.
    rewrite -not_elem_of_dom.
    erewrite <-urn_subst_heap_dom; last done.
    rewrite not_elem_of_dom. apply lookup_delete. 
  Qed. 

  (** same as insert, but this is if i is in the domain *)
  Lemma urn_subst_heap_insert' f i x x' m m':
    i ∈ dom m ->
    urn_subst_val f x = Some x' ->
    urn_subst_heap f m = Some m' ->
    urn_subst_heap f (<[i:=x]> m) = Some (<[i:=x']> m').
  Proof.
    intros Hdom H1 H2.
    rewrite -insert_delete_insert.
    apply urn_subst_heap_forall in H2 as H3.
    eapply urn_subst_heap_delete in Hdom; last done.
    erewrite urn_subst_heap_insert; last first.
    - done.
    - done.
    - rewrite not_elem_of_dom. apply lookup_delete.
    - by rewrite insert_delete_insert. 
  Qed. 

    Lemma urn_subst_heap_subset f f' m m':
    f ⊆ f'->
    urn_subst_heap f m = Some m' ->
    urn_subst_heap f' m = Some m'.
  Proof.
    intros H.
    revert m'.
    revert m.
    apply (map_ind (λ m, forall m', urn_subst_heap f m = Some m' → urn_subst_heap f' m = Some m')); simpl.
    - intros ?. repeat rewrite urn_subst_heap_empty.
      naive_solver.
    - intros ??? Hnone IH.
      intros ?.
      intros H1.
      apply urn_subst_heap_forall in H1 as H2.
      assert (exists m', urn_subst_heap f (m) = Some m') as [? Hrewrite].
      { apply urn_subst_heap_forall'.
        by eapply map_Forall_insert_1_2.
      }
      assert (exists x', urn_subst_val f (x) = Some x') as [? Hrewrite'].
      { eapply map_Forall_lookup_1 in H2; last apply lookup_insert. done. }
      erewrite urn_subst_heap_insert; last first.
      + by apply IH.
      + by eapply urn_subst_val_subset.
      + by rewrite not_elem_of_dom.
      + f_equal.
        eapply urn_subst_heap_insert in Hrewrite'; last done; last by rewrite not_elem_of_dom.
        rewrite Hrewrite' in H1.
        naive_solver.
  Qed. 
End urn_subst.
