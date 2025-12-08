From Coq Require Import Reals Psatz.
Require Import Btauto. 
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

  Fixpoint urn_subst_expr (f: gmap loc nat) (e : expr) : option expr :=
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

  Definition urn_subst_ectx_item (f:gmap loc nat) K : option ectx_item :=
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
    end.

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
    try (rewrite option_bind_comm !option_bind_assoc;
         by apply option_bind_ext_fun);
      try (rewrite option_bind_assoc; by apply option_bind_ext_fun);
    rewrite option_bind_comm !option_bind_assoc;
      apply option_bind_ext_fun;
      intros; simpl; rewrite option_bind_comm option_bind_assoc;
      by apply option_bind_ext_fun.
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
  end.

Lemma is_well_constructed_expr_false e f:
  is_well_constructed_expr e = false -> urn_subst_expr f e = None.
Proof.
  revert e.
  apply (expr_mut (λ e, is_well_constructed_expr e = false -> urn_subst_expr f e = None) (λ v, is_well_constructed_val v = false -> urn_subst_val f v = None)); simpl; repeat setoid_rewrite bind_None; repeat setoid_rewrite andb_false_iff.
  1, 2, 3, 5, 9, 10, 11, 12, 15, 17, 18, 20, 22, 23: naive_solver.
  1, 2, 4, 6, 7: intros; destruct!/=; first naive_solver;
              destruct (urn_subst_expr _ _); naive_solver.
  1, 2: intros; destruct!/=; first naive_solver;
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
    19: { repeat case_match; simplify_eq.
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
        eapply urn_subst_expr_exists in K1, K2; last done; destruct!/=;
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
      destruct K2 as [?[K2 ?]]; destruct K3 as [?[K3 ?]]; simplify_eq;
        apply urn_subst_well_typed in K2 as K2';
        destruct K2' as [? [? Hrewrite1]];
        apply urn_subst_well_typed in K3 as K3';
        destruct K3' as [? [? Hrewrite2]]; simplify_eq;
        rewrite Hrewrite1 Hrewrite2;
      apply urn_subst_is_simple in K2 as K2'';
      apply urn_subst_is_simple in K3 as K3'';
    bind_solver; match_solver;
    simpl in *; simplify_eq;
                            try rewrite K2; try rewrite K3; simpl; bind_solver; match_solver; try case_match; simplify_eq; naive_solver.
  
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
  Admitted.
  (** This proof is correct but SUPER SLOW *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (*   - bin_op_smash. *)
  (* Qed.  *)
End urn_subst.
