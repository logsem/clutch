From Coq Require Import Reals Psatz.
From stdpp Require Import countable gmap stringmap fin_sets.
From clutch.prelude Require Import stdpp_ext.
From clutch.delay_prob_lang Require Import tactics notation.
From clutch.delay_prob_lang Require Export lang.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".

Section urn_subst.
(* In lang.v, we defined functions and lemmas for substituing for baselits, 
   now we do it for expressions and values*)
(* We also replace DRands with Rands *)

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
End urn_subst.
