From Coq Require Import Reals Psatz.
From stdpp Require Import functions gmap stringmap fin_sets.
From clutch.prelude Require Import stdpp_ext NNRbar fin uniform_list.
From clutch.delay_prob_lang Require Import tactics notation.
From clutch.delay_prob_lang Require Export lang.
From iris.prelude Require Import options.
Set Default Proof Using "Type*".

(* In lang.v, we defined functions and lemmas for substituing for baselits, 
   now we do it for expressions and values*)
Section urn_subst.
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
| DRand e => e' ← urn_subst_expr f e; Some (DRand e')
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

End urn_subst.
