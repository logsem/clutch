(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import measure lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state.
Require Import mathcomp.reals_stdlib.Rstruct.
Require Import mathcomp.reals.reals.
Set Warnings "hiding-delimiting-key".

Local Open Scope classical_set_scope.

(** Shape substitution *)
Fixpoint shape_subst (x : string) (v : val_shape) (e : expr_shape) : expr_shape :=
  match e with
  | Val _ => e
  | Var y =>  if (decide (BNamed x = y)) then Val v else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then shape_subst x v e else e
  | App e1 e2 => App (shape_subst x v e1) (shape_subst x v e2)
  | UnOp op e => UnOp op (shape_subst x v e)
  | BinOp op e1 e2 => BinOp op (shape_subst x v e1) (shape_subst x v e2)
  | If e0 e1 e2 => If (shape_subst x v e0) (shape_subst x v e1) (shape_subst x v e2)
  | Pair e1 e2 => Pair (shape_subst x v e1) (shape_subst x v e2)
  | Fst e => Fst (shape_subst x v e)
  | Snd e => Snd (shape_subst x v e)
  | InjL e => InjL (shape_subst x v e)
  | InjR e => InjR (shape_subst x v e)
  | Case e0 e1 e2 => Case (shape_subst x v e0) (shape_subst x v e1) (shape_subst x v e2)
  | Alloc e1 => Alloc (shape_subst x v e1)
  | Load e => Load (shape_subst x v e)
  | Store e1 e2 => Store (shape_subst x v e1) (shape_subst x v e2)
  | AllocTape e => AllocTape (shape_subst x v e)
  | AllocUTape => AllocUTape
  | Rand e1 e2 => Rand (shape_subst x v e1) (shape_subst x v e2)
  | URand e => URand (shape_subst x v e)
  | Tick e => Tick (shape_subst x v e)
  end.

(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y =>  if (decide (BNamed x = y)) then Val v else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
  | Alloc e1 => Alloc (subst x v e1)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | AllocTape e => AllocTape (subst x v e)
  | AllocUTape => AllocUTape
  | Rand e1 e2 => Rand (subst x v e1) (subst x v e2)
  | URand e => URand (subst x v e)
  | Tick e => Tick (subst x v e)
  end.

(**  Uncurried substitution 1: can prove that this is measurable for all b by a shape argument *)
Definition substU (b : string) (x : (val * expr)%type) : expr :=
  subst b x.1 x.2.

(*
Lemma subst_preimage_full (x : string) (s1 : val_shape) (s2 : expr_shape) (s : expr_shape) :
    (s = shape_subst x s1 s2) ->
      ((val_ST (gen_val s1)) `*` (expr_ST (gen_expr s2))) `<=`
      (substU x @^-1` (expr_ST (gen_expr s))).
Proof. Admitted.


Lemma subst_preimage_emp (x : string) (s1 : val_shape) (s2 : expr_shape) (s : expr_shape) :
    (s ≠ shape_subst x s1 s2) ->
      (substU x @^-1` (expr_ST (gen_expr s)) = set0).
Proof. Admitted.
*)


Lemma shape_subst_respect s b v e: expr_ST s (substU b (v, e))-> shape_subst b (shape_val v) (shape_expr e) = shape_expr s.
Proof.
  revert s e b v.
  fix FIX 1.
  intros [v'|x|f x e|e1 e2|x e|x e1 e2|e1 e2 e3|e1 e2|e|e|e|e|e1 e2 e3|e|e|e1 e2|e|e1 e2| |e|e] s b v; simpl.
  all: try (intros [? ? H];
    rewrite /substU/= in H;
    destruct s; try done; simpl in *; [by case_match|];
    simplify_eq;
    rewrite /shape_expr/expr_pre_F-!/(expr_pre_F _ _ _ _ _ _)-!/shape_expr;
    f_equal; simplify_eq; by apply FIX).
  all: try (intros [? ? [y ? H]];
    rewrite /substU/= in H;
    destruct s; try done; simpl in *; [by case_match|];
    simplify_eq;
    rewrite /shape_expr/expr_pre_F-!/(expr_pre_F _ _ _ _ _ _)-!/shape_expr;
    f_equal; simplify_eq; by apply FIX).
  all: try (intros [x ? [y ? [z ? H]]];
    rewrite /substU/= in H;
    destruct s; try done; simpl in *; [by case_match|];
    simplify_eq;
    rewrite /shape_expr/expr_pre_F-!/(expr_pre_F _ _ _ _ _ _)-!/shape_expr;
    f_equal; simplify_eq; by apply FIX).
  - intros [x ? H].
    rewrite /substU/= in H;
      destruct s; try done; simpl in *; last first.
    { case_match; simplify_eq.
      rewrite /shape_expr/=. f_equal.
      by erewrite <-val_ST_shape.
    }
    rewrite /shape_expr/=. f_equal. simplify_eq.
    rewrite -!/(shape_val). 
    by erewrite <-val_ST_shape.
  - destruct s; rewrite /substU/=; try done.
    case_match.
    + subst. intros. simplify_eq.
    + intros. by simplify_eq.
  - intros [?? H].
    destruct s; try done.
    { rewrite /substU/= in H. by case_match. }
    rewrite /substU/= in H.
    simplify_eq.
    rewrite /shape_subst/=-/shape_subst.
    case_match.
    + rewrite /shape_expr/expr_pre_F-/(expr_pre_F _ _ _ _ _ s)-/(expr_pre_F _ _ _ _ _ e)-!/shape_expr.
      f_equal. by apply FIX.
    + rewrite /shape_expr/expr_pre_F-/(expr_pre_F _ _ _ _ _ s)-/(expr_pre_F _ _ _ _ _ e)-!/shape_expr.
      f_equal. by erewrite expr_ST_shape.
  - intros H;
    rewrite /substU/= in H.
    destruct s; try done; simpl in *; by case_match.
Qed.

Definition combine_base_lit_pre (b1 b2: base_lit_S):base_lit_S :=
  match b1, b2 with
    | LitInt s1, LitInt s2 => LitInt (s1 `&` s2)
    | LitBool s1, LitBool s2 => LitBool (s1 `&` s2)
    | LitUnit, LitUnit => LitUnit
    | LitLoc s1, LitLoc s2 => LitLoc (s1 `&` s2)
    | LitLbl s1, LitLbl s2 => LitLbl (s1 `&` s2)
    | LitReal s1, LitReal s2 => LitReal (s1 `&` s2)
    | _,_ => LitUnit
  end.

Fixpoint test (e1 e2: expr_S) : expr_S:=
  match e1, e2 with
  |App s1 s2, App s3 s4 => App (test s1 s3) (test s2 s4)
  | _,_ => Var BAnon
  end. 

Fixpoint combine_expr_pre (e1 e2:expr_S): expr_S :=
  match e1, e2 with
  | Val s1, Val s2          => Val (combine_val_pre s1 s2)
  | Var x, Var x'          => Var x
  | Rec f x s1, Rec f' x' s2      => Rec f x (combine_expr_pre s1 s2)
  | App s1 s2, App s3 s4      => App (combine_expr_pre s1 s3) (combine_expr_pre s2 s4)
  | UnOp op s1, UnOp op' s2      => UnOp op (combine_expr_pre s1 s2)
  | BinOp op s1 s2, BinOp op' s3 s4 => BinOp op (combine_expr_pre s1 s3) (combine_expr_pre s2 s4)
  | If s1 s2 s3, If s4 s5 s6    => If (combine_expr_pre s1 s4) (combine_expr_pre s2 s5) (combine_expr_pre s3 s6)
  | Pair s1 s2, Pair s3 s4     => Pair (combine_expr_pre s1 s3) (combine_expr_pre s2 s4)
  | Fst s1, Fst s2          => Fst (combine_expr_pre s1 s2)
  | Snd s1, Snd s2          => Snd (combine_expr_pre s1 s2)
  | InjL s1, InjL s2         => InjL (combine_expr_pre s1 s2)
  | InjR s1, InjR s2         => InjR (combine_expr_pre s1 s2)
  | Case s1 s2 s3, Case s4 s5 s6  => Case (combine_expr_pre s1 s4) (combine_expr_pre s2 s5) (combine_expr_pre s3 s6)
  | Alloc s1, Alloc s2       => Alloc (combine_expr_pre s1 s2)
  | Load s1, Load s2         => Load (combine_expr_pre s1 s2)
  | Store s1 s2, Store s3 s4    => Store (combine_expr_pre s1 s3) (combine_expr_pre s2 s4)
  | AllocTape s1, AllocTape s2    => AllocTape (combine_expr_pre s1 s2)
  | Rand s1 s2, Rand s3 s4     => Rand (combine_expr_pre s1 s3) (combine_expr_pre s2 s4)
  | AllocUTape, AllocUTape     => AllocUTape
  | URand s1, URand s2        => URand (combine_expr_pre s1 s2)
  | Tick s1, Tick s2         => Tick (combine_expr_pre s1 s2)
  | _, _ => AllocUTape
  end with combine_val_pre (v1 v2 : val_S) {struct v1}:=
  match v1, v2 with
  | LitV s1, LitV s2          => LitV (combine_base_lit_pre s1 s2)
  | RecV f x s1, RecV f' x' s2     => RecV f x (combine_expr_pre s1 s2)
  | PairV s1 s2, PairV s3 s4    => PairV (combine_val_pre s1 s3) (combine_val_pre s2 s4)
  | InjLV s1, InjLV s2       => InjLV (combine_val_pre s1 s2)
  | InjRV s1, InjRV s2       => InjRV (combine_val_pre s1 s2)
  | _, _ => LitV LitUnit
  end.

Lemma combine_val_pre_correct v_shape (v1:val_pre) v2 :
  shape_val v1 = v_shape ->
  shape_val v2 = v_shape ->
  val_ML v1 ->
  val_ML v2->
  shape_val (combine_val_pre v1 v2) = v_shape /\
  val_ML (combine_val_pre v1 v2) /\
  val_ST (combine_val_pre v1 v2) = val_ST v1 `&` val_ST v2.
Proof.
  
Admitted.

Lemma substU_measurable_induction_lemma b v_shape e_shape (s: expr_S):
  expr_ML s->
  shape_subst b v_shape e_shape = shape_expr s ->
  exists v e,
    shape_val v = v_shape /\
    shape_expr e = e_shape /\
    val_ML v /\
    expr_ML e /\
    ([set e | shape_val e = v_shape] `*` [set e | shape_expr e = e_shape]
       `&` substU b @^-1` expr_ST s) = (val_ST v`*`expr_ST e).
Proof.
  revert e_shape s b v_shape.
  fix FIX 1.
  intros [v'|x|f x e|e1 e2|x e|x e1 e2|e1 e2 e3|e1 e2|e|e|e|e|e1 e2 e3|e|e|e1 e2|e|e1 e2| |e|e] s b v_shape Hs Hsubst; simpl in *; simpl.
  - destruct s as [x|x|f x e|e1 e2|x e|x e1 e2|e1 e2 e3|e1 e2|e|e|e|e|e1 e2 e3|e|e|e1 e2|e|e1 e2| |e|e]; simpl in *; try done. 
    inversion Hsubst as [Hrewrite]; rewrite -/(shape_val) in Hrewrite. subst.
    clear Hsubst.
    eexists (gen_val v_shape), (Val x).
    repeat split.
    + apply shape_val_gen_val.
    + apply gen_val_generator. 
    + done. 
    +  rewrite eqEsubset; split; intros []; simpl; intros; destruct!/=; repeat split.
      * by rewrite -val_shape_cyl /=.
      * destruct e; simpl in *; try done.
        by eexists _.
      * cut ([set e | shape_val e = v_shape] v); first done.
        by rewrite val_shape_cyl.
      * rewrite /shape_expr/expr_pre_F/=. f_equal. rewrite -/(shape_val _). by erewrite <-val_ST_shape.
      * rewrite /substU/=.
        by eexists _.
  - case_match; subst.
    + destruct s as [x|x|f x e|e1 e2|x e|x e1 e2|e1 e2 e3|e1 e2|e|e|e|e|e1 e2 e3|e|e|e1 e2|e|e1 e2| |e|e]; simpl in *; try done.
      inversion Hsubst as [Hrewrite]. subst.
      clear Hsubst.
      eexists (x), (Var b). repeat split; try done.
      rewrite -/(shape_val _).
      rewrite eqEsubset; split; intros [v e]; simpl; intros; destruct!/=; repeat split.
      * destruct e; try done. unfold shape_expr in *. simpl in *.
        unfold substU in *. simpl in *. case_match; last done; subst.
        by simplify_eq.
      * destruct e; try done. unfold shape_expr in *. simpl in *. f_equal. naive_solver.
      * by erewrite <-val_ST_shape.
      * rewrite /substU; simpl. case_match; last done. naive_solver.
    + destruct s as [x'|x'|f x' e|e1 e2|x' e|x' e1 e2|e1 e2 e3|e1 e2|e|e|e|e|e1 e2 e3|e|e|e1 e2|e|e1 e2| |e|e]; simpl in *; try done.
      exists (gen_val v_shape), (Var x); simplify_eq. repeat split; try done.
      * apply shape_val_gen_val.
      * apply gen_val_generator.
      * rewrite eqEsubset; split; intros []; simpl; intros; destruct!/=; repeat split; simplify_eq.
        -- by rewrite -val_shape_cyl.
        -- destruct e; try done. unfold substU, shape_expr, expr_pre_F in *. by simplify_eq.
        -- cut ([set e | shape_val e = v_shape] v); first done.
           by rewrite val_shape_cyl.
        -- rewrite /substU/=. case_match; first done.
           unfold shape_expr, expr_pre_F in *; by simplify_eq.
  - case_match; destruct!/=.
    + destruct s ; simpl in *; try done. unfold shape_expr, expr_pre_F in Hsubst. simplify_eq.
      unshelve epose proof FIX e s b v_shape _ _ as [v_pre [e_pre H2]]; try done.
      destruct H2 as (?&?&?&?&Heq); subst.
      eexists (v_pre), (Rec _ _ e_pre); repeat split; try done.
      rewrite !eqEsubset in Heq *. destruct Heq as [Heq1 Heq2].
      split; intros [v e]; simpl; intros; destruct!/=. 
      * destruct e; simplify_eq. unshelve epose proof Heq1 (v,e) _; destruct!/=; repeat split; try done;
        unfold substU, shape_expr, expr_pre_F in *; simplify_eq; simpl in *;
        case_match; simplify_eq; naive_solver.
      * unshelve epose proof Heq2 (v,_) _; [|naive_solver|].
        destruct!/=; repeat split; first naive_solver.
        -- rewrite {1}/shape_expr/expr_pre_F. by f_equal.
        -- rewrite /substU/=. case_match; naive_solver.
    + destruct s; try done. unfold shape_expr, expr_pre_F in Hsubst.
      rewrite -/(expr_pre_F _ _ _ _ _ _)-/shape_expr in Hsubst.
      simplify_eq.
      eexists (gen_val v_shape), (_); simplify_eq. repeat split; try done.
      * apply shape_val_gen_val.
      * by rewrite /shape_expr/expr_pre_F.
      * apply gen_val_generator.
      * rewrite eqEsubset; split; intros [v e']; simpl; intros; destruct!/=; repeat split; simplify_eq.
        -- by rewrite -val_shape_cyl.
        -- destruct e'; try done. unfold substU in *. simpl in *.
           case_match; last (simplify_eq; naive_solver).
           exfalso. naive_solver.
        -- cut ([set e | shape_val e = v_shape] v); first done.
           by rewrite val_shape_cyl.
        -- rewrite /substU/=. rewrite /shape_expr/expr_pre_F/=; f_equal. symmetry.
           by apply expr_ST_shape.
        -- eexists _; first done.
           rewrite /substU/=. case_match; last done.
           exfalso; naive_solver.
  - destruct s; simpl in *; try done.
    destruct Hs.
    inversion Hsubst as [[Hrewrite1 Hrewrite2]]; rewrite -/(shape_val) in Hrewrite1.
    clear Hsubst. rewrite -!/(shape_expr _) in Hrewrite1 Hrewrite2.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite1 as (v_pre1 & e_pre1 & ?&?&?&?&K1); first done.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite2 as (v_pre2 & e_pre2 & ?&?&?&?&K2); first done.
    unshelve epose proof combine_val_pre_correct _ v_pre1 v_pre2 _ _ _ _ as (Hval1 & Hval2 & Hval3); try done.
    exists (combine_val_pre v_pre1 v_pre2), (App e_pre1 e_pre2).
    subst.
    repeat split; try done.
    rewrite Hval3.
    rewrite !eqEsubset in K1 K2 *; split; intros [v e]; simpl; intros; destruct K1 as [Hineq1 Hineq2]; destruct K2 as [Hineq3 Hineq4]; destruct!/=.
    + destruct e as [x'|x'|f x' e|e1 e2|x' e|x' e1 e2|e1 e2 e3|e1 e2|e|e|e|e|e1 e2 e3|e|e|e1 e2|e|e1 e2| |e|e]; simplify_eq.
      unshelve epose proof Hineq1 (v, e1) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      unshelve epose proof Hineq3 (v, e2) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      simpl in *. naive_solver.
    + unshelve epose proof Hineq2 (v,_) _; [|naive_solver|].
      unshelve epose proof Hineq4 (v,_) _; [|naive_solver|].
      simpl in *. destruct!/=.
      repeat split; try done.
      { rewrite /shape_expr/expr_pre_F. simpl. f_equal; naive_solver. }
      naive_solver.
  - destruct s; try done; unfold shape_expr, expr_pre_F in Hsubst;
    rewrite -/(expr_pre_F _ _ _ _ _ _)-/shape_expr in Hsubst;
    simplify_eq;
    unshelve epose proof FIX _ _ _ _ _ _ as (v_pre & e_pre & K); [| | | | |exact|]; first by simpl in *.
    destruct K as (?&?&?&?&Heq); simplify_eq;
    eexists v_pre, (UnOp _ _); simplify_eq. repeat split; try done.
    rewrite !eqEsubset in Heq *. destruct Heq as [Heq1 Heq2].
    split; intros [v e]; simpl; intros; destruct!/=. 
    * destruct e; simplify_eq. unshelve epose proof Heq1 (v,e) _; destruct!/=; repeat split; try done;
        unfold substU, shape_expr, expr_pre_F in *; simplify_eq; simpl in *; naive_solver.
    * unshelve epose proof Heq2 (v,_) _; [|naive_solver|].
      destruct!/=; repeat split; first naive_solver.
      -- rewrite {1}/shape_expr/expr_pre_F. by f_equal.
      -- rewrite /substU/=. naive_solver.
  - destruct s; simpl in *; try done.
    destruct Hs.
    inversion Hsubst as [[H' Hrewrite1 Hrewrite2]]. subst.
    clear Hsubst. rewrite -!/(shape_expr _) in Hrewrite1 Hrewrite2.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite1 as (v_pre1 & e_pre1 & ?&?&?&?&K1); first done.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite2 as (v_pre2 & e_pre2 & ?&?&?&?&K2); first done.
    unshelve epose proof combine_val_pre_correct _ v_pre1 v_pre2 _ _ _ _ as (Hval1 & Hval2 & Hval3); try done.
    eexists (combine_val_pre v_pre1 v_pre2), (BinOp _ e_pre1 e_pre2).
    subst.
    repeat split; try done.
    rewrite Hval3.
    rewrite !eqEsubset in K1 K2 *; split; intros [v e]; simpl; intros; destruct K1 as [Hineq1 Hineq2]; destruct K2 as [Hineq3 Hineq4]; destruct!/=.
    + destruct e as [x'|x'|f x' e|e1 e2|x' e|x' e1 e2|e1 e2 e3|e1 e2|e|e|e|e|e1 e2 e3|e|e|e1 e2|e|e1 e2| |e|e]; simplify_eq.
      unshelve epose proof Hineq1 (v, e1) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      unshelve epose proof Hineq3 (v, e2) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      simpl in *. unfold substU in *. simpl in *. simplify_eq. naive_solver. 
    + unshelve epose proof Hineq2 (v,_) _; [|naive_solver|].
      unshelve epose proof Hineq4 (v,_) _; [|naive_solver|].
      simpl in *. destruct!/=.
      repeat split; try done.
      { rewrite /shape_expr/expr_pre_F. simpl. f_equal; naive_solver. }
      naive_solver.
  - destruct s; simpl in *; try done.
    destruct Hs as [?[]].
    inversion Hsubst as [[Hrewrite1 Hrewrite2 Hrewrite3]].
    clear Hsubst. rewrite -!/(shape_expr _) in Hrewrite1 Hrewrite2 Hrewrite3.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite1 as (v_pre1 & e_pre1 & ?&?&?&?&K1); first done.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite2 as (v_pre2 & e_pre2 & ?&?&?&?&K2); first done.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite3 as (v_pre3 & e_pre3 & ?&?&?&?&K3); first done.
    unshelve epose proof combine_val_pre_correct _ v_pre1 v_pre2 _ _ _ _ as (Hval1 & Hval2 & Hval3); try done.
    unshelve epose proof combine_val_pre_correct _ (combine_val_pre v_pre1 v_pre2) v_pre3 _ _ _ _ as (Hval4 & Hval5 & Hval6); try done.
    exists (combine_val_pre (combine_val_pre v_pre1 v_pre2) v_pre3), (If e_pre1 e_pre2 e_pre3).
    subst.
    repeat split; try done.
    rewrite Hval6 Hval3.
    rewrite !eqEsubset in K1 K2 K3 *; split; intros [v e]; simpl; intros; destruct K1 as [Hineq1 Hineq2]; destruct K2 as [Hineq3 Hineq4]; destruct K3 as [Hineq5 Hineq6]; destruct!/=.
    + destruct e as [x'|x'|f x' e|e1 e2|x' e|x' e1 e2|e1 e2 e3|e1 e2|e|e|e|e|e1 e2 e3|e|e|e1 e2|e|e1 e2| |e|e]; simplify_eq.
      unshelve epose proof Hineq1 (v, e1) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      unshelve epose proof Hineq3 (v, e2) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      unshelve epose proof Hineq5 (v, e3) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      simpl in *. naive_solver.
    + unshelve epose proof Hineq2 (v,_) _; [|naive_solver|].
      unshelve epose proof Hineq4 (v,_) _; [|naive_solver|].
      unshelve epose proof Hineq6 (v,_) _; [|naive_solver|].
      simpl in *. destruct!/=.
      repeat split; try done.
      { rewrite /shape_expr/expr_pre_F. simpl. f_equal; naive_solver. }
      naive_solver.
  - destruct s; simpl in *; try done.
    destruct Hs.
    inversion Hsubst as [[Hrewrite1 Hrewrite2]]; rewrite -/(shape_val) in Hrewrite1.
    clear Hsubst. rewrite -!/(shape_expr _) in Hrewrite1 Hrewrite2.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite1 as (v_pre1 & e_pre1 & ?&?&?&?&K1); first done.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite2 as (v_pre2 & e_pre2 & ?&?&?&?&K2); first done.
    unshelve epose proof combine_val_pre_correct _ v_pre1 v_pre2 _ _ _ _ as (Hval1 & Hval2 & Hval3); try done.
    exists (combine_val_pre v_pre1 v_pre2), (Pair e_pre1 e_pre2).
    subst.
    repeat split; try done.
    rewrite Hval3.
    rewrite !eqEsubset in K1 K2 *; split; intros [v e]; simpl; intros; destruct K1 as [Hineq1 Hineq2]; destruct K2 as [Hineq3 Hineq4]; destruct!/=.
    + destruct e as [x'|x'|f x' e|e1 e2|x' e|x' e1 e2|e1 e2 e3|e1 e2|e|e|e|e|e1 e2 e3|e|e|e1 e2|e|e1 e2| |e|e]; simplify_eq.
      unshelve epose proof Hineq1 (v, e1) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      unshelve epose proof Hineq3 (v, e2) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      simpl in *. naive_solver.
    + unshelve epose proof Hineq2 (v,_) _; [|naive_solver|].
      unshelve epose proof Hineq4 (v,_) _; [|naive_solver|].
      simpl in *. destruct!/=.
      repeat split; try done.
      { rewrite /shape_expr/expr_pre_F. simpl. f_equal; naive_solver. }
      naive_solver.
  - destruct s; try done. unfold shape_expr, expr_pre_F in Hsubst.
    rewrite -/(expr_pre_F _ _ _ _ _ _)-/shape_expr in Hsubst.
    simplify_eq.
    unshelve epose proof FIX _ _ _ _ _ _ as (v_pre & e_pre & K); [| | | | |exact|]; first by simpl in *.
    destruct K as (?&?&?&?&Heq). simplify_eq.
    eexists v_pre, (Fst _); simplify_eq. repeat split; try done.
    rewrite !eqEsubset in Heq *. destruct Heq as [Heq1 Heq2].
    split; intros [v e]; simpl; intros; destruct!/=. 
    * destruct e; simplify_eq. unshelve epose proof Heq1 (v,e) _; destruct!/=; repeat split; try done;
        unfold substU, shape_expr, expr_pre_F in *; simplify_eq; simpl in *; naive_solver.
    * unshelve epose proof Heq2 (v,_) _; [|naive_solver|].
      destruct!/=; repeat split; first naive_solver.
      -- rewrite {1}/shape_expr/expr_pre_F. by f_equal.
      -- rewrite /substU/=. naive_solver.
  - destruct s; try done. unfold shape_expr, expr_pre_F in Hsubst.
    rewrite -/(expr_pre_F _ _ _ _ _ _)-/shape_expr in Hsubst.
    simplify_eq.
    unshelve epose proof FIX _ _ _ _ _ _ as (v_pre & e_pre & K); [| | | | |exact|]; first by simpl in *.
    destruct K as (?&?&?&?&Heq). simplify_eq.
    eexists v_pre, (Snd _); simplify_eq. repeat split; try done.
    rewrite !eqEsubset in Heq *. destruct Heq as [Heq1 Heq2].
    split; intros [v e]; simpl; intros; destruct!/=. 
    * destruct e; simplify_eq. unshelve epose proof Heq1 (v,e) _; destruct!/=; repeat split; try done;
        unfold substU, shape_expr, expr_pre_F in *; simplify_eq; simpl in *; naive_solver.
    * unshelve epose proof Heq2 (v,_) _; [|naive_solver|].
      destruct!/=; repeat split; first naive_solver.
      -- rewrite {1}/shape_expr/expr_pre_F. by f_equal.
      -- rewrite /substU/=. naive_solver.
  - destruct s; try done. unfold shape_expr, expr_pre_F in Hsubst.
    rewrite -/(expr_pre_F _ _ _ _ _ _)-/shape_expr in Hsubst.
    simplify_eq.
    unshelve epose proof FIX _ _ _ _ _ _ as (v_pre & e_pre & K); [| | | | |exact|]; first by simpl in *.
    destruct K as (?&?&?&?&Heq). simplify_eq.
    eexists v_pre, (InjL _); simplify_eq. repeat split; try done.
    rewrite !eqEsubset in Heq *. destruct Heq as [Heq1 Heq2].
    split; intros [v e]; simpl; intros; destruct!/=. 
    * destruct e; simplify_eq. unshelve epose proof Heq1 (v,e) _; destruct!/=; repeat split; try done;
        unfold substU, shape_expr, expr_pre_F in *; simplify_eq; simpl in *; naive_solver.
    * unshelve epose proof Heq2 (v,_) _; [|naive_solver|].
      destruct!/=; repeat split; first naive_solver.
      -- rewrite {1}/shape_expr/expr_pre_F. by f_equal.
      -- rewrite /substU/=. naive_solver.
  - destruct s; try done. unfold shape_expr, expr_pre_F in Hsubst.
    rewrite -/(expr_pre_F _ _ _ _ _ _)-/shape_expr in Hsubst.
    simplify_eq.
    unshelve epose proof FIX _ _ _ _ _ _ as (v_pre & e_pre & K); [| | | | |exact|]; first by simpl in *.
    destruct K as (?&?&?&?&Heq). simplify_eq.
    eexists v_pre, (InjR _); simplify_eq. repeat split; try done.
    rewrite !eqEsubset in Heq *. destruct Heq as [Heq1 Heq2].
    split; intros [v e]; simpl; intros; destruct!/=. 
    * destruct e; simplify_eq. unshelve epose proof Heq1 (v,e) _; destruct!/=; repeat split; try done;
        unfold substU, shape_expr, expr_pre_F in *; simplify_eq; simpl in *; naive_solver.
    * unshelve epose proof Heq2 (v,_) _; [|naive_solver|].
      destruct!/=; repeat split; first naive_solver.
      -- rewrite {1}/shape_expr/expr_pre_F. by f_equal.
      -- rewrite /substU/=. naive_solver.
  - destruct s; simpl in *; try done.
    destruct Hs as [?[]].
    inversion Hsubst as [[Hrewrite1 Hrewrite2 Hrewrite3]].
    clear Hsubst. rewrite -!/(shape_expr _) in Hrewrite1 Hrewrite2 Hrewrite3.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite1 as (v_pre1 & e_pre1 & ?&?&?&?&K1); first done.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite2 as (v_pre2 & e_pre2 & ?&?&?&?&K2); first done.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite3 as (v_pre3 & e_pre3 & ?&?&?&?&K3); first done.
    unshelve epose proof combine_val_pre_correct _ v_pre1 v_pre2 _ _ _ _ as (Hval1 & Hval2 & Hval3); try done.
    unshelve epose proof combine_val_pre_correct _ (combine_val_pre v_pre1 v_pre2) v_pre3 _ _ _ _ as (Hval4 & Hval5 & Hval6); try done.
    exists (combine_val_pre (combine_val_pre v_pre1 v_pre2) v_pre3), (Case e_pre1 e_pre2 e_pre3).
    subst.
    repeat split; try done.
    rewrite Hval6 Hval3.
    rewrite !eqEsubset in K1 K2 K3 *; split; intros [v e]; simpl; intros; destruct K1 as [Hineq1 Hineq2]; destruct K2 as [Hineq3 Hineq4]; destruct K3 as [Hineq5 Hineq6]; destruct!/=.
    + destruct e as [x'|x'|f x' e|e1 e2|x' e|x' e1 e2|e1 e2 e3|e1 e2|e|e|e|e|e1 e2 e3|e|e|e1 e2|e|e1 e2| |e|e]; simplify_eq.
      unshelve epose proof Hineq1 (v, e1) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      unshelve epose proof Hineq3 (v, e2) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      unshelve epose proof Hineq5 (v, e3) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      simpl in *. naive_solver.
    + unshelve epose proof Hineq2 (v,_) _; [|naive_solver|].
      unshelve epose proof Hineq4 (v,_) _; [|naive_solver|].
      unshelve epose proof Hineq6 (v,_) _; [|naive_solver|].
      simpl in *. destruct!/=.
      repeat split; try done.
      { rewrite /shape_expr/expr_pre_F. simpl. f_equal; naive_solver. }
      naive_solver.
  - destruct s; try done. unfold shape_expr, expr_pre_F in Hsubst.
    rewrite -/(expr_pre_F _ _ _ _ _ _)-/shape_expr in Hsubst.
    simplify_eq.
    unshelve epose proof FIX _ _ _ _ _ _ as (v_pre & e_pre & K); [| | | | |exact|]; first by simpl in *.
    destruct K as (?&?&?&?&Heq). simplify_eq.
    eexists v_pre, (Alloc _); simplify_eq. repeat split; try done.
    rewrite !eqEsubset in Heq *. destruct Heq as [Heq1 Heq2].
    split; intros [v e]; simpl; intros; destruct!/=. 
    * destruct e; simplify_eq. unshelve epose proof Heq1 (v,e) _; destruct!/=; repeat split; try done;
        unfold substU, shape_expr, expr_pre_F in *; simplify_eq; simpl in *; naive_solver.
    * unshelve epose proof Heq2 (v,_) _; [|naive_solver|].
      destruct!/=; repeat split; first naive_solver.
      -- rewrite {1}/shape_expr/expr_pre_F. by f_equal.
      -- rewrite /substU/=. naive_solver.
  - destruct s; try done. unfold shape_expr, expr_pre_F in Hsubst.
    rewrite -/(expr_pre_F _ _ _ _ _ _)-/shape_expr in Hsubst.
    simplify_eq.
    unshelve epose proof FIX _ _ _ _ _ _ as (v_pre & e_pre & K); [| | | | |exact|]; first by simpl in *.
    destruct K as (?&?&?&?&Heq). simplify_eq.
    eexists v_pre, (Load _); simplify_eq. repeat split; try done.
    rewrite !eqEsubset in Heq *. destruct Heq as [Heq1 Heq2].
    split; intros [v e]; simpl; intros; destruct!/=. 
    * destruct e; simplify_eq. unshelve epose proof Heq1 (v,e) _; destruct!/=; repeat split; try done;
        unfold substU, shape_expr, expr_pre_F in *; simplify_eq; simpl in *; naive_solver.
    * unshelve epose proof Heq2 (v,_) _; [|naive_solver|].
      destruct!/=; repeat split; first naive_solver.
      -- rewrite {1}/shape_expr/expr_pre_F. by f_equal.
      -- rewrite /substU/=. naive_solver.
  - destruct s; simpl in *; try done.
    destruct Hs.
    inversion Hsubst as [[Hrewrite1 Hrewrite2]]; rewrite -/(shape_val) in Hrewrite1.
    clear Hsubst. rewrite -!/(shape_expr _) in Hrewrite1 Hrewrite2.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite1 as (v_pre1 & e_pre1 & ?&?&?&?&K1); first done.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite2 as (v_pre2 & e_pre2 & ?&?&?&?&K2); first done.
    unshelve epose proof combine_val_pre_correct _ v_pre1 v_pre2 _ _ _ _ as (Hval1 & Hval2 & Hval3); try done.
    exists (combine_val_pre v_pre1 v_pre2), (Store e_pre1 e_pre2).
    subst.
    repeat split; try done.
    rewrite Hval3.
    rewrite !eqEsubset in K1 K2 *; split; intros [v e]; simpl; intros; destruct K1 as [Hineq1 Hineq2]; destruct K2 as [Hineq3 Hineq4]; destruct!/=.
    + destruct e as [x'|x'|f x' e|e1 e2|x' e|x' e1 e2|e1 e2 e3|e1 e2|e|e|e|e|e1 e2 e3|e|e|e1 e2|e|e1 e2| |e|e]; simplify_eq.
      unshelve epose proof Hineq1 (v, e1) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      unshelve epose proof Hineq3 (v, e2) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      simpl in *. naive_solver.
    + unshelve epose proof Hineq2 (v,_) _; [|naive_solver|].
      unshelve epose proof Hineq4 (v,_) _; [|naive_solver|].
      simpl in *. destruct!/=.
      repeat split; try done.
      { rewrite /shape_expr/expr_pre_F. simpl. f_equal; naive_solver. }
      naive_solver.
  - destruct s; try done. unfold shape_expr, expr_pre_F in Hsubst.
    rewrite -/(expr_pre_F _ _ _ _ _ _)-/shape_expr in Hsubst.
    simplify_eq.
    unshelve epose proof FIX _ _ _ _ _ _ as (v_pre & e_pre & K); [| | | | |exact|]; first by simpl in *.
    destruct K as (?&?&?&?&Heq). simplify_eq.
    eexists v_pre, (AllocTape _); simplify_eq. repeat split; try done.
    rewrite !eqEsubset in Heq *. destruct Heq as [Heq1 Heq2].
    split; intros [v e]; simpl; intros; destruct!/=. 
    * destruct e; simplify_eq. unshelve epose proof Heq1 (v,e) _; destruct!/=; repeat split; try done;
        unfold substU, shape_expr, expr_pre_F in *; simplify_eq; simpl in *; naive_solver.
    * unshelve epose proof Heq2 (v,_) _; [|naive_solver|].
      destruct!/=; repeat split; first naive_solver.
      -- rewrite {1}/shape_expr/expr_pre_F. by f_equal.
      -- rewrite /substU/=. naive_solver.
  - destruct s; simpl in *; try done.
    destruct Hs.
    inversion Hsubst as [[Hrewrite1 Hrewrite2]]; rewrite -/(shape_val) in Hrewrite1.
    clear Hsubst. rewrite -!/(shape_expr _) in Hrewrite1 Hrewrite2.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite1 as (v_pre1 & e_pre1 & ?&?&?&?&K1); first done.
    unshelve epose proof FIX _ _ _ _ _ Hrewrite2 as (v_pre2 & e_pre2 & ?&?&?&?&K2); first done.
    unshelve epose proof combine_val_pre_correct _ v_pre1 v_pre2 _ _ _ _ as (Hval1 & Hval2 & Hval3); try done.
    exists (combine_val_pre v_pre1 v_pre2), (Rand e_pre1 e_pre2).
    subst.
    repeat split; try done.
    rewrite Hval3.
    rewrite !eqEsubset in K1 K2 *; split; intros [v e]; simpl; intros; destruct K1 as [Hineq1 Hineq2]; destruct K2 as [Hineq3 Hineq4]; destruct!/=.
    + destruct e as [x'|x'|f x' e|e1 e2|x' e|x' e1 e2|e1 e2 e3|e1 e2|e|e|e|e|e1 e2 e3|e|e|e1 e2|e|e1 e2| |e|e]; simplify_eq.
      unshelve epose proof Hineq1 (v, e1) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      unshelve epose proof Hineq3 (v, e2) _.
      { simpl. repeat split; first done.
        - unfold shape_expr, expr_pre_F in *; by simplify_eq.
        - unfold substU in *. simpl in *. by simplify_eq.
      }
      simpl in *. naive_solver.
    + unshelve epose proof Hineq2 (v,_) _; [|naive_solver|].
      unshelve epose proof Hineq4 (v,_) _; [|naive_solver|].
      simpl in *. destruct!/=.
      repeat split; try done.
      { rewrite /shape_expr/expr_pre_F. simpl. f_equal; naive_solver. }
      naive_solver.
  - destruct s; try done. unfold shape_expr, expr_pre_F in Hsubst.
    rewrite -/(expr_pre_F _ _ _ _ _ _)-/shape_expr in Hsubst.
    simplify_eq.
    eexists (gen_val v_shape), (AllocUTape); simplify_eq. repeat split; try done.
    + apply shape_val_gen_val.
    + apply gen_val_generator.
    + rewrite eqEsubset.
      split; intros [v e]; simpl; intros; destruct!/=. 
      * destruct e; simplify_eq. split; last done.
        by rewrite -val_shape_cyl.
      * repeat split; try done. cut ([set e | shape_val e = v_shape] v); first done.
        by rewrite val_shape_cyl.
  - destruct s; try done. unfold shape_expr, expr_pre_F in Hsubst.
    rewrite -/(expr_pre_F _ _ _ _ _ _)-/shape_expr in Hsubst.
    simplify_eq.
    unshelve epose proof FIX _ _ _ _ _ _ as (v_pre & e_pre & K); [| | | | |exact|]; first by simpl in *.
    destruct K as (?&?&?&?&Heq). simplify_eq.
    eexists v_pre, (URand _); simplify_eq. repeat split; try done.
    rewrite !eqEsubset in Heq *. destruct Heq as [Heq1 Heq2].
    split; intros [v e]; simpl; intros; destruct!/=. 
    * destruct e; simplify_eq. unshelve epose proof Heq1 (v,e) _; destruct!/=; repeat split; try done;
        unfold substU, shape_expr, expr_pre_F in *; simplify_eq; simpl in *; naive_solver.
    * unshelve epose proof Heq2 (v,_) _; [|naive_solver|].
      destruct!/=; repeat split; first naive_solver.
      -- rewrite {1}/shape_expr/expr_pre_F. by f_equal.
      -- rewrite /substU/=. naive_solver.
  - destruct s; try done. unfold shape_expr, expr_pre_F in Hsubst.
    rewrite -/(expr_pre_F _ _ _ _ _ _)-/shape_expr in Hsubst.
    simplify_eq.
    unshelve epose proof FIX _ _ _ _ _ _ as (v_pre & e_pre & K); [| | | | |exact|]; first by simpl in *.
    destruct K as (?&?&?&?&Heq). simplify_eq.
    eexists v_pre, (Tick _); simplify_eq. repeat split; try done.
    rewrite !eqEsubset in Heq *. destruct Heq as [Heq1 Heq2].
    split; intros [v e]; simpl; intros; destruct!/=. 
    * destruct e; simplify_eq. unshelve epose proof Heq1 (v,e) _; destruct!/=; repeat split; try done;
        unfold substU, shape_expr, expr_pre_F in *; simplify_eq; simpl in *; naive_solver.
    * unshelve epose proof Heq2 (v,_) _; [|naive_solver|].
      destruct!/=; repeat split; first naive_solver.
      -- rewrite {1}/shape_expr/expr_pre_F. by f_equal.
      -- rewrite /substU/=. naive_solver.
Qed.

Lemma substU_measurable (b : string) : measurable_fun setT (substU b).
Proof.
  (* Suffices to prove the preimage of all lifted shapes are measurable *)
  eapply measurability; [by eauto|].
  simpl.
  move=> S.
  rewrite /preimage_set_system.
  rewrite -bigcup_imset1 /bigcup/=.
  move=> [SB + ->]; clear S.
  move=> [s ? <-].
  replace [set: val_T * expr_T]
    with (\bigcup_i \bigcup_j ((val_ST (gen_val (val_shape_enum i))) `*` (expr_ST (gen_expr (expr_shape_enum j)))));
    last first.
  { apply /predeqP =>y /=.
    split.
    - by move=>?.
    - move=>?.
      rewrite /setX/bigcup//=.
      destruct (val_shape_enum_surj (shape_val y.1)) as [i Hi].
      destruct (expr_shape_enum_surj (shape_expr y.2)) as [j Hj].
      exists i; [done|].
      exists j; [done|].
      by rewrite Hi Hj -expr_shape_cyl -val_shape_cyl //=.
  }
  rewrite setI_bigcupl.
  apply (@bigcup_measurable _ (val * expr)%type).
  move=>i _.
  rewrite setI_bigcupl.
  apply (@bigcup_measurable _ (val * expr)%type).
  move=>j _.

  (* Checking whether the set is definitely empty because of mismatch of shape *)
  rewrite -val_shape_cyl-expr_shape_cyl.
  destruct (decide (shape_subst b (val_shape_enum i) (expr_shape_enum j) = shape_expr s)) as [H|H]; last first.
  { (* the set is empty *)
    assert (([set e | shape_val e = val_shape_enum i] `*` [set e | shape_expr e = expr_shape_enum j]
               `&` substU b @^-1` expr_ST s) = set0) as Hrewrite; last rewrite Hrewrite; ms_solve.
    rewrite -subset0. intros []; simpl.
    intros [[H1 H2] H3].
    rewrite -H1 -H2 in H. apply H.
    by apply shape_subst_respect.
  }
  
  unshelve epose proof substU_measurable_induction_lemma _ _ _ _ _ H as (v&e&?&?&?&?&Hrewrite); first done.
  rewrite Hrewrite.
  ms_solve; apply: sub_sigma_algebra; by eexists _.
Qed. 
  (* (** Attempt *) *)
  (* generalize dependent s. *)
  (* fix FIX 1. *)
  (* destruct s; simpl. *)
  (* - intros H. *)
  (* (** End of attempt*) *)
  
  (*
  rewrite -(expr_shape_decomp (expr_ST s)).
  rewrite preimage_bigcup.
  rewrite setI_bigcupr.
  apply (@bigcup_measurable _ (val * expr)%type).
  move=>k _.
   *)
  (* So now, we know all terms in (expr_ST s) have a single shape (the shape of s)
     However, it's not all terms of that shape, it's only a susbet.
     How do we describe the preimage in terms of s?

     If the shapes don't match up, the preimage intersect the set is surely empty.
     Otherwise, I need a lemma that uses the fact that the shapes match up
     to get a _generator_ for the preimages in expr_cyl and val_cyl out of s.
     The way to define that generator is probably by strucutral recursion.
   *)

  (*
  case (ExcludedMiddle ((expr_shape_enum k) = shape_subst b (val_shape_enum i) (expr_shape_enum j))).
  - intro H.
    admit.
  - intro H.
    admit.
    *)


(** Uncurried substitution 2: can prove that this is a measurable function, by a covering argument *)
Definition substU' (x : (<<discr binder>> * (val * expr))%type) : expr :=
  match x.1 with BNamed b => substU b x.2 | BAnon => x.2.2 end.

Definition substU'_cover : list (set (<<discr binder>> * (val * expr))) :=
  [ ([set BAnon] `*` setT); ((~` [set BAnon]) `*` setT) ].

Lemma substU'_measurable : measurable_fun setT substU'.
Proof.
  apply (@measurable_by_cover_list _ _ _ _ substU' substU'_cover).
  - have BAnonMeas : binder.-discr.-measurable ([set BAnon] : set <<discr binder>>).
    { by rewrite /measurable/discr_measurable//=. }
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    + apply measurableX; done.
    + apply measurableX; done.
  - rewrite //=.
    rewrite /setX/setI//=.
    apply /predeqP =>y /=.
    split.
    + by move=>?.
    + move=>_.
      destruct ((decide (y.1 = BAnon))).
      * by left.
      * by right; left.
  - simpl.
    repeat (try apply Forall_cons; split); last by apply List.Forall_nil.
    + apply: (mathcomp_measurable_fun_ext _ _ (snd \o snd)); first ms_solve.
      * apply: snd_setX_meas_fun; ms_solve.
      * simpl. intros [?[]]. simpl. intros []. subst. rewrite /substU'/=. rewrite /patch.
        simpl. 
        rewrite /in_mem/mem/=/in_set. 
        by rewrite asboolT.
    + pose ((λ x, match x with |BNamed s => s | _ => "" end):<<discr binder>>-><<discr string>>) as f.
      apply: (mathcomp_measurable_fun_ext _ _ ((uncurry substU) \o (f \o fst △snd))); ms_solve.
      * simpl. apply: measurable_comp; last first.
        { mf_prod.
          - apply: fst_setX_meas_fun; ms_solve.
          - apply: measurable_snd_restriction. ms_solve.
        }
        { apply: uncurry_measurable.
          - intros. apply: substU_measurable.
          - intros x.
            exists (encode_nat x).
            instantiate (1:= λ x, match decode_nat x with |Some y => y | _ => inhabitant end).
            Local Opaque decode_nat. simpl.
            by rewrite decode_encode_nat.
        }
        { done. }
        ms_solve.
      * intros [?[]]. simpl. intros []. subst. rewrite /substU'/=. rewrite /patch.
        simpl. rewrite /in_mem/mem/=/in_set.
        rewrite asboolT; last done.
        rewrite /f. by destruct s.
Qed. 
