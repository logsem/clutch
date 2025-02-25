(* TODO cleanup imports *)
Set Warnings "-hiding-delimiting-key".
From HB Require Import structures.
From Coq Require Import Logic.ClassicalEpsilon Psatz.
From stdpp Require Import base numbers binders strings gmap.
From mathcomp Require Import functions.
From mathcomp.analysis Require Import reals measure itv lebesgue_measure probability.
From mathcomp Require Import ssrbool all_algebra eqtype choice boolp fintype.
From iris.algebra Require Export ofe.
From clutch.prelude Require Export stdpp_ext.
From clutch.common Require Export locations.
From clutch.meas_lang Require Import ectxi_language ectx_language.
From Coq Require Export Reals.
From clutch.prob.monad Require Export giry.
From mathcomp.analysis Require Export Rstruct.
From mathcomp Require Import classical_sets.
Import Coq.Logic.FunctionalExtensionality.
From clutch.prelude Require Import classical.
From clutch.meas_lang.lang Require Export prelude types constructors shapes cover projections tapes state.
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

(* Alternatively, prove something like "subst respects the shapes of shape_subst"? *)



Lemma substU_measurable (b : string) : measurable_fun setT (substU b).
Proof.
  (* Suffices to prove the preimage of all lifted shapes are measurable *)
  eapply measurability; [by eauto|].
  simpl.
  move=> S.
  rewrite /preimage_class.
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

Admitted.


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
    + (* Function restrited to this set the substU'*)
      admit.
    + (* Function restrited to this set the identity *)
      admit.
Admitted.
