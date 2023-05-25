From stdpp Require Import namespaces.
From clutch.prob_lang Require Import spec_ra notation proofmode primitive_laws lang spec_tactics.
From clutch.logrel Require Import model rel_rules rel_tactics adequacy.

(* From clutch.typing Require Import types contextual_refinement soundness. *)
From clutch.prelude Require Import base.
From clutch.program_logic Require Import weakestpre.
Set Default Proof Using "Type*".


Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require all_ssreflect all_algebra
  fingroup.fingroup
  solvable.cyclic
  prime ssrnat
  ssreflect ssrfun ssrbool ssrnum
  eqtype choice
  seq.

  (* Most of all_ssreflect and all_algebra except where the notations
     clash with stdpp. *)
From mathcomp Require Import bigop.
From mathcomp Require Import binomial.
From mathcomp Require Import choice.
From mathcomp Require Import countalg.
From mathcomp Require Import div.
From mathcomp Require Import eqtype.
From mathcomp Require Import finalg.
From mathcomp Require Import finfun.
From mathcomp Require Import fingraph.
From mathcomp Require Import finset.
From mathcomp Require Import fintype.
From mathcomp Require Import fraction.
From mathcomp Require Import generic_quotient.
From mathcomp Require Import intdiv.
From mathcomp Require Import interval.
From mathcomp Require Import matrix.
From mathcomp Require Import mxalgebra.
From mathcomp Require Import mxpoly.
From mathcomp Require Import order.
From mathcomp Require Import path.
From mathcomp Require Import polyXY.
From mathcomp Require Import polydiv.
From mathcomp Require Import prime.
From mathcomp Require Import rat.
From mathcomp Require Import ring_quotient.
From mathcomp Require Import seq.
From mathcomp Require Import ssrAC.
From mathcomp Require Import ssralg.
From mathcomp Require Import ssrbool.
From mathcomp Require Import ssreflect.
(* From mathcomp Require Import poly. *)
(* From mathcomp Require Import ssrfun. *)
From mathcomp Require Import ssrint.
(* From mathcomp Require Import ssrnat. *)
From mathcomp Require Import ssrnum.
From mathcomp Require Import tuple.
From mathcomp Require Import vector.
From mathcomp Require Import zmodp.
Import fingroup.
Import solvable.cyclic.
Set Warnings "notation-overridden,ambiguous-paths".

From deriving Require Import deriving.
From deriving Require Import instances.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From clutch Require Import val_instances.

Section val_group.
  (* A decidable predicate on values. *)
  Variable P : {pred prob_lang.val}.
  (* The subtype of values satisfying P. *)
  Definition vt := sig_subType P.
  (* An enumeration of [vt]... *)
  Variable e : seq vt.
  (* ...in which every element of [vt] appears exactly once. *)
  Variable h_enum : Finite.axiom e.

  Definition vt_finMixin := FinMixin h_enum.
  Canonical vt_finType := Eval hnf in FinType vt vt_finMixin.
  (* Not sure why it doesn't find the finType instance vt_finType. *)
  (* Fail Check [finType of vt]. *)

  Canonical vt_subFinType : subFinType P :=
    Eval hnf in SubFinType (T:=val_choiceType) (subFin_sort:=vt) vt_finMixin.

  (* Now it works. Oh well. *)
  (* Check [finType of vt]. *)

  (* Check {set vt}. *)
  (* Check (@FinGroup.PackBase vt). *)
  (* Check (@FinGroup.mixin_of vt). *)
  (* Check phant (@sub_sort prob_lang.val (fun x : prob_lang.val => P x) vt). *)
  (* Check phant (FinGroup.arg_sort (FinGroup.base _)). *)
  (* Let's spell out the details of assuming we have a group structure. *)
  (* Variable vt_finGroupMixin : FinGroup.mixin_of vt. *)

Variables (one : vt) (mul : vt -> vt -> vt) (inv : vt -> vt).

Hypothesis mulA : ssrfun.associative mul.
Hypothesis mul1 : ssrfun.left_id one mul.
Hypothesis mulV : ssrfun.left_inverse one inv mul.

  Canonical vg_BaseFinGroupType := BaseFinGroupType _ (FinGroup.Mixin mulA mul1 mulV).
  Canonical vg_finGroup : finGroupType := FinGroupType mulV.

  (* Canonical vg := Eval hnf in BaseFinGroupType _ vt_finGroupMixin. *)
End val_group.

Section mk_vg.
  Record val_group :=
    Val_group { P : {pred prob_lang.val}
              ; val_group_enum : seq (vt P)
              ; val_group_finite_axiom : Finite.axiom val_group_enum
              ; vone : vt P
              ; vmul : vt P -> vt P -> vt P
              ; vinv : vt P -> vt P
              ; val_group_associative : ssrfun.associative vmul
              ; val_group_left_id : ssrfun.left_id vone vmul
              ; val_group_left_inverse : ssrfun.left_inverse vone vinv vmul
      }.

  Definition mk_vg (x : val_group) : finGroupType :=
    vg_finGroup _ _ (val_group_finite_axiom x) _ _ _
      (val_group_associative x) (val_group_left_id x) (val_group_left_inverse x).

End mk_vg.

Section EGroup.
  Local Open Scope group_scope.
  (* Import fingroup.GroupScope *)

  Context `{!clutchRGS Σ}.

  Variable x : val_group.
  Let g := mk_vg x.
  Let vt := vt (P x).

  Definition is_id (e : g) := e = 1.

  Definition ζ : {set g} := [set : g].

  Coercion gval := (λ x, `x) : g → prob_lang.val.
  (* Coercion vvt := (λ x, `x) : vt → prob_lang.val. *)

  Definition is_inv (i : prob_lang.val) := ∀ (x : g),
    {{{ True }}}
      i x
    {{{ v, RET v;
        ⌜v = gval (x ^-1)⌝ }}}.

  Definition is_mul (m : prob_lang.val) := ∀ (x y : g),
    {{{ True }}}
      m x y
    {{{ v, RET v; ⌜v = gval (x * y)⌝ }}}.

  Definition is_exp (eexp : prob_lang.val) := ∀ (b : g) (x : nat),
      {{{ True }}}
        eexp b (#x)
        {{{ v, RET v; ⌜v = gval (b ^+ x)%g⌝ }}}.

  Definition is_spec_exp (eexp : prob_lang.val) := ∀ (b : g) (x : nat),
    ∀ K, refines_right K (eexp b (#x))
         ={⊤}=∗
                refines_right K (gval (b ^+ x)%g).
End EGroup.

Section Z5.


  (* Eval cbn in ((8 * 2) : 'Z_5) == 1. *)

  Context `{!clutchRGS Σ}.

  Definition z5 : finGroupType := [finGroupType of 'Z_5].

  Definition p : {pred prob_lang.val} :=
    (λ x, match x with #(LitInt n) => (Z.leb 0 n) && (Z.ltb n 5) | _ => false end).
  Definition p' : {pred prob_lang.val} :=
    (λ x, match x with #(LitInt n) => true | _ => false end).

  Class PVAL (v : prob_lang.val) := in_P : (p v).
  Fact P_PVAL (v : prob_lang.val) : PVAL v -> p v.
  Proof. rewrite /PVAL. move => h. exact h. Qed.
  Definition mkP (v : prob_lang.val) {h : PVAL v} : vt p.
    unfold PVAL in h.
    unshelve econstructor ; [exact v |].
    by apply Is_true_eq_true in h.
  Defined.

  Hint Extern 4 (PVAL ?n) =>
         (unfold P ; cbn ; exact I)
         : typeclass_instances.

  Definition vtp := (vt p).
  Definition zp_of_vt : vtp -> z5.
  Proof.
    intros. destruct X. unfold p in i.
    destruct x ; try by inversion i.
    destruct l ; try (exfalso ; by inversion i).
    unfold z5. simpl.
    Local Open Scope ring_scope.
    exact (inZp (Z.abs_nat n)).
  Defined.
  Coercion zp_of_vt_coe := zp_of_vt : vtp -> z5.
  Coercion zp_of_vt' := zp_of_vt_coe : vtp -> Z.
  Definition vt_of_zp (n : z5) : vt p.
  Proof.
  unfold z5 in n. destruct n.
  exists (#(Z.of_nat m)). unfold p. apply /andP.
  split.
  - apply /Z.leb_spec0.
    apply Nat2Z.is_nonneg.
  - apply /Z.ltb_spec0.
    move /ssrnat.leP in i.
    unfold Zp_trunc in i. simpl in i. lia.
  Defined.
  Coercion vt_of_zp_coe := vt_of_zp : z5 -> vtp.

  Hypothesis zp_vt_C : forall x, zp_of_vt (vt_of_zp x) = x.
  Hypothesis vt_zp_C : forall x, vt_of_zp (zp_of_vt x) = x.

  Definition g : val_group.
    unshelve econstructor.
    - exact p.
    - exact [:: mkP #0 ; mkP #1 ; mkP #2 ; mkP #3 ; mkP #4 ].
    - exact (vt_of_zp 1%g).
    - exact (λ (x y : vt p), vt_of_zp ((zp_of_vt x) * (zp_of_vt y)))%g.
    - exact (λ (x : vt p), vt_of_zp ((zp_of_vt x) ^-1))%g.
    - unfold Finite.axiom.
      intros x.
      destruct x.
      unfold p in i ; destruct x ; try by inversion i.
      destruct l ; try by inversion i.
      destruct n ; try by inversion i.
      repeat (destruct p0 ; try by simpl).
    - intros x y z.
      f_equal.
      rewrite ?zp_vt_C.
      by rewrite mulgA.
    - intros x. rewrite ?zp_vt_C. rewrite mul1g. by rewrite vt_zp_C.
    - intros x. rewrite zp_vt_C. f_equal.
      by rewrite mulVg.
  Defined.

  Definition gg := mk_vg g.
  Eval compute in ((vt_of_zp 8 * (vt_of_zp 2))%g : gg)%g == vt_of_zp 1.
  Eval cbn in ((8 * 2) : 'Z_5) == 1.

End Z5.
