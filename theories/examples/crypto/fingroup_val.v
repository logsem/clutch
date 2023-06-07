From clutch.prelude Require Import base.
From clutch.program_logic Require Import weakestpre.
From clutch.prob_lang Require Import notation lang.
From clutch.rel_logic Require Import model spec_ra.
From clutch.typing Require Import types.
From clutch.examples.crypto Require Import mc_val_instances.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import solvable.cyclic.
From mathcomp Require Import choice.
From mathcomp Require Import eqtype.
From mathcomp Require Import finset.
From mathcomp Require Import fintype.
From mathcomp Require Import seq.
From mathcomp Require ssralg.
From mathcomp Require Import ssrbool.
From mathcomp Require Import ssreflect.
From mathcomp Require Import zmodp.
Import fingroup.
Set Warnings "notation-overridden,ambiguous-paths".
Set Bullet Behavior "Strict Subproofs".

From deriving Require Import deriving.
From deriving Require Import instances.

Local Open Scope group_scope.
Import fingroup.fingroup.
Import prob_lang.

Section val_group.
  (* A decidable predicate on values. *)
  Variable P : {pred val}.
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
  (* Check phant (@sub_sort val (fun x : val => P x) vt). *)
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

Class val_group :=
  Val_group { P : {pred val}
            ; val_group_enum : seq (vt P)
            ; val_group_finite_axiom : Finite.axiom val_group_enum
            ; vgone : vt P
            ; vgmul : vt P -> vt P -> vt P
            ; vginv : vt P -> vt P
            ; val_group_associative : ssrfun.associative vgmul
            ; val_group_left_id : ssrfun.left_id vgone vgmul
            ; val_group_left_inverse : ssrfun.left_inverse vgone vginv vgmul
    }.

Coercion mk_vg (vg : val_group) : finGroupType :=
  vg_finGroup _ _ (@val_group_finite_axiom vg) _ _ _
    (@val_group_associative vg) (@val_group_left_id vg) (@val_group_left_inverse vg).

(* While this commented-out declaration does not trigger a "nonuniform
   inheritance" warning, it unfortunately seems useless, i.e. it does not
   coerce from val_group to val. *)
(* Definition vgval := λ {vg : val_group} (x : vg), `x : val.
   Coercion vgval : val_group >-> Funclass. *)

(* Both of the below seem necessary since there is a subtle difference in the
   domain type DOM, despite DOM being to {x : val | P x} in both cases. *)
#[nonuniform] Coercion vgval_as {vg : val_group}
  (x : FinGroup.arg_sort (FinGroup.base (mk_vg vg))) : val := `x.
#[nonuniform] Coercion vgval_s {vg : val_group}
  (x : FinGroup.sort (FinGroup.base (mk_vg vg))) : val := `x.

Class clutch_group_struct :=
  Clutch_group_struct
    { vunit : val
    ; vinv : val
    ; vmult : val
    ; vexp : val
    ; τG : type
    }.

(* Could push `{clutchRGS Σ} down to the Iris propositions, or move the
   syntactic typing info into the clutch_group_struct. *)
Class clutch_group `{clutchRGS Σ} {vg : val_group} {cg : clutch_group_struct} :=
  Clutch_group
    { τG_closed : forall Δ, interp.interp τG Δ = interp.interp τG []
    ; vmult_typed : val_typed vmult (τG → τG → τG)%ty
    ; vexp_typed : val_typed vexp (τG → TInt → τG)%ty
    ; vall_typed : (∀ (x : vg), ⊢ᵥ x : τG)%ty
    ; vg_log_rel v1 v2 : (⊢ (interp.interp τG [] v1 v2) -∗ ⌜ P v1 /\ P v2 ⌝)%I
    ; is_unit : vunit = 1
    ; is_inv (x : vg) : {{{ True }}} vinv x {{{ v, RET (v : val); ⌜v = x^-1⌝ }}}
    ; is_spec_inv (x : vg) K :
      refines_right K (vinv x) ={⊤}=∗ refines_right K (x^-1)
    ; is_mult (x y : vg) : {{{ True }}} vmult x y {{{ v, RET (v : val); ⌜v = (x * y)%g⌝ }}}
    ; is_spec_mult (x y : vg) K :
      refines_right K (vmult x y) ={⊤}=∗ refines_right K (x * y)
    ; is_exp (b : vg) (x : nat) : {{{ True }}} vexp b #x {{{ v, RET (v : val); ⌜v = b ^+ x⌝ }}}
    ; is_spec_exp (b : vg) (x : nat) K :
      refines_right K (vexp b #x) ={⊤}=∗ refines_right K (b ^+ x)
    }.

#[export] Hint Extern 0 (val_typed _ τG) => apply vall_typed : core.

Definition vg_of_cg := λ {Σ HΣ} vg cg (G : @clutch_group Σ HΣ vg cg), vg.
Coercion vg_of_cg : clutch_group >-> val_group.

(* vg is generated by g. We further include the assumption that vg is
   nontrivial, i.e. of size at least 2, since this allows us to work with
   mathcomp's 'Z_p type of integers modulo p (taking p := #[g]). *)
Class clutch_group_generator {vg : val_group} :=
  Clutch_group_generator
    { g : vg
    ; n'' : nat
    ; g_nontriv : #[g] = S (S n'')
    ; g_generator : generator [set: vg] g
    }.

Section Z5.
  (* Construction of an example val_group. TODO: This needs to be cleaned up. *)
  (* Eval cbn in ((8 * 2) : 'Z_5) == 1. *)

  Context `{!clutchRGS Σ}.

  Definition z5 : finGroupType := [finGroupType of 'Z_5].

  Definition p : {pred val} :=
    (λ x, match x with #(LitInt n) => (Z.leb 0 n) && (Z.ltb n 5) | _ => false end).
  Definition p' : {pred val} :=
    (λ x, match x with #(LitInt n) => true | _ => false end).

  Class PVAL (v : val) := in_P : (p v).
  Fact P_PVAL (v : val) : PVAL v -> p v.
  Proof. rewrite /PVAL. move => h. exact h. Qed.
  Definition mkP (v : val) {h : PVAL v} : vt p.
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

  Definition g5 : val_group.
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
  Definition gg := mk_vg g5.

  Section test.
    Set Warnings "-notation-overridden,-ambiguous-paths".
    Import ssralg.
    Set Warnings "notation-overridden,ambiguous-paths".
    Eval compute in ((vt_of_zp 8 * (vt_of_zp 2))%g : gg)%g == vt_of_zp 1.
    Eval cbn in ((8 * 2) : 'Z_5) == 1.
  End test.

End Z5.
