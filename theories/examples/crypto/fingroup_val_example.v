From clutch Require Import clutch.

From mathcomp Require ssrnat.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import fingroup solvable.cyclic choice eqtype finset
  fintype seq ssrbool zmodp.
Set Warnings "notation-overridden,ambiguous-paths".

From clutch.examples.crypto Require Import fingroup_val.

Local Open Scope group_scope.
Import fingroup.fingroup.
Import prob_lang.

Set Default Proof Using "Type*".
Set Bullet Behavior "Strict Subproofs".

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
