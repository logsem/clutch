From clutch Require Import clutch.

Set Warnings "-hiding-delimiting-key,-overwriting-delimiting-key".
From mathcomp Require Import ssrnat.
Set Warnings "hiding-delimiting-key,overwriting-delimiting-key".
From mathcomp Require Import fingroup solvable.cyclic eqtype fintype ssrbool zmodp.

From clutch.prelude Require Import mc_stdlib.
From clutch.examples.crypto Require Import valgroup.

Local Open Scope group_scope.
Import fingroup.fingroup.

Set Default Proof Using "Type*".
Set Bullet Behavior "Strict Subproofs".

Section Z_p.

  Context (p'' : nat).
  Notation p := (S (S p'')).

  #[local] Definition cval := prob_lang.val.
  Definition z_p : finGroupType := [finGroupType of 'Z_p].

  Definition vgval_p (n : z_p) : cval := #n.
  Fact vgval_inj_p : Inj eq eq vgval_p.
  Proof. intros x y h. inversion h as [hh]. by apply ord_inj, Nat2Z.inj. Qed.

  Instance vg_p : val_group :=
    {| vgG := z_p
    ; vgval := vgval_p
    ; vgval_inj := vgval_inj_p |}.

  Definition vunit_p : cval := vgval (1%g : vgG).
  Definition vmult_p := (λ:"a" "b", ("a" + "b") `rem` #p)%V.
  Definition vinv_p := (λ:"x", (#p - "x") `rem` #p)%V.

  Definition int_of_vg_p := (λ:"a", "a")%V.
  Definition vg_of_int_p :=
    (λ:"a", if: (#0 ≤ "a") && ("a" < #p) then SOME "a" else NONE)%V.

  Instance cgs_p : clutch_group_struct.
  Proof using p''.
    unshelve eapply ({|
          vunit := vunit_p ;
          vinv := vinv_p ;
          vmult := vmult_p ;
          int_of_vg := int_of_vg_p ;
          vg_of_int := vg_of_int_p ;
          τG := TInt ;
        |}) .
    all: cbv ; tychk.
  Defined.

  Import valgroup_tactics.
  Context `{!clutchRGS Σ}.

  Fact int_of_vg_lrel_G_p :
    ⊢ (lrel_G (vg:=vg_p) → lrel_int)%lrel int_of_vg int_of_vg.
  Proof with rel_pures.
    iIntros "!>" (??) "(%v&->&->)".
    unfold int_of_vg, cgs_p, int_of_vg_p... rel_vals.
  Qed.

  Definition vg_of_int_unpacked (x : Z) (vmin : (0 ≤ x)%Z) (vmax : (x < p)%Z) : z_p.
  Proof. exists (Z.to_nat x). rewrite Zp_cast //. apply /leP. lia.
  Defined.

  Fact vg_of_int_lrel_G_p :
    ⊢ (lrel_int → () + lrel_G (vg:=vg_p))%lrel vg_of_int vg_of_int.
  Proof with rel_pures.
    iIntros "!>" (??) "(%v&->&->)". unfold vg_of_int, cgs_p, vg_of_int_p...
    case_bool_decide as vmin ; rel_pures ; [case_bool_decide as vmax|]...
    all: rel_vals.
    unshelve iExists (vg_of_int_unpacked v vmin vmax) => /=.
    rewrite /vgval_p Z2Nat.id //.
  Qed.

  Fact is_inv_p (x : vgG) : ⊢ WP vinv x {{ λ (v : cval), ⌜v = x^-1⌝ }}.
  Proof.
    simpl. unfold vinv_p, vgval_p. cbn -[Zp_opp]. wp_pures.
    rewrite /Zp_trunc -(Nat2Z.inj_sub _ _ (leq_zmodp _ _)). simpl.
    by rewrite rem_modn.
  Qed.

  Fact is_spec_inv_p (x : vgG) K : refines_right K (vinv x) ⊢ |={⊤}=> refines_right K x^-1.
  Proof.
    iIntros => /=. unfold vinv_p, vgval_p. tp_pures => /=.
    rewrite /Zp_trunc -(Nat2Z.inj_sub _ _ (leq_zmodp _ _)) => /=.
    by rewrite rem_modn.
  Qed.

  Fact is_mult_p (x y : vgG) : ⊢ WP vmult x y {{ λ (v : cval), ⌜v = (x * y)%g⌝ }}.
  Proof.
    rewrite /vmult /= /vmult_p /vgval_p /=. wp_pures.
    by rewrite -Nat2Z.inj_add rem_modn // -ssrnat.plusE.
  Qed.

  Fact is_spec_mult_p (x y : vgG) K :
    refines_right K (vmult x y) ⊢ |={⊤}=> refines_right K (x * y)%g.
  Proof.
    iIntros. rewrite /vmult /cgs_p /vmult_p /= /vgval_p. tp_pures => /=.
    by rewrite -Nat2Z.inj_add -ssrnat.plusE rem_modn.
  Qed.

  Fact τG_subtype_p v1 v2 Δ : lrel_G v1 v2 ⊢ interp τG Δ v1 v2.
  Proof. iIntros ((w&->&->)). iExists _. eauto. Qed.

  Definition cg_p : clutch_group (cg := cgs_p).
    unshelve eapply (
        {| int_of_vg_lrel_G := int_of_vg_lrel_G_p
        ; vg_of_int_lrel_G := vg_of_int_lrel_G_p
        ; τG_subtype := τG_subtype_p
        ; is_unit := Logic.eq_refl
        ; is_inv := is_inv_p
        ; is_mult := is_mult_p
        ; is_spec_mult := is_spec_mult_p
        ; is_spec_inv := is_spec_inv_p
        |}).
  Defined.

  Definition cgg_p : clutch_group_generator (vg:=vg_p).
  Proof.
    unshelve econstructor.
    - exact (Zp1 : z_p).
    - exact (Zp_trunc #[Zp1 : z_p]).
    - by rewrite ?(order_Zp1 (S p'')).
    - rewrite /= /generator.
      rewrite Zp_cycle. apply Is_true_eq_left. apply eq_refl.
  Defined.

End Z_p.
