From clutch Require Import clutch.

From mathcomp Require ssrnat.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import fingroup solvable.cyclic choice eqtype finset
  fintype seq ssrbool zmodp.
Set Warnings "notation-overridden,ambiguous-paths".

From clutch.examples.crypto Require Import fingroup_val_inj.

Local Open Scope group_scope.
Import fingroup.fingroup.

#[local] Definition cval := prob_lang.val.

Set Default Proof Using "Type*".
Set Bullet Behavior "Strict Subproofs".

Section Z_p.

  Context `{!clutchRGS Σ}.
  Context (p'' : nat).
  Notation p := (S (S p'')).

  Definition z_p : finGroupType := [finGroupType of 'Z_p].

  Definition vgval_p (n : z_p) : cval := #n.
  Fact vgval_inj_p : Inj eq eq vgval_p.
  Proof.
    intros x y h.
    unfold vgval in h.
    inversion h as [hh].
    apply ord_inj.
    by apply Nat2Z.inj in hh.
  Qed.

  Instance vg_p : val_group :=
    {| vgG := z_p
    ; vgval := vgval_p
    ; vgval_inj := vgval_inj_p |}.

  Definition vunit_p : cval := vgval (1%g : vgG).
  Definition vmult_p := (λ:"a" "b", ("a" + "b") `rem` #p)%V.
  Definition vinv_p := (λ:"x", (#p - "x") `rem` #p)%V.

  Definition int_of_vg_p : cval := (λ:"a", "a")%V.

  Definition vg_of_int_p : cval :=
    (λ:"a", if: (#0 ≤ "a") && ("a" < #p) then SOME "a" else NONE)%V.

  Instance cgs_p : clutch_group_struct.
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

  Fact int_of_vg_lrel_G_p : ⊢ (lrel_G (vg:=vg_p) → interp TInt [::])%lrel
                            int_of_vg
                            int_of_vg.
  Proof.
    iModIntro.
    iIntros (??) "(%v&->&->)".
    unfold int_of_vg. simpl. unfold int_of_vg_p.
    rel_pures_l. rel_pures_r.
    unfold vgval_p. simpl.
    rel_values.
  Qed.

  Definition vg_of_int_unpacked (x : Z) (vmin : (0 ≤ x)%Z) (vmax : (x < p)%Z) : z_p.
  Proof. unshelve econstructor. 1: exact (Z.to_nat x).
         unfold Zp_trunc. simpl.
         apply /ssrnat.leP. lia.
  Defined.

  Fact vg_of_int_lrel_G_p : ⊢ (interp TInt [::] → () + lrel_G (vg:=vg_p))%lrel vg_of_int
                            vg_of_int.
  Proof.
    iModIntro.
    iIntros (??) "(%v&->&->)".
    unfold vg_of_int. simpl. unfold vg_of_int_p.
    rel_pures_l. rel_pures_r.
    case_bool_decide as vmin ; rel_pures_l ; rel_pures_r.
    2: { rel_values. do 2 iExists _. by iLeft. }
    case_bool_decide as vmax ; rel_pures_l ; rel_pures_r.
    2: { rel_values. do 2 iExists _. by iLeft. }
    rel_values. do 2 iExists _. iRight.
    iModIntro.
    repeat (iSplit ; eauto).
    unshelve iExists (vg_of_int_unpacked v _ _) ; eauto.
    simpl. unfold vgval_p. unfold vg_of_int_unpacked. simpl.
    rewrite Z2Nat.id => //.
  Qed.

  Let τG := @τG cgs_p.
  Fact τG_closed_p : ∀ Δ, interp τG Δ = interp τG [::].
  Proof. simpl. done. Qed.

  Fact is_unit_p : vunit = (1 : vgG).
  Proof. by unfold vunit_p. Qed.

  Fact rem_modn : ∀ x : 'Z_p, ((p - x) `rem` p)%Z = div.modn (ssrnat.subn p x) p.
  Proof.
    intros.
    rewrite -ssrnat.minusE.
    destruct x. simpl.
    unfold Zp_trunc in i. simpl in i.
    pose proof i as i'.
    move /ssrnat.leP : i => i.
    pose i as l.
    assert (0 < p - m) by lia.
    assert (0 <= p - m) by lia.
    apply Nat2Z.inj_le in l.
    rewrite Z.rem_mod => //.
    replace (Z.sgn (p - m)) with 1%Z by lia.
    replace (Z.abs (p - m)) with (p - m)%Z by lia.
    replace (Z.abs p)%Z with (p : Z) by lia.
    rewrite Z.mul_1_l.
    rewrite -Nat2Z.inj_sub ; [|lia].
    rewrite -Nat2Z.inj_mod.
    (* rewrite Nat2Z.id. *)
    destruct m eqn:hm.
    { replace (p-0) with p by lia.
      rewrite div.modnn.
      by rewrite Nat.mod_same. }
    assert (p - m < p) by lia.
    rewrite div.modn_small => //.
    2: apply /ssrnat.leP ; lia.
    rewrite Nat.mod_small ; lia.
  Qed.

  Fact zp_rem_pos : ∀ x : 'Z_p, let xy := ((p - x) `rem` p)%Z in (0 ≤ xy)%Z.
  Proof.
    intros.
    destruct x. simpl.
    unfold Zp_trunc in i. simpl in i.
    subst xy.
    simpl.
    move /ssrnat.leP : i => i.
    pose i.
    assert (0 < p - m) by lia.
    assert (0 <= p - m) by lia.
    apply Nat2Z.inj_le in l.
    apply Z.rem_nonneg ; lia.
  Qed.

  Fact zp_rem_bound : ∀ x : 'Z_p, let xy := ((p - x) `rem` p)%Z in (xy < p)%Z.
  Proof.
    destruct x ; simpl ; unfold Zp_trunc in i ; simpl in i.
    move /ssrnat.leP : i => i.
    apply Z.rem_bound_pos ; lia.
  Qed.

  Fact is_inv_p : ∀ (x : vgG) Φ,
      True -∗ ▷ (∀ v : vgG, ⌜v = x^-1⌝ -∗ Φ (v : prob_lang.val)) -∗ WP vinv x {{ v, Φ v }}.
  Proof.
      simpl. unfold vinv_p.
      intros.
      iIntros "_ hlog".
      wp_pures.
      unfold vgval_p.
      match goal with |- context [ # (LitInt ?vxy)] => set (xy := vxy) end.
      iSpecialize ("hlog" $! (vg_of_int_unpacked xy (zp_rem_pos _) (zp_rem_bound _))).
      simpl.
      rewrite Z2Nat.id. 2: apply zp_rem_pos.
      iApply "hlog".
      iPureIntro.
      apply val_inj.
      unfold vg_of_int_unpacked, Zp_trunc ; simpl.
      subst xy.
      rewrite rem_modn.
      by rewrite Nat2Z.id.
  Qed.

  Fact is_spec_inv_p : ∀ (x : vgG) K, refines_right K (vinv x) ={⊤}=∗ refines_right K x^-1.
  Proof.
    intros.
    simpl. unfold vinv_p.
    iIntros "h".
    tp_pures => // ; simpl ; auto.
    unfold vgval_p.
    assert (((p - x) `rem` p)%Z = x^-1) as ->.
    2: done.
    simpl. unfold Zp_trunc.
    simpl. apply rem_modn.
  Qed.

  Fact rem_modn' : ∀ x : nat, (x `rem` p)%Z = div.modn x p.
  Proof.
    intros.
    assert (0 <= x) by lia.
    rewrite Z.rem_mod => //.
    destruct x as [|n] eqn:hx.
    { replace (p-0) with p by lia.
      rewrite div.mod0n.
      simpl.
      rewrite Z.mul_0_l. done.
    }
    rewrite -hx.
    replace (Z.sgn x) with 1%Z by lia.
    replace (Z.abs x) with (x : Z) by lia.
    replace (Z.abs p)%Z with (p : Z) by lia.
    rewrite Z.mul_1_l.
    rewrite -Nat2Z.inj_mod.
    f_equal.
    rewrite {2}(PeanoNat.Nat.div_mod_eq x p).
    set (q := x `div` p).
    set (r := x `mod` p).
    rewrite ssrnat.plusE.
    rewrite ssrnat.multE.
    rewrite ssrnat.mulnC.
    rewrite div.modnMDl.
    rewrite div.modn_small ; [reflexivity|].
    assert (r < p) by by apply PeanoNat.Nat.mod_upper_bound.
    apply /ssrnat.leP. done.
  Qed.

  Fact zp_rem_bound' : (forall n : nat, 0 ≤ (n `rem` p)%Z < p)%Z.
  Proof.
    intros.
    rewrite Z.rem_mod => //.
    destruct n; [lia|].
    replace (Z.sgn (S n)) with 1%Z by lia.
    replace (Z.abs (S n)) with ((S n) : Z) by lia.
    replace (Z.abs p)%Z with (p : Z) by lia.
    rewrite Z.mul_1_l.
    rewrite -Nat2Z.inj_mod.
    rewrite Z2Nat.inj_le ; try lia.
    rewrite Nat2Z.id.
    split ; try lia.
    rewrite Z2Nat.inj_lt ; try lia.
    rewrite ?Nat2Z.id.
    apply Nat.mod_upper_bound. done.
  Qed.

  Fact is_mult_p : ∀ (x y : vgG) Φ, True
      -∗ ▷ (∀ v : vgG, ⌜v = (x * y)%g⌝ -∗ Φ (v : prob_lang.val))
      -∗ WP vmult x y {{ v, Φ v }}.
  Proof.
    intros.
    iIntros "_ hlog".
    unfold vmult ; iSimpl ; unfold vmult_p ; wp_pures.
    simpl ; unfold Zp_trunc ; simpl.
    unfold vgval_p ; simpl.
    match goal with |- context [ # (LitInt ?vxy)] => set (xy := vxy) end.
    destruct (zp_rem_bound' (x+y)) as [h1 h2].
    rewrite Nat2Z.inj_add in h1.
    rewrite Nat2Z.inj_add in h2.
    unshelve iSpecialize ("hlog" $! (vg_of_int_unpacked xy _ _)).
    1,2: eauto.
    assert ((# (LitInt (_ (_ (vg_of_int_unpacked xy _ _))))) = (#xy)) as ->.
    1: subst xy ; simpl. 1: do 2 f_equal.
    1: rewrite Z2Nat.id => //.
    iApply "hlog" ; iPureIntro.
    apply val_inj.
    unfold vg_of_int_unpacked. subst xy ; simpl.
    destruct x, y. simpl.
    rewrite -Nat2Z.inj_add.
    rewrite rem_modn'.
    rewrite -ssrnat.plusE.
    rewrite Nat2Z.id => //.
  Qed.

  Fact is_spec_mult_p : ∀ (x y : vgG) K,
      refines_right K (vmult x y) ={⊤}=∗ refines_right K (x * y)%g.
  Proof.
    intros. iIntros "hlog".
    unfold vmult ; iSimpl ; unfold vmult_p ; tp_pures.
    simpl ; unfold Zp_trunc ; simpl.
    unfold vgval_p, vmult_p ; simpl ; tp_pures.

    assert (#(div.modn _ p) = #((x + y) `rem` p)) as -> => //.
    repeat f_equal.
    rewrite -Nat2Z.inj_add.
    rewrite rem_modn'.
    rewrite -ssrnat.plusE. done.
  Qed.

  Definition cg_p : clutch_group (cg := cgs_p).
    unshelve eapply (
        {| int_of_vg_lrel_G := int_of_vg_lrel_G_p
        ; vg_of_int_lrel_G := vg_of_int_lrel_G_p
        ; τG_closed := τG_closed_p
        ; is_unit := is_unit_p
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
  - exact (Zp_trunc (order (Zp1 : z_p))).
  - simpl.
    pose proof (order_Zp1 (S p'')).
    unfold Zp_trunc.
    rewrite ?H. done.
  - simpl.
    unfold generator.
    rewrite Zp_cycle.
    apply Is_true_eq_left.
    apply eq_refl.
Defined.

End Z_p.
