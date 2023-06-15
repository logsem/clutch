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

Section Z5.
  (* Construction of an example val_group. TODO: This needs to be cleaned up. *)
  (* Eval cbn in ((8 * 2) : 'Z_5) == 1. *)

  Context `{!clutchRGS Σ}.

  Definition z5 : finGroupType := [finGroupType of 'Z_5].

  Definition vgval5 (n : z5) : cval := #n.
  Fact vgval_inj5 : Inj eq eq vgval5.
  Proof.
    intros x y h.
    unfold vgval5 in h.
    inversion h as [hh].
    apply ord_inj.
    by apply Nat2Z.inj in hh.
  Qed.

  Instance vg5 : val_group := {| vgG := z5 ; vgval := vgval5 ; vgval_inj := vgval_inj5 |}.



  Definition vunit5 : cval := vgval5 (1%g : vgG).
  Definition vmult5 := (λ:"a" "b",
              if: "a" = #0 then "b" else
                if: "a" = #1 then
                  if: "b" = #0 then #1 else
                  if: "b" = #1 then #2 else
                  if: "b" = #2 then #3 else
                  if: "b" = #3 then #4 else
                  (* if: "b" = #4 then *) #0
                else
                if: "a" = #2 then
                  if: "b" = #0 then #2 else
                  if: "b" = #1 then #3 else
                  if: "b" = #2 then #4 else
                  if: "b" = #3 then #0 else
                  (* if: "b" = #4 then *) #1
                else
                if: "a" = #3 then
                  if: "b" = #0 then #3 else
                  if: "b" = #1 then #4 else
                  if: "b" = #2 then #0 else
                  if: "b" = #3 then #1 else
                  (* if: "b" = #4 then *) #2
                else
                (* if: "a" = #4 then *)
                  if: "b" = #0 then #4 else
                  if: "b" = #1 then #0 else
                  if: "b" = #2 then #1 else
                  if: "b" = #3 then #2 else
                  (* if: "b" = #4 then *) #3
            )%V.

  Definition vmult5' := (λ:"a" "b", ("a" + "b") `rem` #5)%V.
  Definition vinv5 := (λ:"x", if: "x" = #0 then #0 else
                      if: "x" = #1 then #4 else
                        if: "x" = #2 then #3 else
                          if: "x" = #3 then #2 else
                            #1 )%V.

  Definition int_of_vg5 : cval := (λ:"a", "a")%V.

  Definition vg_of_int5 : cval :=
    (λ:"a", if: (#0 ≤ "a") && ("a" < #5) then SOME "a" else NONE)%V.

  Instance cgs5 : clutch_group_struct.
    unshelve eapply ({|
          vunit := vunit5 ;
          vinv := vinv5 ;
          vmult := vmult5 ;
          int_of_vg := int_of_vg5 ;
          vg_of_int := vg_of_int5 ;
          τG := TInt ;
        |}) .
    all: cbv ; tychk.
  Defined.

  Fact Int_of_vg_lrel_G : ⊢ (lrel_G (vg:=vg5) → interp TInt [::])%lrel
                            int_of_vg
                            int_of_vg.
  Proof.
    iModIntro.
    iIntros (??) "(%v&->&->)".
    unfold int_of_vg. simpl. unfold int_of_vg5.
    rel_pures_l. rel_pures_r.
    unfold vgval5.
    rel_values.
  Qed.

  Definition vg5_of_int (x : Z) (vmin : (0 ≤ x)%Z) (vmax : (x < 5)%Z) : z5.
  Proof. unshelve econstructor. 1: exact (Z.to_nat x).
         unfold Zp_trunc. simpl.
         apply /ssrnat.leP. lia.
  Defined.

  Fact Vg_of_int_lrel_G : ⊢ (interp TInt [::] → () + lrel_G (vg:=vg5))%lrel vg_of_int
                            vg_of_int.
  Proof.
    iModIntro.
    iIntros (??) "(%v&->&->)".
    unfold vg_of_int. simpl. unfold vg_of_int5.
    rel_pures_l. rel_pures_r.
    case_bool_decide as vmin ; rel_pures_l ; rel_pures_r.
    2: { rel_values. do 2 iExists _. by iLeft. }
    case_bool_decide as vmax ; rel_pures_l ; rel_pures_r.
    2: { rel_values. do 2 iExists _. by iLeft. }
    rel_values. do 2 iExists _. iRight.
    iModIntro.
    repeat (iSplit ; eauto).
    unshelve iExists (vg5_of_int v _ _) ; eauto.
    simpl. unfold vgval5. unfold vg5_of_int. simpl.
    rewrite Z2Nat.id => //.
  Qed.

  Let τG := @τG cgs5.
  Fact τG_closed' : ∀ Δ, interp τG Δ = interp τG [::].
  Proof. simpl. done. Qed.

  Fact Is_unit : vunit = (1 : vgG).
  Proof. by unfold vunit5. Qed.

  Fact X' : (forall v, (0 <= v)%Z /\ (v < 5)%Z → {v = 0} + {v = 1%nat} + {v = 2} + {v = 3} + {v = 4}).
  Proof.
    intros x [h1 h2].
    destruct x as [|p|p]. all: try lia.
    1: by repeat left.
    destruct p.
    3: do 3 left; by right.
    all: try destruct p ; simpl ; try lia.
    all: try destruct p ; simpl ; try lia.
    - left. by right.
    - by right.
    - do 2 left; by right.
  Qed.

  Fact X : (forall (v : vgG), {vgval_as v = #0} + {vgval_as v = #1} + {vgval_as v = #2} + {vgval_as v = #3} + {vgval_as v = #4})%Z.
  Proof.
    { intros []. unfold vgval_as. unfold vgval. simpl. unfold vgval5. simpl.
      assert (H : (0 <= m)%Z /\ (m < 5)%Z).
      { split. 1: lia.
        unfold Zp_trunc in i. simpl in i.
        move /ssrnat.leP : i => i.
        lia. }
      pose proof (X' _ H) as s.
      repeat destruct s as [s|s].
      all: apply Nat2Z.inj in s.
      all: subst. all: eauto. }
  Qed.

  Fact Y : (forall (v : vgG), {v = inZp 0} + {v = inZp 1%nat} + {v = inZp 2} + {v = inZp 3} + {v = inZp 4}).
  Proof.
    { intros []. unfold vgval_as. unfold vgval. simpl. unfold vgval5. simpl.
      assert (H : (0 <= m)%Z /\ (m < 5)%Z).
      { split. 1: lia.
        unfold Zp_trunc in i. simpl in i.
        move /ssrnat.leP : i => i.
        lia. }
      pose proof (X' _ H) as s.
      repeat destruct s as [s|s].
      all: apply Nat2Z.inj in s.
      all: subst.
      1: repeat left ; by apply val_inj.
      all: unfold Zp_trunc ; simpl.
      - do 3 left. right. by apply val_inj.
      - do 2 left; right. by apply val_inj.
      - left ; right. by apply val_inj.
      - right. by apply val_inj.
    }
  Qed.

  Fact Is_inv : ∀ (x : vgG) Φ,
      True -∗ ▷ (∀ v : vgG, ⌜v = x^-1⌝ -∗ Φ (v : prob_lang.val)) -∗ WP vinv x {{ v, Φ v }}.
  Proof.
      simpl. unfold vinv5.
      intros.
      iIntros "_ hlog".
      pose (Y x) as h.
      all: unfold vgval_as,vgval in h.
      all: simpl in h.
      repeat destruct h as [h|h].
      all: rewrite h ; wp_pures.
      all: match goal with |- context [(|={⊤}=> _ # (LitInt ?vxy))%I] =>
                             set (xy := vxy) end ;
        match type of h with _ = ?rhs => set (vx := rhs) end.
      all: iSpecialize ("hlog" $! (vg5_of_int xy _ _)) => /=.
      Unshelve. all: try (by lia).
      all: iApply "hlog" ; iPureIntro.
      all: apply val_inj.
      all: unfold vg5_of_int.
      all: by compute.
  Qed.

  Fact Is_spec_inv : ∀ (x : vgG) K, refines_right K (vinv x) ={⊤}=∗ refines_right K x^-1.
  Proof.
    intros.
    simpl. unfold vinv5.
    iIntros "h".
    pose (Y x) as h.
    repeat destruct h as [h|h]; rewrite h ;
      tp_pures => // ; simpl ; auto.
    Qed.

  Fact Is_mult : ∀ (x y : vgG) Φ, True
      -∗ ▷ (∀ v : vgG, ⌜v = (x * y)%g⌝ -∗ Φ (v : prob_lang.val))
      -∗ WP vmult x y {{ v, Φ v }}.
  Proof.
      intros.
      iIntros "_ hlog".
      pose (Y x) as h.
      pose (Y y) as hb.
      assert (forall n, let xy := Z.of_nat (div.modn n 5) in
                        (0 ≤ xy)%Z /\ (xy < 5)%Z) as hh.
      { split ; try lia.
        epose proof (@div.ltn_pmod n 5 _) as H ;
          move /ssrnat.leP : H => H.
        lia. }

      repeat destruct h as [h|h].
      all: repeat destruct hb as [hb|hb].
      all: unfold vmult ; iSimpl ; unfold vmult5 ; rewrite h hb ; wp_pures.
      all: unfold vgval5.
      all: simpl ; unfold Zp_trunc ; simpl.
      all: match goal with |- context [ # (LitInt ?vxy)] => set (xy := vxy) end.
      all: match type of h with _ = ?rhs => set (vx := rhs) end ;
        match type of hb with _ = ?rhs => set (vy := rhs) end.
      all: unshelve iSpecialize ("hlog" $! (vg5_of_int xy _ _)).
      all: try apply hh ; eauto.
      all: try by lia.
      all: assert ((_ (vg5_of_int xy _ _) : cval) = (#xy)) as -> by auto;
        iApply "hlog" ; iPureIntro.
      all: apply val_inj ; compute. all: done.
      Unshelve. by compute.
  Qed.

  Fact Is_spec_mult : ∀ (x y : vgG) K,
      refines_right K (vmult x y) ={⊤}=∗ refines_right K (x * y)%g.
  Proof.
    intros. iIntros "hlog".
    pose (Y x) as h.
    pose (Y y) as hb.
    assert (vals_compare_safe x #0) as H.
    { unfold vgval_as, vgval. simpl. auto. }
    repeat destruct h as [h|h] ;
      repeat destruct hb as [hb|hb] => //.
    all: unfold vmult ; simpl ; unfold vmult5 ; rewrite h hb.
    all: tp_pures ; eauto.
  Qed.

  Definition cg5 : clutch_group (cg := cgs5).
    unshelve eapply (
        {| int_of_vg_lrel_G := Int_of_vg_lrel_G
        ; vg_of_int_lrel_G := Vg_of_int_lrel_G
        ; τG_closed := τG_closed'
        ; is_unit := Is_unit
        ; is_inv := Is_inv
        ; is_mult := Is_mult
        ; is_spec_mult := Is_spec_mult
        ; is_spec_inv := Is_spec_inv
        |}).
  Defined.

Definition cgg5 : clutch_group_generator (vg:=vg5).
Proof.
  unshelve econstructor.
  - exact (Zp1 : z5).
  - exact (Zp_trunc (order (Zp1 : z5))).
  - simpl.
    pose proof (order_Zp1 4).
    unfold Zp_trunc.
    rewrite ?H. done.
  - simpl.
    unfold generator.
    rewrite Zp_cycle.
    set (s := (@cycle (Zp_finGroupType (S (Zp_trunc 5))) (@Zp1 (S (Zp_trunc 5))))).
    assert (s = (@cycle z5 (@Zp1 (S (Zp_trunc 5))))) as h by auto.
    rewrite h.
    pose proof (eq_refl s).
    subst s.
    apply Is_true_eq_left. done.
Defined.

End Z5.
