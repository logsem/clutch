From clutch Require Import clutch.

From mathcomp Require ssrnat.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import fingroup solvable.cyclic choice eqtype finset
  fintype seq ssrbool zmodp.
Set Warnings "notation-overridden,ambiguous-paths".

From clutch.examples.crypto Require Import fingroup_val.

Local Open Scope group_scope.
Import fingroup.fingroup.

Let cval := prob_lang.val.

Set Default Proof Using "Type*".
Set Bullet Behavior "Strict Subproofs".

Section Z5.
  (* Construction of an example val_group. TODO: This needs to be cleaned up. *)
  (* Eval cbn in ((8 * 2) : 'Z_5) == 1. *)

  Context `{!clutchRGS Σ}.

  Definition z5 : finGroupType := [finGroupType of 'Z_5].

  Definition p : {pred cval} :=
    (λ x, match x with #(LitInt n) => (Z.leb 0 n) && (Z.ltb n 5) | _ => false end).

  Class PVAL (v : cval) := in_P : (p v).
  Fact P_PVAL (v : cval) : PVAL v -> p v.
  Proof. rewrite /PVAL. move => h. exact h. Qed.
  Definition mkP (v : cval) {h : PVAL v} : vt p.
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
    exact (inZp (Z.to_nat n)).
  Defined.

  Coercion zp_of_vt_coe := zp_of_vt : vtp -> z5.
  Coercion zp_of_vt' := zp_of_vt_coe : vtp -> Z.

  Definition vt_of_zp (n : z5) : vt p.
  Proof.
    unfold z5 in n. destruct n as [m i].
    exists (#(Z.of_nat m)). unfold p. apply /andP.
    split.
    - apply /Z.leb_spec0.
      apply Nat2Z.is_nonneg.
    - apply /Z.ltb_spec0.
      move /ssrnat.leP in i.
      unfold Zp_trunc in i. simpl in i. lia.
  Defined.
  Coercion vt_of_zp_coe := vt_of_zp : z5 -> vtp.

  Lemma zp_vt_C : forall x, zp_of_vt (vt_of_zp x) = x.
  Proof.
    intros. unfold vt_of_zp. destruct x. simpl.
    rewrite Nat2Z.id.
    eapply val_inj. simpl.
    rewrite div.modn_small => //.
  Qed.

  Lemma vt_zp_C : forall x, vt_of_zp (zp_of_vt x) = x.
  Proof.
    intros [x i] => /=.
    destruct x ; try by inversion i.
    destruct l ; try by inversion i.
    apply val_inj => /=.
    do 2 f_equal.
    unfold p in i.
    move /andP : i => [i1 i2].
    rewrite div.modn_small => //.
    1: by apply Z2Nat.id, Z.leb_le.
    apply /ssrnat.leP.
    unfold Zp_trunc. simpl.
    move /Z.ltb_spec0 : i2 => i2.
    lia.
  Qed.

  Definition vg5 : val_group.
    unshelve econstructor.
    - exact p.
    - exact [:: mkP #0 ; mkP #1 ; mkP #2 ; mkP #3 ; mkP #4].
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
  Definition gg := mk_vg vg5.

  Section test.
    Set Warnings "-notation-overridden,-ambiguous-paths".
    Import ssralg.
    Set Warnings "notation-overridden,ambiguous-paths".
    Eval compute in ((vt_of_zp 8 * (vt_of_zp 2))%g : gg)%g == vt_of_zp 1.
    Eval cbn in ((8 * 2) : z5) == 1.

    Check (zp_of_vt (vt_of_zp 1))%g.
    Eval compute in (zp_of_vt (vt_of_zp 6))%g.
    Eval compute in (6 : z5)%g.
    Eval compute in (zp_of_vt (vt_of_zp 8))%g == (8 : z5).
    Definition val_of_vtp (x : vtp) : cval := `x.
    From clutch.examples.crypto Require Import mc_val_instances.
    Eval compute in (val_of_vtp (vt_of_zp (zp_of_vt (mkP #4))%g)) == (val_of_vtp (mkP #4 : vtp) : cval).
    Goal forall x y, val_of_vtp x = val_of_vtp y → x = y.
    Proof.
      intros.
      eapply val_inj.
      simpl.
      unfold val_of_vtp in H. done.
    Qed.
    Eval compute in (val (vt_of_zp (zp_of_vt (mkP #4))%g)) == (val (mkP #4 : vtp)).
    Eval compute in val ((1 ^-1)%g : gg).
    Eval compute in val (((mkP (#2)%V) ^-1)%g : gg).
    Eval compute in val ((mulg (mkP (#3)%V : gg) (mkP (#4)%V : gg))%g : gg).
    Eval compute in val ((expgn (mkP (#3)%V : gg) 0)%g : gg).
    Eval compute in val ((mulg (3 : z5) 3)%g : z5).
  End test.

  Definition vunit5 := (val (1%g : vg5)).
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
    destruct v. simpl. unfold P in i; simpl in i; unfold p in i.
    destruct x ; inversion i. destruct l ; inversion i.
    rel_values.
  Qed.

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
    assert (p #v) as Pv.
    {
      apply /andb_prop_intro.
      unfold p.
      split.
      - rewrite -Z.leb_le in vmin. unfold Is_true. rewrite vmin. done.
      - rewrite -Z.ltb_lt in vmax. unfold Is_true. rewrite vmax. done.
    }
    iExists (@mkP #v Pv). simpl. done.
  Qed.

  Let τG := @τG cgs5.
  Fact τG_closed' : ∀ Δ, interp τG Δ = interp τG [::].
  Proof. simpl. done. Qed.

  Fact Vall_typed : ∀ x : vg5, ⊢ᵥ x : τG.
  Proof.
    intros. destruct x as [x i]. simpl.
    unfold P in i. simpl in i. unfold p in i.
    destruct x as [l|l|l|l|l] ; inversion i.
    destruct l ; inversion i. tychk.
  Qed.

  Fact Is_unit : vunit = (1 : vg5).
  Proof. by unfold vunit5. Qed.

  Fact X' : (forall v, (0 <= v)%Z /\ (v < 5)%Z → {v = 0} + {v = 1%Z} + {v = 2} + {v = 3} + {v = 4}).
  Proof.
    intros x [h1 h2].
    destruct x. all: try lia.
    1: by repeat left.
    destruct p0.
    3: do 3 left; by right.
    all: try destruct p0 ; simpl ; try lia.
    all: try destruct p0 ; simpl ; try lia.
    - left. by right.
    - by right.
    - do 2 left; by right.
  Qed.

  Fact X : (forall (v : vg5), {vgval_as v = #0} + {vgval_as v = #1} + {vgval_as v = #2} + {vgval_as v = #3} + {vgval_as v = #4}).
  Proof.
    { intros []. unfold P in i; simpl in i ; unfold p in i.
      destruct x ; try (by inversion i).
      destruct l ; try (by inversion i).
      simpl.
      assert (H : (0 <= n)%Z /\ (n < 5)%Z).
      { move /andP : i => [i1 i2].
        apply Z.leb_le in i1.
        apply Z.ltb_lt in i2.
        done. }
      pose proof (X' _ H) as s.
      repeat destruct s as [s|s].
      all: subst. all: eauto.
    }
  Qed.

  Fact Is_inv : ∀ (x : vg5) Φ,
      True -∗ ▷ (∀ v : vg5, ⌜v = x^-1⌝ -∗ Φ (v : prob_lang.val)) -∗ WP vinv x {{ v, Φ v }}.
  Proof.
      simpl. unfold vinv5.
      intros.
      iIntros "_ hlog".
      pose (X x) as h.
      repeat destruct h as [h|h]; rewrite h ; wp_pures.
      all: match goal with |- context [(|={⊤}=> _ # ?vxy)%I] => set (xy := #vxy) end ;
        match type of h with _ = ?rhs => set (vx := rhs) end ;
        iSpecialize ("hlog" $! (mkP xy)) => /=;
        iApply "hlog" ; iPureIntro;
        assert (x = mkP vx) as -> by
            (apply val_inj ; destruct x ; by simpl);
          apply val_inj; by compute.
  Qed.

  Fact Is_spec_inv : ∀ (x : vg5) K, refines_right K (vinv x) ={⊤}=∗ refines_right K x^-1.
  Proof.
    intros.
    simpl. unfold vinv5.
    iIntros "h".
    pose (X x) as h.
    repeat destruct h as [h|h]; rewrite h ;
      tp_pures => // ; simpl ; auto.
    all: match goal with |- context [(refines_right _ (_ (_ (LitInt ?vxy))))] => set (xy := vxy) end ;
      match goal with |- context [(|={⊤}=> (refines_right _ (_ (_ (LitInt ?g)))))%I] => set (rhs := g) end ;
      assert (xy%Z = rhs) as -> ; [|done];
      destruct x ; simpl in h ; by subst.
    Qed.

  Fact Is_mult : ∀ (x y : vg5) Φ, True
      -∗ ▷ (∀ v : vg5, ⌜v = (x * y)%g⌝ -∗ Φ (v : prob_lang.val))
      -∗ WP vmult x y {{ v, Φ v }}.
  Proof.
      intros.
      iIntros "_ hlog".
      pose (X x) as h.
      pose (X y) as hb.
      repeat destruct h as [h|h].
      all: repeat destruct hb as [hb|hb].
      all: unfold fingroup_val.vmult ; iSimpl ; unfold vmult5 ; rewrite h hb ; wp_pures.
      all: match goal with |- context [ # ?vxy] => set (xy := #vxy) end ;
        match type of h with _ = ?rhs => set (vx := rhs) end ;
        match type of hb with _ = ?rhs => set (vy := rhs) end;
        iSpecialize ("hlog" $! (mkP xy));
        assert ((_ (mkP xy) : cval) = (xy)) as -> by auto;
        iApply "hlog" ; iPureIntro;
        assert (x = mkP vx) as -> by
            (apply val_inj ; destruct x ; by simpl);
        assert (y = mkP vy) as -> by
            (apply val_inj; destruct y; by simpl);
        apply val_inj; by compute.
  Qed.

  Fact Is_spec_mult : ∀ (x y : vg5) K,
      refines_right K (vmult x y) ={⊤}=∗ refines_right K (x * y)%g.
  Proof.
    intros. iIntros "hlog".
    pose (X x) as h.
    pose (X y) as hb.
    assert (vals_compare_safe x #0) as H.
    { destruct x as [x i]. simpl. destruct x as [l|l|l|l|l] ; inversion i.
      destruct l ; inversion i. simpl. auto.
    }
    repeat destruct h as [h|h] ;
      repeat destruct hb as [hb|hb] => //.
    all: unfold vmult ; simpl ; unfold vmult5 ; rewrite h hb.
    all: tp_pures ; eauto.
    all: try by rewrite h in H.
    all: match goal with |- context [ # ?vxy] => set (xy := #vxy) end ;
      match type of h with _ = ?rhs => set (vx := rhs) end ;
      match type of hb with _ = ?rhs => set (vy := rhs) end;
      assert (x = mkP vx) as -> by
        (apply val_inj ; destruct x ; by simpl);
      assert (y = mkP vy) as -> by
        (apply val_inj; destruct y; by simpl);
      assert ((Val xy) = (Val
                            (@vgval_s vg5
                               (@mulg (FinGroup.base (mk_vg vg5)) (@mkP vx I) (@mkP vy I)))))
      as -> => //.
  Qed.

  Definition cg5 : clutch_group (vg := vg5) (cg := cgs5).
    unshelve eapply (
        {| int_of_vg_lrel_G := Int_of_vg_lrel_G
        ; vg_of_int_lrel_G := Vg_of_int_lrel_G
        ; τG_closed := τG_closed'
        ; vall_typed := Vall_typed
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
  - exists #(fintype.nat_of_ord (Zp1 : z5)).
    simpl. compute. done.
  - exact (Zp_trunc (order (Zp1 : z5))).
  - simpl.
    pose proof (order_Zp1 4).
    unfold Zp_trunc. simpl.
    rewrite ?H.
    simpl.
    rewrite -{2}H.
    admit.
  - simpl.
    unfold generator.
    admit.
Admitted.

End Z5.
