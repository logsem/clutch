From clutch Require Import clutch.

From mathcomp Require ssrnat.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import fingroup solvable.cyclic choice eqtype finset
  fintype seq ssrbool zmodp.
Set Warnings "notation-overridden,ambiguous-paths".

From clutch.examples.crypto Require Import fingroup_val.

Local Open Scope group_scope.
Import fingroup.fingroup.
(* Import prob_lang. *)
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
  Definition p' : {pred cval} :=
    (λ x, match x with #(LitInt n) => true | _ => false end).

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

  Lemma zp_vt_C : forall x, zp_of_vt (vt_of_zp x) = x.
  Proof.
    intros. unfold vt_of_zp. destruct x. simpl.
    rewrite Nat2Z.id.
    unfold inZp.
    eapply val_inj. simpl.
    rewrite div.modn_small => //.
  Qed.

  Lemma vt_zp_C : forall x, vt_of_zp (zp_of_vt x) = x.
  Proof.
    intros.
    (* eapply val_inj. simpl. *)
    destruct x.
    simpl.
    destruct x ; try by inversion i.
    destruct l ; try by inversion i.
    eapply val_inj. simpl.
    do 2 f_equal.
    unfold p in i.
    move /andP : i => [i1 i2].
    rewrite div.modn_small => //.
    1: by apply Z2Nat.id, Z.leb_le.
    apply /ssrnat.leP.
    unfold Zp_trunc. simpl.
    move : i2.
    move => /Z.ltb_spec0 i2.
    lia.
  Qed.

  Definition g5 : val_group.
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
  Definition gg := mk_vg g5.

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

  Definition vunit5 := (val (1%g : g5)).
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

  Definition vexp5 := (λ:"a", rec: "vexp" "n" := if: "n" ≤ #0 then vunit5 else vmult5 "a" ("vexp" ("n" - #1)))%V.

  Definition int_of_vg5 : cval := (λ:"a", "a")%V.

  Definition vg_of_int5 : cval :=
    (λ:"a", if: (#0 ≤ "a") && ("a" < #5) then SOME "a" else NONE)%V.

  Definition cgs5 : clutch_group_struct.
    unshelve eapply ({|
          vunit := vunit5 ;
          vinv := vinv5 ;
          vmult := vmult5 ;
          vexp := vexp5 ;
          int_of_vg := int_of_vg5 ;
          vg_of_int := vg_of_int5 ;
          τG := TInt ;
        |}) .
    all: cbv ; tychk.
  Defined.


  Definition cg5 `{clutchRGS Σ} : clutch_group (vg := gg) (cg := cgs5).
    assert (forall (v : g5), {vgval_as v = #0} + {vgval_as v = #1} + {vgval_as v = #2} + {vgval_as v = #3} + {vgval_as v = #4}).
    { intros []. unfold P in i; simpl in i ; unfold p in i.
      destruct x ; try (by inversion i).
      destruct l ; try (by inversion i).
      simpl.
      destruct n eqn:hn.
      - by repeat left.
      - destruct p0 eqn:hp ; simpl.
        3: do 3 left; by right.
        all: admit.
      - admit.
    }
    econstructor.
    all: try (by eauto).
    7: {
      intros. destruct x. simpl.
      unfold P in i. simpl in i. unfold p in i.
      destruct x ; inversion i.
      destruct l ; inversion i. tychk.
    }
    2:{
      iModIntro.
      iIntros (??) "#(%a & -> & ->)".
      simpl. unfold vmult5.
      rel_pures_l. rel_pures_r.
      rel_arrow_val.
      iIntros (??) "#(%b & -> & ->)".
      rel_pures_l. rel_pures_r.
      pose (X a) as h.
      pose (X b) as hb.
      repeat destruct h as [h|h].
      all: repeat destruct hb as [hb|hb].
      all: rewrite h hb ; simpl ; rel_pures_l ; rel_pures_r.
      all: rel_values.
      all: iExists (mkP _) ; iModIntro ; eauto.
    }
    8:{
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
    }
    6: {
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
      }
    6:{
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
    }
    3:{
      iModIntro.
      iIntros (??) "(%v&->&->)".
      unfold int_of_vg. simpl. unfold int_of_vg5.
      rel_pures_l. rel_pures_r.
      destruct v. simpl. unfold P in i; simpl in i; unfold p in i.
      destruct x ; inversion i. destruct l ; inversion i.
      rel_values.
    }
    3:{
      iModIntro.
      iIntros (??) "(%v&->&->)".
      unfold vg_of_int. simpl. unfold vg_of_int5.
      rel_pures_l. rel_pures_r.
      case_bool_decide ; rel_pures_l ; rel_pures_r.
      2: { rel_values. do 2 iExists _. by iLeft. }
      case_bool_decide ; rel_pures_l ; rel_pures_r.
      2: { rel_values. do 2 iExists _. by iLeft. }
      rel_values. do 2 iExists _. iRight.
      iModIntro.
      repeat (iSplit ; eauto).
      assert (p #v) as Pv.
      { unfold p. move : H0.
        intros.
        apply andb_prop_intro.
        split.
        - rewrite -Z.leb_le in H0. unfold Is_true. rewrite H0. done.
        - rewrite -Z.ltb_lt in H1. unfold Is_true. rewrite H1. done.
      }
      iExists (@mkP #v Pv). simpl. done.
    }
    1: give_up.
    1: give_up.
    1: give_up.
    1: admit.
    1,2: give_up.
    Unshelve.
    all: try by auto.
Admitted.

End Z5.
