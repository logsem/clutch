From clutch.approxis Require Import approxis.
From clutch.prob_lang.typing Require Import tychk.

#[warning="-hiding-delimiting-key,-overwriting-delimiting-key"] From mathcomp Require Import ssrnat.
From mathcomp Require Import fingroup solvable.cyclic eqtype fintype ssrbool zmodp.

From clutch.prelude Require Import mc_stdlib.
From clutch.approxis.examples Require Import valgroup iterable_expression.

Local Open Scope group_scope.
Import fingroup.fingroup.

Set Default Proof Using "Type*".
Set Bullet Behavior "Strict Subproofs".

Section Z_p.

  Context (p'' : nat).
  Notation p := (S (S p'')).

  #[local] Definition cval := prob_lang.val.
  Definition z_p : finGroupType := FinGroup.clone _ 'Z_p.

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

  Definition int_of_vg_sem (n : z_p) : Z := n.  
  Definition vg_of_int_sem (n : Z) : option z_p :=
    if (0 <=? n)%Z && (n <? p)%Z then Some (inZp (Z.to_nat n)) else None.

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
  Context `{!approxisRGS Σ}.

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

  Fact vg_of_int_det `{approxisRGS Σ} :
    @det_val_fun1 _ _ Z (option vgG) lrel_int (() + lrel_G)%lrel (λ x, #x)
      (λ x, match x with
        | None => NONEV
        | Some x => SOMEV (vgval x) end) vg_of_int vg_of_int_sem.
  Proof with rel_pures_l; rel_pures_r. rewrite /det_val_fun1.
    intros *. iIntros "[#Hrel1 #Hrel2]". iSplit; iIntros "H".
    - rewrite /vg_of_int. simpl. rewrite /vg_of_int_p...
      destruct (bool_decide (0 ≤ arg)%Z) eqn:Hargbound1;
      destruct (bool_decide (arg < p)%Z) eqn:Hargbound2;
      try (rel_pures_l; try rewrite Hargbound2; rel_pures_l; rewrite /vg_of_int_sem;
        try apply bool_decide_eq_false in Hargbound1;
        try apply bool_decide_eq_false in Hargbound2;
        try apply bool_decide_eq_true in Hargbound1;
        try apply bool_decide_eq_true in Hargbound2;
        try rewrite -Z.leb_nle in Hargbound1;
        try rewrite -Z.ltb_nlt in Hargbound2;
        try rewrite -Z.leb_le in Hargbound1;
        try rewrite -Z.ltb_lt in Hargbound2;
        rewrite Hargbound1 Hargbound2; simpl); try rel_apply "H"...
      rewrite /vgval_p. rewrite /inZp. simpl.
      rewrite div.modn_small.
      2:{ rewrite /Zp_trunc. simpl. apply Z.ltb_lt in Hargbound2.
        pose proof (reflect_iff _ _ (@leP (S (Z.to_nat arg)) (S (S p'')))) as H'.
        rewrite <- H'. lia. }
      rewrite Z2Nat.id; last lia. rel_apply "H".
    - rewrite /vg_of_int. simpl. rewrite /vg_of_int_p...
      destruct (bool_decide (0 ≤ arg)%Z) eqn:Hargbound1;
      destruct (bool_decide (arg < p)%Z) eqn:Hargbound2;
      try (rel_pures_r; try rewrite Hargbound2; rel_pures_r; rewrite /vg_of_int_sem;
        try apply bool_decide_eq_false in Hargbound1;
        try apply bool_decide_eq_false in Hargbound2;
        try apply bool_decide_eq_true in Hargbound1;
        try apply bool_decide_eq_true in Hargbound2;
        try rewrite -Z.leb_nle in Hargbound1;
        try rewrite -Z.ltb_nlt in Hargbound2;
        try rewrite -Z.leb_le in Hargbound1;
        try rewrite -Z.ltb_lt in Hargbound2;
        rewrite Hargbound1 Hargbound2; simpl); try rel_apply "H"...
      rewrite /vgval_p. rewrite /inZp. simpl.
      rewrite div.modn_small.
      2:{ rewrite /Zp_trunc. simpl. apply Z.ltb_lt in Hargbound2.
        pose proof (reflect_iff _ _ (@leP (S (Z.to_nat arg)) (S (S p'')))) as H'.
        rewrite <- H'. lia. } rewrite Z2Nat.id; last lia. rel_apply "H".
  Qed.

  Fact int_of_vg_det `{approxisRGS Σ} :
    @det_val_fun1 _ _ vgG Z lrel_G lrel_int vgval (λ x, #x) int_of_vg int_of_vg_sem.
  Proof with rel_pures_l; rel_pures_r. rewrite /det_val_fun1. intros *.
    iIntros "[Hrel1 Hrel2]"; iSplit; iIntros "H";
    rewrite /int_of_vg; simpl; rewrite /int_of_vg_p;
    rewrite /vgval_p; rel_pures_l; rel_pures_r; rewrite /int_of_vg_sem; rel_apply "H".
  Qed.

  Fact int_of_vg_of_int_sem : ∀ (xg : vgG),
    vg_of_int_sem (int_of_vg_sem xg) = Some xg.
  Proof. rewrite /vgG. simpl.
    rewrite /vg_of_int_sem/int_of_vg_sem.
    intro xg.
    assert (Hxgpos : (0 ≤ xg)%Z) by lia.
    pose proof (leq_ord xg) as Hxgbound'.
    rewrite /Zp_trunc in Hxgbound'. simpl in Hxgbound'.
    assert (Hxgbound : (xg < p)%Z).
    { rewrite /Zp_trunc. simpl.
      apply (reflect_iff _ _ (@leP xg (S p''))) in Hxgbound'.
      apply inj_lt.
      apply PeanoNat.le_lt_n_Sm. apply Hxgbound'. }
    clear Hxgbound'.
    apply Z.leb_le in Hxgpos.
    apply Z.ltb_lt in Hxgbound.
    rewrite Hxgpos Hxgbound. simpl.
    rewrite Nat2Z.id. rewrite valZpK. reflexivity.
  Qed. 

  Fact vg_of_int_of_vg_sem : ∀ (n : Z) (xg : vgG),
    vg_of_int_sem n = Some xg →
    int_of_vg_sem xg = n.
  Proof. intros *. rewrite /vg_of_int_sem/int_of_vg_sem.
    destruct (0 <=? n)%Z eqn:Hnbound1;
    destruct (n <? p)%Z eqn:Hnbound2; first last;
    simpl; intro H; try discriminate H.
    injection H; intro eq. rewrite -eq.
    rewrite /inZp. simpl.
    rewrite div.modn_small.
    2:{ rewrite /Zp_trunc. simpl.
      pose proof (reflect_iff _ _ (@leP (S (Z.to_nat n)) (S (S p'')))) as H'.
      rewrite <- H'. apply Z.ltb_lt in Hnbound2. lia. }
    rewrite Z2Nat.id; lia.
  Qed.

  Fact vgval_sem_typed : ⊢ to_val_type_rel lrel_G vgval.
  Proof. iIntros (x). rewrite /vgval. simpl.
    rewrite /vgval_p. Search vgG lrel_G. rewrite /lrel_G. 
    rewrite /lrel_car. iExists x; done.
  Qed.

  Fact is_inv_p (x : vgG) : ⊢ WP vinv x {{ λ (v : cval), ⌜v = x^-1⌝ }}.
  Proof.
    simpl. unfold vinv_p, vgval_p. cbn -[Zp_opp]. wp_pures.
    rewrite /Zp_trunc -(Nat2Z.inj_sub _ _ (leq_zmodp _ _)). simpl.
    by rewrite rem_modn.
  Qed.

  Fact is_spec_inv_p (x : vgG) K : ⤇ fill K (vinv x) -∗ spec_update ⊤ (⤇ fill K x^-1).
  Proof.
    iIntros => /=. unfold vinv_p, vgval_p. tp_pures => /=.
    rewrite /Zp_trunc -(Nat2Z.inj_sub _ _ (leq_zmodp _ _)) => /=.
    iModIntro. 
    by rewrite rem_modn.
  Qed.

  Fact is_mult_p (x y : vgG) : ⊢ WP vmult x y {{ λ (v : cval), ⌜v = (x * y)%g⌝ }}.
  Proof.
    rewrite /vmult /= /vmult_p /vgval_p /=. wp_pures.
    by rewrite -Nat2Z.inj_add rem_modn // -ssrnat.plusE.
  Qed.

  Fact is_spec_mult_p (x y : vgG) K :
    ⤇ fill K (vmult x y) -∗ spec_update ⊤ (⤇ fill K (x * y)%g).
  Proof.
    iIntros. rewrite /vmult /cgs_p /vmult_p /= /vgval_p. tp_pures => /=.
    iModIntro. 
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

  Definition vgg_p : val_group_generator (vg:=vg_p).
  Proof.
    unshelve econstructor.
    - exact (Zp1 : z_p).
    - exact (Zp_trunc #[Zp1 : z_p]).
    - by rewrite ?(order_Zp1 (S p'')).
    - rewrite /= /generator.
      rewrite Zp_cycle. apply Is_true_eq_left. apply eq_refl.
  Defined.

  Definition cgg_p : @clutch_group_generator vg_p cgs_p vgg_p.
  Proof.
    constructor. constructor.
  Defined.

End Z_p.
