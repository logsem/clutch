From clutch.approxis Require Import approxis map list security_aux.
From clutch.approxis Require Export bounded_oracle.
Set Default Proof Using "Type*".

Class XOR {Key Support : nat} :=
  { xor : val
  ; xor_sem : nat → nat → nat
  ; xor_bij x : Bij (xor_sem x)
  ; xor_dom x : x < S Key -> (∀ n : nat, n < S Support → xor_sem x n < S Support)

  ; TKey := TInt
  ; TInput := TNat
  ; TOutput := TNat

  (* TODO: should xor be partial? `xor key input` may fail unless 0 <= key <=
     Key /\ 0 <= input <= Input

     If xor were to operate on strings / byte arrays / bit lists instead, it
     may fail if `key` and `input` are of different lengths. *)

  } .

Class XOR_spec `{!approxisRGS Σ} `{XOR} :=
  { XOR_CORRECT_L := ∀ E K (x : Z) (y : nat)
                       (_: (0<=x)%Z)
                       (_: ((Z.to_nat x) < S Key))
                       (_: y < S Support) e A,
      (REL (fill K (of_val #(xor_sem (Z.to_nat x) (y)))) << e @ E : A)
      -∗ REL (fill K (xor #x #y)) << e @ E : A
  ; XOR_CORRECT_R := ∀ E K (x : Z) (y : nat)
                       (_: (0<=x)%Z)
                       (_: ((Z.to_nat x) < S Key))
                       (_: y < S Support) e A,
      (REL e << (fill K (of_val #(xor_sem (Z.to_nat x) (y)))) @ E : A)
      -∗ REL e << (fill K (xor #x #y)) @ E : A
  ; xor_correct_l : XOR_CORRECT_L
  ; xor_correct_r : XOR_CORRECT_R
  ; xor_sem_typed :
    ⊢ (lrel_int_bounded 0 Key → lrel_int_bounded 0 Support → lrel_int_bounded 0 Support)%lrel
        xor xor
    
  ; xor_sem_inverse_r : forall (x y : nat), x < S Key →
    y < S Support → xor_sem (xor_sem x y) y = x
  }.

Section xor_minus_mod.
  Variable bit : nat.
  Definition Output' := 2^bit - 1.
  Definition Input' := 2^bit-1.
  Definition Key' := 2^bit-1.
  Notation Message2' := Output'.
  Notation Output := (S Output').
  Lemma Output_pos: 0 < Output.
  Proof. lia. Qed.

  Definition xor_minus_mod : val :=
    (λ: "x" "y", let: "diff" := "y" - "x" in
      if: "y" < "x" then "diff" + #Output else "diff")%V.

  Definition xor_minus_mod_sem (x y : nat) : nat :=
    (if bool_decide (0 ≤ x) && bool_decide (x ≤ Output')
     then if bool_decide (0 ≤ y) && bool_decide (y ≤ Output')
          then if bool_decide (y < x)
               then (Output + y - x)
               else (y - x)
          else y
     else y).

  Fact xor_minus_mod_sem_inverse_r : forall (x y : nat),
    x < S Key' → y < S Input' →
      xor_minus_mod_sem (xor_minus_mod_sem x y) y = x.
  Proof. intros x y H1 H2.
    rewrite /Key' in H1.
    rewrite /Input' in H2.
    assert (Hxpos : bool_decide (0 ≤ x) = true) by (apply bool_decide_eq_true; lia).
    assert (Hypos : bool_decide (0 ≤ y) = true) by (apply bool_decide_eq_true; lia).
    assert (Hxbound : bool_decide (x ≤ Output') = true) by
      (apply bool_decide_eq_true; rewrite /Output'; lia).
    assert (Hybound : bool_decide (y ≤ Output') = true) by
      (apply bool_decide_eq_true; rewrite /Output'; lia).
    rewrite /xor_minus_mod_sem.
    rewrite Hxpos Hypos Hxbound Hybound. simpl.
    destruct (bool_decide (y < x)) eqn:Hyx.
    - apply bool_decide_eq_true in Hxpos.
      apply bool_decide_eq_true in Hypos.
      apply bool_decide_eq_true in Hxbound.
      apply bool_decide_eq_true in Hybound.
      apply bool_decide_eq_true in Hyx.
      assert (Hboundxor : bool_decide (S (Message2' + y) - x ≤ Message2') = true).
      { apply bool_decide_eq_true. lia. }
      rewrite Hboundxor.
      assert (Hxbound' : bool_decide (y < S (Message2' + y) - x) = true).
      { apply bool_decide_eq_true. lia. }
      rewrite Hxbound'.
      apply bool_decide_eq_true in Hboundxor.
      apply bool_decide_eq_true in Hxbound'.
      lia.
    - apply bool_decide_eq_true in Hxpos.
      apply bool_decide_eq_true in Hypos.
      apply bool_decide_eq_true in Hxbound.
      apply bool_decide_eq_true in Hybound.
      apply bool_decide_eq_false in Hyx.
      assert (Hyxbound : bool_decide (y - x ≤ Message2') = true).
      { apply bool_decide_eq_true. lia. }
      rewrite Hyxbound; apply bool_decide_eq_true in Hyxbound.
      assert (Hybound' : bool_decide (y < y - x) = false) by
        (apply bool_decide_eq_false; lia).
      rewrite Hybound'. lia.
  Qed.
      


  Lemma xor_minus_mod_sem_bij x: Bij (xor_minus_mod_sem x).
  Proof. split.
    - rewrite /Inj. intros y y'.
      rewrite /xor_minus_mod_sem.
      destruct (bool_decide (0 ≤ x)) eqn:Hxpos; simpl; last done.
      destruct (bool_decide (0 ≤ y)) eqn:Hypos; simpl;
      destruct (bool_decide (x ≤ Output')) eqn:Hxbound; try done.
      destruct (bool_decide (y ≤ Output')) eqn:Hy'bound; simpl;
      destruct (bool_decide (y' ≤ Output')) eqn:Hybound; simpl; try done;
      destruct (bool_decide (y < x)) eqn:Hyx; simpl;
      try apply bool_decide_eq_true in Hxpos;
      try apply bool_decide_eq_true in Hypos;
      try apply bool_decide_eq_true in Hxbound;
      try apply bool_decide_eq_true in Hybound;
      try apply bool_decide_eq_true in Hy'bound;
      try apply bool_decide_eq_true in Hyx;
      try apply bool_decide_eq_false in Hxpos;
      try apply bool_decide_eq_false in Hypos;
      try apply bool_decide_eq_false in Hxbound;
      try apply bool_decide_eq_false in Hybound;
      try apply bool_decide_eq_false in Hy'bound;
      try apply bool_decide_eq_false in Hyx;
      try (intros H; exfalso; lia);
      destruct (bool_decide (y' < x)) eqn:Hy'x; simpl;
      try apply bool_decide_eq_true in Hy'x;
      try apply bool_decide_eq_false in Hy'x;
      try (intros H; lia).
    - intros y.
      destruct (bool_decide (0 ≤ x)) eqn:Hxpos; simpl;
      destruct (bool_decide (x ≤ Output')) eqn:Hxbound; simpl;
      try (exists y; rewrite /xor_minus_mod_sem;
        rewrite Hxpos Hxbound; simpl; reflexivity).
      destruct (bool_decide (0 ≤ y)) eqn:Hypos; simpl;
      destruct (bool_decide (y ≤ Output')) eqn:Hybound; simpl;
      try (exists y; rewrite /xor_minus_mod_sem;
        rewrite Hxpos Hxbound Hypos Hybound; simpl; reflexivity).
      destruct (bool_decide (y + x ≤ Message2')) eqn:Hyplusxbound.
      * exists (y+x). rewrite /xor_minus_mod_sem.
        rewrite Hxpos Hxbound Hyplusxbound; simpl.
        assert (Hyxx : bool_decide (y + x < x) = false)
          by (apply bool_decide_eq_false; lia).
        rewrite Hyxx. lia.
      * exists (y+x - Output).
        rewrite /xor_minus_mod_sem.
        rewrite Hxpos Hxbound; simpl.
        apply bool_decide_eq_true in Hxpos;
        apply bool_decide_eq_true in Hypos;
        apply bool_decide_eq_true in Hxbound;
        apply bool_decide_eq_true in Hybound;
        apply bool_decide_eq_false in Hyplusxbound.
        assert (Hargbound : bool_decide (y + x - Output ≤ Message2') = true)
          by (apply bool_decide_eq_true; lia).
        rewrite Hargbound.
        assert (Hargx : bool_decide (y + x - Output < x) = true)
          by (apply bool_decide_eq_true; lia).
        rewrite Hargx. lia.
  Qed.
  
  Lemma xor_minus_mod_sem_dom: forall x, x < S Message2' -> (∀ n : nat, n < S Output' →  (xor_minus_mod_sem x n) < S Output').
  Proof.
    intros.
    rewrite /xor_minus_mod_sem.
    case_bool_decide;
    last case_bool_decide;
    try case_bool_decide; simpl; try lia.
    case_bool_decide; simpl; try case_bool_decide; try lia.
  Qed.

  Lemma xor_minus_mod_correct_l `{!approxisRGS Σ} E K (x : Z) (y : nat)
    (_: (0<=x)%Z)
    (Hx : ((Z.to_nat x) < S Message2'))
    (Hy : y < S Message2' ) e A:
    (REL (fill K (of_val #(xor_minus_mod_sem (Z.to_nat x) (y)))) << e @ E : A)
    -∗ REL (fill K (xor_minus_mod #x #y)) << e @ E : A.
  Proof with rel_pures_l.
    iIntros "H".
    rewrite /xor_minus_mod...
    rewrite /Output' in Hx.
    rewrite /Output' in Hy.
    rewrite /xor_minus_mod_sem.
    assert (Hxpos : bool_decide (0 ≤ Z.to_nat x) = true);
    assert (Hypos : bool_decide (0 ≤ y) = true);
    assert (Hxbound : bool_decide (Z.to_nat x ≤ Message2') = true);
    assert (Hybound : bool_decide (y ≤ Message2') = true); try apply bool_decide_eq_true;
    try rewrite /Message2'; try lia.
    rewrite Hxpos Hypos Hxbound Hybound. simpl.
    destruct (bool_decide (y < Z.to_nat x)) eqn:Hyx.
    - assert (Hyx' : bool_decide (y < x)%Z = true) by
        (apply bool_decide_eq_true; apply bool_decide_eq_true in Hyx; lia).
        rewrite Hyx'...
        replace (y - x + S (2 ^ bit - 1))%Z with 
          (Z.of_nat (S (2 ^ bit - 1 + y) - Z.to_nat x)) by lia.
        rel_apply "H".
    - assert (Hyx' : bool_decide (y < x)%Z = false) by
        (apply bool_decide_eq_false; apply bool_decide_eq_false in Hyx; lia).
        rewrite Hyx'...
        replace (y - x)%Z with 
          (Z.of_nat (y - Z.to_nat x)); first rel_apply "H".
        apply bool_decide_eq_true in Hypos.
        apply bool_decide_eq_true in Hxbound.
        apply bool_decide_eq_true in Hybound.
        apply bool_decide_eq_false in Hyx.
        apply bool_decide_eq_false in Hyx'.
        lia.
  Qed.

  Lemma xor_minus_mod_correct_r  `{!approxisRGS Σ} E K (x : Z) (y : nat)
    (_: (0<=x)%Z)
    (Hx : ((Z.to_nat x) < S Message2'))
    (Hy: y < S Message2') e A:
    (REL e << (fill K (of_val #(xor_minus_mod_sem (Z.to_nat x) (y)))) @ E : A)
    -∗ REL e << (fill K (xor_minus_mod #x #y)) @ E : A.
  Proof with rel_pures_r.
    iIntros "H".
    rewrite /xor_minus_mod...
    rewrite /Output' in Hx.
    rewrite /Output' in Hy.
    rewrite /xor_minus_mod_sem.
    assert (Hxpos : bool_decide (0 ≤ Z.to_nat x) = true);
    assert (Hypos : bool_decide (0 ≤ y) = true);
    assert (Hxbound : bool_decide (Z.to_nat x ≤ Message2') = true);
    assert (Hybound : bool_decide (y ≤ Message2') = true); try apply bool_decide_eq_true;
    try rewrite /Message2'; try lia.
    rewrite Hxpos Hypos Hxbound Hybound. simpl.
    destruct (bool_decide (y < Z.to_nat x)) eqn:Hyx.
    - assert (Hyx' : bool_decide (y < x)%Z = true) by
        (apply bool_decide_eq_true; apply bool_decide_eq_true in Hyx; lia).
        rewrite Hyx'...
        replace (y - x + S (2 ^ bit - 1))%Z with 
          (Z.of_nat (S (2 ^ bit - 1 + y) - Z.to_nat x)) by lia.
        rel_apply "H".
    - assert (Hyx' : bool_decide (y < x)%Z = false) by
        (apply bool_decide_eq_false; apply bool_decide_eq_false in Hyx; lia).
        rewrite Hyx'...
        replace (y - x)%Z with 
          (Z.of_nat (y - Z.to_nat x)); first rel_apply "H".
        apply bool_decide_eq_true in Hypos.
        apply bool_decide_eq_true in Hxbound.
        apply bool_decide_eq_true in Hybound.
        apply bool_decide_eq_false in Hyx.
        apply bool_decide_eq_false in Hyx'.
        lia.
  Qed.

  #[local] Instance XOR_minus_mod : @XOR Output' Output'.
  Proof.
    unshelve econstructor.
    2: exact xor_minus_mod.
    1: exact xor_minus_mod_sem.
    1: exact xor_minus_mod_sem_bij.
    apply xor_minus_mod_sem_dom.
  Defined.

  Fact xor_minus_mod_sem_typed : forall `{!approxisRGS Σ},
      ⊢ (lrel_int_bounded 0 Key' → lrel_int_bounded 0 Input' → lrel_int_bounded 0 Output')%lrel
          xor_minus_mod xor_minus_mod.
  Proof with (rel_pures_r ; rel_pures_l).
    intros *. rel_vals.
    iIntros (v1 v2 [x [eq1 [eq2 [Hxpos Hxbound]]]]); subst...
    rewrite /xor_minus_mod...
    rel_arrow_val.
    iIntros (v1 v2 [y [eq1 [eq2 [Hypos Hybound]]]]); subst...
    case_bool_decide as Hyminusx; rel_pures_l; rel_pures_r; rel_vals;
      rewrite /Message2'; rewrite /Key' in Hxbound; rewrite /Input' in Hybound;
      lia.
  Qed.

  #[local] Instance XOR_spec_minus_mod `{!approxisRGS Σ} : @XOR_spec _ _ Output' Output' XOR_minus_mod.
  Proof.
    unshelve econstructor.
    - intros. eapply xor_minus_mod_correct_l => //.
    - intros. eapply xor_minus_mod_correct_r => //.
    - intros. simpl. eapply xor_minus_mod_sem_typed.
    - apply xor_minus_mod_sem_inverse_r.
  Qed.

End xor_minus_mod.