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
                       (_: y < S Key) e A,
      (REL (fill K (of_val #(xor_sem (Z.to_nat x) (y)))) << e @ E : A)
      -∗ REL (fill K (xor #x #y)) << e @ E : A
  ; XOR_CORRECT_R := ∀ E K (x : Z) (y : nat)
                       (_: (0<=x)%Z)
                       (_: ((Z.to_nat x) < S Key))
                       (_: y < S Key) e A,
      (REL e << (fill K (of_val #(xor_sem (Z.to_nat x) (y)))) @ E : A)
      -∗ REL e << (fill K (xor #x #y)) @ E : A
  ; xor_correct_l : XOR_CORRECT_L
  ; xor_correct_r : XOR_CORRECT_R
  ; xor_sem_typed :
    ⊢ (lrel_int_bounded 0 Key → lrel_int_bounded 0 Support → lrel_int_bounded 0 Support)%lrel
        xor xor
  }.


Section xor_mod.
  Variable bit : nat.
  Definition Output' := 2^bit - 1.
  Definition Input' := 2^bit-1.
  Definition Key' := 2^bit-1.
  Notation Message' := Output'.
  Notation Output := (S Output').
  Lemma Output_pos: 0<Output.
  Proof. lia. Qed.

  Definition xor_mod : val :=
    (λ: "x" "y", let: "sum" := "x" + "y" in
                 if: "sum" < #Output then "sum" else "sum" - #Output)%V.

  Definition xor_mod_sem (x y : nat) :=
    (if bool_decide (x ≥ Output)
     then y
     else if bool_decide (y ≥ Output)
          then y
          else if bool_decide(x + y < Output)
               then x + y
               else x + y - Output).

  Lemma xor_mod_sem_bij x: Bij (xor_mod_sem x).
  Proof.
    split.
    - intros y y'. rewrite /xor_mod_sem.
      intros H.
      case_bool_decide; [lia |].
      case_bool_decide; case_bool_decide; [ lia | | | ].
      + case_bool_decide; lia.
      + case_bool_decide; [lia | ].
        case_bool_decide; lia.
      + case_bool_decide; [lia | ].
        case_bool_decide; lia.
    - rewrite /xor_mod_sem. intros y.
      case_bool_decide; [eauto |].
      destruct (decide (y ≥ Output)).
      + exists y. case_bool_decide; lia.
      + destruct (decide (x<=y)).
        * exists (y-x).
          case_bool_decide; [lia |].
          case_bool_decide; lia.
        * exists (Output+y-x).
          case_bool_decide; [lia |].
          case_bool_decide; lia.
  Qed.

  Lemma xor_mod_sem_dom: forall x, x < S Message' -> (∀ n : nat, n < S Output' → xor_mod_sem x n < S Output').
  Proof.
    intros.
    rewrite /xor_mod_sem.
    case_bool_decide; [lia |].
    case_bool_decide; [lia |].
    case_bool_decide; lia.
  Qed.

  Lemma xor_mod_correct_l `{!approxisRGS Σ} E K (x : Z) (y : nat)
    (_: (0<=x)%Z)
    (Hx : ((Z.to_nat x) < S Message'))
    (_ : y < S Message' ) e A:
    (REL (fill K (of_val #(xor_mod_sem (Z.to_nat x) (y)))) << e @ E : A)
    -∗ REL (fill K (xor_mod #x #y)) << e @ E : A.
  Proof with rel_pures_l.
    iIntros "H".
    rewrite /xor_mod...
    rewrite /xor_mod_sem.
    rewrite bool_decide_eq_false_2; last lia.
    rewrite bool_decide_eq_false_2; last lia.
    case_bool_decide.
    - rewrite bool_decide_eq_true_2; last lia.
      rel_pures_l.
      replace (Z.of_nat (Z.to_nat x + y))%Z with (x + Z.of_nat y)%Z by lia.
      done.
    - rewrite bool_decide_eq_false_2; last lia...
      replace (Z.of_nat (Z.to_nat x + y - S Message'))%Z with (x + Z.of_nat y - Z.of_nat (S Message'))%Z by lia.
      done.
  Qed.

  Lemma xor_mod_correct_r  `{!approxisRGS Σ} E K (x : Z) (y : nat)
    (_: (0<=x)%Z)
    (Hx : ((Z.to_nat x) < S Message'))
    (_: y < S Message') e A:
    (REL e << (fill K (of_val #(xor_mod_sem (Z.to_nat x) (y)))) @ E : A)
    -∗ REL e << (fill K (xor_mod #x #y)) @ E : A.
  Proof with rel_pures_r.
    iIntros "H".
    rewrite /xor_mod...
    rewrite /xor_mod_sem.
    rewrite bool_decide_eq_false_2; last lia.
    rewrite bool_decide_eq_false_2; last lia.
    case_bool_decide.
    - rewrite bool_decide_eq_true_2; last lia...
      replace (Z.of_nat (Z.to_nat x + y))%Z with (x + Z.of_nat y)%Z; first done.
      rewrite Nat2Z.inj_add. rewrite Z2Nat.id; lia.
    - rewrite bool_decide_eq_false_2; last lia...
      replace (Z.of_nat (Z.to_nat x + y - S Message'))%Z with (x + Z.of_nat y - Z.of_nat (S Message'))%Z by lia.
      done.
  Qed.

  #[local] Instance XOR_mod : @XOR Output' Output'.
  Proof.
    unshelve econstructor.
    2: exact xor_mod. 1: exact xor_mod_sem. 1: exact xor_mod_sem_bij.
    apply xor_mod_sem_dom.
  Defined.

  Fact xor_mod_sem_typed : forall `{!approxisRGS Σ},
      ⊢ (lrel_int_bounded 0 Key' → lrel_int_bounded 0 Input' → lrel_int_bounded 0 Output')%lrel
          xor_mod xor_mod.
  Proof with (rel_pures_r ; rel_pures_l).
    iIntros.
    iIntros (k k').
    iModIntro. lrintro "x".
    rewrite /xor_mod...
    rel_arrow_val. lrintro "y"...
    case_bool_decide as h...
    all: rel_values ; iModIntro ; iExists _ ; iPureIntro.
    -
      rewrite /Key' /Input' /Output'.
      repeat split ;
        rewrite /Output' in h ; rewrite /Output' ;
        try lia.
    - repeat split ; try lia.
      assert (Output <= x + y)%Z as h' by lia.
      cut (x + y <= Output' + Output')%Z. 1: by intros ; lia.
      clear h.

      transitivity (x + Output')%Z.
      2: eapply Zplus_le_compat_r.
      1: eapply Zplus_le_compat_l.
      + rewrite /Output'. rewrite /Input' in y_max.
        lia.
      + rewrite /Output'. rewrite /Output' in h'.
        rewrite /Key' in x_max.
        lia.
  Qed.

  #[local] Instance XOR_spec_mod `{!approxisRGS Σ} : @XOR_spec _ _ Output' Output' XOR_mod.
  Proof.
    unshelve econstructor.
    - intros. eapply xor_mod_correct_l => //.
    - intros. eapply xor_mod_correct_r => //.
    - intros. simpl. eapply xor_mod_sem_typed.
  Qed.

End xor_mod.
