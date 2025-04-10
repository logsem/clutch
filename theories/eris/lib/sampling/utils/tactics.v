From clutch.eris Require Import eris.
From clutch.eris.lib.sampling.utils Require Import lemmas.

#[local] Open Scope R.

Ltac add_hint t := let n := fresh "hint" in have n := t.

Ltac cred_contra := 
    match goal with 
    | |- context[↯ 0] => 
          iAssert (False)%I as "[]";
          iApply ec_contradict_lt0; last iFrame; try done
    | |- context[↯ (1 - _)%R] => 
          iAssert (False)%I as "[]";
          iApply ec_contradict_lt0; last iFrame; try done
    | |- context[↯ _] => 
          iAssert (False)%I as "[]";
          iApply ec_contradict; last iFrame; try done
    end.

Ltac find_contra :=
  solve
  [ contradiction
  | solve[cred_contra] 
  | match goal with 
    | H : ¬ _ |- _ => exfalso; apply H; by eauto
    end ].
  


Ltac full_inv_fin :=
  repeat match goal with 
  | i : fin _ |- _   => 
    inv_fin i; 
    try match goal with 
    | |- ∀ _ : fin _, _ =>  intro i
    end
  end;
  try (reflexivity || find_contra).

Ltac bool_decide :=
  match goal with 
  | H : ?P |- context[bool_decide (?P)] => 
        rewrite (bool_decide_eq_true_2 P); last apply H
  | H : ¬ ?P |- context[bool_decide (?P)] => 
        rewrite (bool_decide_eq_false_2 P); last apply H

  | |- context[bool_decide (?a <= ?b)%nat] => 
        try 
        ( (rewrite (bool_decide_eq_false_2 (a <= b)%nat); last lia) 
        || (rewrite (bool_decide_eq_true_2 (a <= b)%nat); last lia)) 
  | |- context[bool_decide (?a >= ?b)%nat] => 
        try 
        ( (rewrite (bool_decide_eq_false_2 (a >= b)%nat); last lia) 
        || (rewrite (bool_decide_eq_true_2 (a >= b)%nat); last lia)) 
  | |- context[bool_decide (?a < ?b)%nat] => 
        try 
        ( (rewrite (bool_decide_eq_false_2 (a < b)%nat); last lia )
        || (rewrite (bool_decide_eq_true_2 (a < b)%nat); last lia)) 
  | |- context[bool_decide (?a > ?b)%nat] => 
        try 
        ( (rewrite (bool_decide_eq_false_2 (a > b)%nat); last lia) 
        || (rewrite (bool_decide_eq_true_2 (a > b)%nat); last lia))

  | |- context[bool_decide (?a <= ?b)%Z] => 
        try 
        ( (rewrite (bool_decide_eq_false_2 (a <= b)%Z); last lia) 
        || (rewrite (bool_decide_eq_true_2 (a <= b)%Z); last lia)) 
  | |- context[bool_decide (?a >= ?b)%Z] => 
        try 
        ( (rewrite (bool_decide_eq_false_2 (a >= b)%Z); last lia) 
        || (rewrite (bool_decide_eq_true_2 (a >= b)%Z); last lia)) 
  | |- context[bool_decide (?a < ?b)%Z] => 
        try 
        ( (rewrite (bool_decide_eq_false_2 (a < b)%Z); last lia )
        || (rewrite (bool_decide_eq_true_2 (a < b)%Z); last lia)) 
  | |- context[bool_decide (?a > ?b)%Z] => 
        try 
        ( (rewrite (bool_decide_eq_false_2 (a > b)%Z); last lia) 
        || (rewrite (bool_decide_eq_true_2 (a > b)%Z); last lia)) 
  end.


Module SimplExpr.
  #[local] Ltac try_solve := solve[
      lra  || done || auto ||
      apply cond_nonneg ||
      apply pos_INR_S   ||
      apply pos_INR     ||
      apply le_INR; lia ||
      apply lt_INR; lia ||
      apply INR_S_not_0
  ].
  #[local] Ltac simpl_le :=
      match goal with 
      | |- _ * ?n <= _ * ?n => apply Rmult_le_compat_r
      | |- ?n * _ <= ?n * _ => apply Rmult_le_compat_l

      | |- _ <= _ */?n => apply (Rmult_le_reg_l n)
      | |- _ * /?n <= _  => apply (Rmult_le_reg_l n)

      | |- _ + ?n <= _ + ?n => apply (Rplus_le_compat_r n)
      | |- ?n + _ <= ?n + _ => apply (Rplus_le_compat_l n)
      end.
  #[local] Ltac simple_lt :=
    match goal with 
    | |- 0 <  / ?n => apply (Rinv_0_lt_compat n)
    | |- _ * ?n <  _ * ?n => apply Rmult_lt_compat_r
    | |- ?n * _ <  ?n * _ => apply Rmult_lt_compat_l
    | |- _ <  _ */?n => apply (Rmult_lt_reg_l n)
    | |- _ * /?n <  _  => apply (Rmult_lt_reg_l n)
    | |- _ + ?n <  _ + ?n => apply (Rplus_lt_compat_r n)
    | |- ?n + _ <  ?n + _ => apply (Rplus_lt_compat_l n)
    end.
  
  #[local] Ltac simpl_eq :=
    match goal with 
    | |- _ * ?n =  _ * ?n => apply Rmult_eq_compat_r
    | |- ?n * _ =  ?n * _ => apply Rmult_eq_compat_l
    | |- _ =  _ */?n => apply (Rmult_eq_reg_l n)
    | |- _ * /?n =  _  => apply (Rmult_eq_reg_l n)
    | |- _ + ?n =  _ + ?n => apply (Rplus_eq_compat_r n)
    | |- ?n + _ =  ?n + _ => apply (Rplus_eq_compat_l n)
    end.
  
  #[local] Ltac triv_simpl := 
    rewrite Rplus_0_l || rewrite Rplus_0_r    ||
    rewrite Rmult_0_l || rewrite Rmult_0_r    ||
    rewrite Rmult_1_l || rewrite Rmult_1_r    ||
    rewrite Rdiv_1_l  || rewrite Rdiv_1_r     ||
    rewrite !Rinv_1   || rewrite !Rinv_0      ||
    rewrite -!Ropp_mult_distr_r
  .
  

  Ltac simpl_expr :=
    repeat progress (
      rewrite !Rdiv_def || rewrite !Rminus_def  ||
       match goal with 
      | |- context[(?v1 * (?v2 * /?v1))] => 
            rewrite 
              (Rmult_div_assoc v1 v2 v1) 
              (Rmult_div_r v1 v2)

      | |- context[((?v1 * ?v2) * /?v1)] => 
            rewrite (Rmult_div_r v1 v2)

      | |- context[?v * /?v] => rewrite (Rinv_r v)
      end ||
      simpl_le || simple_lt || simpl_eq ||
      triv_simpl || try_solve
    ).
End SimplExpr.



Export SimplExpr.
