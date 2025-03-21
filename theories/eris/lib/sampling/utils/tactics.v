From clutch.eris Require Import eris.
From clutch.eris.lib.sampling.utils Require Import lemmas.

#[local] Open Scope R.

Ltac add_hint t := let n := fresh "hint" in have n := t.

Ltac extract_val_eq :=
  repeat match goal with 
  | H : #?n = #?m |- _ => injection H as H
  | H : Z.of_nat _ = Z.of_nat _ |- _ => apply Nat2Z.inj in H
  end.

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

Ltac simpl_expr :=
  repeat (
      match goal with 
      | |- context[(?v1 * (?v2 * /?v1))] => 
            rewrite (Rmult_div_assoc v1 v2 v1) (Rmult_div_r v1 v2)
      | |- context[((?v1 * ?v2) * /?v1)] => 
            rewrite (Rmult_div_r v1 v2)

      | |- ?n * _ < ?n * _ => apply Rmult_lt_compat_l
      | |- ?n * _ <= ?n * _ => apply Rmult_le_compat_l
      | |- ?n * _ = ?n * _ => apply Rmult_eq_compat_l
      
      | |- _ < _ */?n => apply (Rmult_lt_reg_l n)
      | |- _ <= _ */?n => apply (Rmult_le_reg_l n)
      | |- _ = _ */?n => apply (Rmult_eq_reg_l n)

      | |- _ * /?n < _  => apply (Rmult_lt_reg_l n)
      | |- _ * /?n <= _  => apply (Rmult_le_reg_l n)
      | |- _ * /?n = _  => apply (Rmult_eq_reg_l n)

      | |- _ + ?n = _ + ?n => apply (Rplus_eq_compat_r n)
      | |- ?n + _ = ?n + _ => apply (Rplus_eq_compat_l n)
      end ||
      rewrite Rplus_0_l || rewrite Rplus_0_r ||
      rewrite Rmult_1_l || rewrite Rmult_1_r ||
      rewrite Rmult_0_l || rewrite Rmult_0_r ||
      rewrite Rdiv_1_l  || rewrite Rdiv_1_r ||
      rewrite Rdiv_def ||
      lra ||
      auto||
      solve[apply cond_nonneg] ||
      solve[apply pos_INR_S] ||
      solve[apply pos_INR] ||
      solve[apply le_INR; lia] ||
      solve[apply lt_INR; lia] ||
      solve[apply INR_S_not_0]
    ).

Search (_ = _ -> _ + ?a = _ + ?a).
