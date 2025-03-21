From clutch.eris Require Import eris.
From clutch.eris.lib.sampling Require Export list_double_ind.

Local Open Scope R.

Local Ltac done ::= 
  solve[lia || lra || nra || real_solver || tactics.done || auto].
  
Lemma ec_contradict_lt0 `{!erisGS Σ} (ε : R) : (ε < 0)%R -> ↯ ε ⊢ False.
Proof.
  iIntros "%ε_nonpos Herr".
  iPoseProof (ec_valid with "Herr") as "[%Hε _]". lra.
Qed.
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
  


Ltac add_hint t := let n := fresh "hint" in have n := t.

Set Printing Coercions.


Lemma INR_S_not_0 (n : nat) : 
  INR (S n) ≠ 0.
Proof.
  Set Printing Coercions.
  intros Heq.
  assert (S n ≠ 0)%nat as Heq' by lia.
  by apply Heq', INR_eq.
  Unset Printing Coercions. 
Qed.



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
Ltac extract_val_eq :=
  repeat match goal with 
  | H : #?n = #?m |- _ => injection H as H
  | H : Z.of_nat _ = Z.of_nat _ |- _ => apply Nat2Z.inj in H
  end.

Ltac simpl_expr :=
  repeat (
      match goal with 
      | |- context[(?v * (_ * /?v))] => 
            rewrite !Rmult_div_assoc Rmult_div_r

      | |- ?n * _ < ?n * _ => apply Rmult_lt_compat_l
      | |- ?n * _ <= ?n * _ => apply Rmult_le_compat_l
      | |- ?n * _ = ?n * _ => apply Rmult_eq_compat_l
      
      | |- _ < _ */?n => apply (Rmult_lt_reg_l n)
      | |- _ <= _ */?n => apply (Rmult_le_reg_l n)
      | |- _ = _ */?n => apply (Rmult_eq_reg_l n)

      | |- _ * /?n < _  => apply (Rmult_lt_reg_l n)
      | |- _ * /?n <= _  => apply (Rmult_le_reg_l n)
      | |- _ * /?n = _  => apply (Rmult_eq_reg_l n)
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

Lemma Rmult_le_1_le_r (r1 r2 : R) :
  0 <= r1 <= 1 -> 
  0 <= r2 ->
  0 <= r1 * r2 <= r2.
Proof.
  real_solver.
Qed.

Lemma Rmult_le_1_le_l (r1 r2 : R) :
  0 <= r1 <= 1 -> 
  0 <= r2 ->
  0 <= r2 * r1 <= r2.
Proof.
  real_solver.
Qed.

Lemma Rmult_le_1 (r1 r2 : R) :
  0 <= r1 <= 1 -> 
  0 <= r2 <= 1 ->
  0 <= r1 * r2 <= 1.
Proof.
  real_solver.
Qed.

Lemma Rpow_le_1 (r : R) (k : nat) :
  0 <= r <= 1 -> 
  0 <= r ^ k <= 1.
Proof.
  elim: k => // => n IH //=.
Qed.

  
