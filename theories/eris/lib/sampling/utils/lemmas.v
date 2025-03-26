From clutch.eris Require Import eris.

#[local] Open Scope R.

Lemma ec_contradict_lt0 `{!erisGS Σ} (ε : R) : (ε < 0)%R -> ↯ ε ⊢ False.
Proof.
  iIntros "%ε_nonpos Herr".
  iPoseProof (ec_valid with "Herr") as "[%Hε _]". lra.
Qed.
  
Lemma INR_S_not_0 (n : nat) : 
  INR (S n) ≠ 0.
Proof.
  Set Printing Coercions.
  intros Heq.
  assert (S n ≠ 0)%nat as Heq' by lia.
  by apply Heq', INR_eq.
  Unset Printing Coercions. 
Qed.


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
  elim: k => [|n IH] /=; real_solver.
Qed.

  
