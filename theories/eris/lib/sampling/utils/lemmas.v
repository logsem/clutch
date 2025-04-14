From clutch.eris Require Import eris.
From clutch.eris.lib.sampling.utils Require Import fintools.

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

Lemma Series_fin_first (n : nat) (D : fin (S n) → R) : 
  SeriesC D = (D 0%fin + SeriesC (λ (k : fin n), D (FS k)))%R.
Proof.
  rewrite !SeriesC_finite_foldr /= foldr_fmap //.
Qed.

Lemma foldr_last {A : Type} (l : list A) (x y : A) (f : A → A → A) :
  (∀ x y z, f x (f y z) = f (f x y) z) →
  (∀ x y, f x y = f y x) →
  foldr f x (l ++ [y]) = f y (foldr f x l).
Proof.
  move => Ha Hc.
  elim: l => [|h t IH] //.
  rewrite /= IH Hc -Ha (Hc _ h) //.
Qed.

Lemma Series_fin_last (n : nat) (D : fin (S n) → R) : 
  SeriesC D = (SeriesC (λ (k : fin n), D (fin_S_inj k)) + D (@nat_to_fin n (S n) (Nat.lt_succ_diag_r n)))%R.
Proof.
  rewrite !SeriesC_finite_foldr -foldr_fmap enum_fin_split fmap_app /= foldr_last; try (intros; lra).
  rewrite Rplus_comm.
  f_equal.
  rewrite !foldr_fmap //.
Qed.
