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
  move=> Heq.
  rewrite -INR_0 in Heq.
  by apply INR_eq in Heq.
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

Lemma foldr_last {A : Type} (l : list A) (x y : A) (f : A → A → A) :
  Assoc eq f ->
  Comm eq f ->
  foldr f x (l ++ [y]) = f y (foldr f x l).
Proof.
  move => Ha Hc.
  rewrite -!fold_symmetric // fold_left_app //=.
Qed.

Lemma Series_fin_first (n : nat) (D : fin (S n) → R) : 
  SeriesC D = (D 0%fin + SeriesC (λ (k : fin n), D (FS k)))%R.
Proof.
  rewrite !SeriesC_finite_foldr /= foldr_fmap //.
Qed.

Lemma Series_fin_last (n : nat) (D : fin (S n) → R) : 
  SeriesC D = (SeriesC (λ (k : fin n), D (fin_S_inj k)) + D (@nat_to_fin n (S n) (Nat.lt_succ_diag_r n)))%R.
Proof.
  assert (Assoc eq Rplus ∧ Comm eq Rplus) as [??]. {
    pose proof Rplus_assoc.
    pose proof Rplus_comm.
    by split=>>.
  }
  rewrite !SeriesC_finite_foldr -foldr_fmap enum_fin_split fmap_app /= foldr_last.
  rewrite Rplus_comm !foldr_fmap //.
Qed.


  Lemma fmap_repeat : ∀ (A B : Type) (f : A → B) (a : A) (n : nat), f <$> (repeat a n) = repeat (f a) n.
  Proof.
    move=>A B f a.
    elim=>[//|n /= <- //].
  Qed.

  Lemma list_sum_repeat : ∀ (n k : nat), list_sum (repeat n k) = (n * k)%nat.
  Proof.
    move=>n.
    elim=>[/=|k /= ->]; lia.
  Qed.
