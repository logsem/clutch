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

  Lemma SeriesC_finite_elem_lt :
    ∀ (n : nat) (f : (fin (S (S n)) → R)) (r : R),
    (0 < r)%R →
    (∀ k, 0 < f k) →
    is_seriesC f r →
    ∀ k, f k < r.
  Proof.
    move=>n f r r_pos f_pos is_seriesC_f k.
    rewrite -(is_seriesC_unique _ _ is_seriesC_f).
    rewrite (SeriesC_split_elem _ k);
      last first.
    { by eexists. }
    { move=>b.
      pose proof (f_pos b).
      lra.
    }
    rewrite SeriesC_singleton_dependent Series_fin_first Series_fin_first /=.
    pose proof (f_pos 0%fin).
    pose proof (f_pos 1%fin).
    match goal with
    | |- context [SeriesC ?f] => unshelve epose proof (SeriesC_ge_0' f _)
    end.
    { move=>i /=.
      case_bool_decide; last lra.
      pose proof (f_pos (FS (FS i))).
      lra.
    }
    do 2 case_bool_decide; subst; last discriminate; lra.
  Qed.
  
  Lemma SeriesC_nat_elem_lt :
    ∀ (f : nat → R) (r : R),
    (0 < r)%R →
    (∀ k, 0 < f k) →
    is_seriesC f r →
    ∀ k, f k < r.
  Proof.
    move=>f r r_pos f_pos is_seriesC_f k.
    rewrite -(is_seriesC_unique _ _ is_seriesC_f).
    rewrite (SeriesC_split_elem _ k);
      last first.
    { by eexists. }
    { move=>b.
      pose proof (f_pos b).
      lra.
    }
    rewrite SeriesC_singleton_dependent SeriesC_Series_nat (Series.Series_incr_n _ 2) /=; try lia; last first.
    { apply ex_seriesC_nat, (ex_seriesC_le _ f); last by eexists.
      move=>i.
      pose proof (f_pos i).
      case_bool_decide; lra.
    } 
    pose proof (f_pos 0%nat).
    pose proof (f_pos 1%nat).
    rewrite -SeriesC_Series_nat.
    match goal with
    | |- context [SeriesC ?f] => unshelve epose proof (SeriesC_ge_0' f _)
    end.
    { move=>i /=.
      case_bool_decide; last lra.
      pose proof (f_pos (S (S i))).
      lra.
    }
    do 2 case_bool_decide; subst; last discriminate; lra.
  Qed.
