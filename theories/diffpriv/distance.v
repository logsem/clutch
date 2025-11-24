From Coq Require Export Reals Psatz.
From clutch.common Require Import inject.
From clutch.prob_lang Require Export lang.
From clutch.diffpriv.examples Require Import list.
From clutch.prelude Require Import base stdpp_ext.

#[local] Open Scope R.

Class Distance (A : Type) : Type := {
    distance_car :: Inject A val
  ; distance : A -> A -> R
  ; distance_pos a1 a2 : 0 <= distance a1 a2
  ; distance_0 a1 a2 : a1 = a2 → distance a1 a2 = 0
  (* leaving out symmetry and triangle inequality until they're needed. *)
  (* ; distance_sym a1 a2 : distance a1 a2 = distance a2 a1 *)
  (* ; distance_triangle a1 a2 a3 : distance a1 a3 <= distance a1 a2 + distance a2 a3 *)
}.
Arguments distance_car {_} _.
Coercion distance_car : Distance >-> Inject.
Arguments distance {_} _ _ _.
Coercion distance : Distance >-> Funclass.

Program Definition dZ : Distance Z := {| distance z z' := Rabs (IZR (z - z')) |}.
Next Obligation. intros => /= ; eauto using Rabs_pos. Qed.
Next Obligation. intros ?? -> => /=; replace (a2 - a2)%Z with 0%Z by lia. exact Rabs_R0. Qed.

Lemma dZ_bounded_cases x y k : dZ x y <= (IZR k) -> (- k <= x - y ∧ x - y <= k)%Z.
Proof.
  rewrite /dZ/distance Rabs_Zabs. intros h. apply le_IZR in h. revert h.
  apply Zabs_ind ; intros ; lia.
Qed.

Program Definition dnat : Distance nat := {| distance n n' := Rabs (IZR (n - n')) |}.
Next Obligation. intros => /= ; eauto using Rabs_pos. Qed.
Next Obligation. intros ?? -> => /=; replace (a2 - a2)%Z with 0%Z by lia. exact Rabs_R0. Qed.

Program Definition dtensor `(dA : Distance A) `(dB : Distance B) : Distance (A * B) :=
  {| distance x y := let (x1, x2) := x in let (y1, y2) := y in dA x1 y1 + dB x2 y2 |}.
Next Obligation. intros ???? [] []. apply Rplus_le_le_0_compat ; apply distance_pos. Qed.
Next Obligation. intros ???? [] [] [=]. rewrite !distance_0 //. lra. Qed.

Definition list_dist `{Countable T} (xs ys : list T) : Z :=
  sum_list_with (λ z, Z.abs (list_count z xs - list_count z ys)) (remove_dups (xs ++ ys)).

Section list_dist.
  Context `{Countable T}.

  #[global] Instance list_dist_Comm : Comm (=) (list_dist (T := T)).
  Proof.
    intros ??. rewrite /list_dist.
    rewrite Permutation_app_comm.
    apply sum_list_with_ext => ??.
    lia.
  Qed.

  #[global] Instance list_dist_proper :
    Proper ((≡ₚ) ==> (≡ₚ) ==> (=)) (list_dist (T := T)).
  Proof.
    intros x x' Hxs y y' Hys. rewrite /list_dist.
    rewrite (sum_list_with_proper _ (remove_dups (x ++ y)) (remove_dups (x' ++ y'))); last first.
    { by do 2 f_equiv. }
    apply sum_list_with_ext => ??.
    rewrite Hxs Hys. done.
  Qed.

  Lemma list_dist_nonneg (xs ys : list T) :
    (0 ≤ list_dist xs ys)%Z.
  Proof.
    rewrite /list_dist.
    apply sum_list_with_pos => ??. lia.
  Qed.

  Lemma list_dist_same `{Countable T} (xs : list T) :
    (list_dist xs xs = 0)%Z.
  Proof.
    rewrite /list_dist.
    rewrite -(sum_list_with_0 (remove_dups (xs ++ xs))).
    apply sum_list_with_ext => ??.
    lia.
  Qed.

  Lemma list_dist_cons x (xs ys : list T) :
    list_dist (x :: xs) (x :: ys) = list_dist xs ys.
  Proof.
    rewrite /list_dist.
    assert (remove_dups ((x :: xs) ++ x :: ys) ≡ₚ remove_dups (x :: xs ++ ys)) as ->.
    { rewrite {1}[remove_dups _]/= decide_True //; [|set_solver].
      apply remove_dups_Permutation. rewrite -Permutation_middle //. }
    rewrite (sum_list_with_elem_of x); [|apply elem_of_remove_dups; set_solver].
    rewrite !list_count_hd.
    erewrite (sum_list_with_ext _ _ (λ z, Z.abs (list_count z xs - list_count z ys))); last first.
    { intros ??%elem_of_list_remove => /=. rewrite decide_False //. }
    assert (Z.abs ((1 + list_count x xs)%nat - (1 + list_count x ys)%nat) =
            Z.abs ((list_count x xs)%nat - (list_count x ys)%nat)) as -> by lia.
    destruct (decide (x ∈ xs ++ ys)).
    - rewrite [list_delete _ _]/= decide_True //.
      rewrite -(sum_list_with_elem_of x) //.
      apply elem_of_remove_dups; set_solver.
    - rewrite list_count_not_elem_of; [|set_solver].
      rewrite list_count_not_elem_of; [|set_solver].
      rewrite [list_delete _ _]/= decide_False //= decide_True //.
  Qed.

  Lemma list_dist_fmap_le zs1 zs2 (f : Z → Z) :
    (list_dist (f <$> zs1) (f <$> zs2) ≤ list_dist zs1 zs2)%Z.
  Proof.
    rewrite /list_dist.
    rewrite -fmap_app.
    rewrite (sum_list_map_list_preimage f _ (remove_dups (zs1 ++ zs2))).

    erewrite sum_list_with_ext; last first.
    { intros ??.
      erewrite (list_count_sum_list_preimage _ zs2).
      erewrite (list_count_sum_list_preimage _ zs1).
      rewrite /list_preimage.
      erewrite (sum_list_with_Permutation _ (filter _ (remove_dups (zs2 ++ _)))); last first.
      { erewrite remove_dups_Permutation; [done|]. apply Permutation_app_comm. }
      rewrite -sum_list_with_sub.
      reflexivity. }

    etrans.
    { eapply sum_list_with_le => x Hx. apply Z_abs_sum_le => /=. }

    erewrite (sum_list_with_Permutation _ (remove_dups (_ <$> remove_dups _))); [done|].
    symmetry.
    apply remove_dups_fmap_permutation.
  Qed.

  Lemma Z_add_le_mono_nonneg_r (z1 z2 z3 : Z) :
    (0 ≤ z3 → z1 ≤ z2 → z1 ≤ z2 + z3)%Z.
  Proof. lia. Qed.

  Lemma list_filter_bound `{!∀ a, Decision (P a)} (xs ys : list T):
    (list_dist (filter P xs) (filter P ys) ≤ list_dist xs ys)%Z.
  Proof.
    rewrite /list_dist.
    rewrite -list.filter_app.
    rewrite /list_dist.
    rewrite (sum_list_with_split P (remove_dups (xs ++ ys))).
    apply Z_add_le_mono_nonneg_r.
    { apply sum_list_with_pos => ??. lia. }
    rewrite filter_remove_dups.
    apply sum_list_with_le => z.
    rewrite elem_of_list_filter => ?.
    rewrite 2!list_count_filter_alt.
    case_bool_decide; lia.
  Qed.

  Lemma length_sum_list_with_1 (xs : list Z) :
    (sum_list_with (λ _, 1) xs = length xs)%Z.
  Proof. induction xs; [done|]. rewrite sum_list_with_cons /=. lia. Qed.

  Lemma list_length_bound (xs ys : list Z):
    (Z.abs (length xs - length ys) ≤ list_dist xs ys)%Z.
  Proof.
    rewrite /list_dist.
    rewrite -2!length_sum_list_with_1.
    rewrite (sum_list_with_multiplicity xs ys) (sum_list_with_multiplicity ys xs).
    rewrite Permutation_app_comm.
    rewrite -sum_list_with_sub /=.
    etrans; [apply Z_abs_sum_le|].
    eapply sum_list_with_le => ??.
    lia.
  Qed.

  Inductive neighbour {T} (xs ys : list T) : Prop :=
  | neighbour_add_l a b n : xs = a ++ [n] ++ b → ys = a ++ b → neighbour xs ys
  | neighbour_add_r a b n : xs = a ++ b → ys = a ++ [n] ++ b → neighbour xs ys.

  Lemma neighbour_dist (xs ys : list T) :
    neighbour xs ys → list_dist xs ys = 1%nat.
  Proof.
    rewrite /list_dist.
    inversion_clear 1; subst.
    - rewrite (sum_list_with_elem_of n); last first.
      { apply elem_of_remove_dups. set_solver. }
      rewrite !list_count_app list_count_hd /=.
      erewrite (sum_list_with_ext _ _ (λ _, 0%Z)); last first.
      { intros z ?. rewrite !list_count_app /=.
        rewrite decide_False; [lia|].
        intros ->.
        eapply (remove_dups_list_remove (T := T)); [|done].
        apply elem_of_remove_dups. set_solver.  }
      rewrite sum_list_with_0. lia.
    - rewrite (sum_list_with_elem_of n); last first.
      { apply elem_of_remove_dups. set_solver. }
      rewrite !list_count_app list_count_hd /=.
      erewrite (sum_list_with_ext _ _ (λ _, 0%Z)); last first.
      { intros z ?. rewrite !list_count_app /=.
        rewrite decide_False; [lia|].
        intros ->.
        eapply (remove_dups_list_remove (T := T)); [|done].
        apply elem_of_remove_dups. set_solver.  }
      rewrite sum_list_with_0. lia.
  Qed.

End list_dist.

Program Definition dlist T `{Countable T, Inject T val} : Distance (list T) :=
  {| distance xs ys := IZR (list_dist xs ys) |}.
Next Obligation. intros => /=. apply IZR_le, list_dist_nonneg. Qed.
Next Obligation. move => ?????? ->. rewrite -INR_0 list_dist_same //. Qed.
