From Coq Require Export Reals Psatz.
From stdpp Require Import gmultiset.
From clutch.prelude Require Import base.
From clutch.common Require Import inject.
From clutch.prob_lang Require Export lang.
From clutch.diffpriv_simple_pw.examples Require Import list.

#[local] Open Scope R. 

Class Distance (A : Type) : Type := {
    distance_car :: Inject A val                                                  
  ; distance : A -> A -> R
  (* Not using [Equiv A] directly to avoid universe issues when quantifying over
     [Distance] in the logic, in particular. *)
  ; distance_equiv : A -> A -> Prop   
  ; distance_pos a1 a2 : 0 <= distance a1 a2
  ; distance_0 a1 a2 : distance_equiv a1 a2 → distance a1 a2 = 0
  ; distance_sep a1 a2 : distance a1 a2 <= 0 -> distance_equiv a1 a2
  (* leaving out symmetry and triangle inequality until they're needed. *)
  (* ; distance_sym a1 a2 : distance a1 a2 = distance a2 a1 *)
  (* ; distance_triangle a1 a2 a3 : distance a1 a3 <= distance a1 a2 + distance a2 a3 *)
}.
Arguments distance_car {_} _.
Coercion distance_car : Distance >-> Inject.
Arguments distance {_} _ _ _.
Coercion distance : Distance >-> Funclass.

#[global] Instance Distance_equiv `{Distance A} : Equiv A := distance_equiv. 

Program Definition dZ : Distance Z := {| distance z z' := Rabs (IZR (z - z')); distance_equiv := (=) |}.
Next Obligation. intros => /= ; eauto using Rabs_pos. Qed.
Next Obligation. intros ?? -> => /=; replace (a2 - a2)%Z with 0%Z by lia. exact Rabs_R0. Qed.
Next Obligation.
  intros ?? => /= ; rewrite -abs_IZR. pose proof (IZR_le _ _ $ Zabs_pos (a1-a2)).
  intros h. assert (IZR (Z.abs (a1 - a2)) = 0) as h' by lra. revert h'.
  rewrite /equiv. apply Zabs_ind ; intros ? h' ; apply eq_IZR in h' ; lia.
Qed.

Program Definition dtensor `(dA : Distance A) `(dB : Distance B) : Distance (A * B) :=
  {| distance x y := let (x1, x2) := x in let (y1, y2) := y in dA x1 y1 + dB x2 y2;
     distance_equiv x y := let (x1, x2) := x in let (y1, y2) := y in x1 ≡ y1 ∧ x2 ≡ y2;
  |}.
Next Obligation. intros ???? [] []. apply Rplus_le_le_0_compat ; apply distance_pos. Qed.
Next Obligation. intros ???? [] [] []. rewrite !distance_0 //. lra. Qed.
Next Obligation.
  intros ???? [a b] [a' b'] ?.
  pose proof (distance_pos a a'). pose proof (distance_pos b b').
  assert (dA a a' <= 0) by lra. assert (dB b b' <= 0) by lra.
  pose proof (distance_sep a a'). pose proof (distance_sep b b').
  rewrite /equiv. intuition auto.
Qed.

(* TODO: move *)
Lemma size_list_to_set_disj `{Countable T} (xs : list T) :
  size (list_to_set_disj xs : gmultiset _) = length xs.
Proof.
  induction xs.
  - rewrite list_to_set_disj_nil //.
  - rewrite list_to_set_disj_cons.
    rewrite gmultiset_size_disj_union gmultiset_size_singleton IHxs //.
Qed.

Definition list_dist `{Countable T} (xs ys : list T) : nat :=
  let XS := list_to_set_disj xs : gmultiset T in
  let YS := list_to_set_disj ys : gmultiset T in
  size (XS ∖ YS ⊎ YS ∖ XS).

Section list_dist.
  Context `{Countable T}.

  #[global] Instance list_dist_Comm : Comm (=) (list_dist (T := T)).
  Proof. intros ??. rewrite /list_dist. f_equal. multiset_solver. Qed.

  #[global] Instance list_dist_proper :
    Proper ((≡ₚ) ==> (≡ₚ) ==> (=)) (list_dist (T := T)).
  Proof. intros ?? Hxs ?? Hys. rewrite /list_dist Hxs Hys //. Qed.

  Lemma list_dist_remove (xs1 xs2 ys1 ys2 : list T) (n : T) :
    list_dist (xs1 ++ [n] ++ xs2) (ys1 ++ [n] ++ ys2) = list_dist (xs1 ++ xs2) (ys1 ++ ys2).
  Proof. rewrite /list_dist !list_to_set_disj_app. f_equal. multiset_solver. Qed.

  Lemma list_dist_update (xs ys : list T) (n m : T) :
    n ≠ m → list_dist (xs ++ [n] ++ ys) (xs ++ [m] ++ ys) = 2%nat.
  Proof.
    intros Hneq. rewrite /list_dist.
    rewrite !list_to_set_disj_app.
    match goal with
    | |- size ?X = _ => assert (X = {[+ n; m +]}) as -> by multiset_solver
    end.
    rewrite gmultiset_size_disj_union 2!gmultiset_size_singleton //.
  Qed.

  Lemma list_dist_same `{Countable T} (xs : list T) :
    list_dist xs xs = 0%nat.
  Proof.
    rewrite /list_dist.
    by match goal with
       | |- size ?X = _ => assert (X = ∅) as -> by multiset_solver
       end.
  Qed.

  Lemma list_dist_cons_l (x : T) (xs : list T) :
    list_dist (x :: xs) xs = 1%nat.
  Proof.
    rewrite /list_dist.
    rewrite list_to_set_disj_cons.
    match goal with
    | |- size ?X = _ => assert (X = {[+ x +]}) as -> by multiset_solver
    end.
    rewrite gmultiset_size_singleton //.
  Qed.

  Lemma list_dist_cons_r (x : T) (xs : list T) :
    list_dist xs (x :: xs) = 1%nat.
  Proof. rewrite (comm list_dist). apply list_dist_cons_l. Qed.

  Lemma list_dist_nil_l (xs : list T) :
    list_dist [] xs = length xs.
  Proof.
    rewrite /list_dist.
    match goal with
    | |- size ?X = _ => assert (X = list_to_set_disj xs) as -> by multiset_solver
    end.
    rewrite size_list_to_set_disj //.
  Qed.

  Lemma list_dist_nil_r (xs : list T) :
    list_dist xs [] = length xs.
  Proof. rewrite (comm list_dist). apply list_dist_nil_l. Qed.

  Inductive neighbour {T} (xs ys : list T) : Prop :=
  | neighbour_add_l a b n : xs = a ++ [n] ++ b → ys = a ++ b → neighbour xs ys
  | neighbour_add_r a b n : xs = a ++ b → ys = a ++ [n] ++ b → neighbour xs ys.

  Lemma neighbour_dist (xs ys : list T) :
    neighbour xs ys → list_dist xs ys = 1%nat.
  Proof.
    rewrite /list_dist.
    inversion_clear 1; subst;
      rewrite !list_to_set_disj_app;
      match goal with
      | |- size ?X = _ => assert (X = {[+ n +]}) as -> by multiset_solver
      end;
      rewrite gmultiset_size_singleton //.
  Qed.  

End list_dist.

Program Definition dlist T `{Countable T, Inject T val} : Distance (list T) :=
  {| distance xs ys := INR (list_dist xs ys); distance_equiv := (≡ₚ) |}.
Next Obligation. intros => /=. apply pos_INR. Qed.
Next Obligation. move => ?????? ->. rewrite -INR_0 list_dist_same //. Qed.
Next Obligation.
  move => ???? xs ys /=.
  induction xs as [|x xs] in ys |-* => //=.
  - rewrite list_dist_nil_l. destruct ys; [done|].
    rewrite cons_length S_INR. pose proof (pos_INR (length ys)). lra.
  - destruct (decide (x ∈ ys)) as [Hin|Hnin].
    + destruct (proj1 (elem_of_Permutation _ _) Hin) as [ys' ->].
      intros Hdist.
      f_equiv. apply IHxs. etrans; [|apply Hdist]. right.
      rewrite /list_dist. do 2 f_equal. rewrite list_to_set_disj_cons.
      multiset_solver.
    + rewrite /list_dist list_to_set_disj_cons.
      set X := (list_to_set_disj xs).
      set Y := (list_to_set_disj ys).
      assert (x ∉ Y) by rewrite elem_of_list_to_set_disj //.
      assert (({[+ x +]} ⊎ X) ∖ Y = {[+ x +]} ⊎ X ∖ Y) as -> by multiset_solver.
      rewrite 2!gmultiset_size_disj_union gmultiset_size_singleton.
      rewrite !plus_INR INR_1.
      assert (0 <= size (X ∖ Y))%R by real_solver.
      assert (0 <= size (Y ∖ ({[+ x +]} ⊎ X)))%R by real_solver. lra.
Qed.
