From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list sparse_vector_technique.

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
  size (XS ∖ YS ∪ YS ∖ XS).

Section list_dist.
  Context `{Countable T}.

  #[global] Instance list_dist_Comm : Comm (=) (list_dist (T := T)).
  Proof. intros ??. rewrite /list_dist. f_equal. multiset_solver. Qed.

  Lemma list_dist_remove (xs1 xs2 ys1 ys2 : list T) (n : T) :
    list_dist (xs1 ++ [n] ++ xs2) (ys1 ++ [n] ++ ys2) = list_dist (xs1 ++ xs2) (ys1 ++ ys2).
  Proof. rewrite /list_dist !list_to_set_disj_app. f_equal. multiset_solver. Qed.

  Lemma list_dist_update (xs ys : list T) (n m : T) :
    n ≠ m → list_dist (xs ++ [n] ++ ys) (xs ++ [m] ++ ys) = 2.
  Proof.
    intros Hneq. rewrite /list_dist.
    rewrite !list_to_set_disj_app.
    match goal with
    | |- size ?X = _ => assert (X = {[+ n; m +]}) as -> by multiset_solver
    end.
    rewrite gmultiset_size_disj_union 2!gmultiset_size_singleton //.
  Qed.

  Lemma list_dist_same `{Countable T} (xs : list T) :
    list_dist xs xs = 0.
  Proof.
    rewrite /list_dist.
    by match goal with
       | |- size ?X = _ => assert (X = ∅) as -> by multiset_solver
       end.
  Qed.

  Lemma list_dist_cons_l (x : T) (xs : list T) :
    list_dist (x :: xs) xs = 1.
  Proof.
    rewrite /list_dist.
    rewrite list_to_set_disj_cons.
    match goal with
    | |- size ?X = _ => assert (X = {[+ x +]}) as -> by multiset_solver
    end.
    rewrite gmultiset_size_singleton //.
  Qed.

  Lemma list_dist_cons_r (x : T) (xs : list T) :
    list_dist xs (x :: xs) = 1.
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

End list_dist.

#[global] Program Instance list_Distance `{Countable T, Inject T val} : Distance (list T) :=
  {| distance xs ys := INR (list_dist xs ys) |}.
Next Obligation. intros => /=. apply pos_INR. Qed.
Next Obligation. intros => /=. rewrite list_dist_same //. Qed.
Next Obligation.
  move => ???? xs ys /=.


  (* Hmm, this is of course not true - [xs] and [ys] are only permutationally equal... *)
Admitted.


Inductive neighbour {T} (xs ys : list T) : Prop :=
| Addition a b n : xs = a ++ b → ys = a ++ [n] ++ b → neighbour xs ys
| Deletion a b n : xs = a ++ [n] ++ b → ys = a ++ b → neighbour xs ys.

Lemma neighbour_dist `{Countable T} (xs ys : list T) :
  neighbour xs ys → list_dist xs ys = 1.
Proof.
  rewrite /list_dist.
  inversion_clear 1; subst;
    rewrite !list_to_set_disj_app;
    match goal with
    | |- size ?X = _ => assert (X = {[+ n +]}) as -> by multiset_solver
    end;
    rewrite gmultiset_size_singleton //.
Qed.
