(** * Meldable Heaps *)
From clutch.ert_logic Require Import ert_weakestpre lifting ectx_lifting primitive_laws expected_time_credits cost_models problang_wp proofmode ert_rules.
From clutch.lib Require Import utils.
From iris.proofmode Require Export tactics.
From Coq Require Export Reals Psatz.
From stdpp Require Import sorting.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Set Default Proof Using "Type*".
Require Import Lra.


Section program.

End program.


Section heaps.

  (** Binary trees *)
  Context (A : Type).

  Inductive BinaryTree : Type :=
    | Nil
    | Node (v : A) (l : BinaryTree) (r : BinaryTree).


  Fixpoint tree_size (t : BinaryTree) : nat
    := match t with
        | Nil => 0%nat
        | (Node _ l r) => 1 + (tree_size l) + (tree_size r)
       end.

  Fixpoint tree_to_list (t : BinaryTree) : list A
    := match t with
        | Nil => []
        | (Node x l r) => [x] ++ (tree_to_list l) ++ (tree_to_list r)
       end.


  (** Injections of Binary trees to val *)
  Fixpoint inject_binarytree `{!Inject A val} (b : BinaryTree) : val
    := match b with
        | Nil => NONEV
        | Node x l r => SOMEV (PairV (inject x) (PairV (inject_binarytree l) (inject_binarytree r)))
       end.

  Global Program Instance Inject_binarytree `{!Inject A val} : Inject BinaryTree val :=
    {| inject := inject_binarytree |}.
  Next Obligation. Admitted.


  Fixpoint is_binarytree `{!Inject A val} (b : BinaryTree) (v : val) :=
      match b with
      | Nil => v = NONEV
      | Node x l r => ∃ vl vr, v = SOMEV ((inject x), (vl, vr)) ∧ is_binarytree l vl /\ is_binarytree r vr
    end.

  Lemma is_binarytree_inject `{!Inject A val} b v :
      is_binarytree b v ↔ v = (inject b).
  Proof. Admitted.
  (*
      revert v.
      induction xs as [|x xs IH]; [done|]. split.
      - destruct 1 as (? & -> & ?). simpl.
        do 2 f_equal. by apply IH.
      - intros ->. eexists. split; [done|]. by apply IH.
    Qed.
   *)

  (** Heaps: Heap-ordered binary trees *)

  Context (R : relation A).
  Context (HTo : TotalOrder R).

  Definition HeapOrdered (v : A) (next : BinaryTree) : Prop
    := match next with
        | Nil => True
        | (Node v' _ _) => R v v'
       end.

  Inductive IsHeap : BinaryTree -> Prop :=
      | Heap_nil : IsHeap Nil
      | Heap_node (v : A) (l r : BinaryTree) :
          IsHeap l -> IsHeap r -> HeapOrdered v l -> HeapOrdered v r -> IsHeap (Node v l r).

  (** Heap operations *)

  (* Due to randomization, we will not be able to (or even want to) specify that the implementation
     produces a particular heap.

     Instead, we will only specify that it produces _some_ heap, and that heap has some properties
     with respect to the total order.  *)


  (* PROPERTY 1: First element of tree_to_list is always less than or equal to all subsequent elements *)

  (* SPEC (remove): if tree_to_list h = (a :: as), then tree_to_list (pop h) = as *)

  (* SPEC (insert): [x] ++ (tree_to_list h) ≡ₚ tree_to_list (insert x h)*)

  (* SPEC (merge): (tree_to_list h1) ++ (tree_to_list h2) ≡ₚ (tree_to_list (merge h1 h2)) *)




End heaps.


Section cmp.
  Context `{!ert_clutchGS Σ CostTick}.

  Context (A : Type).
  Context `[!Inject A val].

  Definition computable_relation (f : A -> A -> bool) : relation A
    := (fun a1 a2 => f a1 a2 = true).

  Definition cmp_spec (xs : list A) (c : val) (k : nat) (f : A -> A -> bool) : iProp Σ
    := ∀ (a1 a2 : A), {{{ ⧖ k }}} (c (inject a1) (inject a2)) {{{ v, RET #v; ⌜v = f a1 a2⌝ }}}.

End cmp.


Section program.

End program.
