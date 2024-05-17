From clutch.app_rel_logic Require Import adequacy.
From clutch.app_rel_logic Require Export app_clutch.
Set Default Proof Using "Type*".
Open Scope R.

Section b_tree.
  Context `{!app_clutchGS Σ}.
  Context {min_child_num' : nat}.
  Context {depth : nat}.
  Local Definition min_child_num := S min_child_num'.
  (** For this example, intermediate nodes do not store keys themselves
      If the depth is 0, the node is a leaf, storing a single value
      otherwise, if the depth is S n, it has stores a list of k children, each pointing to a tree of depth n
      where k varies from min_child_num to 2* min_child_num inclusive
   *)

  (** Intermediate nodes of ranked b-trees store extra info, specifically for each branch it has as a child, 
      the number of leafs it has *)

  (** The naive algorithm for ranked b -tree is to sample from the sum of the total number of children, 
      and then traverse down to find that particular value *)

  (** The optimized algorithm for non-ranked b-tree is at each node, sample from 2*min_child_num 
      then walk down that branch. If the number exceeds the total number of children, repeat from the root
   *)

  (** The intuition is that we assume we are sampling from a "full"tree that has max children,
      but repeat if the child does not exist
   *)
  
End b_tree.

Section proofs.

End proofs.

