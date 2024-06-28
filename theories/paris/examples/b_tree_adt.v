(* This file is a continuation of the B+ tree example from b_tree.v We
   define additional operations for creating B+ and ranked B+ trees,
   and then prove contextual equivalence of a packaged ADT that
   combines these operations with the sampling routines defined in
   b_tree.v *)


From Coq.Program Require Import Wf.
From stdpp Require Import list.
From clutch.paris Require Import paris list.
From clutch.paris Require adequacy.
From clutch.paris Require Import b_tree.
Set Default Proof Using "Type*".
Open Scope R.
Opaque INR.

Section b_tree_adt.

  Context {max_child_num' : nat}.

  Definition init_tree : val :=
    λ: "v", ref (InjL "v").

  Definition init_ranked_tree : val :=
    λ: "v", ref ((#1, InjL "v")).

  (*
  Definition select_child : val :=
    rec: "select" "l",
        match: "l" with
        | InjL <> => NONE
        | InjR "a" =>
            match: Snd ("a") with
            | InjL <> => Fst "a"
            | InjR "_" =>
                let: "b" = flip ()
   *)

  (* Tries to insert a new child into a list of children. The child list may already be full,
     so we return a pair, where the second component is (optionally)  list of the subset of children
     resulting from splitting the list.

     An optimal B+-tree would try to split the lists evenly, but that is really irrelevant for our purposes,
     so for simplicity we just put solely the new element in the second list.
   *)

  Definition insert_child_list : val :=
    λ: "l" "v",
      if: list_length "l" < #(S max_child_num') then
        (InjR (list_cons "v" "l"), NONE) 
      else
        (InjR ("l"), SOME (InjR (list_cons "v" list_nil))).
  
  Definition insert_tree_aux : val :=
    rec: "insert_tree" "p" "v" :=
        let: "t" := !"p" in
        match: "t" with
        | InjL "v" => SOME (InjL "v")
        | InjR "l" =>
            (* Insert into a random child, this shows our sampler code is "robust"
               to a variety of tree shapes *)
            let: "n" := rand (list_length "l") in
            let: "c" := list_nth "l" "n" in
            match: "insert_tree" "c" "v" with
            | NONE => NONE
            | SOME "new" =>
                (* Either the child was a leaf, or we had to split the child, so
                   we must insert "new" into the current node *)
                let, ("t'", "opt") := insert_child_list "l" "v" in
                "p" <- "t'";;
                "opt"
            end
        end.

  Definition insert_tree : val :=
    λ: "p" "v",
      match: insert_tree_aux "p" "v" with
      | NONE => #()
      | SOME "t'" =>
          (* The root node had to be split, so we need to create a new root node which will have as children
             t' and the sibling stored in !p *)
          let: "new_root" := InjR (list_cons (ref !"p") (list_cons (ref "t'") list_nil)) in
          "p" <- "new_root"
      end.
      

End b_tree_adt.
