From clutch.ub_logic Require Export ub_clutch lib.map hash lib.list merkle.merkle_tree.
Import Hierarchy.
Set Default Proof Using "Type*".
Open Scope nat.

Section unreliable_storage.
  Context `{!ub_clutchGS Σ}.
  Variables unreliable_alloc_program unreliable_write_program unreliable_read_program:val.

  Axiom unreliable_alloc_spec :
    ∀ (m:nat),
    m>0 -> 
    {{{ True }}}
      unreliable_alloc_program #m
      {{{ (x:nat), RET #x; True }}}.

  
  Axiom unreliable_read_spec :
    ∀ (l : nat),
    {{{ True }}}
      unreliable_read_program #l 
      {{{(n:nat), RET #n; True}}}.


  Axiom unreliable_write_spec :
    ∀ (n l: nat),
    {{{ True }}}
      unreliable_write_program #l #n
      {{{ RET #(); True}}}.

  Variables val_bit_size':nat.
  Variables max_hash_size : nat.
  Definition val_bit_size : nat := S val_bit_size'.
  Definition val_size_for_hash := 2^val_bit_size -1.

  Definition pow : val :=
    rec: "pow" "x":=
      if: "x"=#0 then #1 else #2 * ("pow" ("x"-#1)).

  Definition tree_builder_helper : val:=
    rec: "helper" "lhmf" "n" "list":=
      if: "n" = #0
      then
        let: "head":= list_head "list" in 
        let: "hash" := "lhmf" "head" in
        let: "l" := unreliable_alloc_program #2 in
        unreliable_write_program "l" "hash";;
        unreliable_write_program ("l"+#1) "head";;
        ("hash", "l")
      else
        let, ("list1", "list2") := list_split (pow ("n"-#1)) "list" in
        let, ("lhash", "ltree") := "helper" ("n"-#1) "list1" in
        let, ("rhash", "rtree") := "helper" ("n"-#1) "list2" in
        let: "hash" := "lhmf" (pow "n" * "lhash" + "rhash") in
        let: "l" := unreliable_alloc_program #3 in
        unreliable_write_program "l" "hash";;
        unreliable_write_program ("l"+#1) "ltree";;
        unreliable_write_program ("l"+#2) "rtree";;
        ("hash", "l")
  .

  Definition tree_builder : val :=
    λ: "list" "height",
      let: "lhmf" := init_hash val_size_for_hash #() in
      tree_builder_helper "lhmf" "height" "list"
  .
  
                                 
    

  
End unreliable_storage.
