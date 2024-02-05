From clutch.ub_logic Require Export ub_clutch lib.map hash lib.list merkle.merkle_tree.
Import Hierarchy.
Set Default Proof Using "Type*".
Open Scope nat.

Section unreliable_storage.
  Context `{!ub_clutchGS Σ}.
  Variables ε_write ε_read: nonnegreal.
  Variables unreliable_write_program unreliable_read_program:val.

  Axiom unreliable_write_spec :
    ∀ l (n:nat), 
    {{{€ ε_write ∗ ∃ v, l ↦ v }}}
      unreliable_write_program #l #n
      {{{ RET #(); l ↦ #n}}}.
  Axiom unreliable_read_spec :
    ∀ l (n:nat), 
    {{{€ ε_read ∗ l ↦ #n }}}
      unreliable_read_program #l 
      {{{ RET #n; l ↦ #n}}}.

  Variables val_bit_size':nat.
  Variables max_hash_size : nat.
  Definition val_bit_size : nat := S val_bit_size'.
  Definition val_size_for_hash := 2^val_bit_size -1.
  
  Fixpoint tree_relate (n:nat) (l:loc) (t:merkle_tree) :iProp Σ :=
    match n with
    | O => (∃ (hv v:nat),  l ↦ (#hv, #v)%V ∗ ⌜t= (Leaf hv v)⌝)
    | S n' => ∃ (hv:nat) (leftbrl rightbrl:loc) leftbr rightbr,
               l ↦ (#hv, #leftbrl, #rightbrl)%V ∗
               ⌜t=(Branch hv leftbr rightbr)⌝ ∗
               tree_relate n' leftbrl leftbr ∗
               tree_relate n' rightbrl rightbr
  end.

  Definition pow : val :=
    rec: "pow" "x":=
      if: "x"=#0 then #1 else #2 * ("pow" ("x"-#1)).

  Definition tree_builder_helper : val:=
    rec: "helper" "lhmf" "n" "list":=
      if: "n" = #0
      then
        let: "head":= list_head "list" in 
        let: "hash" := "lhmf" "head" in
        ("hash", Alloc ("hash", "head"))
      else
        let, ("list1", "list2") := list_split (pow ("n"-#1)) "list" in
        let, ("lhash", "ltree") := "helper" ("n"-#1) "list1" in
        let, ("rhash", "rtree") := "helper" ("n"-#1) "list2" in
        let: "hash" := "lhmf" (pow "n" * "lhash" + "rhash") in
        ("hash", Alloc ("hash", "ltree", "rtree"))
  .

  Definition tree_builder : val :=
    λ: "list" "height",
      let: "lhmf" := init_hash val_size_for_hash #() in
      tree_builder_helper "lhmf" "height" "list"
  .
  
                                 
    

  
End unreliable_storage.
