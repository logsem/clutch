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

  Lemma pow_spec (n:nat):
    {{{ True }}}
      pow #n
      {{{(x:nat), RET (#x); ⌜x = 2^n⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iLöb as "IH" forall (Φ n).
    rewrite /pow.
    wp_pures. rewrite -/pow.
    case_bool_decide; wp_pures.
    - iModIntro. replace (1%Z) with (Z.of_nat 1) by lia. iApply "HΦ".
      iPureIntro. inversion H. assert (n=0) by lia. subst. by simpl.
    - replace (Z.of_nat n - 1)%Z with (Z.of_nat (n-1)); last first.
      + rewrite Nat2Z.inj_sub; first lia.
        destruct n; last lia. done.
      + wp_apply ("IH"). 
        iIntros (x) "%".
        wp_pures.
        iModIntro.
        replace (2*_)%Z with (Z.of_nat (2*x)); last first.
        * rewrite Nat2Z.inj_mul. f_equal.
        * iApply "HΦ". iPureIntro. subst.
          rewrite -PeanoNat.Nat.pow_succ_r'. f_equal.
          destruct n; try done. lia.
  Qed.

  (* Building the tree*)
  Definition tree_builder_helper : val:=
    rec: "helper" "lhmf" "n" "list":=
      if: "n" = #0
      then
        let: "head":= (match: (list_head "list") with
                       | SOME "a" => "a"
                       |NONE => #()
                       end ) in 
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
      (tree_builder_helper "lhmf" "height" "list", "lhmf")
  .

  Inductive tree_leaf_list: merkle_tree -> list nat -> Prop :=
  | tree_leaf_list_lf h lf: tree_leaf_list (Leaf h lf) (lf::[])
  | tree_leaf_list_br a alist b blist h: tree_leaf_list a alist ->
                       tree_leaf_list b blist ->
                       tree_leaf_list (Branch h a b) (alist ++ blist).

  Lemma tree_builder_helper_spec (list:list nat) (vlist: val) (height:nat) (m:gmap nat Z) (f:val):
    size (m) + 2^(S height) - 1 <= max_hash_size ->
    length list = 2^height ->
    is_list list vlist ->
    {{{ hashfun_amortized val_size_for_hash max_hash_size f m ∗
        ⌜coll_free m⌝ ∗
        € (nnreal_nat (2^(S height)-1) * amortized_error val_size_for_hash max_hash_size)%NNR
    }}}
      tree_builder_helper f #height vlist 
      {{{ (hash:nat) (l:nat), RET (#hash, #l);
          ∃ (m':gmap nat Z) (tree:merkle_tree),
            ⌜m ⊆ m'⌝ ∗
            ⌜size (m') <= size (m) + 2^(S height) - 1⌝ ∗
            hashfun_amortized val_size_for_hash max_hash_size f m' ∗
            ⌜coll_free m'⌝ ∗
            ⌜tree_leaf_list tree list⌝ ∗
            ⌜tree_valid val_bit_size height tree m'⌝ ∗
            ⌜root_hash_value tree = hash ⌝
      }}}.
  Proof.
    iIntros (Hmsize Hlength Hislist Φ) "(H&%Hcollfree&Herr) HΦ".
    iInduction height as [|] "IH" forall (list vlist m Hmsize Hlength Hislist Φ Hcollfree).
    - rewrite /tree_builder_helper. wp_pures.
      assert (∃ x:nat, list = x::[]) as [x ->].
      { destruct list as [_| x [|]]; first done.
        - naive_solver.
        - done.
      }
      wp_apply (wp_list_head); first done.
      iIntros (?) "[[%?]|(%&%&%K&->)]"; first done.
      inversion K; subst.
      wp_pures.
      admit.
    - admit.
    Admitted.

  Lemma tree_builder_spec (list:list nat) (vlist: val) (height:nat):
    2^(S height) - 1  <= max_hash_size ->
    length list = 2^height ->
    is_list list vlist ->
    {{{ 
          € (nnreal_nat (2^(S height)-1) * amortized_error val_size_for_hash max_hash_size)%NNR
    }}}
      tree_builder vlist #height
      {{{ (hash:nat) (l:nat) (f:val), RET ((#hash, #l), f);
          ∃ (m:gmap nat Z) (tree:merkle_tree),
            hashfun_amortized val_size_for_hash max_hash_size f m ∗
            ⌜tree_valid val_bit_size height tree m⌝ ∗
            ⌜coll_free m⌝ ∗
            ⌜size (m) <= 2^(S height) - 1⌝ ∗
            ⌜tree_leaf_list tree list⌝ ∗
            ⌜root_hash_value tree = hash ⌝
      }}}.
  Proof.
    iIntros (Hmsize Hlistsize Hislist Φ) "Herr HΦ".
    rewrite /tree_builder.
    wp_pures.
    wp_apply (wp_init_hash_amortized _ max_hash_size); first done.
    iIntros (f) "H".
    wp_pures.
    wp_apply (tree_builder_helper_spec with "[$H $Herr]"); [done|done|done|..].
    { iPureIntro. intros ???H??. exfalso. destruct H. set_solver. }
    iIntros (hash l) "(%m'&%tree&%&%&H&%&%&%&%)".
    wp_pures. iModIntro.
    iApply "HΦ".
    iExists m', tree. iFrame.
    repeat iSplit; done.
  Qed.
  

  
  
                                 
    

  
End unreliable_storage.
