From clutch.ub_logic Require Export ub_clutch lib.map hash lib.list.
Import Hierarchy.
Set Default Proof Using "Type*".
Open Scope nat.

Section merkle_tree.
  Context `{!ub_clutchGS Σ}.
  Variables height:nat.
  Variables val_bit_size':nat.
  Variables max_hash_size : nat.
  Definition val_bit_size : nat := S val_bit_size'.
  Definition val_size:nat := (2^val_bit_size)-1.
  Variable (Hineq: (max_hash_size <= val_size)%nat).
  Definition leaf_bit_size : nat := 2*val_bit_size.
  (* Definition identifier : nat := 2^leaf_bit_size. *)
  Definition num_of_leafs : nat := 2^height.
  
  Inductive merkle_tree :=
  | Leaf (hash_value : nat) (leaf_value:nat)
  | Branch (hash_value : nat) (t1 t2:merkle_tree).

  Definition root_hash_value (t: merkle_tree) :=
    match t with
    | Leaf h _ => h
    | Branch h _ _ => h
    end.

  Inductive tree_relate: nat -> val -> merkle_tree -> Prop:=
  | tree_relate_lf (hv v:nat): tree_relate 0 (InjLV (#hv, #v)) (Leaf hv v)
  | tree_relate_br n (hv:nat) ll l lr r:
    tree_relate n ll l ->
    tree_relate n lr r ->
    tree_relate (S n) (InjRV (#hv, ll, lr)) (Branch hv l r)
  .

  Inductive tree_valid: merkle_tree -> gmap nat Z -> Prop :=
  |tree_valid_lf (h l:nat) m:
    h < 2^val_bit_size ->
    l < 2^leaf_bit_size ->
    m!!l%nat = Some (Z.of_nat h) ->
    tree_valid (Leaf h l) m
  |tree_valid_br (h:nat) l r m:
    tree_valid l m ->
    tree_valid r m ->
    h < 2^val_bit_size ->
    m!!((root_hash_value l)*2^val_bit_size + root_hash_value r)%nat=Some (Z.of_nat h) ->
    tree_valid (Branch h l r) m.
    

  Definition map_valid (m:gmap nat Z) : Prop := coll_free m.

  Definition compute_hash_from_leaf : val :=
    rec: "compute_hash_from_leaf" "ltree" "lhmf" "ll" "lf" := 
    match: "ltree" with
    | InjL "x" => "lhmf" "lf"  
    | InjR "x"  => let: "b" := (match: list_head "ll" with
                               | SOME "a" => "a"
                               | NONE => #()
                               end
                              ) in
                  let: "ll'" := (match: list_tail "ll" with
                               | SOME "a" => "a"
                               | NONE => #()
                                 end
                                ) in
                  let, ("l", "r") := Snd "x" in
                  if: "b"
                  then "lhmf"
                         (("compute_hash_from_leaf" "l" "lhmf" "ll'" "lleaf")*#(2^val_bit_size)+"r")
                  else "lhmf"
                         ("l"*#(2^val_bit_size)+("compute_hash_from_leaf" "r" "lhmf" "ll'" "lleaf"))
    end

  .

  Inductive tree_value_match: merkle_tree -> nat -> list bool -> Prop:=
  | tree_value_match_lf h lf: tree_value_match (Leaf h lf) lf []
  | tree_value_match_left h l r xs v:
    tree_value_match l v xs ->
    tree_value_match (Branch h l r) v (true::xs)
  | tree_value_match_right h l r xs v:
    tree_value_match r v xs ->
    tree_value_match (Branch h l r) v (false::xs).

  (** Lemmas *)
  

  (** Spec *)
  Lemma wp_correct_check (ltree:val) (tree:merkle_tree) (m:gmap nat Z) (v:nat) (path:list bool) llist f E:
     {{{ ⌜tree_relate height ltree tree⌝ ∗
        ⌜tree_valid tree m⌝ ∗
        hashfun_amortized (val_size-1)%nat max_hash_size f m ∗
        ⌜is_list path llist⌝ ∗
        ⌜tree_value_match tree v path⌝ ∗
        ⌜map_valid m⌝ }}}
      compute_hash_from_leaf ltree f llist (#v) @ E
      {{{ (retv:Z), RET #retv;
          hashfun_amortized (val_size-1) max_hash_size f m ∗
          ⌜retv = root_hash_value tree⌝
      }}}.
  Proof.
    iIntros (Φ) "(%Htrelate&%Htvalid&H&%Hlsit&%Hvmatch&%Hmvalid) HΦ".
    revert Htrelate Htvalid Hlsit Hvmatch Hmvalid.
    revert height ltree v path llist f.
    induction tree.
    - intros.
      rewrite /compute_hash_from_leaf.
      wp_pures. inversion Htrelate; subst. 
      wp_match.
      wp_apply (wp_hashfun_prev_amortized with "[$]").
      + lia.
      + admit.
      + admit.
      
    - admit.
  Admitted.
  
End merkle_tree.
