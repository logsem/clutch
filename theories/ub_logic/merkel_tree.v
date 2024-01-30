From clutch.ub_logic Require Export ub_clutch lib.map hash lib.list.
Import Hierarchy.
Set Default Proof Using "Type*".

Section merkel_tree.
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
  
  Inductive merkel_tree :=
  | Leaf (hash_value : nat) (leaf_value:nat)
  | Branch (hash_value : nat) (t1 t2:merkel_tree).

  Definition root_hash_value (t: merkel_tree) :=
    match t with
    | Leaf h _ => h
    | Branch h _ _ => h
    end.
    
  Fixpoint tree_relate (h:nat) (lt : val) (t:merkel_tree) : Prop:=
    match h with
    |0 => (∃ (hv v:nat), lt = InjLV (#hv, #v) /\ t = Leaf hv v)
    |S h' => ∃ (hv:nat) (ll lr:val) (l r:merkel_tree), lt = InjRV (#hv, ll, lr) /\ t = Branch hv l r /\
                                tree_relate h' ll l /\ tree_relate h' lr r 
  end.

  Fixpoint tree_valid (t:merkel_tree) (m:gmap nat Z) : Prop :=
    match t with
    | Leaf h l => h < 2^val_bit_size /\ l < 2^leaf_bit_size /\ m!!l%nat = Some (Z.of_nat h)
    | Branch h l r => h < 2^val_bit_size /\ m!!((root_hash_value l)*2^val_bit_size + root_hash_value r)%nat=Some (Z.of_nat h) /\ tree_valid l m /\ tree_valid r m
    end.

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

   Fixpoint tree_value_match (tree:merkel_tree) (v:nat) (path:list bool) :=
     match (tree, path) with
     | (Leaf h lf, []) => lf=v
     | (Branch h l r, x::xs) => if x then tree_value_match l v xs else tree_value_match r v xs
     | _ => False
     end.

  (** Lemmas *)
  Lemma tree_relate_leaf h ltree a b :
    tree_relate h ltree (Leaf a b) -> h = 0%nat /\ ltree = InjLV (#a, #b).
  Proof.
  Admitted.
  

  (** Spec *)
  Lemma wp_correct_check (ltree:val) (tree:merkel_tree) (m:gmap nat Z) (v:nat) (path:list bool) llist f E:
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
      wp_pures. apply tree_relate_leaf in Htrelate as [-> ->].
      wp_match.
      wp_apply (wp_hashfun_prev_amortized with "[$]").
      + lia.
      + admit.
      + admit.
      
    - admit.
  Admitted.
  
End merkel_tree.
