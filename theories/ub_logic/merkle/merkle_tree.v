From clutch.ub_logic Require Export ub_clutch lib.map hash lib.list.
Import Hierarchy.
Set Default Proof Using "Type*".
Open Scope nat.

Section merkle_tree.
  (*val_bit_size is a positive integer, 
    referring to the bit size of the return value of the hash function
    Therefore all hashes are smalelr than 2 ^ val_bit_size
    val_bit_size_for_hash is one smaller than 2^val_bit_size since the spec for hash
    adds one to that value implicitly (to ensure positive codomain size)
    Leaf bit size is fixed to be twice of val_bit_size.
    For each branch, the concatentation of the left and right hash are provided as input.
    
    In other words, input bit size = 2 * 2 ^ val_bit_size 
                    and output bit size = 2 ^ val_bit_size
    
   *)
  Context `{!ub_clutchGS Σ}.
  Variables height:nat.
  Variables val_bit_size':nat.
  Variables max_hash_size : nat.
  Definition val_bit_size : nat := S val_bit_size'.
  Definition val_size_for_hash:nat := (2^val_bit_size)-1.
  Variable (Hineq: (max_hash_size <= val_size_for_hash)%nat).
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


  Inductive tree_valid: nat -> merkle_tree -> gmap nat Z -> Prop :=
  |tree_valid_lf (h l:nat) m:
    h < 2^val_bit_size ->
    l < 2^leaf_bit_size ->
    m!!l%nat = Some (Z.of_nat h) ->
    tree_valid 0 (Leaf h l) m
  |tree_valid_br n (h:nat) l r m:
    tree_valid n l m ->
    tree_valid n r m ->
    h < 2^val_bit_size ->
    m!!((root_hash_value l)*2^val_bit_size + root_hash_value r)%nat=Some (Z.of_nat h) ->
    tree_valid (S n) (Branch h l r) m.
    

  Definition map_valid (m:gmap nat Z) : Prop := coll_free m.
  

  Inductive tree_leaf_value_match: merkle_tree -> nat -> list (bool*nat) -> Prop:=
  | tree_value_match_lf h lf: tree_leaf_value_match (Leaf h lf) lf []
  | tree_leaf_value_match_left h l r xs v rhash:
    tree_leaf_value_match l v xs->
    tree_leaf_value_match (Branch h l r) v ((true,rhash)::xs)
  | tree_value_match_right h l r xs v lhash:
    tree_leaf_value_match r v xs ->
    tree_leaf_value_match (Branch h l r) v ((false,lhash)::xs).

  (*This ensures all numbers in the proof are smaller than 2^val_bit_size
    If the numbers are larger or equal to 2^val_bit_size
    One knows immediately that the proof is invalid and should not be considered.
   *)
  Inductive possible_proof: merkle_tree -> list (bool*nat) -> Prop:=
  | possible_proof_lf h v: possible_proof (Leaf h v) [] 
  | possible_proof_br_left h ltree rtree hash prooflist:
    possible_proof ltree prooflist ->
    hash < 2^val_bit_size ->
    possible_proof (Branch h ltree rtree) ((true,hash)::prooflist)
  | possible_proof_br_right h ltree rtree hash prooflist:
    possible_proof rtree prooflist ->
    hash < 2^val_bit_size ->
    possible_proof (Branch h ltree rtree) ((false,hash)::prooflist).
  

  Inductive correct_proof: merkle_tree -> list (bool*nat) -> Prop :=
  | correct_proof_lf h l: correct_proof (Leaf h l) []
  | correct_proof_left ltree rtree h prooflist:
    correct_proof (ltree) prooflist ->
    correct_proof (Branch h ltree rtree) ((true, root_hash_value rtree)::prooflist)
  | correct_proof_right ltree rtree h prooflist:
    correct_proof (rtree) prooflist ->
    correct_proof (Branch h ltree rtree) ((false, root_hash_value ltree)::prooflist).

  Inductive incorrect_proof : merkle_tree -> list (bool*nat) -> Prop :=
  | incorrect_proof_base_left ltree rtree h v prooflist:
    v ≠ root_hash_value rtree ->
    incorrect_proof (Branch h ltree rtree) ((true, v)::prooflist)
  | incorrect_proof_next_left ltree rtree h prooflist:
    incorrect_proof ltree prooflist ->
    incorrect_proof (Branch h ltree rtree) ((true, root_hash_value rtree)::prooflist)
  | incorrect_proof_base_right ltree rtree h v prooflist:
    v ≠ root_hash_value ltree ->
    incorrect_proof (Branch h ltree rtree) ((false, v)::prooflist)
  | incorrect_proof_next_right ltree rtree h prooflist:
    incorrect_proof rtree prooflist ->
    incorrect_proof (Branch h ltree rtree) ((false, root_hash_value ltree)::prooflist).
    

  (* Definition root_hash_value_program : val := *)
  (*   λ: "ltree", *)
  (*     match: "ltree" with *)
  (*     | InjL "x" => Fst "x" *)
  (*     | InjR "x" => let, ("a", "b", "c") := "x" in "a" *)
  (*     end. *)

  Definition compute_hash_from_leaf : val :=
    rec: "compute_hash_from_leaf" "lhmf" "lproof" "lleaf" := 
       match: list_head "lproof" with
       | SOME "head" =>
           let: "lproof'" := list_tail "lproof"  in
           let, ("b", "hash") := "head" in
           if: "b"
           then "lhmf"
                  (("compute_hash_from_leaf" "lhmf" "lproof'" "lleaf")*#(2^val_bit_size)+
                "hash")
           else "lhmf"
                  ("hash"*#(2^val_bit_size)+("compute_hash_from_leaf" "lhmf" "lproof'" "lleaf"))
      
        | NONE => "lhmf" "lleaf"
        end.

  (** Lemmas *)
  (* Lemma wp_root_hash_value_program n lt tree E: *)
  (*   {{{ ⌜tree_relate n lt tree⌝ }}} *)
  (*   root_hash_value_program lt @ E *)
  (*   {{{ (retv:Z), RET #retv; ⌜retv = root_hash_value tree⌝}}}. *)
  (* Proof. *)
  (*   iIntros (Φ) "%H HΦ". *)
  (*   rewrite /root_hash_value_program. wp_pures. *)
  (*   inversion H. *)
  (*   - wp_pures. iApply "HΦ". by iPureIntro. *)
  (*   - wp_pures. iApply "HΦ". by iPureIntro. *)
  (* Qed. *)

  Lemma tree_valid_superset n m m' tree:
    tree_valid n tree m -> m ⊆ m' -> tree_valid n tree m'.
  Proof.
    revert n.
    induction tree.
    - intros. inversion H; subst.
      constructor; try done.
      by eapply lookup_weaken.
    - intros. inversion H; subst. constructor; try naive_solver.
      by eapply lookup_weaken.
  Qed.

  Lemma coll_free_lemma m v v' k:
    coll_free m -> m!!v=Some k -> m!! v' = Some k -> v= v'.
  Proof.
    intros H ? ?.
    apply H; try done.
    repeat erewrite lookup_total_correct; try done.
  Qed.

  Lemma proof_correct_implies_not_incorrect tree proof:
    possible_proof tree proof -> correct_proof tree proof -> incorrect_proof tree proof -> False.
  Proof.
    revert proof.
    induction tree; intros proof H1 H2 H3 .
    - inversion H3. 
    - inversion H1; inversion H2; inversion H3; subst; try done.
      + inversion H14; subst. inversion H9; subst. done.
      + inversion H9; inversion H14; subst. eapply IHtree1; try done. 
      + inversion H14; inversion H9; subst. done.
      + inversion H9; inversion H14; subst. eapply IHtree2; try done.
  Qed.

  Lemma proof_not_correct_implies_incorrect tree proof:
    possible_proof tree proof -> (¬ correct_proof tree proof) -> incorrect_proof tree proof.
  Proof.
    revert proof.
    induction tree; intros proof H1 H2.
    - inversion H1; subst. exfalso. apply H2. constructor. 
    - inversion H1; subst.
      + destruct (decide(hash = root_hash_value tree2)).
        * subst. apply incorrect_proof_next_left. apply IHtree1; first done.
          intro; apply H2. by constructor.
        * by apply incorrect_proof_base_left.
      + destruct (decide(hash = root_hash_value tree1)).
        * subst. apply incorrect_proof_next_right. apply IHtree2; first done.
          intro; apply H2. by constructor.
        * by apply incorrect_proof_base_right.
  Qed.

  Lemma possible_proof_implies_exists_leaf tree proof:
    possible_proof tree proof -> ∃ v, tree_leaf_value_match tree v proof.
  Proof.
    revert proof.
    induction tree; intros proof H; inversion H; subst.
    - eexists _. constructor.
    - destruct (IHtree1 _ H4). eexists _. constructor. naive_solver.
    - destruct (IHtree2 _ H4). eexists _. constructor. naive_solver.
  Qed.

  (*This lemma is here to ensure that the return value lies within a bound 
    This lemma is eventually used in the case where the proof is incorrect.
   *)
  Lemma wp_compute_hash_from_leaf_size (n:nat) (tree:merkle_tree) (m:gmap nat Z) (v:nat) (proof:list (bool*nat)) lproof f E:
    {{{ ⌜tree_valid n tree m⌝ ∗
        hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
        ⌜is_list proof lproof⌝ ∗
        ⌜possible_proof tree proof⌝ ∗
        ⌜map_valid m⌝ ∗
        ⌜ size m + (S n) <= max_hash_size⌝ ∗
        € (nnreal_nat (S n) * amortized_error (val_size_for_hash)%nat max_hash_size)%NNR 
     }}}
      compute_hash_from_leaf f lproof (#v) @ E
      {{{ (retv:Z), RET #retv;
          ∃ m', ⌜m ⊆ m'⌝ ∗
                hashfun_amortized (val_size_for_hash) max_hash_size f m' ∗
                ⌜map_valid m'⌝ ∗
                ⌜size (m') <= size m + (S n)⌝ ∗
                ⌜(0 <= retv < 2^val_bit_size)%Z⌝
      }}}.
  Proof.
    iIntros (Φ) "(%Htvalid & H & %Hproof & %Hposs & %Hmvalid & %Hmsize &Herr) HΦ".
    iInduction tree as [hash leaf|hash tree1 Htree1 tree2 Htree2] "IH"
                         forall (n v m proof lproof Φ
                              Htvalid Hproof Hposs Hmsize Hmvalid).
    - rewrite /compute_hash_from_leaf. wp_pures. rewrite -/compute_hash_from_leaf.
      wp_apply (wp_list_head); first done.
      iIntros (?) "[[->->]|(%&%&%&%)]"; last first.
      { inversion Hposs; subst. done. }
      wp_pures.
      inversion Htvalid; subst.
      wp_apply (wp_insert_amortized with "[$H Herr]"); try lia.
      + iSplit; try done. iApply ec_spend_irrel; last done.
        simpl. lra.
      + iIntros (retv) "(%m' & H & %Hmvalid' & %Hfound & %Hmsize' & %Hmsubset)".
        iApply ("HΦ" with "[H]").
        iExists _; repeat iSplit; try done.
        * iPureIntro; lia.
        * rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
          iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done.
          lia.
        * rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
          iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. 
          rewrite /val_size_for_hash in Hforall. destruct Hforall as [? K].
          apply Zle_lt_succ in K.
          eapply Z.lt_stepr; try done.
          rewrite -Nat2Z.inj_succ. replace (2)%Z with (Z.of_nat 2) by lia.
          rewrite -Nat2Z.inj_pow. f_equal.
          assert (1<=2 ^val_bit_size); last lia. clear.
          induction val_bit_size; simpl; lia.
    - rewrite /compute_hash_from_leaf. wp_pures. rewrite -/compute_hash_from_leaf.
      wp_apply wp_list_head; first done.
      iIntros (?) "[[->->]|(%head & %lproof' & -> & ->)]".
      { inversion Hposs. }
      wp_pures. wp_apply wp_list_tail; first done.
      iIntros (proof') "%Hproof'".
      wp_pures. 
      inversion Htvalid; subst.
      iAssert (€ ((nnreal_nat (S n0) * amortized_error val_size_for_hash max_hash_size)%NNR) ∗
               € (amortized_error val_size_for_hash max_hash_size)%NNR)%I with "[Herr]" as "[Herr Herr']".
      { iApply ec_split. iApply (ec_spend_irrel with "[$]").
        simpl. lra.
      }
      wp_pures.
      inversion Hposs; subst; wp_pures; try done.
      + wp_apply ("IH" with "[][][][][][$H][$Herr]"); try done.
        { iPureIntro; lia. }
        iIntros (lefthash') "(%m' & %Hmsubset & H & %Hmvalid' & %Hmsize' & %Hlefthashsize')".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (Z.to_nat lefthash' * 2 ^ val_bit_size + hash0)); last first.
        { rewrite Nat2Z.inj_add. f_equal. rewrite Nat2Z.inj_mul.
          rewrite Z2Nat.id; last lia. f_equal.
          rewrite Z2Nat.inj_pow. f_equal.
        } 
        wp_apply (wp_insert_amortized with "[$H $Herr']").
        * lia.
        * lia.
        * by iPureIntro.
        * iIntros (finalhash) "(%m'' & H & %Hmvalid'' & %Hmfound'' & %Hmsize'' & %Hmsubset')".
          iApply "HΦ".
          iExists m''. repeat iSplit.
          -- iPureIntro; etrans; exact.
          -- done.
          -- by iPureIntro.
          -- iPureIntro; lia.
          -- rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
             iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. lia.
          -- rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
             iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. 
             rewrite /val_size_for_hash in Hforall. destruct Hforall as [? K].
             apply Zle_lt_succ in K.
             eapply Z.lt_stepr; try done.
             rewrite -Nat2Z.inj_succ. replace (2)%Z with (Z.of_nat 2) by lia.
             rewrite -Nat2Z.inj_pow. f_equal.
             assert (1<=2 ^val_bit_size); last lia. clear.
             induction val_bit_size; simpl; lia.        
      + wp_apply ("IH1" with "[][][][][][$H][$Herr]"); try done.
        { iPureIntro; lia. }
        iIntros (lefthash') "(%m' & %Hmsubset & H & %Hmvalid' & %Hmsize' & %Hlefthashsize')".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (hash0 * 2 ^ val_bit_size + Z.to_nat lefthash')); last first.
        { rewrite Nat2Z.inj_add. f_equal; last lia. rewrite Nat2Z.inj_mul. f_equal.
          apply Z2Nat.inj_pow.
        }
        wp_apply (wp_insert_amortized with "[$H $Herr']").
        * lia.
        * lia.
        * by iPureIntro.
        * iIntros (finalhash) "(%m'' & H & %Hmvalid'' & %Hmfound'' & %Hmsize'' & %Hmsubset')".
          iApply "HΦ".
          iExists m''. repeat iSplit.
          -- iPureIntro; etrans; exact.
          -- done.
          -- by iPureIntro.
          -- iPureIntro; lia.
          -- rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
             iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. lia.
          -- rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
             iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. 
             rewrite /val_size_for_hash in Hforall. destruct Hforall as [? K].
             apply Zle_lt_succ in K.
             eapply Z.lt_stepr; try done.
             rewrite -Nat2Z.inj_succ. replace (2)%Z with (Z.of_nat 2) by lia.
             rewrite -Nat2Z.inj_pow. f_equal.
             assert (1<=2 ^val_bit_size); last lia. clear.
             induction val_bit_size; simpl; lia.        
  Qed.
  
  (* The case where everything is correct *)
  Lemma wp_compute_hash_from_leaf_correct (tree:merkle_tree) (m:gmap nat Z) (v:nat) (proof:list (bool*nat)) lproof f E:
     {{{ ⌜tree_valid height tree m⌝ ∗
        hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
        ⌜is_list proof lproof⌝ ∗
        ⌜correct_proof tree proof⌝ ∗
        ⌜tree_leaf_value_match tree v proof⌝ ∗
        ⌜map_valid m⌝ }}}
      compute_hash_from_leaf f lproof (#v) @ E
      {{{ (retv:Z), RET #retv;
          hashfun_amortized (val_size_for_hash) max_hash_size f m ∗
          ⌜retv = root_hash_value tree⌝
      }}}.
  Proof.
    iIntros (Φ) "(%Htvalid & H & %Hlist & %Hcorrect & %Hvmatch & %Hmvalid) HΦ".
    iInduction tree as [hash leaf|hash tree1 Htree1 tree2 Htree2] "IH"
                         forall (height m proof lproof Φ
                              Htvalid Hlist Hcorrect Hvmatch Hmvalid).
    - rewrite /compute_hash_from_leaf. wp_pures. rewrite -/compute_hash_from_leaf.
      wp_apply wp_list_head; first done.
      iIntros (?) "[[-> ->]|%]"; last first.
      { inversion Hcorrect; subst. destruct H as [?[?[??]]].
        inversion H. }
      wp_pures. inversion Htvalid; inversion Hvmatch; subst.
      wp_apply (wp_hashfun_prev_amortized with "[$]").
      + lia.
      + done.
      + iIntros "H". iApply "HΦ"; iFrame.
        done.
    - rewrite /compute_hash_from_leaf. wp_pures.
      rewrite -/compute_hash_from_leaf.
      wp_apply wp_list_head; first done.
      iIntros (head) "[[->->]|(%&%&->&->)]".
      { inversion Hcorrect. }
      wp_pures. wp_apply wp_list_tail; first done.
      iIntros (tail) "%Htail".
      inversion Hcorrect; wp_pures.
      + inversion Htvalid. inversion Hvmatch; subst; last done.
        wp_apply ("IH" with "[][][][][][$]"); try done.
        iIntros (lhash) "[H ->]".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2)); last first.
        { rewrite Nat2Z.inj_add. f_equal. rewrite Nat2Z.inj_mul. f_equal.
          apply Z2Nat.inj_pow.
        }
        wp_apply (wp_hashfun_prev_amortized with "H").
        * lia.
        * done.
        * iIntros "H". iApply "HΦ".
          iFrame. done.
      + inversion Htvalid. inversion Hvmatch; subst; first done.
        wp_apply ("IH1" with "[][][][][][$]"); try done.
        iIntros (rhash) "[H ->]".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2)); last first.
        { rewrite Nat2Z.inj_add. f_equal. rewrite Nat2Z.inj_mul. f_equal.
          apply Z2Nat.inj_pow.
        }
        wp_apply (wp_hashfun_prev_amortized with "H").
        * lia.
        * done.
        * iIntros "H". iApply "HΦ".
          iFrame. done.
  Qed.

  (*The case where the leaf is incorrect*)
  Lemma wp_compute_hash_from_leaf_incorrect (tree:merkle_tree) (m:gmap nat Z) (v v':nat) (proof:list (bool*nat)) lproof f E:
     {{{ ⌜tree_valid height tree m⌝ ∗
        hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
        ⌜is_list proof lproof⌝ ∗
        ⌜possible_proof tree proof⌝ ∗
        ⌜tree_leaf_value_match tree v proof⌝ ∗
        ⌜v ≠ v'⌝ ∗
        ⌜map_valid m⌝ ∗
        ⌜ size m + (S height) <= max_hash_size⌝ ∗
        € (nnreal_nat (S height) * amortized_error (val_size_for_hash)%nat max_hash_size)%NNR 
     }}}
      compute_hash_from_leaf f lproof (#v') @ E
      {{{ (retv:Z), RET #retv;
          ∃ m', ⌜m ⊆ m'⌝ ∗
                hashfun_amortized (val_size_for_hash) max_hash_size f m' ∗
                ⌜map_valid m'⌝ ∗
                ⌜size (m') <= size m + (S height)⌝ ∗
                ⌜retv ≠ root_hash_value tree⌝ ∗
                ⌜(0 <= retv < 2^val_bit_size)%Z⌝
      }}}.
  Proof.
    iIntros (Φ) "(%Htvalid & H & %Hlist & %Hpossible & %Hvmatch & %Hneq & %Hmvalid & %Hmsize & Herr) HΦ".
    iInduction tree as [|] "IH"
                         forall (height m proof lproof Φ Htvalid Hlist Hpossible Hvmatch Hmvalid Hmsize).
    - inversion Htvalid; subst. rewrite /compute_hash_from_leaf. wp_pures.
      rewrite -/compute_hash_from_leaf. inversion Hvmatch; subst.
      wp_apply wp_list_head; first done.
      iIntros (?) "[[_ ->]|(%&%&%&%)]"; last done.
      wp_pures.
      wp_apply (wp_insert_amortized with "[$H Herr]"); try lia.
      + iSplit; try done. iApply ec_spend_irrel; last done.
        simpl. lra.
      + iIntros (hash_value') "(%m' & H & %Hvalid' & %Hmfound & %Hmsize' & %Hmsubset)".
        iApply "HΦ".
        iExists _.
        repeat iSplit; try done.
        * iPureIntro; lia.
        * simpl.
          inversion Htvalid; subst.
          iPureIntro. intro; subst. apply Hneq. eapply coll_free_lemma; try done.
          by erewrite lookup_weaken.
        * rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
          iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done.
          lia.
        * rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
          iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. 
          rewrite /val_size_for_hash in Hforall. destruct Hforall as [? K].
          apply Zle_lt_succ in K.
          eapply Z.lt_stepr; try done.
          rewrite -Nat2Z.inj_succ. replace (2)%Z with (Z.of_nat 2) by lia.
          rewrite -Nat2Z.inj_pow. f_equal.
          assert (1<=2 ^val_bit_size); last lia. clear.
          induction val_bit_size; simpl; lia.
    - rewrite /compute_hash_from_leaf. wp_pures. rewrite -/compute_hash_from_leaf.
      wp_apply wp_list_head; first done.
      iIntros (?) "[[->->]|(%head & %lproof' & -> & ->)]".
      { inversion Hvmatch. }
      wp_pures. wp_apply wp_list_tail; first done.
      iIntros (proof') "%Hproof'".
      wp_pures. 
      inversion Htvalid; subst.
      iAssert (€ ((nnreal_nat (S n) * amortized_error val_size_for_hash max_hash_size)%NNR) ∗
               € (amortized_error val_size_for_hash max_hash_size)%NNR)%I with "[Herr]" as "[Herr Herr']".
      { iApply ec_split. iApply (ec_spend_irrel with "[$]").
        simpl. lra.
      }
      inversion Hpossible; inversion Hvmatch; inversion Htvalid; subst; wp_pures; try done.
      + wp_apply ("IH" with "[][][][][][][$H][$Herr]"); try done.
        { iPureIntro; lia. }
        iIntros (lefthash') "(%m' & %Hmsubset & H & %Hmvalid' & %Hmsize' & %Hlefthashneq & %Hlefthashsize')".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (Z.to_nat lefthash' * 2 ^ val_bit_size + hash)); last first.
        { rewrite Nat2Z.inj_add. f_equal. rewrite Nat2Z.inj_mul.
          rewrite Z2Nat.id; last lia. f_equal.
          rewrite Z2Nat.inj_pow. f_equal.
        } 
        wp_apply (wp_insert_amortized with "[$H $Herr']").
        * lia.
        * lia.
        * by iPureIntro.
        * iIntros (finalhash) "(%m'' & H & %Hmvalid'' & %Hmfound'' & %Hmsize'' & %Hmsubset')".
          iApply "HΦ".
          iExists m''. repeat iSplit.
          -- iPureIntro; etrans; exact.
          -- done.
          -- by iPureIntro.
          -- iPureIntro; lia.
          -- iPureIntro. simpl.
             intro; subst. apply Hlefthashneq.
             assert (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2 =
                     Z.to_nat lefthash' * 2 ^ val_bit_size + hash) as helper.
             { eapply (coll_free_lemma m''); try done.
               eapply lookup_weaken; first done.
               etrans; exact.
             }
             epose proof (Nat.mul_split_l _ _ _ _ _ _ _ helper) as [Hsplit _].
             lia.
             Unshelve.
             ++ by inversion H22.
             ++ by inversion Hpossible. 
          -- rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
             iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. lia.
          -- rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
             iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. 
             rewrite /val_size_for_hash in Hforall. destruct Hforall as [? K].
             apply Zle_lt_succ in K.
             eapply Z.lt_stepr; try done.
             rewrite -Nat2Z.inj_succ. replace (2)%Z with (Z.of_nat 2) by lia.
             rewrite -Nat2Z.inj_pow. f_equal.
             assert (1<=2 ^val_bit_size); last lia. clear.
             induction val_bit_size; simpl; lia.        
      + wp_apply ("IH1" with "[][][][][][][$H][$Herr]"); try done.
        { iPureIntro; lia. }
        iIntros (righthash') "(%m' & %Hmsubset & H & %Hmvalid' & %Hmsize' & %Hrighthashneq & %Hrighthashsize')".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (hash * 2 ^ val_bit_size + Z.to_nat righthash')); last first.
        { rewrite Nat2Z.inj_add. f_equal; last lia. rewrite Nat2Z.inj_mul. f_equal.
          rewrite Z2Nat.inj_pow. f_equal.
        } 
        wp_apply (wp_insert_amortized with "[$H $Herr']").
        * lia.
        * lia.
        * by iPureIntro.
        * iIntros (finalhash) "(%m'' & H & %Hmvalid'' & %Hmfound'' & %Hmsize'' & %Hmsubset')".
          iApply "HΦ".
          iExists m''. repeat iSplit.
          -- iPureIntro; etrans; exact.
          -- done.
          -- by iPureIntro.
          -- iPureIntro; lia.
          -- iPureIntro. simpl.
             intro; subst. apply Hrighthashneq.
             assert (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2 =
                     hash * 2 ^ val_bit_size + Z.to_nat righthash') as helper.
             { eapply (coll_free_lemma m''); try done.
               eapply lookup_weaken; first done.
               etrans; exact.
             }
             epose proof (Nat.mul_split_l _ _ _ _ _ _ _ helper) as [Hsplit _].
             lia.
             Unshelve.
             ++ by inversion H22.
             ++ destruct Hrighthashsize' as [Hrighthashsize Hrighthashsize'].
                rewrite Nat2Z.inj_lt. rewrite Z2Nat.inj_pow.
                replace (Z.of_nat 2) with 2%Z by lia.
                rewrite Z2Nat.id; lia.
          -- rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
             iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. lia.
          -- rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
             iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. 
             rewrite /val_size_for_hash in Hforall. destruct Hforall as [? K].
             apply Zle_lt_succ in K.
             eapply Z.lt_stepr; try done.
             rewrite -Nat2Z.inj_succ. replace (2)%Z with (Z.of_nat 2) by lia.
             rewrite -Nat2Z.inj_pow. f_equal.
             assert (1<=2 ^val_bit_size); last lia. clear.
             induction val_bit_size; simpl; lia. 
  Qed.

  (*The case where the leaf is correct but the proof is not *)
  Lemma wp_compute_hash_from_leaf_incorrect_proof (tree:merkle_tree) (m:gmap nat Z) (v:nat) (proof:list (bool*nat)) lproof f E:
    {{{ ⌜tree_valid height tree m⌝ ∗
        hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
        ⌜is_list proof lproof⌝ ∗
        ⌜possible_proof tree proof⌝ ∗
        ⌜incorrect_proof tree proof ⌝ ∗
        ⌜tree_leaf_value_match tree v proof⌝ ∗
        ⌜map_valid m⌝ ∗
        ⌜ size m + (S height) <= max_hash_size⌝ ∗
        € (nnreal_nat (S height) * amortized_error (val_size_for_hash)%nat max_hash_size)%NNR 
     }}}
      compute_hash_from_leaf f lproof (#v) @ E
      {{{ (retv:Z), RET #retv;
          ∃ m', ⌜m ⊆ m'⌝ ∗
                hashfun_amortized (val_size_for_hash) max_hash_size f m' ∗
                ⌜map_valid m'⌝ ∗
                ⌜size (m') <= size m + (S height)⌝ ∗
                ⌜retv ≠ root_hash_value tree⌝ ∗
                ⌜(0 <= retv < 2^val_bit_size)%Z⌝
      }}}.
  Proof.
    iIntros (Φ) "(%Htvalid & H & %Hlist & %Hposs & %Hincorrect & %Hvmatch & %Hmvalid & %Hmsize & Herr) HΦ".
    iInduction tree as [|] "IH"
                         forall (height m proof lproof Φ Htvalid Hlist Hposs Hincorrect Hvmatch Hmvalid Hmsize).
    - inversion Hincorrect.
    - rewrite /compute_hash_from_leaf. wp_pures.
      rewrite -/compute_hash_from_leaf.
      wp_apply wp_list_head; first done.
      iIntros (?) "[[->->]|(%head & %lproof' & -> & ->)]".
      { inversion Hvmatch. }
      wp_pures. wp_apply wp_list_tail; first done.
      iIntros (proof') "%Hproof'".
      wp_pures. inversion Htvalid; subst.
      iAssert (€ ((nnreal_nat (S n) * amortized_error val_size_for_hash max_hash_size)%NNR) ∗
               € (amortized_error val_size_for_hash max_hash_size)%NNR)%I with "[Herr]" as "[Herr Herr']".
      { iApply ec_split. iApply (ec_spend_irrel with "[$]").
        simpl. lra.
      }
      inversion Hposs; inversion Hvmatch; inversion Htvalid; inversion Hincorrect; subst; wp_pures; try done.
      + (*right neq guess right*)
        wp_apply (wp_compute_hash_from_leaf_size with "[$H $Herr]").
        * repeat iSplit; last first; iPureIntro; try done. lia.
        * iIntros (lefthash) "(%m' & %Hmsubset & H & %Hmvalid' & %Hmsize' & %Hlefthashsize)".
          wp_pures.
          replace (_*_+_)%Z with (Z.of_nat (Z.to_nat lefthash * 2 ^ val_bit_size + hash)); last first.
          { rewrite Nat2Z.inj_add. f_equal. rewrite Nat2Z.inj_mul.
            rewrite Z2Nat.id; last lia. f_equal.
            rewrite Z2Nat.inj_pow. f_equal.
          }
          wp_apply (wp_insert_amortized with "[$H $Herr']"); try done.
          -- lia.
          -- lia.
          -- iIntros (retv) "(%m'' & H & %Hmvalid'' & %Hmfound & %Hsize'' & %Hmsubset')".
             iApply "HΦ".
             iExists m''. repeat iSplit; try done.
             ++ iPureIntro; etrans; exact.
             ++ iPureIntro; lia.
             ++ iPureIntro. simpl. intros ->. 
                inversion H30; subst.
                assert (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2 =
                        Z.to_nat lefthash * 2 ^ val_bit_size + hash) as helper.
                { eapply (coll_free_lemma m''); try done.
                  eapply lookup_weaken; first done.
                  etrans; exact.
                }
                epose proof (Nat.mul_split_l _ _ _ _ _ _ _ helper) as [Hsplit Hsplit']; subst. done.
                Unshelve.
                ** by inversion H22.
                ** by inversion Hposs. 
             ++ rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
                iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. lia.
             ++  rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
                 iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. 
                 rewrite /val_size_for_hash in Hforall. destruct Hforall as [? K].
                 apply Zle_lt_succ in K.
                 eapply Z.lt_stepr; try done.
                 rewrite -Nat2Z.inj_succ. replace (2)%Z with (Z.of_nat 2) by lia.
                 rewrite -Nat2Z.inj_pow. f_equal.
                 assert (1<=2 ^val_bit_size); last lia. clear.
                 induction val_bit_size; simpl; lia. 
      + (*incorrect happens above*)
        wp_apply ("IH" with "[][][][][][][][$H][$Herr]"); try done.
        * iPureIntro; lia.
        * iIntros (lefthash) "(%m' & %Hmsubset & H & %Hmvalid' & %Hmsize' & %Hlefthashneq & %Hlefthashsize)".
          wp_pures.
          replace (_*_+_)%Z with (Z.of_nat (Z.to_nat lefthash * 2 ^ val_bit_size + hash)); last first.
          { rewrite Nat2Z.inj_add. f_equal. rewrite Nat2Z.inj_mul.
            rewrite Z2Nat.id; last lia. f_equal.
            rewrite Z2Nat.inj_pow. f_equal.
          }
          wp_apply (wp_insert_amortized with "[$H $Herr']"); try done.
          -- lia.
          -- lia.
          -- iIntros (retv) "(%m'' & H & %Hmvalid'' & %Hmfound & %Hsize'' & %Hmsubset')".
             iApply "HΦ".
             iExists m''. repeat iSplit; try done.
             ++ iPureIntro; etrans; exact.
             ++ iPureIntro; lia.
             ++ iPureIntro. simpl. intros ->. apply Hlefthashneq.
                inversion H30; subst.
                assert (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2 =
                        Z.to_nat lefthash * 2 ^ val_bit_size + root_hash_value tree2) as helper.
                { eapply (coll_free_lemma m''); try done.
                  eapply lookup_weaken; first done.
                  etrans; exact.
                }
                epose proof (Nat.mul_split_l _ _ _ _ _ _ _ helper) as [Hsplit _].
                lia.
                Unshelve.
                ** by inversion H22.
                ** by inversion Hposs. 
             ++ rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
                iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. lia.
             ++  rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
                 iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. 
                 rewrite /val_size_for_hash in Hforall. destruct Hforall as [? K].
                 apply Zle_lt_succ in K.
                 eapply Z.lt_stepr; try done.
                 rewrite -Nat2Z.inj_succ. replace (2)%Z with (Z.of_nat 2) by lia.
                 rewrite -Nat2Z.inj_pow. f_equal.
                 assert (1<=2 ^val_bit_size); last lia. clear.
                 induction val_bit_size; simpl; lia. 
      + (*left neq guess left *)
        wp_apply (wp_compute_hash_from_leaf_size with "[$H $Herr]").
        * repeat iSplit; last first; iPureIntro; try done. lia.
        * iIntros (righthash) "(%m' & %Hmsubset & H & %Hmvalid' & %Hmsize' & %Hrighthashsize)".
          wp_pures.
          replace (_*_+_)%Z with (Z.of_nat (hash * 2 ^ val_bit_size + Z.to_nat righthash )); last first.
          { rewrite Nat2Z.inj_add. f_equal; last lia. rewrite Nat2Z.inj_mul. f_equal.
            rewrite Z2Nat.inj_pow. f_equal.
          }
          wp_apply (wp_insert_amortized with "[$H $Herr']"); try done.
          -- lia.
          -- lia.
          -- iIntros (retv) "(%m'' & H & %Hmvalid'' & %Hmfound & %Hsize'' & %Hmsubset')".
             iApply "HΦ".
             iExists m''. repeat iSplit; try done.
             ++ iPureIntro; etrans; exact.
             ++ iPureIntro; lia.
             ++ iPureIntro. simpl. intros ->. 
                inversion H30; subst.
                assert (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2 =
                        hash * 2 ^ val_bit_size + Z.to_nat righthash) as helper.
                { eapply (coll_free_lemma m''); try done.
                  eapply lookup_weaken; first done.
                  etrans; exact.
                }
                epose proof (Nat.mul_split_l _ _ _ _ _ _ _ helper) as [Hsplit Hsplit']; subst. done.
                Unshelve.
                ** by inversion H22.
                ** destruct Hrighthashsize as [Hrighthashsize Hrighthashsize'].
                   rewrite Nat2Z.inj_lt. rewrite Z2Nat.inj_pow.
                   replace (Z.of_nat 2) with 2%Z by lia.
                   rewrite Z2Nat.id; lia.
             ++ rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
                iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. lia.
             ++  rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
                 iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. 
                 rewrite /val_size_for_hash in Hforall. destruct Hforall as [? K].
                 apply Zle_lt_succ in K.
                 eapply Z.lt_stepr; try done.
                 rewrite -Nat2Z.inj_succ. replace (2)%Z with (Z.of_nat 2) by lia.
                 rewrite -Nat2Z.inj_pow. f_equal.
                 assert (1<=2 ^val_bit_size); last lia. clear.
                 induction val_bit_size; simpl; lia. 
      + (*incorrect happens above *)
        wp_apply ("IH1" with "[][][][][][][][$H][$Herr]"); try done.
        * iPureIntro; lia.
        * iIntros (righthash) "(%m' & %Hmsubset & H & %Hmvalid' & %Hmsize' & %Hrighthashneq & %Hrighthashsize)".
          wp_pures.
          replace (_*_+_)%Z with (Z.of_nat (hash * 2 ^ val_bit_size + Z.to_nat righthash)); last first.
          { rewrite Nat2Z.inj_add. f_equal; last lia. rewrite Nat2Z.inj_mul. f_equal.
            rewrite Z2Nat.inj_pow. f_equal.
          } 
          wp_apply (wp_insert_amortized with "[$H $Herr']"); try done.
          -- lia.
          -- lia.
          -- iIntros (retv) "(%m'' & H & %Hmvalid'' & %Hmfound & %Hsize'' & %Hmsubset')".
             iApply "HΦ".
             iExists m''. repeat iSplit; try done.
             ++ iPureIntro; etrans; exact.
             ++ iPureIntro; lia.
             ++ iPureIntro. simpl. intros ->. apply Hrighthashneq.
                inversion H30; subst.
                assert (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2 =
                        root_hash_value tree1 * 2 ^ val_bit_size + Z.to_nat righthash) as helper.
                { eapply (coll_free_lemma m''); try done.
                  eapply lookup_weaken; first done.
                  etrans; exact.
                }
                epose proof (Nat.mul_split_l _ _ _ _ _ _ _ helper) as [Hsplit _].
                lia.
                Unshelve.
                ** by inversion H22.
                ** destruct Hrighthashsize as [Hrighthashsize Hrighthashsize'].
                   rewrite Nat2Z.inj_lt. rewrite Z2Nat.inj_pow.
                   replace (Z.of_nat 2) with 2%Z by lia.
                   rewrite Z2Nat.id; lia.
             ++ rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
                iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. lia.
             ++  rewrite /hashfun_amortized. iDestruct "H" as "(%&%&%&%&%Hforall&H)".
                 iPureIntro. eapply map_Forall_lookup_1 in Hforall; last done. 
                 rewrite /val_size_for_hash in Hforall. destruct Hforall as [? K].
                 apply Zle_lt_succ in K.
                 eapply Z.lt_stepr; try done.
                 rewrite -Nat2Z.inj_succ. replace (2)%Z with (Z.of_nat 2) by lia.
                 rewrite -Nat2Z.inj_pow. f_equal.
                 assert (1<=2 ^val_bit_size); last lia. clear.
                 induction val_bit_size; simpl; lia. 
  Qed.

  (** checker*)
  Definition merkle_tree_decider_program : val :=
    λ: "correct_root_hash" "lhmf",
      (λ: "lproof" "lleaf",
         "correct_root_hash" = compute_hash_from_leaf "lhmf" "lproof" "lleaf"
      ).

  Lemma merkle_tree_decider_program_spec tree (m:gmap nat Z) f:
    {{{ ⌜tree_valid height tree m⌝ ∗
        hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
        ⌜map_valid m⌝ 
    }}} merkle_tree_decider_program #(root_hash_value tree) f
    {{{
          (checker:val), RET checker;
          hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
          (∀ lproof proof v m',
             {{{
                  ⌜m⊆m'⌝ ∗
                  hashfun_amortized (val_size_for_hash)%nat max_hash_size f m' ∗
                  ⌜is_list proof lproof⌝ ∗
                  ⌜possible_proof tree proof ⌝∗
                  ⌜map_valid m'⌝ ∗
                  ⌜ size m' + (S height) <= max_hash_size⌝ ∗
                  € (nnreal_nat (S height) * amortized_error (val_size_for_hash)%nat max_hash_size)%NNR
                   
            }}}
              checker lproof (#v)
              {{{ (b:bool), RET #b;
                  if b then
                    ⌜correct_proof tree proof⌝ ∗
                    ⌜tree_leaf_value_match tree v proof⌝ ∗
                    hashfun_amortized (val_size_for_hash) max_hash_size f m' ∗
                    € (nnreal_nat (S height) * amortized_error (val_size_for_hash)%nat max_hash_size)%NNR
                  else
                    ⌜incorrect_proof tree proof \/
                      (∃ v', tree_leaf_value_match tree v' proof /\ v ≠ v')⌝ ∗
                    ∃ m'', ⌜m' ⊆ m''⌝ ∗
                        hashfun_amortized (val_size_for_hash) max_hash_size f m'' ∗
                        ⌜map_valid m''⌝ ∗
                        ⌜size (m'') <= size m' + (S height)⌝ 
          }}} )
    }}}.
  Proof.
    iIntros (Φ) "(%Htvalid & H & %Hmvalid) IH".
    rewrite /merkle_tree_decider_program.
    wp_pures. iModIntro.
    iApply "IH". iFrame.
    iIntros (?????) "!> (%&H&%&%&%&%&Herr) HΦ".
    wp_pures.
    epose proof (possible_proof_implies_exists_leaf tree proof _) as [v' ?].
    destruct (decide (v=v')).
    - destruct (@decide (correct_proof tree proof) (make_decision (correct_proof tree proof))) as [K|K].
      + wp_apply (wp_compute_hash_from_leaf_correct with "[$H]").
        * repeat iSplit; try done; iPureIntro.
          -- by eapply tree_valid_superset.
          -- by subst.
        * iIntros (?) "(H&%)".
          wp_pures. subst. case_bool_decide; last done.
          iModIntro. iApply "HΦ". iFrame.
          by iSplit.
      + epose proof (proof_not_correct_implies_incorrect _ _ _ K).
        wp_apply (wp_compute_hash_from_leaf_incorrect_proof with "[$H $Herr]").
        * repeat iSplit; try done; iPureIntro.
          -- by eapply tree_valid_superset.
          -- by subst.
        * iIntros (?) "(%&%&H&%&%&%&%)".
          wp_pures.
          rewrite bool_decide_eq_false_2; last first.
          { intros K'; inversion K'; by subst. }
          iModIntro; iApply "HΦ".
          repeat iSplit.
          -- iPureIntro. naive_solver.
          -- iExists _; by repeat iSplit.
    - wp_apply (wp_compute_hash_from_leaf_incorrect with "[$H $Herr]").
      + repeat iSplit; try done. iPureIntro. by eapply tree_valid_superset.
      + iIntros (?) "(%&%&H&%&%&%&%)".
        wp_pures. rewrite bool_decide_eq_false_2; last first.
        { intros K. inversion K. by subst. }
        iModIntro. iApply "HΦ".
        repeat iSplit.
        * iPureIntro. right. eexists _; naive_solver.
        * iExists _; by repeat iSplit.
          Unshelve.
          all: done.
  Qed.
  
End merkle_tree.


