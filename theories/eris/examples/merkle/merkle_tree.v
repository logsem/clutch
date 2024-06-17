From clutch.eris Require Export eris lib.map hash lib.list.
Import Hierarchy.
Set Default Proof Using "Type*".
Open Scope nat.

Section merkle_tree.
  (* val_bit_size is a positive integer,
    referring to the bit size of the return value of the hash function
    Therefore all hashes are smaller than 2 ^ val_bit_size
    val_bit_size_for_hash is one smaller than 2^val_bit_size since the spec for hash
    adds one to that value implicitly (to ensure positive codomain size)
    Leaf bit size is fixed to be twice of val_bit_size.
    For each branch, the concatentation of the left and right hash are provided as input.

    In other words, input bit size = 2 * 2 ^ val_bit_size
                    and output bit size = 2 ^ val_bit_size

   *)
  Context `{!erisGS Σ}.
  Variables height:nat.
  Variables val_bit_size':nat.
  Variables max_hash_size : nat.
  Hypothesis max_hash_size_pos: (0<max_hash_size)%nat.
  Definition val_bit_size : nat := S val_bit_size'.
  Definition val_size_for_hash:nat := (2^val_bit_size)-1.
  (* Variable (Hineq: (max_hash_size <= val_size_for_hash)%nat). *)
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


  Inductive tree_valid: nat -> merkle_tree -> gmap nat nat -> Prop :=
  |tree_valid_lf (h l:nat) m:
    h < 2^val_bit_size ->
    l < 2^leaf_bit_size ->
    m!!l%nat = Some (h) ->
    tree_valid 0 (Leaf h l) m
  |tree_valid_br n (h:nat) l r m:
    tree_valid n l m ->
    tree_valid n r m ->
    h < 2^val_bit_size ->
    m!!((root_hash_value l)*2^val_bit_size + root_hash_value r)%nat=Some (h) ->
    tree_valid (S n) (Branch h l r) m.


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

  Lemma hash_bound_manipulation finalhash:
    (0 ≤ finalhash) -> (finalhash ≤ val_size_for_hash) ->
    (0 ≤ finalhash < 2 ^ val_bit_size)%Z.
  Proof.
    clear.
    intros. split; try lia.
    rewrite /val_size_for_hash in H0.
    replace 2%Z with (Z.of_nat 2); last lia.
    rewrite -Z2Nat.inj_pow. apply inj_lt.
    assert (0<2^val_bit_size); try lia.
    clear.
    induction val_bit_size; simpl; try lia.
  Qed.

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
  Local Lemma wp_compute_hash_from_leaf_size (n:nat) (tree:merkle_tree) (m:gmap nat nat) (v:nat) (proof:list (bool*nat)) lproof f E:
    {{{ ⌜tree_valid n tree m⌝ ∗
        coll_free_hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
        ⌜is_list proof lproof⌝ ∗
        ⌜possible_proof tree proof⌝ ∗
        ⌜ size m + (S n) <= max_hash_size⌝ ∗
        ↯ (nnreal_nat (S n) * amortized_error (val_size_for_hash)%nat max_hash_size max_hash_size_pos)%NNR
     }}}
      compute_hash_from_leaf f lproof (#v) @ E
      {{{ (retv:Z), RET #retv;
          ∃ m', ⌜m ⊆ m'⌝ ∗
                coll_free_hashfun_amortized (val_size_for_hash) max_hash_size f m' ∗
                ⌜size (m') <= size m + (S n)⌝ ∗
                ⌜(0 <= retv < 2^val_bit_size)%Z⌝
      }}}.
  Proof.
    iIntros (Φ) "(%Htvalid & H & %Hproof & %Hposs & %Hmsize &Herr) HΦ".
    iInduction tree as [hash leaf|hash tree1 Htree1 tree2 Htree2] "IH"
                         forall (n v m proof lproof Φ
                              Htvalid Hproof Hposs Hmsize).
    - rewrite /compute_hash_from_leaf. wp_pures. rewrite -/compute_hash_from_leaf.
      wp_apply (wp_list_head); first done.
      iIntros (?) "[[->->]|(%&%&%&%)]"; last first.
      { inversion Hposs; subst. done. }
      wp_pures.
      inversion Htvalid; subst.
      wp_apply (wp_insert_amortized with "[$H Herr]"); try lia.
      + iApply ec_eq; last done.
        simpl. lra.
      + iIntros (retv) "(%m' & H & %Hfound & %Hmsize' & %Hmsubset)".
        iApply ("HΦ" with "[H]").
        iExists _; do 2 (iSplit; try done).
        iSplit.
        * iPureIntro; lia.
        * iPoseProof (coll_free_hashfun_amortized_implies_bounded_range with "[$H][//]") as "[% %K]"; first done.
          iPureIntro. by apply hash_bound_manipulation.
    - rewrite /compute_hash_from_leaf. wp_pures. rewrite -/compute_hash_from_leaf.
      wp_apply wp_list_head; first done.
      iIntros (?) "[[->->]|(%head & %lproof' & -> & ->)]".
      { inversion Hposs. }
      wp_pures. wp_apply wp_list_tail; first done.
      iIntros (proof') "%Hproof'".
      wp_pures.
      inversion Htvalid; subst.
      iAssert (↯ ((nnreal_nat (S n0) * amortized_error val_size_for_hash max_hash_size _)%NNR) ∗
               ↯ (amortized_error val_size_for_hash max_hash_size _)%NNR)%I with "[Herr]" as "[Herr Herr']".
      { rewrite nnreal_nat_Sn Rmult_plus_distr_r.
        rewrite nnreal_nat_1 Rmult_1_l.
        iDestruct (ec_split with "Herr") as "[$ $]".
        { apply cond_nonneg. }
        { apply Rmult_le_pos; [apply pos_INR|apply cond_nonneg]. }
      }
      wp_pures.
      inversion Hposs; subst; wp_pures; try done.
      + wp_apply ("IH" with "[][][][][$H][$Herr]"); try done.
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
        * iIntros (finalhash) "(%m'' & H  & %Hmfound'' & %Hmsize'' & %Hmsubset')".
          iApply "HΦ".
          iExists m''.
          iSplit; try (iPureIntro; etrans; exact).
          do 2 (iSplit; try done).
          -- iPureIntro; lia.
          -- iPoseProof (coll_free_hashfun_amortized_implies_bounded_range with "[$H][//]") as "[% %K]"; first done.
             iPureIntro. by apply hash_bound_manipulation.
      + wp_apply ("IH1" with "[][][][][$H][$Herr]"); try done.
        { iPureIntro; lia. }
        iIntros (lefthash') "(%m' & %Hmsubset & H & %Hmsize' & %Hlefthashsize')".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (hash0 * 2 ^ val_bit_size + Z.to_nat lefthash')); last first.
        { rewrite Nat2Z.inj_add. f_equal; last lia. rewrite Nat2Z.inj_mul. f_equal.
          apply Z2Nat.inj_pow.
        }
        wp_apply (wp_insert_amortized with "[$H $Herr']").
        * lia.
        * iIntros (finalhash) "(%m'' & H & %Hmfound'' & %Hmsize'' & %Hmsubset')".
          iApply "HΦ".
          iExists m''. iSplit; first (iPureIntro; etrans; exact).
          do 2 (iSplit; try done).
          -- iPureIntro; lia.
          -- iPoseProof (coll_free_hashfun_amortized_implies_bounded_range with "[$H][//]") as "[% %K]"; first done.
             iPureIntro. by apply hash_bound_manipulation.
             Unshelve.
             all: done.
  Qed.

  (* The case where everything is correct *)
  Local Lemma wp_compute_hash_from_leaf_correct (tree:merkle_tree) (m:gmap nat nat) (v:nat) (proof:list (bool*nat)) lproof f E:
     {{{ ⌜tree_valid height tree m⌝ ∗
        coll_free_hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
        ⌜is_list proof lproof⌝ ∗
        ⌜correct_proof tree proof⌝ ∗
        ⌜tree_leaf_value_match tree v proof⌝
     }}}
      compute_hash_from_leaf f lproof (#v) @ E
      {{{ (retv:Z), RET #retv;
          coll_free_hashfun_amortized (val_size_for_hash) max_hash_size f m ∗
          ⌜retv = root_hash_value tree⌝
      }}}.
  Proof.
    iIntros (Φ) "(%Htvalid & H & %Hlist & %Hcorrect & %Hvmatch) HΦ".
    iInduction tree as [hash leaf|hash tree1 Htree1 tree2 Htree2] "IH"
                         forall (height m proof lproof Φ
                              Htvalid Hlist Hcorrect Hvmatch).
    - rewrite /compute_hash_from_leaf. wp_pures. rewrite -/compute_hash_from_leaf.
      wp_apply wp_list_head; first done.
      iIntros (?) "[[-> ->]|%]"; last first.
      { inversion Hcorrect; subst. destruct H as [?[?[??]]].
        inversion H. }
      wp_pures. inversion Htvalid; inversion Hvmatch; subst.
      wp_apply (wp_coll_free_hashfun_prev_amortized with "[$]").
      + done.
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
        wp_apply ("IH" with "[][][][][$]"); try done.
        iIntros (lhash) "[H ->]".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2)); last first.
        { rewrite Nat2Z.inj_add. f_equal. rewrite Nat2Z.inj_mul. f_equal.
          apply Z2Nat.inj_pow.
        }
        wp_apply (wp_coll_free_hashfun_prev_amortized with "H").
        * done.
        * done.
        * iIntros "H". iApply "HΦ".
          iFrame. done.
      + inversion Htvalid. inversion Hvmatch; subst; first done.
        wp_apply ("IH1" with "[][][][][$]"); try done.
        iIntros (rhash) "[H ->]".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2)); last first.
        { rewrite Nat2Z.inj_add. f_equal. rewrite Nat2Z.inj_mul. f_equal.
          apply Z2Nat.inj_pow.
        }
        wp_apply (wp_coll_free_hashfun_prev_amortized with "H").
        * done.
        * done.
        * iIntros "H". iApply "HΦ".
          iFrame. done.
  Qed.

  (*The case where the leaf is incorrect*)
  Local Lemma wp_compute_hash_from_leaf_incorrect (tree:merkle_tree) (m:gmap nat nat) (v v':nat) (proof:list (bool*nat)) lproof f E:
     {{{ ⌜tree_valid height tree m⌝ ∗
        coll_free_hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
        ⌜is_list proof lproof⌝ ∗
        ⌜possible_proof tree proof⌝ ∗
        ⌜tree_leaf_value_match tree v proof⌝ ∗
        ⌜v ≠ v'⌝ ∗
        ⌜ size m + (S height) <= max_hash_size⌝ ∗
        ↯ (nnreal_nat (S height) * amortized_error (val_size_for_hash)%nat max_hash_size max_hash_size_pos)%NNR
     }}}
      compute_hash_from_leaf f lproof (#v') @ E
      {{{ (retv:Z), RET #retv;
          ∃ m', ⌜m ⊆ m'⌝ ∗
                coll_free_hashfun_amortized (val_size_for_hash) max_hash_size f m' ∗
                ⌜size (m') <= size m + (S height)⌝ ∗
                ⌜retv ≠ root_hash_value tree⌝ ∗
                ⌜(0 <= retv < 2^val_bit_size)%Z⌝
      }}}.
  Proof.
    iIntros (Φ) "(%Htvalid & H & %Hlist & %Hpossible & %Hvmatch & %Hneq & %Hmsize & Herr) HΦ".
    iInduction tree as [|] "IH"
                         forall (height m proof lproof Φ Htvalid Hlist Hpossible Hvmatch Hmsize).
    - inversion Htvalid; subst. rewrite /compute_hash_from_leaf. wp_pures.
      rewrite -/compute_hash_from_leaf. inversion Hvmatch; subst.
      wp_apply wp_list_head; first done.
      iIntros (?) "[[_ ->]|(%&%&%&%)]"; last done.
      wp_pures.
      wp_apply (wp_insert_amortized with "[$H Herr]"); try lia.
      + iApply ec_eq; last done.
        simpl. lra.
      + iIntros (hash_value') "(%m' & H & %Hmfound & %Hmsize' & %Hmsubset)".
        iApply "HΦ".
        iExists _.
        iSplit; first done.
        do 3 (try iSplit; try done).
        * iPureIntro; lia.
        * simpl.
          inversion Htvalid; subst.
          iAssert (⌜coll_free m'⌝)%I with "[H]" as "%".
          { by iApply coll_free_hashfun_amortized_implies_coll_free. }
          iPureIntro. intro; subst. apply Hneq. eapply coll_free_lemma; try done.
          erewrite lookup_weaken; try exact. apply Nat2Z.inj in H0. by subst.
        * iPoseProof (coll_free_hashfun_amortized_implies_bounded_range with "[$H][//]") as "[% %K]"; first done.
          iPureIntro. apply hash_bound_manipulation; done.
    - rewrite /compute_hash_from_leaf. wp_pures. rewrite -/compute_hash_from_leaf.
      wp_apply wp_list_head; first done.
      iIntros (?) "[[->->]|(%head & %lproof' & -> & ->)]".
      { inversion Hvmatch. }
      wp_pures. wp_apply wp_list_tail; first done.
      iIntros (proof') "%Hproof'".
      wp_pures.
      inversion Htvalid; subst.
      iAssert (↯ ((nnreal_nat (S n) * amortized_error val_size_for_hash max_hash_size _)%NNR) ∗
               ↯ (amortized_error val_size_for_hash max_hash_size _)%NNR)%I with "[Herr]" as "[Herr Herr']".
      { rewrite nnreal_nat_Sn Rmult_plus_distr_r.
        rewrite nnreal_nat_1 Rmult_1_l.
        iDestruct (ec_split with "Herr") as "[$ $]".
        { apply cond_nonneg. }
        { apply Rmult_le_pos; [apply pos_INR|apply cond_nonneg]. }
      }
      inversion Hpossible; inversion Hvmatch; inversion Htvalid; subst; wp_pures; try done.
      + wp_apply ("IH" with "[][][][][][$H][$Herr]"); try done.
        { iPureIntro; lia. }
        iIntros (lefthash') "(%m' & %Hmsubset & H & %Hmsize' & %Hlefthashneq & %Hlefthashsize')".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (Z.to_nat lefthash' * 2 ^ val_bit_size + hash)); last first.
        { rewrite Nat2Z.inj_add. f_equal. rewrite Nat2Z.inj_mul.
          rewrite Z2Nat.id; last lia. f_equal.
          rewrite Z2Nat.inj_pow. f_equal.
        }
        wp_apply (wp_insert_amortized with "[$H $Herr']").
        * lia.
        * iIntros (finalhash) "(%m'' & H & %Hmfound'' & %Hmsize'' & %Hmsubset')".
          iApply "HΦ".
          iExists m''.
          iSplit; first (iPureIntro; etrans; exact).
          iAssert (⌜coll_free m''⌝)%I with "[H]" as "%".
          { by iApply coll_free_hashfun_amortized_implies_coll_free. }
          do 3 (try iSplit; try done).
          -- iPureIntro; lia.
          -- iPureIntro. simpl.
             intro; subst. apply Hlefthashneq.
             assert (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2 =
                     Z.to_nat lefthash' * 2 ^ val_bit_size + hash) as helper.
             { eapply (coll_free_lemma m''); try done.
               assert (finalhash=hash_value) as ->. { by apply Nat2Z.inj. }
               eapply lookup_weaken; first done.
               etrans; exact.
             }
             epose proof (Nat.mul_split_l _ _ _ _ _ _ _ helper) as [Hsplit _].
             lia.
             Unshelve.
             ++ done.
             ++ done.
             ++ by inversion H22.
             ++ by inversion Hpossible.
          --  iPoseProof (coll_free_hashfun_amortized_implies_bounded_range with "[$H][//]") as "[% %K]"; first done.
              iPureIntro. by apply hash_bound_manipulation.
      + wp_apply ("IH1" with "[][][][][][$H][$Herr]"); try done.
        { iPureIntro; lia. }
        iIntros (righthash') "(%m' & %Hmsubset & H & %Hmvalid' & %Hmsize' & %Hrighthashneq & %Hrighthashsize')".
        wp_pures.
        replace (_*_+_)%Z with (Z.of_nat (hash * 2 ^ val_bit_size + Z.to_nat righthash')); last first.
        { rewrite Nat2Z.inj_add. f_equal; last lia. rewrite Nat2Z.inj_mul. f_equal.
          rewrite Z2Nat.inj_pow. f_equal.
        }
        wp_apply (wp_insert_amortized with "[$H $Herr']").
        * lia.
        * iIntros (finalhash) "(%m'' & H & %Hmfound'' & %Hmsize'' & %Hmsubset')".
          iApply "HΦ".
          iExists m''.
          iSplit; first (iPureIntro; etrans; exact).
          iAssert (⌜coll_free m''⌝)%I with "[H]" as "%".
          { by iApply coll_free_hashfun_amortized_implies_coll_free. }
          do 3 (try iSplit; try done).
          -- iPureIntro; lia.
          -- iPureIntro. simpl.
             intro; subst. apply Hrighthashneq.
             assert (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2 =
                     hash * 2 ^ val_bit_size + Z.to_nat righthash') as helper.
             { eapply (coll_free_lemma m''); try done.
               assert (finalhash=hash_value) as ->. { by apply Nat2Z.inj. }
               eapply lookup_weaken; first done.
               etrans; exact.
             }
             epose proof (Nat.mul_split_l _ _ _ _ _ _ _ helper) as [Hsplit _].
             lia.
             Unshelve.
             ++ by inversion H22.
             ++ rewrite Nat2Z.inj_lt. rewrite Z2Nat.inj_pow.
                replace (Z.of_nat 2) with 2%Z by lia.
                rewrite Z2Nat.id; lia.
          -- iPoseProof (coll_free_hashfun_amortized_implies_bounded_range with "[$H][//]") as "[% %K]"; first done.
             iPureIntro. by apply hash_bound_manipulation.
  Qed.

  (*The case where the leaf is correct but the proof is not *)
  Local Lemma wp_compute_hash_from_leaf_incorrect_proof (tree:merkle_tree) (m:gmap nat nat) (v:nat) (proof:list (bool*nat)) lproof f E:
    {{{ ⌜tree_valid height tree m⌝ ∗
        coll_free_hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
        ⌜is_list proof lproof⌝ ∗
        ⌜possible_proof tree proof⌝ ∗
        ⌜incorrect_proof tree proof ⌝ ∗
        ⌜tree_leaf_value_match tree v proof⌝ ∗
        ⌜ size m + (S height) <= max_hash_size⌝ ∗
        ↯ (nnreal_nat (S height) * amortized_error (val_size_for_hash)%nat max_hash_size max_hash_size_pos)%NNR
     }}}
      compute_hash_from_leaf f lproof (#v) @ E
      {{{ (retv:Z), RET #retv;
          ∃ m', ⌜m ⊆ m'⌝ ∗
                coll_free_hashfun_amortized (val_size_for_hash) max_hash_size f m' ∗
                ⌜size (m') <= size m + (S height)⌝ ∗
                ⌜retv ≠ root_hash_value tree⌝ ∗
                ⌜(0 <= retv < 2^val_bit_size)%Z⌝
      }}}.
  Proof.
    iIntros (Φ) "(%Htvalid & H & %Hlist & %Hposs & %Hincorrect & %Hvmatch & %Hmsize & Herr) HΦ".
    iInduction tree as [|] "IH"
                         forall (height m proof lproof Φ Htvalid Hlist Hposs Hincorrect Hvmatch Hmsize).
    - inversion Hincorrect.
    - rewrite /compute_hash_from_leaf. wp_pures.
      rewrite -/compute_hash_from_leaf.
      wp_apply wp_list_head; first done.
      iIntros (?) "[[->->]|(%head & %lproof' & -> & ->)]".
      { inversion Hvmatch. }
      wp_pures. wp_apply wp_list_tail; first done.
      iIntros (proof') "%Hproof'".
      wp_pures. inversion Htvalid; subst.
      iAssert (↯ ((nnreal_nat (S n) * amortized_error val_size_for_hash max_hash_size _)%NNR) ∗
                 ↯ (amortized_error val_size_for_hash max_hash_size _)%NNR)%I with "[Herr]" as "[Herr Herr']".
      { rewrite nnreal_nat_Sn Rmult_plus_distr_r.
        rewrite nnreal_nat_1 Rmult_1_l.
        iDestruct (ec_split with "Herr") as "[$ $]".
        { apply cond_nonneg. }
        { apply Rmult_le_pos; [apply pos_INR|apply cond_nonneg]. }
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
          -- iIntros (retv) "(%m'' & H & %Hmfound & %Hsize'' & %Hmsubset')".
             iApply "HΦ".
             iAssert (⌜coll_free m''⌝)%I with "[H]" as "%".
             { by iApply coll_free_hashfun_amortized_implies_coll_free. }
             iExists m''. iSplit; first (iPureIntro; etrans; exact).
             do 3 (try iSplit; try done).
             ++ iPureIntro; lia.
             ++ iPureIntro. simpl. intro.
                assert (retv=hash_value) as ->. { by apply Nat2Z.inj. }
                inversion H30; subst.
                assert (root_hash_value tree1 * 2 ^ val_bit_size + root_hash_value tree2 =
                        Z.to_nat lefthash * 2 ^ val_bit_size + hash) as helper.
                { eapply (coll_free_lemma m''); try done.
                  eapply lookup_weaken; first done.
                  etrans; exact.
                }
                epose proof (Nat.mul_split_l _ _ _ _ _ _ _ helper) as [Hsplit Hsplit']; subst. done.
                Unshelve.
                all: try done.
                ** by inversion H22.
             ++ iPoseProof (coll_free_hashfun_amortized_implies_bounded_range with "[$H][//]") as "[% %K]"; first done.
                iPureIntro. by apply hash_bound_manipulation.
      + (*incorrect happens above*)
        wp_apply ("IH" with "[][][][][][][$H][$Herr]"); try done.
        * iPureIntro; lia.
        * iIntros (lefthash) "(%m' & %Hmsubset & H & %Hmsize' & %Hlefthashneq & %Hlefthashsize)".
          wp_pures.
          replace (_*_+_)%Z with (Z.of_nat (Z.to_nat lefthash * 2 ^ val_bit_size + hash)); last first.
          { rewrite Nat2Z.inj_add. f_equal. rewrite Nat2Z.inj_mul.
            rewrite Z2Nat.id; last lia. f_equal.
            rewrite Z2Nat.inj_pow. f_equal.
          }
          wp_apply (wp_insert_amortized with "[$H $Herr']"); try done.
          -- lia.
          -- iIntros (retv) "(%m'' & H & %Hmfound & %Hsize'' & %Hmsubset')".
             iApply "HΦ".
             iAssert (⌜coll_free m''⌝)%I with "[H]" as "%".
             { by iApply coll_free_hashfun_amortized_implies_coll_free. }
             iExists m''. iSplit; first (iPureIntro; etrans; exact).
             do 3 (try iSplit; try done).
             ++ iPureIntro; lia.
             ++ iPureIntro. simpl. intro.
                assert (retv=hash_value) as ->. { by apply Nat2Z.inj. }
                apply Hlefthashneq.
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
             ++ iPoseProof (coll_free_hashfun_amortized_implies_bounded_range with "[$H][//]") as "[% %K]"; first done.
                iPureIntro. by apply hash_bound_manipulation.
      + (*left neq guess left *)
        wp_apply (wp_compute_hash_from_leaf_size with "[$H $Herr]").
        * repeat iSplit; last first; iPureIntro; try done. lia.
        * iIntros (righthash) "(%m' & %Hmsubset & H & %Hmsize' & %Hrighthashsize)".
          wp_pures.
          replace (_*_+_)%Z with (Z.of_nat (hash * 2 ^ val_bit_size + Z.to_nat righthash )); last first.
          { rewrite Nat2Z.inj_add. f_equal; last lia. rewrite Nat2Z.inj_mul. f_equal.
            rewrite Z2Nat.inj_pow. f_equal.
          }
          wp_apply (wp_insert_amortized with "[$H $Herr']"); try done.
          -- lia.
          -- iIntros (retv) "(%m'' & H & %Hmfound & %Hsize'' & %Hmsubset')".
             iApply "HΦ".
             iAssert (⌜coll_free m''⌝)%I with "[H]" as "%".
             { by iApply coll_free_hashfun_amortized_implies_coll_free. }
             iExists m''. iSplit; first (iPureIntro; etrans; exact).
             do 3 (try iSplit; try done).
             ++ iPureIntro; lia.
             ++ iPureIntro. simpl. intro.
                assert (retv=hash_value) as ->. { by apply Nat2Z.inj. }
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
             ++ iPoseProof (coll_free_hashfun_amortized_implies_bounded_range with "[$H][//]") as "[% %K]"; first done.
                iPureIntro. by apply hash_bound_manipulation.
      + (*incorrect happens above *)
        wp_apply ("IH1" with "[][][][][][][$H][$Herr]"); try done.
        * iPureIntro; lia.
        * iIntros (righthash) "(%m' & %Hmsubset & H & %Hmsize' & %Hrighthashneq & %Hrighthashsize)".
          wp_pures.
          replace (_*_+_)%Z with (Z.of_nat (hash * 2 ^ val_bit_size + Z.to_nat righthash)); last first.
          { rewrite Nat2Z.inj_add. f_equal; last lia. rewrite Nat2Z.inj_mul. f_equal.
            rewrite Z2Nat.inj_pow. f_equal.
          }
          wp_apply (wp_insert_amortized with "[$H $Herr']"); try done.
          -- lia.
          -- iIntros (retv) "(%m'' & H & %Hmfound & %Hsize'' & %Hmsubset')".
             iApply "HΦ".
             iAssert (⌜coll_free m''⌝)%I with "[H]" as "%".
             { by iApply coll_free_hashfun_amortized_implies_coll_free. }
             iExists m''. iSplit; first (iPureIntro; etrans; exact).
             do 3 (try iSplit; try done).
             ++ iPureIntro; lia.
             ++ iPureIntro. simpl. intro.
                assert (retv=hash_value) as ->. { by apply Nat2Z.inj. } apply Hrighthashneq.
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
             ++ iPoseProof (coll_free_hashfun_amortized_implies_bounded_range with "[$H][//]") as "[% %K]"; first done.
                iPureIntro. by apply hash_bound_manipulation.
  Qed.

  Definition is_possible_proof_list proof lproof tree :=
    is_list proof lproof /\ possible_proof tree proof.

  Definition tree_leaf_proof_match tree proof v :=
    correct_proof tree proof /\ tree_leaf_value_match tree v proof.

  (** checker*)

  Definition incorrect_proof_or_leaf tree proof v :=
    incorrect_proof tree proof \/ (∃ v', tree_leaf_value_match tree v' proof /\ v ≠ v').

  Definition merkle_tree_decider_program : val :=
    λ: "correct_root_hash" "lhmf",
      (λ: "lproof" "lleaf",
         "correct_root_hash" = compute_hash_from_leaf "lhmf" "lproof" "lleaf"
      ).

  Definition decider_program_helper_spec (checker:val) (tree:merkle_tree) (f:val) : iProp Σ:=
    (∀ lproof proof v m',
             {{{
                  ⌜tree_valid height tree m'⌝ ∗
                  coll_free_hashfun_amortized (val_size_for_hash)%nat max_hash_size f m' ∗
                  ⌜is_possible_proof_list proof lproof tree ⌝∗
                  ⌜ size m' + (S height) <= max_hash_size⌝ ∗
                  ↯ (nnreal_nat (S height) * amortized_error (val_size_for_hash)%nat max_hash_size max_hash_size_pos)%NNR

            }}}
              checker lproof (#v)
              {{{ (b:bool), RET #b;
                  if b then
                    ⌜tree_leaf_proof_match tree proof v⌝∗
                    coll_free_hashfun_amortized (val_size_for_hash) max_hash_size f m' ∗
                    ↯ (nnreal_nat (S height) * amortized_error (val_size_for_hash)%nat max_hash_size max_hash_size_pos)%NNR
                  else
                    ⌜incorrect_proof_or_leaf tree proof v⌝ ∗
                    ∃ m'', ⌜m' ⊆ m''⌝ ∗
                        coll_free_hashfun_amortized (val_size_for_hash) max_hash_size f m'' ∗
                        ⌜size (m'') <= size m' + (S height)⌝
          }}} )%I.

  Lemma merkle_tree_decider_program_spec tree (m:gmap nat nat) f:
    {{{ ⌜tree_valid height tree m⌝ ∗
        coll_free_hashfun_amortized (val_size_for_hash)%nat max_hash_size f m
    }}} merkle_tree_decider_program #(root_hash_value tree) f
    {{{
          (checker:val), RET checker;
          coll_free_hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
          decider_program_helper_spec checker tree f
    }}}.
  Proof.
    iIntros (Φ) "(%Htvalid & H) IH".
    rewrite /merkle_tree_decider_program.
    wp_pures. iModIntro.
    iApply "IH". iFrame.
    iIntros (?????) "!> (%&H&[%%]&%&Herr) HΦ".
    wp_pures.
    epose proof (possible_proof_implies_exists_leaf tree proof _) as [v' ?].
    destruct (decide (v=v')).
    - destruct (decide (correct_proof tree proof)) as [K|K].
      + wp_apply (wp_compute_hash_from_leaf_correct with "[$H]").
        * repeat iSplit; try done; iPureIntro.
          -- by subst.
        * iIntros (?) "(H&%)".
          wp_pures. subst. case_bool_decide; last done.
          iModIntro. iApply "HΦ". iFrame.
          by iSplit.
      + epose proof (proof_not_correct_implies_incorrect _ _ _ K).
        wp_apply (wp_compute_hash_from_leaf_incorrect_proof with "[$H $Herr]").
        * repeat iSplit; try done; iPureIntro.
          -- by subst.
        * iIntros (?) "(%&%&H&%&%&%&%)".
          wp_pures.
          rewrite bool_decide_eq_false_2; last first.
          { intros K'; inversion K'; by subst. }
          iModIntro; iApply "HΦ".
          repeat iSplit.
          -- iPureIntro. left. naive_solver.
          -- iExists _. by iFrame.
    - wp_apply (wp_compute_hash_from_leaf_incorrect with "[$H $Herr]").
      + repeat iSplit; done.
      + iIntros (?) "(%&%&H&%&%&%&%)".
        wp_pures. rewrite bool_decide_eq_false_2; last first.
        { intros K. inversion K. by subst. }
        iModIntro. iApply "HΦ".
        repeat iSplit.
        * iPureIntro. right. eexists _; naive_solver.
        * iExists _. iFrame. by repeat iSplit.
          Unshelve.
          all: done.
  Qed.




  (** Useful predicates **)


  Inductive proof_idx_relate : nat -> list (bool*nat) -> nat -> Prop :=
  | proof_idx_relate_lf: proof_idx_relate 0 [] 0
  | proof_idx_relate_left idx n rhash proof:
    proof_idx_relate n proof idx ->
    idx < 2^n ->
    proof_idx_relate (S n) ((true, rhash)::proof) idx
  | proof_idx_relate_right idx n lhash proof:
      proof_idx_relate n proof (idx - 2^n) ->
      2^n <= idx ->
      proof_idx_relate (S n) ((false, lhash)::proof) idx
  .

  Lemma proof_idx_relate_implies_possible_proof tree proof h idx m:
    tree_valid h tree m ->
    proof_idx_relate h proof idx ->
    Forall (λ x : bool * nat, x.2 < 2 ^ val_bit_size) proof ->
    possible_proof tree proof.
  Proof.
    revert tree proof idx.
    induction h as [|h IHheight]; intros tree proof idx Htvalid Hrelate Hforall.
    - inversion Hrelate; inversion Htvalid; subst. constructor.
    - inversion Htvalid; inversion Hrelate; subst.
      + constructor.
        * eapply IHheight; try done. by eapply Forall_inv_tail.
        * by apply Forall_inv in Hforall.
      + constructor.
        * eapply IHheight; try done. by eapply Forall_inv_tail.
        * by apply Forall_inv in Hforall.
  Qed.


  Inductive tree_leaf_list: nat -> merkle_tree -> list nat -> Prop :=
  | tree_leaf_list_lf h lf: tree_leaf_list 0 (Leaf h lf) (lf::[])
  | tree_leaf_list_br n a alist b blist h:
    tree_leaf_list n a alist ->
    tree_leaf_list n b blist ->
    tree_leaf_list (S n) (Branch h a b) (alist ++ blist).

  Definition tree_valid_with_leaf_list height tree list m:=
    tree_leaf_list height tree list /\ tree_valid height tree m.

  Lemma tree_valid_with_leaf_list_implies_tree_leaf_list h tree list m:
    tree_valid_with_leaf_list h tree list m -> tree_leaf_list h tree list.
  Proof.
    by intros [].
  Qed.

  Lemma tree_valid_with_leaf_list_implies_tree_valid h tree list m:
    tree_valid_with_leaf_list h tree list m -> tree_valid h tree m.
  Proof.
    by intros [].
  Qed.

  Lemma tree_valid_with_leaf_list_br h treea l1 (m:gmap nat nat) treeb l2 hash:
    hash < 2 ^ val_bit_size ->
    m !! (root_hash_value treea * 2 ^ val_bit_size + root_hash_value treeb) = Some (hash)->
    tree_valid_with_leaf_list h treea l1 m -> tree_valid_with_leaf_list h treeb l2 m ->
    tree_valid_with_leaf_list (S h) (Branch hash treea treeb) (l1++l2) m.
  Proof.
    clear.
    intros ? ?[??] [??]. split; by constructor.
  Qed.

  Lemma tree_valid_with_leaf_list_superset m m' h tree l:
    m⊆m' -> tree_valid_with_leaf_list h tree l m -> tree_valid_with_leaf_list h tree l m'.
  Proof.
    intros ? [??]. split; first done.
    by eapply tree_valid_superset.
  Qed.


  Lemma tree_valid_with_leaf_list_length n tree lis m:
    tree_valid_with_leaf_list n tree lis m -> length lis = 2^n.
  Proof.
    clear.
    intros [Hlist _]. revert Hlist.
    revert tree lis.
    induction n; intros tree lis Hlist.
    - inversion Hlist. by simpl.
    - inversion Hlist; subst. rewrite app_length. simpl. erewrite !IHn; try done.
      lia.
  Qed.

  Lemma tree_valid_with_leaf_list_implies_lookup_some lis tree h proof idx leafv m:
    tree_valid_with_leaf_list h tree lis m ->
    proof_idx_relate h proof idx ->
    (tree_leaf_value_match tree leafv proof <->
    lis !! idx = Some leafv).
  Proof.
    clear.
    revert lis tree proof idx leafv.
    induction h as [|h IHheight]; intros lis tree proof idx leafv [Hlist Hvalid] Hrelate.
    - split.
      + intros Hmatch. inversion Hrelate; inversion Hmatch; subst; try done.
        by inversion Hlist; subst.
      + intros Hfound. inversion Hrelate; inversion Hlist; subst; try done.
        simpl in Hfound. inversion Hfound.
        constructor.
    - split.
      + intros Hmatch. inversion Hrelate; subst.
        * inversion Hrelate; inversion Hmatch; inversion Hlist; inversion Hvalid; subst. inversion H15; inversion H22; subst.
          assert (length alist = 2^h).
          { eapply tree_valid_with_leaf_list_length; split; try done. }
          rewrite lookup_app_l; last lia.
          rewrite -IHheight; try done.
        * inversion Hrelate; inversion Hmatch; inversion Hlist; inversion Hvalid; subst. inversion H15; inversion H22; subst.
          assert (length alist = 2^h) as K.
          { by eapply tree_valid_with_leaf_list_length. }
          rewrite lookup_app_r; last lia.
          rewrite K.
          by rewrite -IHheight.
      + intros Hfound.
        pose proof (tree_valid_with_leaf_list_length) as Hlen.
        inversion Hrelate; inversion Hlist; inversion Hvalid; subst.
        * constructor. inversion H14; subst.
          rewrite IHheight; [|done|done].
          erewrite <-lookup_app_l; first done.
          by erewrite Hlen.
        * constructor. inversion H14; subst.
          rewrite IHheight; [|done|done].
          erewrite <-Hlen; first erewrite <-lookup_app_r; try done.
          by erewrite Hlen.
  Qed.


End merkle_tree.
