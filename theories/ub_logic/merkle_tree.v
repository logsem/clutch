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
  

  Inductive tree_leaf_value_match: merkle_tree -> nat -> list (bool*nat) -> Prop:=
  | tree_value_match_lf h lf: tree_leaf_value_match (Leaf h lf) lf []
  | tree_leaf_value_match_left h l r xs v rhash:
    tree_leaf_value_match l v xs->
    tree_leaf_value_match (Branch h l r) v ((true,rhash)::xs)
  | tree_value_match_right h l r xs v lhash:
    tree_leaf_value_match r v xs ->
    tree_leaf_value_match (Branch h l r) v ((false,lhash)::xs).

  (*This ensures all numbers in the proof are smaller than 2^val_bit_size*)
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
    

  Definition root_hash_value_program : val :=
    λ: "ltree",
      match: "ltree" with
      | InjL "x" => Fst "x"
      | InjR "x" => let, ("a", "b", "c") := "x" in "a"
      end.

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
  Lemma wp_root_hash_value_program n lt tree E:
    {{{ ⌜tree_relate n lt tree⌝ }}}
    root_hash_value_program lt @ E
    {{{ (retv:Z), RET #retv; ⌜retv = root_hash_value tree⌝}}}.
  Proof.
    iIntros (Φ) "%H HΦ".
    rewrite /root_hash_value_program. wp_pures.
    inversion H.
    - wp_pures. iApply "HΦ". by iPureIntro.
    - wp_pures. iApply "HΦ". by iPureIntro.
  Qed.

  Lemma tree_valid_superset m m' tree:
    tree_valid tree m -> m ⊆ m' -> tree_valid tree m'.
  Proof.
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

  Lemma proof_correct_iff_not_incorrect tree proof:
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
  
  (** Spec *)
  Lemma wp_compute_hash_from_leaf_correct (ltree:val) (tree:merkle_tree) (m:gmap nat Z) (v:nat) (proof:list (bool*nat)) lproof f E:
     {{{ ⌜tree_relate height ltree tree⌝ ∗
        ⌜tree_valid tree m⌝ ∗
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
    iIntros (Φ) "(%Htrelate & %Htvalid & H & %Hlist & %Hcorrect & %Hvmatch & %Hmvalid) HΦ".
    iInduction tree as [hash leaf|hash tree1 Htree1 tree2 Htree2] "IH"
                         forall (height ltree m proof lproof Φ
                              Htrelate Htvalid Hlist Hcorrect Hvmatch Hmvalid).
    - rewrite /compute_hash_from_leaf. wp_pures. rewrite -/compute_hash_from_leaf.
      wp_apply wp_list_head; first done.
      iIntros (?) "[[-> ->]|%]"; last first.
      { inversion Hcorrect; subst. destruct H as [?[?[??]]].
        inversion H. }
      wp_pures. inversion Htvalid; inversion Hvmatch. subst.
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
      + inversion Htrelate. inversion Htvalid. inversion Hvmatch; subst; last done.
        wp_apply ("IH" with "[][][][][][][$]"); try done.
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
      + inversion Htrelate. inversion Htvalid. inversion Hvmatch; subst; first done.
        wp_apply ("IH1" with "[][][][][][][$]"); try done.
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

  Lemma wp_compute_hash_from_leaf_incorrect (ltree:val) (tree:merkle_tree) (m:gmap nat Z) (v v':nat) (proof:list (bool*nat)) lproof f E:
     {{{ ⌜tree_relate height ltree tree⌝ ∗
        ⌜tree_valid tree m⌝ ∗
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
    iIntros (Φ) "(%Htrelate & %Htvalid & H & %Hlist & %Hpossible & %Hvmatch & %Hneq & %Hmvalid & %Hmsize & Herr) HΦ".
    iInduction tree as [|] "IH"
                         forall (height ltree m proof lproof Φ Htrelate Htvalid Hlist Hpossible Hvmatch Hmvalid Hmsize).
    - inversion Htrelate; subst. rewrite /compute_hash_from_leaf. wp_pures.
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
          rewrite /val_size_for_hash in Hforall. destruct Hforall as [? H1].
          apply Zle_lt_succ in H1.
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
      inversion Htrelate; subst.
      iAssert (€ ((nnreal_nat (S n) * amortized_error val_size_for_hash max_hash_size)%NNR) ∗
               € (amortized_error val_size_for_hash max_hash_size)%NNR)%I with "[Herr]" as "[Herr Herr']".
      { iApply ec_split. iApply (ec_spend_irrel with "[$]").
        simpl. lra.
      }
      inversion Hpossible; inversion Hvmatch; inversion Htvalid; subst; wp_pures; try done.
      + wp_apply ("IH" with "[][][][][][][][$H][$Herr]"); try done.
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
             ++ by inversion H19.
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
      + wp_apply ("IH1" with "[][][][][][][][$H][$Herr]"); try done.
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
             ++ by inversion H19.
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

  (** checker*)
  Definition merkle_tree_decider_program : val :=
    λ: "correct_root_hash" "lhmf",
      (λ: "lproof" "lleaf",
         "correct_root_hash" = compute_hash_from_leaf "lhmf" "lproof" "lleaf"
      ).

  Lemma merkle_tree_decider_program_spec ltree tree (m:gmap nat Z) f:
    {{{ ⌜tree_relate height ltree tree⌝ ∗
        ⌜tree_valid tree m⌝ ∗
        hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
        ⌜map_valid m⌝ 
    }}} merkle_tree_decider_program #(root_hash_value tree) f
    {{{
          (checker:val), RET checker;
          hashfun_amortized (val_size_for_hash)%nat max_hash_size f m ∗
          (** correct*)
          (∀ lproof proof v m',
             {{{
                  ⌜m⊆m'⌝ ∗
                  hashfun_amortized (val_size_for_hash)%nat max_hash_size f m' ∗
                  ⌜is_list proof lproof⌝ ∗
                  ⌜correct_proof tree proof⌝ ∗
                  ⌜tree_leaf_value_match tree v proof⌝∗
                  ⌜map_valid m'⌝ 
                   
            }}}
              checker lproof (#v)
              {{{ RET #true;
                    hashfun_amortized (val_size_for_hash)%nat max_hash_size f m' 
          }}}) ∗
          (** incorrect*)
          (∀ lproof proof v v' m',
             {{{  ⌜m⊆m'⌝ ∗
                  hashfun_amortized (val_size_for_hash)%nat max_hash_size f m' ∗
                  ⌜is_list proof lproof⌝ ∗
                  ⌜possible_proof tree proof⌝ ∗
                  ⌜tree_leaf_value_match tree v proof⌝ ∗
                  ⌜v ≠ v'⌝ ∗
                  ⌜map_valid m'⌝ ∗
                  ⌜ size m' + (S height) <= max_hash_size⌝ ∗
                  € (nnreal_nat (S height) * amortized_error (val_size_for_hash)%nat max_hash_size)%NNR 
                   
            }}}
              checker lproof (#v')
              {{{ RET #false;
                  ∃ m'', ⌜m' ⊆ m''⌝ ∗
                        hashfun_amortized (val_size_for_hash) max_hash_size f m'' ∗
                        ⌜map_valid m''⌝ ∗
                        ⌜size (m'') <= size m' + (S height)⌝ 
          }}})
    }}}.
  Proof.
    iIntros (Φ) "(%Htrelate & %Htvalid & H & %Hmvalid) IH".
    rewrite /merkle_tree_decider_program.
    wp_pures. iModIntro.
    iApply "IH". iFrame.
    iSplit.
    - iIntros (?????). iModIntro.
      iIntros "(%&H&%&%&%&%)IH".
      wp_pures.
      wp_apply (wp_compute_hash_from_leaf_correct with "[$H]").
      + repeat iSplit; iPureIntro; try done.
        by eapply tree_valid_superset.
      + iIntros (?) "[H ->]". wp_pures.
        iModIntro. case_bool_decide; last done.
        iApply "IH"; iFrame.
    - iIntros (??????).
      iModIntro.
      iIntros "(%&H&%&%&%&%&%&%&Herr) IH".
      wp_pures.
      wp_apply (wp_compute_hash_from_leaf_incorrect with "[$H $Herr]").
      + repeat iSplit; iPureIntro; try done.
        by eapply tree_valid_superset.
      + iIntros (?) "(%&%&H&%&%&%&%)".
        wp_pures. iModIntro.
        case_bool_decide as K; first by inversion K.
        iApply "IH".
        iExists _; iFrame.
        repeat iSplit; try done.
  Qed.
  
End merkle_tree.
