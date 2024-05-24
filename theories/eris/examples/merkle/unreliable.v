From clutch.common Require Import inject.
From clutch.eris.lib Require Export map list.
From clutch.eris.examples Require Import hash.
From clutch.eris.examples.merkle Require Import merkle_tree.
Import Hierarchy.
Set Default Proof Using "Type*".
Open Scope nat.

Section unreliable_storage.
  Context `{!erisGS Σ}.
  Variables unreliable_alloc_program unreliable_write_program unreliable_read_program:val.

  (*We provide three axioms of the specification of the operations of the unreliable storage*)
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
  Hypothesis max_hash_size_pos: (0<max_hash_size)%nat.
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
    clear max_hash_size_pos max_hash_size.
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



  (** Building the tree*)
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
        let, ("lhash", "ltree") := "helper" "lhmf" ("n"-#1) "list1" in
        let, ("rhash", "rtree") := "helper" "lhmf" ("n"-#1) "list2" in
        let: "hash" := "lhmf" (pow #val_bit_size * "lhash" + "rhash") in
        let: "l" := unreliable_alloc_program #3 in
        unreliable_write_program "l" "hash";;
        unreliable_write_program ("l"+#1) "ltree";;
        unreliable_write_program ("l"+#2) "rtree";;
        ("hash", "l")
  .

  Definition tree_builder : val :=
    λ: "list" "height",
      let: "lhmf" := init_hash val_size_for_hash #() in
      let, ("hash", "l") := tree_builder_helper "lhmf" "height" "list" in
      ("l", merkle_tree_decider_program val_bit_size' "hash" "lhmf").
  
  Definition is_valid_list list vlist height max_size :=
    length list = 2^height /\ Forall (λ x, x < max_size) list /\ is_list list vlist.

  Lemma tree_builder_helper_spec (list:list nat) (vlist: val) (height:nat) (m:gmap nat nat) (f:val):
    size (m) + 2^(S height) - 1 <= max_hash_size ->
    is_valid_list list vlist height (2^(2*val_bit_size))->
    {{{ coll_free_hashfun_amortized val_size_for_hash max_hash_size f m ∗
        € (nnreal_nat (2^(S height)-1) * amortized_error val_size_for_hash max_hash_size max_hash_size_pos)%NNR
    }}}
      tree_builder_helper f #height vlist 
      {{{ (hash:nat) (l:nat), RET (#hash, #l);
          ∃ (m':gmap nat nat) (tree:merkle_tree),
            ⌜m ⊆ m'⌝ ∗
            ⌜size (m') <= size (m) + 2^(S height) - 1⌝ ∗
            coll_free_hashfun_amortized val_size_for_hash max_hash_size f m' ∗
            ⌜tree_valid_with_leaf_list val_bit_size' height tree list m'⌝∗
            ⌜root_hash_value tree = hash ⌝
      }}}.
  Proof.
    iIntros (Hmsize (Hlength&Hforall&Hislist) Φ) "(H&Herr) HΦ".
    iInduction height as [|height] "IH" forall (list vlist m Hmsize Hlength Hforall Hislist Φ).
    - rewrite /tree_builder_helper. wp_pures.
      assert (∃ x:nat, list = x::[]) as [x ->].
      { destruct list as [| ? [|]]; first done.
        - naive_solver.
        - done.
      }
      wp_apply (wp_list_head); first done.
      iIntros (?) "[[%?]|(%&%&%K&->)]"; first done.
      inversion K; subst.
      wp_pures.
      wp_apply (wp_insert_amortized with "[$H Herr]").
      + simpl in Hmsize. lia.
      + iApply ec_spend_irrel; last done.
        simpl. lra.
      + iIntros (hash) "(%m' & H&%&%&%)".
        wp_pures. replace 2%Z with (Z.of_nat 2) by lia.
        wp_apply unreliable_alloc_spec; [lia|done|].
        iIntros (l) "_".
        wp_pures.
        iAssert (⌜(0<=hash<2^val_bit_size)%Z⌝)%I as "[%Ha %Hb]".
        { iPoseProof (coll_free_hashfun_amortized_implies_bounded_range with "[$H][//]") as "[% %T]"; first done.
          iPureIntro. by apply hash_bound_manipulation.
        }
        (* replace (hash) with (Z.of_nat $ Z.to_nat hash); last lia. *)
        wp_apply unreliable_write_spec; first done.
        iIntros "_".
        wp_pures.
        replace (_+_)%Z with (Z.of_nat (l+1)%nat); last lia.
        wp_apply unreliable_write_spec; first done.
        iIntros "_"; wp_pures.
        iModIntro.
        iApply "HΦ".
        iExists m', _.
        repeat (try iSplit; try done).
        * iPureIntro. simpl; lia.
        * iPureIntro. constructor.
        * iPureIntro; constructor.
          -- instantiate (1 := Z.to_nat hash).
             rewrite /merkle_tree.val_bit_size.
             rewrite Z2Nat.inj_lt in Hb; try lia.
             rewrite Znat.Z2Nat.inj_pow in Hb; try lia.
             eapply Nat.lt_stepr; first done. f_equal. 
             rewrite Nat2Z.id. done.
          -- apply Forall_inv in Hforall. done.
          -- rewrite Nat2Z.id; done. 
        * rewrite Nat2Z.id. done. 
    - rewrite /tree_builder_helper. wp_pures. rewrite -/tree_builder_helper.
      replace (_-_)%Z with (Z.of_nat (height)); last lia.
      wp_apply pow_spec; first done.
      iIntros (?) "->".
      wp_apply wp_list_split; first (iSplit; iPureIntro; try done; rewrite Hlength).
      { apply PeanoNat.Nat.pow_le_mono_r; lia. }
      iIntros (a b) "(%l1 & %l2 &%&%&%&%)"; wp_pures.
      iAssert (€ ((nnreal_nat (2 ^ S height - 1) * amortized_error val_size_for_hash max_hash_size _)%NNR) ∗
               € ((nnreal_nat (2 ^ S height - 1) * amortized_error val_size_for_hash max_hash_size _)%NNR) ∗
               € ((nnreal_nat (1) * amortized_error val_size_for_hash max_hash_size _)%NNR)
                 
              )%I with "[Herr]" as "[Herr [Herr' Herr'']]".
      { repeat rewrite  -ec_split. iApply ec_spend_irrel; last done.
        remember (amortized_error val_size_for_hash max_hash_size) as x.
        clear.
        assert (forall x y z, (nnreal_nat x * z + nnreal_nat y * z)%NNR = (nnreal_nat (x+y) * z)%NNR) as Hr; last erewrite !Hr.
        - clear. intros. destruct z. apply nnreal_ext. simpl. rewrite plus_INR. lra. 
        - repeat f_equal. remember (S height) as h.
          simpl. assert (1<=2^h).
          + clear. induction h; simpl; lia.
          + lia. 
      }
      subst.
      replace (Z.of_nat (S height) - 1)%Z with (Z.of_nat height); last lia.
      wp_apply ("IH" with "[][][][][$H][$Herr]"); try iPureIntro; try done.
      + assert (2^S height <= 2^ S (S height)); try lia.
        simpl. lia.
      + by apply Forall_app in Hforall as [Hforall1 Hforall2].
      + iIntros (hasha la) "(%m' & %treea & %&%&H&%&%)".
        wp_pures.
        replace (Z.of_nat (S height) - 1)%Z with (Z.of_nat height); last lia.
        wp_apply ("IH"$! l2 with "[][][][][$H][$Herr']"); try iPureIntro; try done.
        * trans (size m + 2^ S height - 1 + 2 ^ S height - 1); try lia.
          etrans; last exact. simpl. lia.
        * replace (2^ S height) with (2^height + 2 ^ height) in Hlength; last first.
          { simpl. lia. }
          rewrite app_length in Hlength. lia.
        * rewrite Forall_app in Hforall. set_solver.
        * iIntros (hashb lb) "(%m'' & %treeb & %&%&H&%&%)".
          wp_pures.
          wp_apply pow_spec; first done.
          iIntros (?) "->".
          wp_pures. rewrite <-Nat2Z.inj_mul. rewrite  <-Nat2Z.inj_add.
          replace (_+(_+0)) with (2^S val_bit_size'); last (simpl; lia).
          wp_apply (wp_insert_amortized with "[$H Herr'']").
          -- eapply PeanoNat.Nat.le_lt_trans; first exact.
             eapply PeanoNat.Nat.lt_le_trans; last exact.
             apply (PeanoNat.Nat.le_lt_trans _ (size m + 2 ^ S height - 1 + 2^S height - 1)); try lia.
             clear. simpl. assert (0<2^height); try lia.
             induction height; simpl; lia.
          -- iApply ec_spend_irrel; last done.
             simpl. lra.
          -- iIntros (hash) "(%m''' & H&%Hfound&%&%)".
             wp_pures.
             replace 3%Z with (Z.of_nat 3) by lia.
             wp_apply unreliable_alloc_spec; [lia|done|].
             iIntros (?) "_".
             wp_pures.
             iAssert (⌜(0<=hash<2^val_bit_size)%Z⌝)%I as "[%Ha %Hb]".
             { iPoseProof (coll_free_hashfun_amortized_implies_bounded_range with "[$H][//]") as "[% %T]"; first done.
               iPureIntro. by apply hash_bound_manipulation.
             }
             (* replace (hash) with (Z.of_nat (Z.to_nat hash)); last lia. *)
             wp_apply unreliable_write_spec; first done.
             iIntros "_".
             wp_pures.
             replace (_+1)%Z with (Z.of_nat (x+1)) by lia.
             wp_apply unreliable_write_spec; first done.
             iIntros "_".
             wp_pures.
             replace (_+2)%Z with (Z.of_nat (x+2)) by lia.
             wp_apply unreliable_write_spec; first done.
             iIntros "_".
             wp_pures.
             iModIntro. iApply "HΦ".
             iExists m''', (Branch (Z.to_nat hash) treea treeb).
             do 4 (try iSplit; try done).
             ++ iPureIntro. by do 3 (etrans; last exact).
             ++ iPureIntro. replace (_+_-_) with (size m + 2 ^ S height + 2^ S height - 1); last by (simpl;lia).
                trans (size m' + 2^S height); last lia.
                etrans; first exact.
                assert (0<2^S height); try lia.
                clear.
                remember (S height) as x; clear. 
                induction x; simpl; lia.
             ++ iPureIntro. apply tree_valid_with_leaf_list_br; last first.
                --- by eapply tree_valid_with_leaf_list_superset; [done|..]. 
                --- eapply tree_valid_with_leaf_list_superset; [..|done].
                    by etrans; last exact.
                --- rewrite Nat2Z.id.
                    rewrite -Hfound. f_equal. subst. simpl. lia.
                --- rewrite Z2Nat.inj_lt in Hb; try lia.
                    eapply Nat.lt_stepr; first exact.
                    rewrite Znat.Z2Nat.inj_pow; try lia. rewrite Nat2Z.id.
                    f_equal.
                    Unshelve. all: done.
             ++ by rewrite Nat2Z.id.
  Qed.

  Definition is_acceptable_list height list vlist:=
    length list = 2^height /\
    Forall (λ x, x < 2^(2*val_bit_size)) list /\
    is_list list vlist .

  Lemma tree_builder_spec (list:list nat) (vlist: val) (height:nat):
    2^(S height) - 1  <= max_hash_size ->
    is_acceptable_list height list vlist ->
    {{{ 
          € (nnreal_nat (2^(S height)-1) * amortized_error val_size_for_hash max_hash_size max_hash_size_pos)%NNR
    }}}
      tree_builder vlist #height
      {{{ (l:nat) (checker:val), RET (#l, checker);
          ∃ (m:gmap nat nat) (tree:merkle_tree) (f:val),
            coll_free_hashfun_amortized val_size_for_hash max_hash_size f m ∗
            ⌜size (m) <= 2^(S height) - 1⌝ ∗
            ⌜tree_valid_with_leaf_list val_bit_size' height tree list m⌝ ∗
            decider_program_helper_spec height val_bit_size' max_hash_size max_hash_size_pos checker tree f
      }}}.
  Proof.
    iIntros (Hmsize (Hlistsize&Hforall&Hislist) Φ) "Herr HΦ".
    rewrite /tree_builder.
    wp_pures.
    wp_apply (wp_init_hash_amortized _ max_hash_size); [done|done|].
    iIntros (f) "H". iMod "H".
    wp_pures.
    wp_apply (tree_builder_helper_spec with "[$H $Herr]"); [done|done|..].
    iIntros (hash l) "(%m'&%tree&%&%&H&%&%Hhash)".
    wp_pures. rewrite <-Hhash.
    wp_apply (merkle_tree_decider_program_spec with "[$H]").
    - iPureIntro. by eapply tree_valid_with_leaf_list_implies_tree_valid.
    - iIntros (checker) "[H #Hchecker]".
      wp_pures.
      iApply "HΦ".
      iModIntro.
      iExists _,_,_. iFrame. by do 2 (iSplit; first done).
  Qed.
  
  (** looking up the tree *)
  Definition tree_lookup_helper : val :=
    rec: "tree_lookup_helper" "tree" "height" "idx" :=
      if: "height" = #0
      then (InjLV #(), unreliable_read_program ("tree"+#1))
      else
        let: "height'" := "height" - #1 in
        let: "split" := pow "height'" in
        if: "idx" < "split"
        then let: "rhash" := unreliable_read_program (unreliable_read_program ("tree"+#2)) in
             let, ("proof", "leaf"):=
               "tree_lookup_helper" (unreliable_read_program ("tree"+#1)) "height'" "idx" in
             (list_cons (#true, "rhash") "proof","leaf")
        else let: "lhash" := unreliable_read_program (unreliable_read_program ("tree"+#1)) in
             let, ("proof", "leaf"):=
               "tree_lookup_helper" (unreliable_read_program ("tree"+#2)) "height'" ("idx"-"split") in
             (list_cons (#false, "lhash") "proof","leaf").

  Definition proof_bound_checker : val :=
    λ: "x",
      let, ("a", "b") := "x" in
      "b" < #(2^val_bit_size).

  Definition tree_lookup : val :=
    λ: "tree" "height" "idx" "checker",
      let, ("proof", "leaf") := tree_lookup_helper "tree" "height" "idx" in
      if: list_forall proof_bound_checker "proof" && (#0 < "leaf") && ("leaf" < #(2^(val_bit_size*2)))
      then if: "checker" "proof" "leaf" then (SOME "leaf") else NONEV
      else NONEV.

  Lemma tree_lookup_helper_spec (ltree:nat) (height:nat) (idx:nat):
    idx < 2^height -> 
    {{{ True }}}
      tree_lookup_helper #ltree #height #idx
      {{{ (a:val) (b:nat), RET (a, #b)%V;
          ∃ lis:(list (bool*nat)),
            ⌜is_list lis a⌝ ∗
            ⌜proof_idx_relate height lis idx⌝
      }}}.
  Proof.
    clear max_hash_size_pos max_hash_size.
    iIntros (Hidx Φ) "_ HΦ".
    iInduction height as [|height] "IH" forall (ltree idx Hidx Φ) "HΦ".
    - simpl in Hidx. assert (idx = 0) as -> by lia.
      rewrite /tree_lookup_helper.
      wp_pures. replace (_+_)%Z with (Z.of_nat (ltree + 1)) by lia.
      wp_apply unreliable_read_spec; first done.
      iIntros (?) "_".
      wp_pures.
      iModIntro.
      iApply "HΦ".
      iExists [].
      iSplit; first done.
      iPureIntro; constructor.
    - rewrite /tree_lookup_helper.
      wp_pures.
      rewrite -/tree_lookup_helper.
      replace (Z.of_nat (S height) - 1)%Z with (Z.of_nat height) by lia.
      wp_apply pow_spec; first done.
      iIntros (?) "->".
      wp_pures.
      case_bool_decide.
      + (*left case*)
        wp_pures. replace (Z.of_nat _+_)%Z with (Z.of_nat (ltree+2)) by lia.
        wp_apply unreliable_read_spec; first done.
        iIntros (?) "_".
        wp_apply unreliable_read_spec; first done.
        iIntros (rhash) "_". wp_pures. replace (Z.of_nat _+_)%Z with (Z.of_nat (ltree+1)) by lia.
        wp_apply unreliable_read_spec; first done.
        iIntros (?) "_".
        wp_apply "IH"; first (iPureIntro; lia).
        iIntros (lproof ?) "(%proof & %&%)".
        wp_pures.
        replace (_,_)%V with (inject (true, rhash) : val); last done.
        wp_apply wp_list_cons; first done.
        iIntros (lproof') "%".
        wp_pures.
        iModIntro. iApply "HΦ".
        iExists ((true, rhash)::proof).
        iSplit; first done.
        iPureIntro. constructor; [done|lia].
      + (*right case*)
        wp_pures. replace (Z.of_nat _+_)%Z with (Z.of_nat (ltree+1)) by lia.
        wp_apply unreliable_read_spec; first done.
        iIntros (?) "_".
        wp_apply unreliable_read_spec; first done.
        iIntros (lhash) "_". wp_pures. replace (Z.of_nat _+_)%Z with (Z.of_nat (ltree+2)) by lia.
        wp_apply unreliable_read_spec; first done.
        iIntros (?) "_".
        rewrite -Nat2Z.inj_sub; last lia.
        wp_apply "IH".
        { iPureIntro.  simpl in Hidx. lia. }
        iIntros (lproof ?) "(%proof & %&%)".
        wp_pures.
        replace (_,_)%V with (inject (false, lhash) : val); last done.
        wp_apply wp_list_cons; first done.
        iIntros (lproof') "%".
        wp_pures.
        iModIntro. iApply "HΦ".
        iExists ((false, lhash)::proof).
        iSplit; first done.
        iPureIntro. constructor; [done|lia].
  Qed.

  Lemma list_forall_proof_bound_checker_spec (lproof:val) (proof : list (bool*nat)):
    {{{ ⌜is_list proof lproof⌝ }}}
      list_forall proof_bound_checker lproof
    {{{ (b:bool), RET #b; if b then ⌜Forall (λ x, snd x < 2^val_bit_size) proof⌝ else True }}}
  .
  Proof.
    iIntros (Φ) "% HΦ".
    wp_apply wp_list_forall; [|done|]; last first.
    - iIntros (b) "H".
      iApply "HΦ".
      destruct b; last done.
      instantiate (1 := (λ '(a, b), ⌜b < 2^val_bit_size⌝)%I).
      clear.
      iInduction proof as [|] "IH"; first done.
      rewrite Forall_cons_iff.
      destruct a. rewrite big_sepL_cons.
      iDestruct "H" as "[%H1 H2]".
      iSplit; [done|].
      by iApply "IH".
    - iIntros ([??] Φ') "!>_ HΦ".
      rewrite /proof_bound_checker.
      wp_pures. case_bool_decide; iModIntro.
      + iApply "HΦ".
        iPureIntro. rewrite Nat2Z.inj_lt.
        rewrite Nat2Z.inj_pow. done.
      + iApply "HΦ".
        by instantiate (1:= (λ _, True)%I).
  Qed.



  Lemma tree_lookup_spec (ltree:nat) (height:nat) (idx:nat) (checker:val) (lis:list nat) f tree m:
    idx < 2^height ->
    {{{ decider_program_helper_spec height val_bit_size' max_hash_size max_hash_size_pos checker tree f ∗
        ⌜tree_valid_with_leaf_list val_bit_size' height tree lis m⌝ ∗
        coll_free_hashfun_amortized val_size_for_hash max_hash_size f m ∗
        ⌜size (m) + S height <= max_hash_size⌝ ∗
        € ((nnreal_nat (S height)) * amortized_error val_size_for_hash max_hash_size max_hash_size_pos)%NNR              
    }}}
      tree_lookup #ltree #height #idx checker
      {{{ (v:val), RET v;
          ⌜∀ x:nat, v=SOMEV #x -> lis!!idx = Some x⌝
      }}}.
  Proof.
    iIntros (Hidx Φ) "(#Hdecider & %Htvalid & H & %Hmsize & Herr) HΦ".
    rewrite /tree_lookup.
    wp_pures.
    wp_apply tree_lookup_helper_spec; [done|done|].
    iIntros (lproof leafv) "(%proof & %Hproof & %Hproofrelate)".
    wp_pures.
    wp_apply list_forall_proof_bound_checker_spec; first done.
    iIntros ([]) "%Hb"; last first.
    { wp_pures. iModIntro. iApply "HΦ". iPureIntro. naive_solver. }
    wp_pures. case_bool_decide; last first.
    { wp_pures. iModIntro. iApply "HΦ". iPureIntro. naive_solver. }
    wp_pures. case_bool_decide; last first.
    { wp_pures. iModIntro. iApply "HΦ". iPureIntro. naive_solver. }
    wp_pures.
    wp_apply ("Hdecider" with "[$H $Herr]").
    - iSplit.
      + iPureIntro. by eapply tree_valid_with_leaf_list_implies_tree_valid.
      + iSplit; try done. iSplit; iPureIntro; first done. eapply proof_idx_relate_implies_possible_proof; try done. by eapply tree_valid_with_leaf_list_implies_tree_valid.
    - iIntros ([]) "Hb"; last first.
      { wp_pures. iApply "HΦ". iPureIntro. naive_solver. }
      iDestruct "Hb" as "(%Hcorrect & H & Herr)".
      wp_pures.
      iApply "HΦ". iPureIntro.
      intros x Hx.
      inversion Hx as [Hx1]; apply Nat2Z.inj in Hx1; subst.
      eapply tree_valid_with_leaf_list_implies_lookup_some; try done.
      by destruct Hcorrect.
  Qed.

  
End unreliable_storage.
                 
