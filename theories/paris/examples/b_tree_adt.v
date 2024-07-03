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
From clutch Require Export paris.
Set Default Proof Using "Type*".
Opaque INR.

(* TODO: upstream? *)
Section big_sepL.
  Context `{!parisRGS Σ}.

  Lemma big_sepL_combine_swap {A B : Type} (l1 : list A) (l2: list B) (Φ : A → B → iProp Σ) :
    ([∗ list] x ∈ combine l1 l2, Φ x.1 x.2) ⊢ ([∗ list] y ∈ combine l2 l1, Φ y.2 y.1).
  Proof.
    iInduction l1 as [| a l1] "IH" forall (l2).
    - rewrite //=. destruct l2; eauto.
    - destruct l2 as [| b l2].
      * rewrite //=.
      * rewrite /=. iIntros "($&H)". iApply "IH". auto.
  Qed.

  Lemma big_sepL_combine_left {A B : Type} (l1 : list A) (l2: list B) (Φ : A → B → iProp Σ) :
    length l1 = length l2 →
    ([∗ list] x ∈ combine l1 l2, Φ x.1 x.2) ⊣⊢ ([∗ list] i ↦ a ∈ l1, ∃ b, ⌜ l2 !! i = Some b ⌝ ∗ Φ a b).
  Proof.
    iInduction l1 as [| a l1] "IH" forall (l2).
    - rewrite //=.
    - iIntros (Hlen). destruct l2 as [| b l2].
      * simpl in Hlen; lia.
      * rewrite /=. inversion Hlen; subst. iSpecialize ("IH" $! l2 with "[//]").
        iDestruct "IH" as "(IH1&IH2)".
        iSplit; iIntros "(Hhd&Htl)".
        { iDestruct ("IH1" with "[$]") as "$"; by iFrame. }
        { iDestruct ("IH2" with "[$]") as "$".
          iDestruct "Hhd" as (?) "(%Heq&?)". inversion Heq; iFrame. }
  Qed.

  Lemma big_sepL_combine_right {A B : Type} (l1 : list A) (l2: list B) (Φ : A → B → iProp Σ) :
    length l1 = length l2 →
    ([∗ list] x ∈ combine l1 l2, Φ x.1 x.2) ⊣⊢ ([∗ list] i ↦ b ∈ l2, ∃ a, ⌜ l1 !! i = Some a ⌝ ∗ Φ a b).
  Proof.
    iIntros (Hlen). rewrite -big_sepL_combine_left; auto.
    iSplit.
    - iApply big_sepL_combine_swap.
    - iIntros "H". iDestruct (big_sepL_combine_swap _ _ (λ b a, Φ a b) with "H") as "H".
      auto.
  Qed.

  Lemma big_sepL_combine_chain_left {A B C: Type} l1 l2 l3 (Φ : A → C → iProp Σ) (Ψ : B → C → iProp Σ) :
    length l1 = length l3 →
    length l2 = length l3 →
    ([∗ list] x ∈ combine l1 l3, Φ x.1 x.2) ∗
    ([∗ list] x ∈ combine l2 l3, Ψ x.1 x.2)
    ⊢ ([∗ list] i ↦ a ∈ l1, ∃ b c, ⌜ l2 !! i = Some b ∧ l3 !! i = Some c ⌝ ∗ Φ a c ∗ Ψ b c).
  Proof.
    iInduction l1 as [| a l1] "IH" forall (l2 l3).
    - rewrite /=; auto.
    -  iIntros (Hlen13 Hlen23) "(Hl1l3&Hl2l3)".
       destruct l3 as [| c l3]; first by (inversion Hlen13).
       destruct l2 as [| b l2]; first by (inversion Hlen23).
       rewrite /=.
       iDestruct "Hl1l3" as "(Hac&Hl1l3)".
       iDestruct "Hl2l3" as "(Hbc&Hl2l3)".
       iSplitL "Hac Hbc"; first by iFrame.
       iApply "IH"; iFrame; eauto.
  Qed.

  Lemma big_sepL_combine_unchain_left {A B C: Type} l1 l2 l3 (Φ : A → C → iProp Σ) (Ψ : B → C → iProp Σ) :
    length l1 = length l3 →
    length l2 = length l3 →
    ([∗ list] i ↦ a ∈ l1, ∃ b c, ⌜ l2 !! i = Some b ∧ l3 !! i = Some c ⌝ ∗ Φ a c ∗ Ψ b c)
    ⊢ ([∗ list] x ∈ combine l1 l3, Φ x.1 x.2) ∗ ([∗ list] x ∈ combine l2 l3, Ψ x.1 x.2).
  Proof.
    iInduction l1 as [| a l1] "IH" forall (l2 l3);
    iIntros (Hlen13 Hlen23) "H";
    destruct l3 as [| c l3]; try (by inversion Hlen13);
    destruct l2 as [| b l2]; try (by inversion Hlen23).
    - rewrite /=; auto.
    - rewrite /=.
      iDestruct "H" as "(Hhd&Htl)".
      iDestruct ("IH" with "[] [] Htl") as "(Htl1&Htl2)"; [ auto | auto |].
      iDestruct "Hhd" as (? ?) "(%Heq&HΦ&HΨ)".
      destruct Heq as (Heq1&Heq2). inversion Heq1; subst. inversion Heq2; subst.
      iFrame.
  Qed.

End big_sepL.


Section b_tree_adt.

  Context {max_child_num' : nat}.
  Context (max_child_num_lt : 2 ≤ S max_child_num').

  Definition init_tree : val :=
    λ: "v", ref (InjL "v").

  Definition init_ranked_tree : val :=
    λ: "v", ref ((#1, InjL "v")).

  (* Given a non-ranked tree, creates a copy that is ranked and
     returns it.  Of course, this would be quite an expensive
     operation. But we are only using this for purposes of the
     specification (showing that the optimized sampling algorithm
     behaves like the "naive" algorithm, so we do not particularly
     care. *)

  Definition do_list_sum : val :=
    λ: "l", list_fold_right (λ: "x" "y", "x" + "y") "l" #0.

  Definition build_ranked : val :=
    rec: "build_ranked" "t" :=
        match: "t" with
        | InjL "v" => (#1, InjL "v")
        | InjR "l" =>
            let: "rl" := list_map (λ: "p",
                                      let: "c" := "build_ranked" !"p" in
                                      (Fst "c", ref "c")) "l" in
            let: "lens" := list_map (λ: "v", Fst "v") "rl" in
            (do_list_sum "lens", InjR "rl")
        end.

  (* Tries to insert a new child v into the list of children l pointed to by p.
     If the child list l is not already full, this returns None.
     However, if the list l is full full, we return a new node that will need to become a sibling of p.

     An optimal B+-tree would try to split l evenly, with half (+- new node) going to the new sibling and
     half staying in p, but that is really irrelevant for our purposes,
     so for simplicity we just put solely the new child v in the second list.
   *)

  Definition insert_child_list' : val :=
    λ: "p" "l" "v",
      if: list_length "l" < #(S max_child_num') then
        "p" <- InjR (list_cons (ref "v") "l") ;;
        NONE
      else
        SOME (InjR (list_cons (ref "v") list_nil)).

  Definition get : val :=
    (λ: "ov",
      match: "ov" with
      | SOME "v" => "v"
      | NONE => #()
      end).

  Definition find_depth : val :=
    rec: "find_depth" "p" :=
      let: "t" := !"p" in
        match: "t" with
        | InjL "_" => #0
        | InjR "l" =>
            let: "c" := get (list_head "l") in
            #1 + "find_depth" "c"
        end.

  Definition insert_tree_aux : val :=
    rec: "insert_tree" "p" "v" :=
        let: "t" := !"p" in
        match: "t" with
        | InjL "_" => SOME (InjL "v")
        | InjR "l" =>
            (* Insert into a random child, this shows our sampler code is "robust"
               to a variety of tree shapes *)
            let: "n" := rand (list_length "l" - #1) in
            let: "c" := get (list_nth "l" "n") in
            match: "insert_tree" "c" "v" with
            | NONE => NONE
            | SOME "new" =>
                (* Either the child was a leaf, or we had to split the child, so
                   we must insert "new" into the current node *)
                insert_child_list' "p" "l" "new"
            end
        end.

  Definition insert_tree_curry : val :=
    λ: "p" "v",
      match: insert_tree_aux "p" "v" with
      | NONE => #()
      | SOME "t'" =>
          (* The root node had to be split, so we need to create a new root node which will have as children
             t' and the sibling stored in !p *)
          let: "new_root" := InjR (list_cons (ref !"p") (list_cons (ref "t'") list_nil)) in
          "p" <- "new_root"
      end.

  Definition insert_tree : val :=
    λ: "pv", insert_tree_curry (Fst "pv") (Snd "pv").

  Context `{!parisRGS Σ}.

  Definition btree_ptrv p treev depth tree l : iProp Σ :=
    ⌜ @is_ab_b_tree max_child_num' depth l tree ⌝ ∗
        p ↦ treev ∗
        relate_ab_tree_with_v tree treev.

  Definition btree_ptrv' p treev depth tree l : iProp Σ :=
    ⌜ @is_ab_b_tree max_child_num' depth l tree ⌝ ∗
        p ↦ₛ treev ∗
        relate_ab_tree_with_v' tree treev.

  Definition btree_ptr p depth tree l : iProp Σ :=
    ∃ treev, btree_ptrv p treev depth tree l.

  Definition btree_ptr' p depth tree l : iProp Σ :=
    ∃ treev, btree_ptrv' p treev depth tree l.

  Lemma wp_do_list_sum (l : list nat) (v: val) :
    {{{ ⌜ is_list l v ⌝ }}}
      do_list_sum v
    {{{ RET #(list_sum l); True }}}.
  Proof.
    clear.
    iIntros (Φ) "%Hlist HΦ".
    rewrite /do_list_sum.
    wp_pures.
    iInduction l as [| n l] "IH" forall (v Hlist Φ).
    - wp_rec. inversion Hlist; subst. wp_pures.
      iApply "HΦ"; auto.
    - wp_rec. inversion Hlist as [tl [-> ?]]; subst. wp_pures.
      wp_apply ("IH" with "[//]").
      iIntros "_". wp_pures. iModIntro. simpl.
      replace (Z.of_nat n + Z.of_nat (list_sum l))%Z with
              (Z.of_nat (n + list_sum l)) by lia.
      by iApply "HΦ".
  Qed.

  Lemma map_fst_combine {A B: Type} (l1 : list A) (l2: list B) :
    length l1 = length l2 →
    map fst (combine l1 l2) = l1.
  Proof.
    revert l2; induction l1 as [| a l1 IH] => //=.
    intros [| b l2] => //=. intros. rewrite IH; eauto.
  Qed.

  Lemma wp_build_ranked tree (treev : val) depth l :
    {{{ ⌜ @is_ab_b_tree max_child_num' depth l tree ⌝ ∗
        relate_ab_tree_with_v tree treev
    }}}
      build_ranked treev
   {{{ treev', RET treev';
       relate_ab_tree_with_v tree treev ∗
       relate_ab_tree_with_ranked_v tree treev' }}}.
  Proof.
    iInduction depth as [| depth] "IH" forall (tree treev l).
    - iIntros (Φ) "(%Htree&Hrelate) HΦ".
      wp_rec.
      inversion Htree; subst.
      iEval (rewrite relate_ab_tree_with_v_Lf) in "Hrelate". iDestruct "Hrelate" as %->.
      wp_pures. iModIntro.
      iApply "HΦ".
      rewrite relate_ab_tree_with_v_Lf.
      rewrite relate_ab_tree_with_ranked_v_Lf; eauto.
    - iIntros (Φ) "(%Htree&Hrelate) HΦ".
      wp_rec.
      inversion Htree as [| ? l0 Hforall Hnumchild]; subst.
      iEval (rewrite relate_ab_tree_with_v_Br) in "Hrelate".
      iDestruct "Hrelate" as (??? Heq1 Heq2 Heq3 Hloc_lis) "(H1&H2)".
      subst. wp_pures.
      wp_bind (list_map _ _).
      (* Sadly, we can't just use wp_list_map because this doesn't fall into a pattern
         where there's a Gallina level map function. *)
      (* wp_apply (wp_list_mapi with "[$H1]"). *)
      iAssert (WP list_map (λ: "p",
                                      let: "c" := build_ranked !"p" in
                                      (Fst "c", ref "c"))%V v'
                  {{ v', ∃ loc_lis' v_lis' num_lis',
                        ⌜length l0.*2 = length loc_lis'⌝ ∗
                        ⌜length l0.*2 = length v_lis'⌝ ∗
                        ⌜length l0.*2 = length num_lis'⌝ ∗
                        ⌜is_list (combine num_lis' loc_lis') v'⌝ ∗
                        ([∗ list] x ∈ combine loc_lis v_lis, x.1 ↦ x.2) ∗
                        ([∗ list] x ∈ combine l0.*2 v_lis, relate_ab_tree_with_v x.1 x.2) ∗
                        ([∗ list] x ∈ combine loc_lis' v_lis', x.1 ↦ x.2) ∗
                        ([∗ list] x ∈ combine l0.*2 num_lis', ⌜children_num x.1 = x.2⌝) ∗
                        ([∗ list] x ∈ combine l0.*2 v_lis', relate_ab_tree_with_ranked_v x.1 x.2) }})%I
        with "[H1 H2]" as "Hwp".
      { clear Htree Hnumchild.
        iInduction loc_lis as [| p loc_lis'] "IHmap" forall (l0 v_lis Heq2 Heq3 Hforall v' Hloc_lis).
        - wp_rec. inversion Hloc_lis. subst. wp_pures.
          iModIntro. iExists [], [], []. rewrite /=. iFrame.
          destruct l0; simpl in Heq2; try lia. rewrite //=.
        - wp_rec. inversion Hloc_lis as [vtl [Heq Hlist']]. subst.
          wp_pures.
          destruct l0 as [| (ov&t) l0]; simpl in Heq2; first by lia.
          destruct v_lis as [| v' v_lis]; simpl in Heq3; first by lia.
          iEval (rewrite /=) in "H1". iDestruct "H1" as "(Hp&Htl1)".
          iEval (rewrite /=) in "H2". iDestruct "H2" as "(Hrel&Htl2)".
          wp_bind (list_map _ _).
          iApply (wp_wand with "[Htl1 Htl2]").
          { iDestruct ("IHmap" with "[] [] [] [] Htl1 Htl2") as "$"; eauto.
            { inversion Hforall; eauto. }
          }
          iIntros (?) "Htl".
          iDestruct "Htl" as (???) "(%His_list_tl&%&%&%&H1&H2&H1'&H2'&H3')".
          inversion Hforall.
          subst.
          wp_pures. wp_load. wp_apply ("IH" with "[$Hrel //]").
          iIntros (treev') "(Hrel&Hrel')".
          wp_alloc p' as "Hp'".
          wp_apply (wp_fst_ranked_tree' with "[$]"); first eauto.
          iIntros "Hn".
          iDestruct "Hn" as "(%Hn&Hrel')".
          destruct Hn as (treeb'&->).
          wp_pures.
          replace ((#(children_num t), #p')%V) with (inject (children_num t : nat, p' : loc) : val) by auto.
          wp_apply (wp_list_cons); eauto.
          iIntros (v0' Hlist).
          iExists (p' :: _), ((#(children_num t), treeb')%V :: v_lis'), ((children_num t) :: num_lis').
          simpl. iFrame. iPureIntro; split_and!; eauto.
      }
      iApply (wp_wand with "Hwp").
      iIntros (?) "H".
      iDestruct "H" as (???????) "(H1&H2&H1'&H2'&H3')".
      wp_pures.
      wp_bind (list_map _ _).
      wp_apply (wp_list_map (combine num_lis' loc_lis') fst).
      { iSplit; last by done.
        iIntros ((n&l) Φ') "_ !> HΦ".
        wp_pures. iApply "HΦ". eauto.
      }
      iIntros (rv) "%Hislist".
      wp_pures.
      wp_apply (wp_do_list_sum); first eauto.
      iIntros "_". wp_pures.
      iModIntro. iApply "HΦ".
      iSplitL "H1 H2".
      { rewrite relate_ab_tree_with_v_Br. iFrame. eauto. }
      { rewrite relate_ab_tree_with_ranked_v_Br. iFrame.
        iExists _, _. rewrite map_fst_combine //. lia. }
  Qed.

  Lemma wp_init_tree (v : val) :
    {{{ True }}}
      init_tree v
    {{{ (p : loc), RET (#p); btree_ptr p O (Lf v) [Some v] }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_tree. wp_pures. wp_alloc p as "Hp".
    iModIntro. iApply "HΦ". iFrame.
    iSplit.
    { iPureIntro. econstructor. }
    { rewrite relate_ab_tree_with_v_Lf //=. }
  Qed.

  Lemma spec_init_tree (v: val) K E:
    ⤇ fill K (init_tree v) -∗ spec_update E (∃ (p:loc), ⤇ fill K #p ∗ btree_ptr' p O (Lf v) [Some v]).
  Proof.
    iIntros "H".
    rewrite /init_tree. tp_pures.
    tp_alloc as p "Hp".
    iModIntro. iExists _. iFrame.
    iSplit.
    { iPureIntro. econstructor. }
    { rewrite relate_ab_tree_with_v_Lf' //=. }
  Qed.

  Lemma wp_find_depth p tv depth t vs :
    {{{ btree_ptrv p tv depth t vs }}}
      find_depth #p
    {{{ RET #depth; btree_ptrv p tv depth t vs }}}.
  Proof.
    iInduction depth as [| depth] "IH" forall (p tv t vs).
    - iIntros (Φ) "Hbtree HΦ".
      wp_rec.
      iDestruct "Hbtree" as "(%Hwft0&Hp&Hrelate)".
      wp_load.
      inversion Hwft0. subst.
      rewrite relate_ab_tree_with_v_Lf. iDestruct "Hrelate" as %Heq. subst.
      wp_pures. iModIntro. iApply "HΦ". iFrame.
      rewrite relate_ab_tree_with_v_Lf. eauto.
    - iIntros (Φ) "Hbtree HΦ".
      wp_rec.
      iDestruct "Hbtree" as "(%Hwft0&Hp&Hrelate)".
      wp_load.
      inversion Hwft0. subst.
      rewrite relate_ab_tree_with_v_Br.
      iDestruct "Hrelate" as (??? Heq1 Heq2 Heq3 ?) "(H1&H2)".
      subst. wp_pures.
      specialize (b_tree.min_child_num_pos) => ?.
      wp_apply wp_list_head; first eauto.
      iIntros (? [(->&->)|Hvals]).
      { rewrite fmap_length /= in Heq2; lia. }
      destruct Hvals as (pc&?&->&->).
      rewrite /get; wp_pures.
      destruct v_lis as [|tv v_lis]; first by (rewrite fmap_length /= in Heq3; lia).
      iDestruct (big_sepL_lookup_acc _ _ O with "H1") as "(H1&H1clos)".
      { eauto. }
      destruct l as [|(?&t) l_lis]; first by (rewrite fmap_length /= in Heq3; lia).
      iDestruct (big_sepL_lookup_acc _ _ O with "H2") as "(H2&H2clos)".
      { eauto. }
      wp_apply ("IH" with "[H1 H2]").
      { rewrite /btree_ptrv. iFrame. inversion H0; eauto. }
      iIntros "Hb". wp_pures.
      iModIntro.
      replace (1 + Z.of_nat depth)%Z with (Z.of_nat (S depth)) by lia.
      iApply "HΦ".
      iDestruct "Hb" as "(%&H1&H2)".
      iDestruct ("H1clos" with "H1") as "H1".
      iDestruct ("H2clos" with "H2") as "H2".
      iFrame. iSplit.
      { iPureIntro. econstructor; eauto. }
      rewrite relate_ab_tree_with_v_Br.
      iExists _, _, _. iFrame. eauto.
  Qed.

  Lemma spec_find_depth E K p tv depth t vs :
    btree_ptrv' p tv depth t vs -∗
    ⤇ fill K (find_depth #p) -∗
    spec_update E (⤇ fill K #depth ∗ btree_ptrv' p tv depth t vs).
  Proof.
    iInduction depth as [| depth] "IH" forall (K p tv t vs).
    - iIntros "Hbtree Hspec".
      tp_rec.
      iDestruct "Hbtree" as "(%Hwft0&Hp&Hrelate)".
      tp_load.
      inversion Hwft0. subst.
      rewrite relate_ab_tree_with_v_Lf'. iDestruct "Hrelate" as %Heq. subst.
      tp_pures. iModIntro. iFrame.
      rewrite relate_ab_tree_with_v_Lf'. eauto.
    - iIntros "Hbtree Hspec".
      tp_rec.
      iDestruct "Hbtree" as "(%Hwft0&Hp&Hrelate)".
      tp_load.
      inversion Hwft0. subst.
      rewrite relate_ab_tree_with_v_Br'.
      iDestruct "Hrelate" as (??? Heq1 Heq2 Heq3 ?) "(H1&H2)".
      subst. tp_pures.
      specialize (b_tree.min_child_num_pos) => ?.
      tp_bind (list_head _).
      iMod (spec_list_head with "[$]") as "Hhd"; first eauto.
      iDestruct "Hhd" as (?) "(Hspec&%Hcases)".
      destruct Hcases as [(->&->)|Hvals].
      { rewrite fmap_length /= in Heq2; lia. }
      destruct Hvals as (pc&?&->&->).
      rewrite /get; tp_pures.
      destruct v_lis as [|tv v_lis]; first by (rewrite fmap_length /= in Heq3; lia).
      iDestruct (big_sepL_lookup_acc _ _ O with "H1") as "(H1&H1clos)".
      { eauto. }
      destruct l as [|(?&t) l_lis]; first by (rewrite fmap_length /= in Heq3; lia).
      iDestruct (big_sepL_lookup_acc _ _ O with "H2") as "(H2&H2clos)".
      { eauto. }
      iEval (simpl) in "Hspec". tp_pures.
      tp_bind (find_depth _).
      iMod ("IH" with "[H1 H2] Hspec") as "IHres".
      { rewrite /btree_ptrv. iFrame. inversion H0; eauto. }
      iDestruct "IHres" as "(Hspec&Hb)".
      iEval (simpl) in "Hspec". tp_pures.
      iModIntro.
      replace (1 + Z.of_nat depth)%Z with (Z.of_nat (S depth)) by lia.
      iFrame.
      iDestruct "Hb" as "(%&H1&H2)".
      iDestruct ("H1clos" with "H1") as "H1".
      iDestruct ("H2clos" with "H2") as "H2".
      iFrame. iSplit.
      { iPureIntro. econstructor; eauto. }
      rewrite relate_ab_tree_with_v_Br'.
      iExists _, _, _. iFrame. eauto.
  Qed.

  Definition olift (P : val -> Prop) : option val → Prop :=
    λ ov,
    match ov with
    | Some v => P v
    | None => True
    end.

  Lemma rel_insert_child_list' K P p p' ltv ltv' depth l vs vs2 t tv tv' :
    {{{ btree_ptrv p (InjRV ltv) (S depth) (Br l) vs ∗
        btree_ptrv' p' (InjRV ltv') (S depth) (Br l) vs ∗
        ⌜ @is_ab_b_tree max_child_num' depth vs2 t ⌝ ∗
        ⌜ Forall (olift P) vs ⌝ ∗
        ⌜ Forall (olift P) vs2 ⌝ ∗
        relate_ab_tree_with_v t tv ∗
        relate_ab_tree_with_v' t tv' ∗
        ⤇ fill K (insert_child_list' #p' ltv' tv')
    }}}
      insert_child_list' #p ltv tv
    {{{ res, RET res;
        ∃ ltv ltv' vs l' (res' : val),
        ⤇ fill K res' ∗
          btree_ptrv p ltv (S depth) (Br l') vs ∗
          btree_ptrv' p' ltv' (S depth) (Br l') vs ∗
          ⌜ Forall (olift P) vs ⌝ ∗
          ((⌜ res = NONEV ⌝ ∗ ⌜ res' = NONEV ⌝) ∨
           (∃ tvnew tvnew' tnew vs2new,
               ⌜ res = SOMEV tvnew ⌝ ∗ ⌜ res' = SOMEV tvnew' ⌝ ∗
               ⌜ @is_ab_b_tree max_child_num' (S depth) vs2new tnew ⌝ ∗
               ⌜ Forall (olift P) vs2new ⌝ ∗
               relate_ab_tree_with_v tnew tvnew ∗
               relate_ab_tree_with_v' tnew tvnew'))
    }}}.
  Proof.
    iIntros (Φ) "(Hbtree&Hbtree'&%Htwf&%Hforall&%Hforall2&Htv&Htv'&Hspec) HΦ".
    rewrite /insert_child_list'.
    wp_pures.
    tp_pures.
    iDestruct "Hbtree" as "(%Hwft0&Hp&Hrelate)".
    iDestruct "Hbtree'" as "(%Hwft0'&Hp'&Hrelate')".
    iEval (rewrite relate_ab_tree_with_v_Br) in "Hrelate".
    iEval (rewrite relate_ab_tree_with_v_Br') in "Hrelate'".
    iDestruct "Hrelate" as (??? Heq1 Heq2 Heq3 ?) "(H1&H2)".
    inversion Heq1; subst.
    iDestruct "Hrelate'" as (??? Heq1' Heq2' Heq3' ?) "(H1'&H2')".
    inversion Heq1'; subst.
    wp_apply (wp_list_length); eauto.
    iIntros (? ->).
    tp_bind (list_length _)%E.
    iMod (spec_list_length with "[//] Hspec") as (?) "(Hspec&->)". simpl.
    wp_pures.
    case_bool_decide.
    - tp_pures. rewrite bool_decide_true; last by lia.
      wp_pures. tp_pures.
      wp_alloc ptrv as "Hptv".
      replace (#ptrv) with (inject ptrv) by auto.
      wp_apply (wp_list_cons); eauto.
      iIntros (? Hlist).
      tp_alloc as ptrv' "Hptv'".
      tp_bind (list_cons _ _)%E.
      replace (#ptrv') with (inject ptrv') by auto.
      iMod (spec_list_cons with "[] Hspec") as (?) "(Hspec&%Hlist')".
      { eauto. }
      simpl.
      tp_pures. tp_store. tp_pures.
      wp_store. wp_pures.
      iApply "HΦ".
      iModIntro.
      inversion Hwft0.
      set (l0' := ((vs2, t) :: l0)).
      set (vs' :=
              flat_map (λ x : list (option val), x) l0'.*1 ++
       replicate ((S max_child_num' - length l0') * S max_child_num' ^ depth) None).
      set (l' := (snd <$> l0')).
      iExists _, _, vs', l', _.
      iFrame "Hspec".
      rewrite /btree_ptrv/btree_ptrv'.
      iFrame "Hp Hp'".
      iSplitL "Hptv Htv H1 H2".
      { iSplit.
        * iPureIntro. rewrite /l'/vs'. econstructor.
          ** rewrite /l0'. econstructor; eauto.
          ** rewrite /l0'. simpl. split; first lia.
             rewrite /b_tree.max_child_num.
             cut (length l0 = length l); first by lia.
             subst. rewrite map_length //.
        * rewrite relate_ab_tree_with_v_Br. iExists _, (ptrv :: loc_lis), (tv :: v_lis).
          iSplit; first eauto.
          iSplit.
          { iPureIntro; rewrite /l'/l0'. rewrite fmap_cons ?cons_length. congruence. }
          iSplit.
          { iPureIntro; rewrite /l'/l0'. rewrite fmap_cons ?cons_length. congruence. }
          iSplit; first done.
          simpl. iFrame.
      }
      iSplitL "Hptv' Htv' H1' H2'".
      { iSplit.
        * iPureIntro. rewrite /l'/vs'. econstructor.
          ** rewrite /l0'. econstructor; eauto.
          ** rewrite /l0'. simpl. split; first lia.
             rewrite /b_tree.max_child_num.
             cut (length l0 = length l); first by lia.
             subst. rewrite map_length //.
        * rewrite relate_ab_tree_with_v_Br'. iExists _, (ptrv' :: loc_lis0), (tv' :: v_lis0).
          iSplit; first eauto.
          iSplit.
          { iPureIntro; rewrite /l'/l0'. rewrite fmap_cons ?cons_length. congruence. }
          iSplit.
          { iPureIntro; rewrite /l'/l0'. rewrite fmap_cons ?cons_length. congruence. }
          iSplit; first done.
          simpl. iFrame.
      }
      eauto.
      iSplit; last eauto.
      { rewrite /vs'. iPureIntro. apply Forall_app. split.
        * apply Forall_flat_map.
          rewrite /l0'.
          rewrite fmap_cons; econstructor; first done.
          subst. eapply Forall_app in Hforall as [Hforall0 ?].
          apply Forall_flat_map in Hforall0; auto.
        * apply Forall_replicate. rewrite //=.
      }
    - tp_pures. rewrite bool_decide_false; last by lia.
      wp_pures. tp_pures.
      wp_alloc ptrv as "Hptv".
      replace (#ptrv) with (inject ptrv) by auto.
      wp_apply (wp_list_cons _ nil); eauto.
      iIntros (? Hlist).
      tp_alloc as ptrv' "Hptv'".
      tp_bind (list_cons _ _)%E.
      replace (#ptrv') with (inject ptrv') by auto.
      iMod (spec_list_cons _ _ _ nil with "[] Hspec") as (?) "(Hspec&%Hlist')".
      { eauto. }
      simpl.
      tp_pures.
      wp_pures.
      iApply "HΦ".
      iModIntro.
      iExists _, _, _, _, _.
      iFrame "Hspec".
      rewrite /btree_ptrv/btree_ptrv'.
      iFrame "Hp Hp'".
      iSplitL "H1 H2".
      { iSplit.
        * iPureIntro. eapply Hwft0.
        * rewrite relate_ab_tree_with_v_Br. iExists _, _, _. iFrame. eauto.
      }
      iSplitL "H1' H2'".
      { iSplit.
        * iPureIntro. eapply Hwft0.
        * rewrite relate_ab_tree_with_v_Br'. iExists _, _, _. iFrame. eauto.
      }
      iSplit; first done.
      iRight.
      set (l0' := [(vs2, t)]).
      set (vs' :=
              flat_map (λ x : list (option val), x) l0'.*1 ++
       replicate ((S max_child_num' - length l0') * S max_child_num' ^ depth) None).
      set (l' := (snd <$> l0')).
      iExists _, _, (Br [t]), vs'.
      iSplit; first eauto.
      iSplit; first eauto.
      iSplit.
      {
        iPureIntro.
        econstructor.
        { rewrite /l0'. econstructor; eauto. }
        { rewrite /l0'; simpl. rewrite /b_tree.min_child_num/b_tree.max_child_num; lia. }
      }
      iSplit.
      { rewrite /vs'. iPureIntro. apply Forall_app. split.
        * apply Forall_flat_map.
          rewrite /l0'.
          rewrite fmap_cons; econstructor; first done.
          subst. econstructor.
        * apply Forall_replicate. rewrite //=.
      }
      iSplitL "Htv Hptv".
      {
        rewrite relate_ab_tree_with_v_Br. iExists _, [ptrv], [tv].
        repeat (iSplit; first eauto).
        iFrame.
        rewrite //=.
      }
      {
        rewrite relate_ab_tree_with_v_Br'. iExists _, [ptrv'], [tv'].
        repeat (iSplit; first eauto).
        iFrame.
        rewrite //=.
      }
  Qed.

   (* Specifying the unary behavior would be handy, since then we
   could cut out on having to effectively do the proof as many
   redundant times, but it's annoying to do so because we would have
   to specify its behavior quite specifically. *)

  (*
  Lemma wp_insert_child_list' p lsv v depth vs1 vs2 ls t:
    {{{ btree_ptrv p (InjRV lsv) (S depth) (Br ls) vs2 ∗
        ⌜ @is_ab_b_tree max_child_num' depth vs1 t ⌝ ∗
        relate_ab_tree_with_v t v
    }}}
      insert_child_list' #p lsv v
    {{{ res, RET res;
        if decide (length ls < S max_child_num')%nat then
          ⌜ res = NONEV ⌝ ∗ btree_ptrv p (InjRV (v, lsv)) depth (Br (t :: ls)) (vs1 ++ vs2)
        else
          True }}}.
  Proof.
  Abort.
  *)

  Lemma combine_insert {A B} (n: nat) (a : A) (b : B) la lb:
    <[n := (a, b) ]> (combine la lb) = combine (<[n := a]> la) (<[n := b]> lb).
  Proof.
    revert lb n.
    induction la as [| a' la IHla] => //=.
    - intros lb. induction lb as [| b' lb IHlb].
      * intros [|n] => //=.
      * intros [|n] => //=. rewrite IHla //.
  Qed.

  Lemma rel_insert_tree_aux K P p p' tv tv' depth t vs (v: val) :
    {{{ btree_ptrv p tv depth t vs ∗
        btree_ptrv' p' tv' depth t vs ∗
        ⌜ Forall (olift P) vs ⌝ ∗
        ⌜ P v ⌝ ∗
        ⤇ fill K (insert_tree_aux #p' v)
    }}}
      insert_tree_aux #p v
    {{{ res, RET res;
        ∃ tv tv' vs t' (res' : val),
        ⤇ fill K res' ∗
          btree_ptrv p tv depth t' vs ∗
          btree_ptrv' p' tv' depth t' vs ∗
        ⌜ Forall (olift P) vs ⌝ ∗
          ((⌜ res = NONEV ⌝ ∗ ⌜ res' = NONEV ⌝) ∨
           (∃ tvnew tvnew' tnew vs2new,
               ⌜ res = SOMEV tvnew ⌝ ∗ ⌜ res' = SOMEV tvnew' ⌝ ∗
               ⌜ @is_ab_b_tree max_child_num' depth vs2new tnew ⌝ ∗
               ⌜ Forall (olift P) vs2new ⌝ ∗
               relate_ab_tree_with_v tnew tvnew ∗
               relate_ab_tree_with_v' tnew tvnew'))
    }}}.
  Proof.
    iIntros (Φ) "(Hbtree&Hbtree'&Hforall&%HPv&Hspec) HΦ".
    iInduction depth as [| depth'] "IH" forall (K p p' tv tv' t vs Φ); iDestruct "Hforall" as %Hforall.
    - rewrite /insert_tree_aux. wp_pures.
      tp_pures.
      rewrite -/insert_tree_aux.
      iDestruct "Hbtree" as "(%Hwft0&Hp&Hrelate)".
      iDestruct "Hbtree'" as "(%Hwft0'&Hp'&Hrelate')".
      wp_load; tp_load.
      wp_pures; tp_pures.
      inversion Hwft0.
      subst.
      rewrite relate_ab_tree_with_v_Lf.
      rewrite relate_ab_tree_with_v_Lf'.
      iDestruct "Hrelate" as %?; subst.
      iDestruct "Hrelate'" as %?; subst.
      tp_pures. wp_pures.
      iModIntro. iApply "HΦ".
      iExists _, _, [Some v0], (Lf v0), _. iFrame.
      iSplitL.
      { iSplitL; eauto.
        rewrite relate_ab_tree_with_v_Lf; eauto.
      }
      iSplitL.
      { iSplitL; eauto.
        rewrite relate_ab_tree_with_v_Lf'; eauto.
      }
      iSplit; first done.
      iRight.
      iExists _, _, (Lf v), ([Some v]).
      iSplit; first done.
      iSplit; first done.
      iSplit; first by (iPureIntro; econstructor).
      rewrite relate_ab_tree_with_v_Lf.
      rewrite relate_ab_tree_with_v_Lf'.
      eauto.
    - rewrite /insert_tree_aux. wp_pures.
      tp_pures.
      rewrite -/insert_tree_aux.
      iDestruct "Hbtree" as "(%Hwft0&Hp&Hrelate)".
      iDestruct "Hbtree'" as "(%Hwft0'&Hp'&Hrelate')".
      wp_load; tp_load.
      wp_pures; tp_pures.
      inversion Hwft0.
      subst.
      rewrite relate_ab_tree_with_v_Br.
      rewrite relate_ab_tree_with_v_Br'.
      iDestruct "Hrelate" as (??? Heq1 Heq2 Heq3 ?) "(H1&H2)".
      inversion Heq1; subst.
      iDestruct "Hrelate'" as (??? Heq1' Heq2' Heq3' ?) "(H1'&H2')".
      inversion Heq1'; subst.
      tp_pures. wp_pures.
      wp_bind (list_length _).
      wp_apply (wp_list_length); first eauto.
      iIntros (? ->).
      tp_bind (list_length _).
      iMod (spec_list_length with "[] [$]") as (?) "(H&->)"; first eauto.
      iEval (simpl) in "H".
      iEval (rewrite -Heq2' Heq2) in "H".
      wp_pures.
      tp_pures.
      tp_bind (rand _)%E.
      assert (1<= length loc_lis)%nat.
      { rewrite -Heq2 map_length. rewrite /b_tree.min_child_num in H1. lia. }
      assert ((Z.of_nat (length loc_lis) - 1)%Z = (length loc_lis - 1)%nat) as ->.
      { lia. }
      wp_apply (wp_couple_rand_rand with "H").
      iIntros (n) "Hspec".
      simpl.
      wp_pures.
      tp_pures.
      wp_apply (wp_list_nth); first eauto.
      iIntros (? Hlist_nth).
      assert (n < length loc_lis)%nat.
      { specialize (fin_to_nat_lt n). lia. }
      destruct Hlist_nth as [(?&Hbad)|Hlist_nth].
      { exfalso. specialize (fin_to_nat_lt n). lia. }
      tp_bind (list_nth _ _)%E.
      iMod (spec_list_nth with "Hspec") as (?) "(Hspec&%Hlist_nth')"; first eauto.
      destruct Hlist_nth' as [(?&Hbad)|Hlist_nth'].
      { exfalso. specialize (fin_to_nat_lt n). lia. }
      destruct Hlist_nth as (ptr&->&Hnth_ptr).
      destruct Hlist_nth' as (ptr'&->&Hnth_ptr').
      simpl.
      rewrite /get. wp_pures. tp_pures.
      wp_bind (insert_tree_aux _ _).
      tp_bind (insert_tree_aux _ _).
      assert (is_Some (list_lookup n v_lis)) as (vl&Hvl).
      { apply lookup_lt_is_Some_2. lia. }
      apply nth_error_lookup in Hnth_ptr.
      assert (combine loc_lis v_lis !! (n : nat) = Some (ptr, vl)).
      { apply combine_lookup. split; eauto. }
      iDestruct (big_sepL_insert_acc with "H1") as "(Hp1&H1)"; first eauto.
      assert (is_Some (list_lookup n l.*2)) as (tvl&Htvl).
      { apply lookup_lt_is_Some_2. lia. }
      assert (combine (l.*2) v_lis !! (n : nat) = Some (tvl, vl)).
      { apply combine_lookup. split; eauto. }
      iDestruct (big_sepL_insert_acc with "H2") as "(Ht&H2)"; first eauto.

      assert (is_Some (list_lookup n v_lis0)) as (vl'&Hvl').
      { apply lookup_lt_is_Some_2. lia. }
      apply nth_error_lookup in Hnth_ptr'.
      assert (combine loc_lis0 v_lis0 !! (n : nat) = Some (ptr', vl')).
      { apply combine_lookup. split; eauto. }
      iDestruct (big_sepL_insert_acc with "H1'") as "(Hp1'&H1')"; first eauto.
      assert (is_Some (list_lookup n l.*2)) as (tvl'&Htvl').
      { apply lookup_lt_is_Some_2. lia. }
      assert (combine (l.*2) v_lis0 !! (n : nat) = Some (tvl, vl')).
      { apply combine_lookup. split; eauto. }
      iDestruct (big_sepL_insert_acc with "H2'") as "(Ht'&H2')"; first eauto.
      simpl.

      assert (Hvs1 : ∃ vs1, l !! (n : nat) = Some (vs1, tvl) /\ @is_ab_b_tree max_child_num' depth' vs1 tvl).
      { rewrite list_lookup_fmap_Some in Htvl.
        destruct Htvl as ((vs1&?)&Hvs1&Heq'). simpl in Heq'. symmetry in Heq'. subst.
        exists vs1. split; auto.
        eapply Forall_lookup_1 in Hvs1; eauto. simpl in Hvs1.
        eauto.
      }
      tp_bind (insert_tree_aux _ _)%E.
      destruct Hvs1 as (vs1&Hlookupl&His_ab_b_tree1).
      iApply ("IH" with "[Hp1 Ht] [Hp1' Ht'] [] Hspec ").
      { rewrite /btree_ptrv. iFrame. simpl. eauto. }
      { rewrite /btree_ptrv'. iFrame. simpl. eauto. }
      { iPureIntro.
        apply Forall_app in Hforall as [Hforall1 _].
        apply Forall_flat_map in Hforall1.
        rewrite Forall_fmap in Hforall1.
        eapply Forall_lookup_1 in Hlookupl; eauto.
        simpl; eauto.
      }
      iNext. iIntros (res) "IHres".
      iDestruct "IHres" as (tv tv' vs t' res') "(Hspec&Hp1&Hp1'&%Hforall1&Hres)".

      (* Rebuild the btree_ptrv facts p after "putting back" the child we recursively inserted into *)
      set (l' :=  <[ (n : nat) := (vs, t') ]> l).
      set (vs' :=
             (flat_map (λ x : list (option val), x) l'.*1 ++
              replicate ((S max_child_num' - length l') * S max_child_num' ^ depth') None)).
      iAssert (btree_ptrv p _ (S depth') (Br l'.*2) vs')%I
        with "[Hp H1 H2 Hp1]" as "Hp".
      {
        rewrite /btree_ptrv. iFrame.
        iDestruct "Hp1" as "(%Hab'&Hptr&Hrelate)".
        iDestruct ("H2" $! (t', tv) with "Hrelate") as "H2".
        iDestruct ("H1" $! (ptr, tv) with "Hptr") as "H1".
        rewrite ?combine_insert.
        iSplit; last first.
        { rewrite relate_ab_tree_with_v_Br.
          iExists _, _, _. iSplit; first eauto. iFrame.
          rewrite ?insert_length //.
          iSplit; first eauto.
          { rewrite /l'. iPureIntro.
            rewrite list_fmap_insert /= insert_length //.
          }
          iSplit; first eauto.
          { rewrite /l'. iPureIntro.
            rewrite list_fmap_insert /= insert_length //.
          }
          iSplit.
          { iPureIntro. rewrite list_insert_id //. }
          rewrite /l' list_fmap_insert /=. eauto.
        }
        iPureIntro.
        econstructor.
        * rewrite /l'. eapply Forall_insert; eauto.
        * rewrite /l' insert_length //.
      }

      iAssert (btree_ptrv' p' _ (S depth') (Br l'.*2) vs')%I with "[Hp' H1' H2' Hp1']" as "Hp'".
      { rewrite /btree_ptrv. iFrame.
        iDestruct "Hp1'" as "(%Hab'&Hptr&Hrelate)".
        iDestruct ("H2'" $! (t', tv') with "Hrelate") as "H2".
        iDestruct ("H1'" $! (ptr', tv') with "Hptr") as "H1".
        rewrite ?combine_insert.
        iSplit; last first.
        { rewrite relate_ab_tree_with_v_Br'.
          iExists _, _, _. iSplit; first eauto. iFrame.
          rewrite ?insert_length //.
          iSplit; first eauto.
          { rewrite /l'. iPureIntro.
            rewrite list_fmap_insert /= insert_length //.
          }
          iSplit; first eauto.
          { rewrite /l'. iPureIntro.
            rewrite list_fmap_insert /= insert_length //.
          }
          iSplit.
          { iPureIntro. rewrite list_insert_id //. }
          rewrite /l' list_fmap_insert /=. eauto.
        }
        iPureIntro.
        econstructor.
        * rewrite /l'. eapply Forall_insert; eauto.
        * rewrite /l' insert_length //.
      }

      assert (Forall (olift P) vs').
      { rewrite /vs'. apply Forall_app. split.
        * apply Forall_flat_map.
          rewrite /l'.
          eapply Forall_app in Hforall as [Hforall0 ?].
          eapply Forall_fmap, Forall_insert.
          { apply Forall_fmap; eauto. apply Forall_flat_map in Hforall0; auto. }
          rewrite /=. eauto.
        * apply Forall_replicate. rewrite //=.
      }
      iDestruct "Hres" as "[Hnone|Hsome]".
      * iDestruct "Hnone" as "(->&->)".
        simpl.
        tp_pures. wp_pures. iModIntro.
        iApply "HΦ". iExists _, _, vs', (Br (l'.*2)), _.
        iFrame. iSplit; first done.
        iLeft. eauto.
      * iDestruct "Hsome" as (tvnew tvnew' tnew vs2new) "(->&->&%Hwfnew&%Hforallnew&Htvnew&Htvnew')".
        simpl.
        tp_pures. wp_pures.
        wp_apply (rel_insert_child_list' with "[$Hp $Hp' $Htvnew $Htvnew' $Hspec //]").
        iIntros (res) "Hres".
        iApply "HΦ".
        iDestruct "Hres" as (?????) "H".
        iExists _, _, _, _, _. iFrame.
  Qed.

  Lemma rel_insert_tree_curry K P p p' tv tv' depth t vs (v: val) :
    {{{ btree_ptrv p tv depth t vs ∗
        btree_ptrv' p' tv' depth t vs ∗
        ⌜ Forall (olift P) vs ⌝ ∗
        ⌜ P v ⌝ ∗
        ⤇ fill K (insert_tree_curry #p' v)
    }}}
      insert_tree_curry #p v
    {{{ RET #();
        ∃ depth' tv tv' vs t,
        ⤇ fill K #() ∗
        btree_ptrv p tv depth' t vs ∗
        btree_ptrv' p' tv' depth' t vs ∗
        ⌜ Forall (olift P) vs ⌝
    }}}.
  Proof.
    iIntros (Φ) "(Hbtree&Hbtree'&%Hforall&%HPv&Hspec) HΦ".
    rewrite /insert_tree_curry.
    wp_pures. tp_pures.
    tp_bind (insert_tree_aux _ _).
    wp_apply (rel_insert_tree_aux _ P with "[$Hbtree $Hbtree' $Hspec //]").
    iIntros (res) "Hres".
    iDestruct "Hres" as (?????) "(Hspec&Hbtree&Hbtree'&%Hforall'&Hres)".
    iDestruct "Hres" as "[(->&->)|Hres]".
    - simpl. tp_pures. wp_pures. iModIntro. iApply "HΦ". iExists _, _, _, _. iFrame; eauto.
    - iDestruct "Hres" as (????) "(->&->&%Hab&%Hforall''&Htvnew&Htvnew')".
      simpl. tp_pures. wp_pures.
      tp_alloc as ptrnew1' "Hptrnew'".
      wp_alloc ptrnew1 as "Hptrnew".
      wp_pures.
      replace (#ptrnew1) with (@inject loc val _ ptrnew1) by auto.
      wp_apply (wp_list_cons (A:=loc) _ []); first eauto.
      iIntros (? Hlist).
      tp_bind (list_cons #ptrnew1' _)%E.
      replace (#ptrnew1') with (inject ptrnew1') by auto.
      iMod (spec_list_cons _ _ _ nil with "[] Hspec") as (?) "(Hspec&%Hlist')".
      { eauto. }
      simpl.

      iDestruct "Hbtree" as "(%&Hp&Hrelp)".
      iDestruct "Hbtree'" as "(%&Hp'&Hrelp')".
      tp_load.
      wp_load.

      tp_alloc as ptrnew2' "Hptrnew2'".
      wp_alloc ptrnew2 as "Hptrnew2".

      replace (#ptrnew2) with (inject ptrnew2) by auto.
      wp_apply (wp_list_cons); first eauto.
      iIntros (? Hlist2).


      tp_bind (list_cons #ptrnew2' _)%E.
      replace (#ptrnew2') with (inject ptrnew2') by auto.
      iMod (spec_list_cons (A:=loc) _ _ _ _ with "[] Hspec") as (?) "(Hspec&%Hlist2')".
      { eauto. }

      simpl.
      tp_pures; tp_store.
      wp_pures; wp_store.
      simpl.
      iModIntro. iApply "HΦ".
      iExists (S depth), (InjRV v2), (InjRV v3), _, (Br [t'; tnew]). iFrame "Hspec Hp Hp'".
      iSplitL "Hrelp Htvnew Hptrnew Hptrnew2".
      * iSplitR; last first.
        ** rewrite relate_ab_tree_with_v_Br. iExists _, [ptrnew2; ptrnew1], [tv0; tvnew].
           repeat (iSplit; first eauto).
           rewrite /=. iFrame.
        ** iPureIntro.
           set (l' := ((vs0, t') :: (vs2new, tnew) :: nil)).
           replace ([t'; tnew]) with (l'.*2) by auto.
           econstructor.
           *** rewrite /l'. econstructor; eauto.
           *** rewrite /b_tree.min_child_num /b_tree.max_child_num. rewrite /l'. econstructor; eauto => //=. lia.
      * iSplit; last first.
        { iPureIntro. apply Forall_app.
          split.
          * apply Forall_flat_map.
            rewrite fmap_cons; econstructor; first done.
            econstructor; eauto.
          * apply Forall_replicate. rewrite //=.
        }
        iSplitR; last first.
        ** rewrite relate_ab_tree_with_v_Br'. iExists _, [ptrnew2'; ptrnew1'], [tv'0; tvnew'].
           repeat (iSplit; first eauto).
           rewrite /=. iFrame.
        ** iPureIntro.
           set (l' := ((vs0, t') :: (vs2new, tnew) :: nil)).
           replace ([t'; tnew]) with (l'.*2) by auto.
           econstructor.
           *** rewrite /l'. econstructor; eauto.
           *** rewrite /b_tree.min_child_num /b_tree.max_child_num. rewrite /l'. econstructor; eauto => //=. lia.
  Qed.


  (* We need some wrappers around the sampler programs from b_tree.v to handle
     uncurrying and loading trees from the pointer. Additionally, the intermediate
     versions need to use find_depth to compute depth instead of taking as argument *)

  (* Version that computes depth and then calls the version from
     b_tree.v.  Of course it's "silly" to compute the depth on every
     sampling call, but recall that this intermediate program is just
     a proof device, so we don't care about its efficiency.  *)
  Definition intermediate_sampler_prog' : val :=
    λ: "pt",
      let: "d" := find_depth "pt" in
      let: "t" := !"pt" in
      intermediate_sampler_annotated_prog (max_child_num' := max_child_num') "d" "t" #().

  Definition opt_sampler_annotated_prog' : val :=
    λ: "pt",
      let: "t" := !"pt" in
      optimized_sampler_annotated_prog (max_child_num' := max_child_num') "t" #().

  Definition naive_sampler_annotated_prog' : val :=
    λ: "pt",
       let: "t" := !"pt" in
       let: "rt" := build_ranked "t" in
       naive_sampler_annotated_prog "rt" #().

  Local Close Scope R.

  (* The abstract type of btrees, as an existential. The first operation is
     creating a tree, second is inserting, and third is sampling *)
  Definition btreeτ : type := ∃: (TInt → #0) * (#0 * TInt → TUnit) * (#0 → TInt).

  Definition opt_annotated_btree_pack : val :=
    (init_tree, insert_tree, opt_sampler_annotated_prog').

  Definition intermediate_btree_pack : val :=
    (init_tree, insert_tree, intermediate_sampler_prog').

  Definition naive_annotated_btree_pack : val :=
    (init_tree, insert_tree, naive_sampler_annotated_prog').

  Definition bN := nroot.@"b_tree".

  Definition isInt := (λ v : val, ∃ n : Z, v = #n).
  Definition btree_inv (p1 p2: loc) :=
    (∃ depth t l, ⌜ Forall (olift isInt) l⌝ ∗
                    btree_ptr p1 depth t l ∗ btree_ptr' p2 depth t l)%I.

  Definition R : lrel Σ :=
    LRel (λ v1 v2, ∃ (p1 p2 : loc),
          ⌜ v1 = #p1 ⌝ ∗ ⌜ v2 = #p2 ⌝ ∗
           na_inv parisRGS_nais bN (btree_inv p1 p2))%I.

  Lemma init_tree_self_lrel : ⊢ (lrel_int → R)%lrel init_tree init_tree.
  Proof.
    iIntros (v1 v2) "!>".
    iDestruct 1 as (z) "(->&->)".
    rewrite refines_eq. iIntros (K ε) "HK Hown Heps %Hlt".
    iApply wp_fupd.
    iMod (spec_init_tree with "HK") as (p2) "(Hspec&Hp2)".
    wp_apply (wp_init_tree with "[//]").
    iIntros (p1) "Hp1".
    iMod (na_inv_alloc parisRGS_nais _ bN (btree_inv p1 p2) with "[Hp1 Hp2]") as "Hinv".
    { iNext. rewrite /btree_inv. iExists _, _, _. iFrame "Hp1". iFrame "Hp2".
      iPureIntro. econstructor => //=. rewrite /isInt; eauto. }
    iModIntro. iExists _, _. iFrame. eauto.
  Qed.

  Lemma insert_tree_self_lrel : ⊢ (R * lrel_int → ())%lrel insert_tree insert_tree.
  Proof.
    iIntros (vv1 vv2) "!>".
    iIntros "Hpair".
    iDestruct "Hpair" as (????) "(->&->&(HR&Hint))".
    iDestruct "Hint" as (z) "(->&->)".
    iDestruct "HR" as (p1 p2) "(->&->&Hinv)".
    iApply (refines_na_inv with "[$Hinv]"); first done.
    iIntros "(Hbtree&Hclo)".
    rewrite /insert_tree. rel_pures_l. rel_pures_r.
    rewrite refines_eq /refines_def.
    iIntros (K ε) "HK Hna Heps %Hlt".
    iDestruct "Hbtree" as (???) "(%Hforall&Hb1&Hb2)".
    iDestruct "Hb1" as (?) "Hb1".
    iDestruct "Hb2" as (?) "Hb2".
    iApply wp_fupd.
    wp_apply (rel_insert_tree_curry _ isInt with "[$Hb1 $Hb2 $HK]").
    { iPureIntro; split; rewrite /isInt; eauto. }
    iDestruct 1 as (?????) "(HK&Hb1&Hb2&Hforall')".
    iMod ("Hclo" with "[Hb1 Hb2 $Hna $Hforall']").
    { iNext. iExists _, _. iSplitL "Hb1"; iExists _; iFrame. }
    iModIntro. iExists _, _; iFrame. eauto.
  Qed.

  Lemma intermediate_refines_opt_annotated Δ :
    ⊢ REL intermediate_btree_pack  << opt_annotated_btree_pack : interp btreeτ Δ.
  Proof.
    iApply (refines_pack R).
    rewrite refines_eq /refines_def. iIntros (K ε) "HK Hown Heps %Hlt".
    wp_pures.
    iModIntro. iExists _; iFrame. iSplit; first eauto. simpl.
    iExists _, _, _, _.
    iSplit; first eauto.
    iSplit; first eauto.
    clear Δ K ε Hlt.
    (* Break up the nested pair interpretation on the left so
       that we get a flat hierarchy of 3 goals for each component of the 3 tuple *)
    iSplit; first (iExists _, _, _, _; iSplit; first eauto; iSplit; first eauto; iSplit).
    - iApply init_tree_self_lrel.
    - iApply insert_tree_self_lrel.
    - iIntros (vv1 vv2) "!>".
      iIntros "HR".
      iDestruct "HR" as (p1 p2) "(->&->&Hinv)".
      iApply (refines_na_inv with "[$Hinv]"); first done.
      iIntros "(Hbtree&Hclo)".
      rewrite /intermediate_sampler_prog'.
      rewrite /opt_sampler_annotated_prog'.
      rel_pures_l. rel_pures_r.
      rewrite refines_eq /refines_def.
      iIntros (K ε) "HK Hna Heps %Hlt".
      wp_pures.
      iDestruct "Hbtree" as (???) "(%Hforall&Hb1&Hb2)".
      iDestruct "Hb1" as (?) "Hb1".
      iDestruct "Hb2" as (?) "Hb2".
      wp_apply (wp_find_depth with "Hb1").
      iIntros "Hb1".
      wp_pures.

      iDestruct "Hb1" as "(%His_tree&Hp1&Hrel1)".
      iDestruct "Hb2" as "(%&Hp2&Hrel2)".
      iApply wp_fupd.
      wp_load. wp_pures.
      tp_load. tp_pures.
      iMod (ec_zero) as "Hz".
      wp_apply (intermediate_annotated_optimized_refinement with "[$Hrel1 $Hrel2 $Hz HK]"); eauto.
      iIntros (?) "(HK&%Helem&Hrel1&Hrel2)". iMod ("Hclo" with "[Hp1 Hp2 $Hna Hrel1 Hrel2]").
      { iNext. rewrite /btree_inv. iExists _, _, _.
        iFrame "%". iSplitL "Hp1 Hrel1"; iExists _; iFrame; eauto. }
      iModIntro. iExists _, _. iFrame. iSplit; first done.
      iPureIntro.
      eapply Forall_forall in Hforall; last eauto.
      destruct Hforall as (n&->). naive_solver.
  Qed.

  Lemma opt_annotated_refines_intermediate Δ :
    ⊢ REL opt_annotated_btree_pack  << intermediate_btree_pack : interp btreeτ Δ.
  Proof.
    iApply (refines_pack R).
    rewrite refines_eq /refines_def. iIntros (K ε) "HK Hown Heps %Hlt".
    wp_pures.
    iModIntro. iExists _; iFrame. iSplit; first eauto. simpl.
    iExists _, _, _, _.
    iSplit; first eauto.
    iSplit; first eauto.
    clear Δ K ε Hlt.
    (* Break up the nested pair interpretation on the left so
       that we get a flat hierarchy of 3 goals for each component of the 3 tuple *)
    iSplit; first (iExists _, _, _, _; iSplit; first eauto; iSplit; first eauto; iSplit).
    - iApply init_tree_self_lrel.
    - iApply insert_tree_self_lrel.
    - iIntros (vv1 vv2) "!>".
      iIntros "HR".
      iDestruct "HR" as (p1 p2) "(->&->&Hinv)".
      iApply (refines_na_inv with "[$Hinv]"); first done.
      iIntros "(Hbtree&Hclo)".
      rewrite /intermediate_sampler_prog'.
      rewrite /opt_sampler_annotated_prog'.
      rel_pures_l. rel_pures_r.
      rewrite refines_eq /refines_def.
      iIntros (K ε) "HK Hna Heps %Hlt".
      wp_pures.
      iDestruct "Hbtree" as (???) "(%Hforall&Hb1&Hb2)".
      iDestruct "Hb1" as (?) "Hb1".
      iDestruct "Hb2" as (?) "Hb2".
      tp_bind (find_depth _)%E.
      iMod (spec_find_depth with "Hb2 HK") as "(HK&Hb2)".
      iEval (simpl) in "HK".
      tp_pures.

      iDestruct "Hb1" as "(%His_tree&Hp1&Hrel1)".
      iDestruct "Hb2" as "(%&Hp2&Hrel2)".
      iApply wp_fupd.
      wp_load. wp_pures.
      tp_load. tp_pures.
      iMod (ec_zero) as "Hz".
      wp_apply (annotated_optimized_intermediate_refinement with "[$Hrel1 $Hrel2 $Hz HK]"); eauto.
      iIntros (?) "(HK&%Helem&Hrel1&Hrel2)". iMod ("Hclo" with "[Hp1 Hp2 $Hna Hrel1 Hrel2]").
      { iNext. rewrite /btree_inv. iExists _, _, _.
        iFrame "%". iSplitL "Hp1 Hrel1"; iExists _; iFrame; eauto. }
      iModIntro. iExists _, _. iFrame. iSplit; first done.
      iPureIntro.
      eapply Forall_forall in Hforall; last eauto.
      destruct Hforall as (n&->). naive_solver.
  Qed.

  Lemma naive_annotated_refines_intermediate Δ :
    ⊢ REL naive_annotated_btree_pack  << intermediate_btree_pack : interp btreeτ Δ.
  Proof.
    iApply (refines_pack R).
    rewrite refines_eq /refines_def. iIntros (K ε) "HK Hown Heps %Hlt".
    wp_pures.
    iModIntro. iExists _; iFrame. iSplit; first eauto. simpl.
    iExists _, _, _, _.
    iSplit; first eauto.
    iSplit; first eauto.
    clear Δ K ε Hlt.
    (* Break up the nested pair interpretation on the left so
       that we get a flat hierarchy of 3 goals for each component of the 3 tuple *)
    iSplit; first (iExists _, _, _, _; iSplit; first eauto; iSplit; first eauto; iSplit).
    - iApply init_tree_self_lrel.
    - iApply insert_tree_self_lrel.
    - iIntros (vv1 vv2) "!>".
      iIntros "HR".
      iDestruct "HR" as (p1 p2) "(->&->&Hinv)".
      iApply (refines_na_inv with "[$Hinv]"); first done.
      iIntros "(Hbtree&Hclo)".
      rewrite /intermediate_sampler_prog'.
      rewrite /naive_sampler_annotated_prog'.
      rel_pures_l. rel_pures_r.
      rewrite refines_eq /refines_def.
      iIntros (K ε) "HK Hna Heps %Hlt".
      wp_pures.
      iDestruct "Hbtree" as (???) "(%Hforall&Hb1&Hb2)".
      iDestruct "Hb1" as (?) "Hb1".
      iDestruct "Hb2" as (?) "Hb2".
      tp_bind (find_depth _)%E.
      iMod (spec_find_depth with "Hb2 HK") as "(HK&Hb2)".
      iEval (simpl) in "HK".
      tp_pures.

      iDestruct "Hb1" as "(%His_tree&Hp1&Hrel1)".
      iDestruct "Hb2" as "(%&Hp2&Hrel2)".
      iApply wp_fupd.
      wp_load. wp_pures.
      tp_load. tp_pures.

      wp_apply (wp_build_ranked with "[$Hrel1]"); first eauto.
      iIntros (treev') "(Hrel1&Hrel1_ranked)".
      wp_pures.
      assert (Hsplit: (ε = ε/2 + ε/2)%R).
      { nra. }
      assert (Hle: (0 <= ε / 2)%R).
      { nra. }
      rewrite Hsplit ec_split; auto.
      iDestruct "Heps" as "(Heps1&Heps2)".
      wp_apply (annotated_naive_intermediate_refinement with "[$Hrel1_ranked $Hrel2 $HK Heps1]"); eauto.
      2:{ set (eps' := mknonnegreal _ Hle).
          replace (ε/2)%R with (NNRbar_to_real (NNRbar.Finite eps')); eauto. }
      { rewrite //=. nra. }
      iIntros (?) "(HK&%Helem&Hrel1_ranked&Hrel2)". iMod ("Hclo" with "[Hp1 Hp2 $Hna Hrel1 Hrel2]").
      { iNext. rewrite /btree_inv. iExists _, _, _.
        iFrame "%". iSplitL "Hp1 Hrel1"; iExists _; iFrame; eauto. }
      iModIntro. iExists _, _. iFrame. iSplit; first by (iPureIntro; nra).
      iPureIntro.
      eapply Forall_forall in Hforall; last eauto.
      destruct Hforall as (n&->). naive_solver.
  Qed.

End b_tree_adt.
