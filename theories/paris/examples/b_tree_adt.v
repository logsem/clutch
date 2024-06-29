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
Set Default Proof Using "Type*".
Open Scope R.
Opaque INR.

Section b_tree_adt.

  Context {max_child_num' : nat}.

  Definition init_tree : val :=
    λ: "v", ref (InjL "v").

  Definition init_ranked_tree : val :=
    λ: "v", ref ((#1, InjL "v")).

  (* Tries to insert a new child into a list of children. The child list may already be full,
     so we return a pair, where the second component is (optionally)  list of the subset of children
     resulting from splitting the list.

     An optimal B+-tree would try to split the lists evenly, but that is really irrelevant for our purposes,
     so for simplicity we just put solely the new element in the second list.
   *)

  (*
  Definition insert_child_list : val :=
    λ: "l" "v",
      if: list_length "l" < #(S max_child_num') then
        (InjR (list_cons (ref "v") "l"), NONE)
      else
        (InjR ("l"), SOME (InjR (list_cons (ref "v") list_nil))).
   *)

  Definition insert_child_list' : val :=
    λ: "p" "l" "v",
      if: list_length "l" < #(S max_child_num') then
        "p" <- InjR (list_cons (ref "v") "l") ;;
        NONE
      else
        SOME (InjR (list_cons (ref "v") list_nil)).

  Definition insert_tree_aux : val :=
    rec: "insert_tree" "p" "v" :=
        let: "t" := !"p" in
        match: "t" with
        | InjL "v" => SOME (InjL "v")
        | InjR "l" =>
            (* Insert into a random child, this shows our sampler code is "robust"
               to a variety of tree shapes *)
            let: "n" := rand (list_length "l") in
            let: "c" := list_nth "l" "n" in
            match: "insert_tree" "c" "v" with
            | NONE => NONE
            | SOME "new" =>
                (* Either the child was a leaf, or we had to split the child, so
                   we must insert "new" into the current node *)
                insert_child_list' "p" "l" "new"
            end
        end.

  Definition insert_tree : val :=
    λ: "p" "v",
      match: insert_tree_aux "p" "v" with
      | NONE => #()
      | SOME "t'" =>
          (* The root node had to be split, so we need to create a new root node which will have as children
             t' and the sibling stored in !p *)
          let: "new_root" := InjR (list_cons (ref !"p") (list_cons (ref "t'") list_nil)) in
          "p" <- "new_root"
      end.



  Context `{!parisGS Σ}.

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

  Lemma rel_insert_child_list' K p p' ltv ltv' depth l vs vs2 t tv tv' :
    {{{ btree_ptrv p (InjRV ltv) (S depth) (Br l) vs ∗
        btree_ptrv' p' (InjRV ltv') (S depth) (Br l) vs ∗
        ⌜ @is_ab_b_tree max_child_num' depth vs2 t ⌝ ∗
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
          ((⌜ res = NONEV ⌝ ∗ ⌜ res' = NONEV ⌝) ∨
           (∃ tvnew tvnew' tnew vs2new,
               ⌜ res = SOMEV tvnew ⌝ ∗ ⌜ res' = SOMEV tvnew' ⌝ ∗
               ⌜ @is_ab_b_tree max_child_num' (S depth) vs2new tnew ⌝ ∗
               relate_ab_tree_with_v tnew tvnew ∗
               relate_ab_tree_with_v' tnew tvnew'))
    }}}.
  Proof.
    iIntros (Φ) "(Hbtree&Hbtree'&%Htwf&Htv&Htv'&Hspec) HΦ".
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
    iIntros (Φ) "(Hbtree_ptrv&%Htwf&Htv) HΦ".
    rewrite /insert_child_list'.
    wp_pures.
    iDestruct "Hbtree_ptrv" as "(%Hwft'&Hp&Hrelate)".
    iEval (rewrite relate_ab_tree_with_v_Br) in "Hrelate".
    iDestruct "Hrelate" as (??? Heq1 Heq2 Heq3 ?) "(H1&H2)".
    inversion Heq1; subst.
    wp_apply (wp_list_length); eauto.
    iIntros (? ->).
    wp_pures. case_bool_decide.
    { wp_pures.
      wp_alloc lv as "Hlv".
      replace (#lv) with (inject lv) by auto.
      wp_apply (wp_list_cons); eauto.
      iIntros (? Hlist).
      wp_store.
      wp_pures.
      iModIntro. iApply "HΦ".
      rewrite decide_True; last first.
      { lia. }
      iSplit; auto.
      rewrite /btree_ptrv.
      iSplit.
      { iPureIntro.
        inversion Hwft'.
        Print is_ab_b_tree.
        simpl.
        eapply (is_ab_b_tree_br _ ((vs1, t) :: _)).
        econstructor. simpl.
      simpl.
      iFrame.
      iExists _.
      wp_pures.
   *)

End b_tree_adt.
