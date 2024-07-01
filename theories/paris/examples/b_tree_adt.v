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
  Context (max_child_num_lt : 2 ≤ S max_child_num').

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

  Lemma rel_insert_tree_aux K p p' tv tv' depth t vs (v: val) :
    {{{ btree_ptrv p tv depth t vs ∗
        btree_ptrv' p' tv' depth t vs ∗
        ⤇ fill K (insert_tree_aux #p' v)
    }}}
      insert_tree_aux #p v
    {{{ res, RET res;
        ∃ tv tv' vs t' (res' : val),
        ⤇ fill K res' ∗
          btree_ptrv p tv depth t' vs ∗
          btree_ptrv' p' tv' depth t' vs ∗
          ((⌜ res = NONEV ⌝ ∗ ⌜ res' = NONEV ⌝) ∨
           (∃ tvnew tvnew' tnew vs2new,
               ⌜ res = SOMEV tvnew ⌝ ∗ ⌜ res' = SOMEV tvnew' ⌝ ∗
               ⌜ @is_ab_b_tree max_child_num' depth vs2new tnew ⌝ ∗
               relate_ab_tree_with_v tnew tvnew ∗
               relate_ab_tree_with_v' tnew tvnew'))
    }}}.
  Proof.
    iIntros (Φ) "(Hbtree&Hbtree'&Hspec) HΦ".
    iInduction depth as [| depth'] "IH" forall (K p p' tv tv' t vs Φ).
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
      iApply ("IH" with "[Hp1 Ht] [Hp1' Ht'] Hspec ").
      { rewrite /btree_ptrv. iFrame. simpl. eauto. }
      { rewrite /btree_ptrv'. iFrame. simpl. eauto. }
      iNext. iIntros (res) "IHres".
      iDestruct "IHres" as (tv tv' vs t' res') "(Hspec&Hp1&Hp1'&Hres)".

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

      iDestruct "Hres" as "[Hnone|Hsome]".
      * iDestruct "Hnone" as "(->&->)".
        simpl.
        tp_pures. wp_pures. iModIntro.
        iApply "HΦ". iExists _, _, vs', (Br (l'.*2)), _.
        iFrame. iLeft. eauto.
      * iDestruct "Hsome" as (tvnew tvnew' tnew vs2new) "(->&->&%Hwfnew&Htvnew&Htvnew')".
        simpl.
        tp_pures. wp_pures.
        wp_apply (rel_insert_child_list' with "[$Hp $Hp' $Htvnew $Htvnew' $Hspec //]").
        iIntros (res) "Hres".
        iApply "HΦ".
        iDestruct "Hres" as (?????) "H".
        iExists _, _, _, _, _. iFrame.
  Qed.

  Lemma rel_insert_tree K p p' tv tv' depth t vs (v: val) :
    {{{ btree_ptrv p tv depth t vs ∗
        btree_ptrv' p' tv' depth t vs ∗
        ⤇ fill K (insert_tree #p' v)
    }}}
      insert_tree #p v
    {{{ RET #();
        ∃ depth' tv tv' vs t,
        ⤇ fill K #() ∗
        btree_ptrv p tv depth' t vs ∗
        btree_ptrv' p' tv' depth' t vs
    }}}.
  Proof.
    iIntros (Φ) "(Hbtree&Hbtree'&Hspec) HΦ".
    rewrite /insert_tree.
    wp_pures. tp_pures.
    tp_bind (insert_tree_aux _ _).
    wp_apply (rel_insert_tree_aux with "[$Hbtree $Hbtree' $Hspec]").
    iIntros (res) "Hres".
    iDestruct "Hres" as (?????) "(Hspec&Hbtree&Hbtree'&Hres)".
    iDestruct "Hres" as "[(->&->)|Hres]".
    - simpl. tp_pures. wp_pures. iModIntro. iApply "HΦ". iExists _, _, _, _. iFrame.
    - iDestruct "Hres" as (????) "(->&->&%Hab&Htvnew&Htvnew')".
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
      * iSplitR; last first.
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

End b_tree_adt.
