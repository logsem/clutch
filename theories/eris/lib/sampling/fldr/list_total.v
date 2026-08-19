From clutch Require Import eris.
From clutch.common Require Import inject.
From clutch.eris.lib Require Import list.

Set Default Proof Using "Type*".

Section list_total_specs.

  Context {A : Type}.
  Context `{!erisGS Σ}.
  Context `[!Inject A val].

  Lemma twp_list_nil E :
    [[{ True }]]
      list_nil @ E
    [[{ v, RET v; ⌜is_list [] v⌝}]].
  Proof.
    iIntros (Φ) "_ HΦ". unfold list_nil. wp_pure. by iApply "HΦ".
  Qed.

  Lemma twp_list_length E l lv :
    [[{ ⌜is_list l lv⌝ }]]
      list_length lv @ E
    [[{ v, RET #v; ⌜v = length l⌝ }]].
  Proof.
    iIntros (Φ) "Ha HΦ".
    iInduction l as [|a l'] "IH" forall (lv Φ);
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_rec.
    - wp_match. iApply ("HΦ" $! 0%nat); done.
    - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_match. wp_proj. wp_bind (list_length _).
      iApply ("IH" $! _ _ Hlcoh). iIntros; simpl.
      wp_op. iSpecialize ("HΦ" $! (1 + v)%nat).
      rewrite Nat2Z.inj_add. iApply "HΦ"; by auto.
  Qed.

  Lemma twp_list_nth E (i: nat) l lv :
   [[{ ⌜is_list l lv⌝ }]]
      list_nth (Val lv) #i @ E
    [[{ v, RET v; (⌜v = NONEV⌝ ∧ ⌜length l <= i⌝) ∨
              ⌜∃ r, v = SOMEV (inject r) ∧ l !! i = Some r⌝ }]].
  Proof.
    iIntros (Φ) "Ha HΦ".
    iInduction l as [|a l'] "IH" forall (i lv Φ);
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_rec; wp_let.
    - wp_match. wp_pures.
      iApply ("HΦ" $! (InjLV #())). iLeft. simpl. eauto with lia.
    - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_match. wp_pures. case_bool_decide; wp_pures.
      + iApply "HΦ". iRight. simpl. iExists a. by destruct i.
      + destruct i; first done.
        assert ((S i - 1)%Z = i) as -> by lia.
        iApply ("IH" $! i lv' _ Hlcoh).
        iIntros (v [ (Hv & Hs) | Hps]); simpl.
        * iApply "HΦ"; try eauto with lia.
        * iApply "HΦ"; try eauto with lia.
  Qed.

  Lemma twp_list_nth_some E (i: nat) l lv :
    [[{ ⌜is_list l lv ∧ i < length l⌝ }]]
      list_nth (Val lv) #i @ E
    [[{ v, RET v; ⌜∃ r, v = SOMEV (inject r) ∧ l !! i = Some r⌝ }]].
  Proof.
    iIntros (Φ (Hcoh & Hi)) "HΦ".
    iApply (twp_list_nth $! Hcoh).
    iIntros (v [H | H]); first eauto with lia.
    by iApply "HΦ".
  Qed.

  Local Lemma twp_list_rev_aux E l lM r rM:
   [[{ ⌜is_list lM l ∧ is_list rM r⌝ }]]
     list_rev_aux (Val l) (Val r) @ E
   [[{ v, RET v; ⌜is_list (rev_append lM rM) v⌝ }]].
  Proof.
    iIntros (? [Hl Hr]) "H".
    iInduction lM as [|a lM] "IH" forall (l r rM Hl Hr).
    - simpl in *; subst. rewrite /list_rev_aux. wp_pures. by iApply "H".
    - destruct Hl as [l' [Hl'eq Hl']]; subst.
      wp_rec; wp_pures.
      wp_apply twp_list_cons; [done|].
      iIntros (w Hw).
      wp_pures. by iApply "IH".
  Qed.

  Lemma twp_list_rev E l lM :
    [[{ ⌜is_list lM l⌝ }]]
      list_rev (Val l) @ E
    [[{ v, RET v; ⌜is_list (reverse lM) v⌝ }]].
  Proof.
    iIntros (??) "H". rewrite /list_rev. wp_pures.
    by iApply (twp_list_rev_aux _ _ _ NONEV []).
  Qed.

  Lemma twp_list_append E l lM r rM :
    [[{ ⌜is_list lM l⌝ ∗ ⌜is_list rM r⌝}]]
      list_append (Val l) (Val r) @ E
    [[{ v, RET v; ⌜is_list (lM ++ rM) v⌝ }]].
  Proof.
    iIntros (Φ) "[%Hl %Hr] HΦ". rewrite /list_append.
    iInduction lM as [|a lM] "IH" forall (l r Hl Hr Φ).
    - simpl in Hl; subst. wp_pures. by iApply "HΦ".
    - destruct Hl as [l' [Hl'eq Hl']]; subst.
      do 12 wp_pure _.
      wp_bind (((rec: "list_append" _ _:= _)%V _ _)).
      iApply "IH"; [done..|].
      iIntros (v Hv).
      by wp_apply twp_list_cons.
  Qed.

  Lemma twp_list_filter (l : list A) (P : A -> bool) (f lv : val) E :
    [[{ (∀ (x : A),
            [[{ True }]]
              f (inject x) @ E
            [[{ w, RET w; ⌜w = inject (P x)⌝ }]] ) ∗
        ⌜is_list l lv⌝ }]]
       list_filter f lv @ E
     [[{ rv, RET rv; ⌜is_list (List.filter P l) rv⌝ }]].
  Proof.
    iIntros (Φ) "[#Hf %Hil] HΦ".
    iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil.
    - subst.
      rewrite /list_filter; wp_pures.
      iApply "HΦ"; done.
    - destruct Hil as (lv' & -> & Hil).
      rewrite /list_filter.
      do 7 (wp_pure _).
      fold list_filter.
      wp_apply ("IH" $! lv'); [done |].
      iIntros (rv) "%Hilp"; wp_pures.
      wp_apply "Hf"; [done |].
      iIntros (w) "->".
      destruct (P h) eqn:HP; wp_pures.
      + wp_apply twp_list_cons; [by eauto |].
        iIntros (v) "%Hil'".
        iApply "HΦ"; iPureIntro.
        simpl; rewrite HP; simpl.
        simpl in Hil'; done.
      + iApply "HΦ"; iPureIntro.
        simpl. rewrite HP. done.
  Qed.

  Lemma twp_list_map_pure `{!Inject B val} (l : list A) (f : A -> B) (fv lv : val) E :
    [[{ (∀ (x : A),
          [[{ True }]]
            fv (inject x) @ E
          [[{ fr, RET fr; ⌜fr = inject (f x)⌝ }]]) ∗
          ⌜is_list l lv⌝ }]]
      list_map fv lv @ E
    [[{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ }]].
  Proof.
    iIntros (Φ) "[#H %Hl] HΦ".
    iApply (twp_list_map l f fv lv (λ _ : A, True)%I (λ (_ : A) (_ : val), True)%I E); last first.
    - iIntros (?) "[% ?]". by iApply "HΦ".
    - iIntros. repeat iSplit.
      + iIntros (??) "!> _ K". wp_apply "H"; [done|].
        iIntros. iApply "K". by iSplit.
      + done.
      + done.
  Qed.

  Lemma twp_list_mapi_loop `{!Inject B val}
        (f : nat -> A -> B) (k : nat) (l : list A) (fv lv : val)
        (γ : nat -> A -> iProp Σ) (ψ : nat -> B -> iProp Σ) E :
    [[{ □ (∀ (i : nat) (x : A),
              [[{ γ (k + i)%nat x }]]
                fv (inject (k + i)%nat) (inject x) @ E
                [[{ fr, RET fr;
                    let r := f (k + i)%nat x in
                    ⌜fr = (inject r)⌝ ∗ ψ (k + i)%nat r }]]) ∗
        ⌜is_list l lv⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ (k + i)%nat a)
    }]]
      list_mapi_loop fv #k lv @ E
    [[{ rv, RET rv;
        let l' := mapi_loop f k l in
        ⌜is_list l' rv⌝ ∗
        ([∗ list] i ↦ a ∈ l', ψ (k + i)%nat a)}]].
  Proof.
    iInduction l as [ | h l'] "IH" forall (lv k);
      iIntros (Φ) "[#Hf [%Hil Hown]] HΦ"; simpl in Hil;
      rewrite /list_mapi_loop.
    - subst.
      wp_pures.
      iApply "HΦ".
      iSplitL ""; done.
    - destruct Hil as [lv' [-> Hil']].
      do 10 wp_pure _.
      fold list_mapi_loop.
      wp_bind (list_mapi_loop _ _ _).
      iAssert (⌜#(k + 1) = #(k + 1)%nat⌝%I) as "->".
      { iPureIntro. do 2 apply f_equal; lia. }
      iDestruct (big_sepL_cons with "Hown") as "[Hhead Hown]".
      iApply ("IH" with "[Hown]").
      + iSplitL "".
        * iModIntro. iIntros (i x).
          iPoseProof ("Hf" $! (1 + i)%nat x) as "Hf'".
          iAssert (⌜(k + (1 + i))%nat = (k + 1 + i)%nat⌝%I) as %<-.
          { iPureIntro; by lia. }
          iApply "Hf".
        * iSplitL ""; [done|].
          iApply (big_sepL_impl with "Hown").
          iModIntro. iIntros (k' x) "_ Hpre".
          iAssert (⌜(k + 1 + k')%nat = (k + S k')%nat⌝%I) as %->.
          { iPureIntro; lia. }
          done.
      + iIntros (rv) "[%Hil'' Hown]".
        wp_pures.
        iAssert (⌜#k = (inject (k + 0)%nat)⌝%I) as %->.
        { simpl. iPureIntro. do 2 f_equal. lia. }
        wp_apply ("Hf" with "Hhead").
        iIntros (fr) "[-> HΨ]".
        wp_apply twp_list_cons; [done |].
        iIntros (v) "%Hil'''".
        iApply "HΦ".
        iSplitL ""; [iPureIntro |].
        { assert (f (k + 0)%nat h :: mapi_loop f (k + 1) l' = mapi_loop f k (h :: l')) as <-.
          { simpl. assert ((k + 0)%nat = k) as -> by lia.
            assert (k + 1 = S k)%nat as -> by lia. reflexivity. }
          done. }
        simpl. iSplitL "HΨ".
        * assert (f k h = f (k + 0)%nat h) as -> by (assert (k = (k + 0))%nat as <- by lia; done).
          done.
        * iAssert (⌜(k + 1)%nat = S k⌝%I) as %->.
          { iPureIntro. do 2 f_equal. lia. }
          iApply (big_sepL_impl with "Hown").
          iModIntro. iIntros (k' x) "_ HΨ".
          iAssert (⌜(S k + k')%nat = (k + S k')%nat⌝%I) as %->.
          { iPureIntro. lia. }
          done.
  Qed.

  Lemma twp_list_mapi `{!Inject B val}
        (f : nat -> A -> B) (l : list A) (fv lv : val)
        (γ : nat -> A -> iProp Σ) (ψ : nat -> B -> iProp Σ) E :
    [[{ □ (∀ (i : nat) (x : A),
              [[{ γ i x }]]
                fv #i (inject x) @ E
                [[{ fr, RET fr;
                    let r := f i x in
                    ⌜fr = (inject r)⌝ ∗ ψ i r }]]) ∗
        ⌜is_list l lv⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ i a)
    }]]
      list_mapi fv lv @ E
    [[{ rv, RET rv;
        let l' := mapi f l in
        ⌜is_list l' rv⌝ ∗
        ([∗ list] i ↦ a ∈ l', ψ i a)}]].
  Proof.
    iIntros (Φ) "[#Hf [%Hil Hown]] HΦ".
    rewrite /list_mapi.
    do 3 wp_pure _.
    iAssert (⌜#0 = #(0%nat)⌝%I) as %->; [done |].
    iApply (twp_list_mapi_loop with "[Hown]").
    - iSplitL ""; last first.
      + iFrame; done.
      + iModIntro. iIntros (i x).
        iAssert (⌜(0 + i)%nat = i⌝%I) as %->; [done |].
        iApply "Hf".
    - assert (mapi f l = mapi_loop f 0 l) as <-; [done |].
      iFrame.
  Qed.

  Lemma twp_list_fold P Φ Ψ E handler (l : list A) acc lv :
    (∀ (a : A) acc lacc lrem,
        [[{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc ∗ Φ a }]]
          (Val handler) (Val acc) (inject a) @ E
        [[{v, RET v; P (lacc ++ [a]) v ∗ Ψ a }]]) -∗
    [[{ ⌜is_list l lv⌝ ∗ P [] acc ∗ [∗ list] a∈l, Φ a }]]
      list_fold handler acc lv @ E
    [[{v, RET v; P l v ∗ [∗ list] a∈l, Ψ a }]].
  Proof.
    iIntros "#Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
    change l with ([] ++ l) at 1 4.
    generalize (@nil A) at 1 3 4 as lproc => lproc.
    iInduction l as [|x l] "IHl" forall (Ξ lproc acc lv) "Hacc Hl HΞ".
    - iDestruct "Hl" as %?; simpl in *; simplify_eq.
      wp_rec. wp_pures. iApply "HΞ".
      rewrite app_nil_r; iFrame; done.
    - iDestruct "Hl" as %[lw [? Hlw]]; subst.
      iDestruct "HΦ" as "[Hx HΦ]".
      wp_rec. wp_pures.
      wp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
      iIntros (w) "[Hacc HΨ]"; simpl. wp_pures.
      iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
      { rewrite -app_assoc; auto. }
      iIntros (v) "[HP HΨs]".
      rewrite -app_assoc.
      iApply "HΞ"; iFrame.
  Qed.

End list_total_specs.
