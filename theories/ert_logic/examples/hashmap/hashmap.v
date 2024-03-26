(** * Hashmap *)
From stdpp Require Export list_numbers.
From clutch.ert_logic Require Export expected_time_credits ert_weakestpre problang_wp proofmode
  derived_laws cost_models ert_rules.
From clutch.prob_lang Require Import notation tactics metatheory lang.
From iris.proofmode Require Export proofmode.
From Coq Require Export Reals Psatz.
From Coquelicot Require Export Hierarchy.
Require Import Lra.
From clutch.ert_logic.examples.hashmap Require Export map hash linkedlist.

Set Default Proof Using "Type*".
Local Hint Resolve pos_INR:core.
Local Hint Resolve pos_INR_S:core.

Section hashmap.
  Context `{!ert_clutchGS Σ CostTick}.

  Variable val_size : nat.
  Definition insert_elem: val :=
    λ: "hm" "v",
      let, ("l", "hf") := "hm" in
      let: "off" := "hf" "v" in
      let: "w" := !("l" +ₗ "off") in
      tick #1;;
      ("l" +ₗ "off") <- insert "w" "v";;
      "off"
  .

  Definition lookup_elem: val :=
    λ: "hm" "v",
      let, ("l", "hf") := "hm" in
      let: "off" := "hf" "v" in
      let: "w" := !("l" +ₗ "off") in
      tick #1;;
      lookup "w" "v".

  Definition ishashmaplist (l:val) (m:gmap nat (list (nat))) :=
    (∃ (a:loc) (arr:list val) , ⌜l=#a⌝ ∗ a ↦∗ arr ∗ ⌜(length arr = S val_size)%nat⌝ ∗
                                 [∗ list] idx ∈ seq 0 (S val_size), ∃ v lis, ⌜arr!!idx = Some v⌝ ∗ isList v lis ∗ ⌜m!!idx=Some lis⌝ ∗ ⌜NoDup lis⌝
    )%I.

  Definition ishashmap (hm:val) (m1:gmap nat nat) (m2:gmap nat (list nat)) :=
    (∃ (l hf:val), ⌜hm = (l, hf)%V⌝ ∗ hashfun val_size hf m1 ∗ ishashmaplist l m2 ∗
                   ⌜∀ k v l,  m2!!k=Some l -> v∈l -> m1!!v=Some k⌝
    )%I.

  Definition hashmap_size (m:gmap nat (list nat)):=
    SeriesC (λ x : fin (S val_size),INR match m !! (fin_to_nat x) with
                                   | Some l0 => length l0
                                   | None => 0
                                   end). 

  Local Lemma seq_split m n:
    0<=m<n->
    seq 0 n = seq 0 m++m::seq (S m) (n - 1 - m).
  Proof.
    intros H. rewrite cons_seq.
    replace (m) with (0+m) at 2 by lia.
    rewrite -seq_app. f_equal. lia.
  Qed.

  
  Local Hint Resolve fin_to_nat_lt:core.

  Lemma wp_hm_insert_new E hm m1 m2 (n : nat) :
    n∉dom m1 -> 
    {{{ ishashmap hm m1 m2 ∗
          ⧖ (1+ (hashmap_size m2/(S val_size))%R) }}}
      insert_elem hm #n  @ E
      {{{ (off:nat), RET #off;
          ishashmap hm (<[n:=off]>m1) (<[off:=(m2!!!off)++n::[]]>m2) }}}.
  Proof.
    iIntros (Hnotin Φ) "[(%&%&->&H1&H2&%) Hx] HΦ".
    rewrite /insert_elem.
    wp_pures.
    iDestruct (etc_split with "[$]") as "[Hx1 Hx2]".
    { simpl; lra. }
    { apply Rcomplements.Rdiv_le_0_compat; auto. rewrite /hashmap_size. apply SeriesC_ge_0'.
    intros. case_match; done. }
    wp_apply (wp_insert_tc _ _ _ _ _ _ (λ x, INR (if m2!!(fin_to_nat x) is Some l then length l else 0%nat) ) with "[$Hx2 $H1]").
    { apply not_elem_of_dom_1. done. }
    { rewrite SeriesC_scal_l. rewrite Rdiv_1_l Rmult_comm Rdiv_def.
      f_equal. }
    { intros; case_match; auto. }
    iIntros (v) "(%v'&Hx&<-&H1)".
    wp_pures. iDestruct "H2" as "(%&%&->&Ha&%Hlen&K)".
    wp_pures.
    assert (∃ l, arr!!fin_to_nat v'=Some l) as [? Heqn].
    { apply lookup_lt_is_Some_2. pose proof fin_to_nat_lt v'; lia. }
    wp_apply (wp_load_offset with "[$Ha]"); first done.
    { simpl. case_bool_decide; done. }
    iIntros "Ha".
    wp_pures. wp_pure with "Hx1".
    wp_pures.
    erewrite (seq_split (fin_to_nat v')); last first.
    { split; auto; lia. }
    rewrite big_sepL_app big_sepL_cons.
    iDestruct "K" as "(K1&(%&%&%H1&K&%H2&%H3)&K2)".
    assert (x=v) as ->.
    { naive_solver. }
    wp_apply (wp_insert_new with "[K Hx]"); [|rewrite H2; iFrame|].
    { intros ?. exfalso. apply not_elem_of_dom_1 in Hnotin. naive_solver. }
    iIntros (l) "Hl".
    wp_pures.
    wp_apply (wp_store_offset with "[$Ha]").
    { done. }
    { simpl. case_bool_decide; done. }
    iIntros "Ha".
    wp_pures.
    iModIntro. iApply "HΦ".
    iExists _, _. iSplit; first done. iFrame.
    iSplit; last first.
    { iPureIntro. intros k v1 l1 Hm2 Hl1.
      rewrite lookup_insert_Some in Hm2. destruct Hm2 as [[-> Hm2] | [Hv Hm2]]; subst.
      - rewrite elem_of_app in Hl1. destruct Hl1.
        + rewrite lookup_insert_Some. right. split.
          * intros ->. apply Hnotin. rewrite elem_of_dom. erewrite H; [done|..|done].
            apply lookup_lookup_total. destruct (m2!!k) eqn :Heq'; first done.
            rewrite lookup_total_correct_2 in H0; [set_solver|done].
          * eapply H; last done. apply lookup_lookup_total. destruct (m2!!k) eqn :Heq'; first done.
            rewrite lookup_total_correct_2 in H0; [set_solver|done].
        + rewrite lookup_insert_Some. set_solver.
      - rewrite lookup_insert_Some. right. split.
        + intros ->. eapply H in Hm2; last done. apply Hnotin. apply elem_of_dom.
          rewrite Hm2. done.
        + naive_solver.
    }
    iExists _, _.
    iFrame. iSplit; first done.
    iSplit.
    { iPureIntro. rewrite insert_length. done. } 
    rewrite (seq_split (fin_to_nat v') (S _)); last first.
    { split; auto; lia. }
    rewrite big_sepL_app big_sepL_cons.
    iSplitL "K1".
    { iApply big_sepL_mono; last done. simpl.
      iIntros (k y H') "(%&%&%&Hl&%&%)".
      iExists _, _. iFrame.
      iPureIntro. split.
      - eapply list_lookup_insert_Some; right; split; try done.
        intros <-. apply elem_of_list_lookup_2 in H'. rewrite elem_of_seq in H'. lia.
      - split; last done. eapply lookup_insert_Some; right; split; try done.
        intros <-. apply elem_of_list_lookup_2 in H'. rewrite elem_of_seq in H'. lia.
    }
    iSplitL "Hl".
    { iExists _, _. iFrame. iPureIntro. split.
      - apply list_lookup_insert. by rewrite Hlen.
      - rewrite lookup_insert. f_equal. split; first (repeat f_equal; by apply lookup_total_correct).
        rewrite NoDup_app. split; first set_solver. split; last apply NoDup_singleton.
        intros ???. assert (x=n) as -> by set_solver. eapply H in H2; last done.
        apply Hnotin. rewrite elem_of_dom. naive_solver.
    }
    iApply big_sepL_mono; last done. simpl.
    iIntros (k y H') "(%&%&%&Hl&%&%)".
    iExists _, _. iFrame.
    iPureIntro. split.
    - eapply list_lookup_insert_Some; right; split; try done.
      intros <-. apply elem_of_list_lookup_2 in H'. rewrite elem_of_seq in H'. lia.
    - split; last done. eapply lookup_insert_Some; right; split; try done.
      intros <-. apply elem_of_list_lookup_2 in H'. rewrite elem_of_seq in H'. lia.
  Qed.

  
  Lemma wp_hm_lookup_new E hm m1 m2 (n : nat) :
    n∉dom m1 -> 
    {{{ ishashmap hm m1 m2 ∗
          ⧖ (1+ (hashmap_size m2/(S val_size))%R) }}}
      lookup_elem hm #n  @ E
      {{{ RET #false;
         ∃ off, ishashmap hm (<[n:=off]>m1) m2 }}}.
  Proof.
    iIntros (Hnotin Φ) "[(%&%&->&H1&H2&%) Hx] HΦ".
    rewrite /lookup_elem.
    wp_pures.
    iDestruct (etc_split with "[$]") as "[Hx1 Hx2]".
    { simpl; lra. }
    { apply Rcomplements.Rdiv_le_0_compat; auto. rewrite /hashmap_size. apply SeriesC_ge_0'.
    intros. case_match; done. }
    wp_apply (wp_insert_tc _ _ _ _ _ _ (λ x, INR (if m2!!(fin_to_nat x) is Some l then length l else 0%nat) ) with "[$Hx2 $H1]").
    { apply not_elem_of_dom_1. done. }
    { rewrite SeriesC_scal_l. rewrite Rdiv_1_l Rmult_comm Rdiv_def.
      f_equal. }
    { intros; case_match; auto. }
    iIntros (v) "(%v'&Hx&<-&H1)".
    wp_pures. iDestruct "H2" as "(%&%&->&Ha&%Hlen&K)".
    wp_pures.
    assert (∃ l, arr!!fin_to_nat v'=Some l) as [? Heqn].
    { apply lookup_lt_is_Some_2. pose proof fin_to_nat_lt v'; lia. }
    wp_apply (wp_load_offset with "[$Ha]"); first done.
    { simpl. case_bool_decide; done. }
    iIntros "Ha".
    wp_pures. wp_pure with "Hx1".
    wp_pures.
    erewrite (seq_split (fin_to_nat v')); last first.
    { split; auto; lia. }
    rewrite big_sepL_app big_sepL_cons.
    iDestruct "K" as "(K1&(%&%&%H1&K&%H2&%H3)&K2)".
    assert (x=v) as ->.
    { naive_solver. }
    wp_apply (wp_lookup_notin with "[K Hx]"); [|rewrite H2; iFrame|].
    { intros ?. exfalso. apply not_elem_of_dom_1 in Hnotin. naive_solver. }
    iIntros "Hl". iApply "HΦ".
    iExists _, _, _. iSplit; first done. iFrame.
    iSplit; last first.
    { iPureIntro. intros k v1 l1 Hm2 Hl1. rewrite lookup_insert_Some.
      destruct (decide (n=v1)).
      { subst. left. split; first done. eapply H in Hm2; last done. exfalso. apply Hnotin.
        rewrite elem_of_dom. done. }
      naive_solver.
    }
    iExists _, _. iSplit; first done. iSplitL "Ha"; first done.
    iSplit; first done.
    rewrite (seq_split (fin_to_nat v') (S _)); last first.
    { split; auto; lia. }
    rewrite big_sepL_app big_sepL_cons. iFrame.
    iExists _, _. iFrame. iPureIntro. by split.
  Qed.
  
  
  
End hashmap.
