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
      ("l" +ₗ "off") <- insert "w" "v"
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
      {{{ RET #();
          ∃ (off:fin(S val_size)),
          ishashmap hm (<[n:=fin_to_nat off]>m1) (<[fin_to_nat off:=(m2!!!fin_to_nat off)++n::[]]>m2) }}}.
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
    iApply "HΦ".
    iExists _, _, _. iSplit; first done. iFrame.
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
          ∃ (off:fin(S val_size)), ishashmap hm (<[n:=fin_to_nat off]>m1) m2 }}}.
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
  
  


  (** Amortized version *)
  Variable MAXSIZE:nat.
  Definition amortized_tc:=((MAXSIZE-1)/2/(S val_size))%R.
  Definition isamortizedhashmap hm m1 m2 n:=
    (ishashmap hm m1 m2 ∗
     ⌜INR n=hashmap_size m2⌝ ∗
     ⌜n<=MAXSIZE⌝ ∗
     ⧖ (n*(amortized_tc-(n-1)/2/(S val_size)))
    )%I.

  
  Local Lemma amortized_tc_split (s:nat):
    s < MAXSIZE ->
    (INR s * (amortized_tc - (INR s - 1) / 2 / INR (S val_size)) + (1 + amortized_tc))%R =
    (1 + INR s / INR (S val_size) + INR (S s) * (amortized_tc - INR s / 2 / INR (S val_size)))%R.
  Proof.
    intros Hineq.
    rewrite (S_INR s).
    cut ( (s * (- (s - 1) / 2 / S val_size))%R =
          (s / S val_size - (s + 1) * (s / 2 / S val_size))%R); first lra.
    cut ((s * (- (s - 1) / S val_size))%R = (2*s / S val_size - (s + 1) * (s  / S val_size))%R); first lra.
    replace (s * (- (s - 1) / S val_size))%R with ((s*(1-s) / S val_size))%R; last lra.
    replace ((2 * s / S val_size - (s + 1) * (s / S val_size))%R) with ((2 * s - (s + 1) * s) / S val_size)%R; last lra.
    apply Rdiv_eq_compat_r. lra.
  Qed.
  
  Lemma wp_amortized_hm_insert_new E hm m1 m2 s (n : nat) :
    n∉dom m1 ->
    s<MAXSIZE->
    {{{ isamortizedhashmap hm m1 m2 s∗
          ⧖ (1+ (amortized_tc)%R) }}}
      insert_elem hm #n  @ E
      {{{ RET #(); ∃ off:fin(S val_size),
          isamortizedhashmap hm (<[n:=fin_to_nat off]>m1) (<[fin_to_nat off:=(m2!!!fin_to_nat off)++n::[]]>m2) (S s) }}}.
  Proof.
    iIntros (Hnotin Hsize Φ) "[H Hx1] HΦ".
    iDestruct "H" as "(H&%H&%&Hx2)".
    iAssert (⧖ (1+ (hashmap_size m2/(S val_size))%R)∗⧖ ((S s) * (amortized_tc - (s) / 2 / S val_size)))%I with "[Hx1 Hx2]" as "[Hx1 Hx2]".
    { iDestruct (etc_combine with "[$]") as "Hx".
      iApply etc_split.
      - apply Rplus_le_le_0_compat; first lra. apply Rcomplements.Rdiv_le_0_compat; auto.
        apply SeriesC_ge_0'. intros. auto.
      - apply Rmult_le_pos; auto. apply Rle_0_le_minus.
        rewrite /amortized_tc. rewrite !Rdiv_def. repeat apply Rmult_le_compat_r.
        + rewrite -Rdiv_1_l. apply Rcomplements.Rdiv_le_0_compat; try lra. auto.
        + lra.
        + rewrite Rcomplements.Rle_minus_r. rewrite -S_INR. apply le_INR. lia.
      - iApply etc_irrel; last done. rewrite -H. apply amortized_tc_split. done.
    }
    iApply (wp_hm_insert_new with "[$]"); first done.
    iModIntro. iIntros "(% & ?)". iApply "HΦ". rewrite /isamortizedhashmap. iExists _. iFrame.
    repeat iSplit.
    - iPureIntro. rewrite S_INR. erewrite <-(SeriesC_singleton' off 1%R).
      rewrite H. rewrite /hashmap_size. rewrite -SeriesC_plus; try apply ex_seriesC_finite.
      apply SeriesC_ext. intros.
      case_match eqn: H1; case_bool_decide as H2; subst.
      + rewrite lookup_insert. rewrite app_length. simpl. erewrite lookup_total_correct; last done.
        rewrite plus_INR. done.
      + rewrite lookup_insert_ne; last first.
        { intros K. apply fin_to_nat_inj in K. done. }
        rewrite H1. lra.
      + rewrite lookup_insert. rewrite app_length. simpl. erewrite lookup_total_correct_2; last done.
        rewrite plus_INR. done.
      + rewrite lookup_insert_ne; last first.
        { intros K. apply fin_to_nat_inj in K. done. }
        rewrite H1. lra.
    - iPureIntro; lia.
    - replace (S _ - 1)%R with (INR s); first done.
      rewrite S_INR. lra.
  Qed.
                                                                                                           
End hashmap.
