(** Fisher-Yates samples permutations uniformly, in total Eris. *)

From clutch.common Require Import inject.
From clutch.eris Require Export eris total_weakestpre total_primitive_laws.
From clutch.eris Require Import total_adequacy.
From clutch.prob_lang.gwp Require Export list.
From clutch.prob_lang Require Import lang notation tactics metatheory.

Set Default Proof Using "Type*".


Definition fisher_yates_loop : val :=
  rec: "loop" "l" "i" :=
    if: "i" ≤ #0
    then "l"
    else
      let: "j" := rand "i" in
      let: "l'" := list_swap "l" "i" "j" in
      "loop" "l'" ("i" - #1).

Definition fisher_yates : val :=
  λ: "l",
    let: "i" := list_length "l" - #1 in
    fisher_yates_loop "l" "i".


(* ========================================================================== *)
(* Pure list/permutation and credit lemmas                                    *)
(* ========================================================================== *)

Lemma permutation_insert_swap {B : Type} (l : list B) (i j : nat) (x y : B) :
  l !! i = Some x ->
  l !! j = Some y ->
  l ≡ₚ (<[i := y]>(<[j := x]> l)).
Proof.
  intros Hi Hj.
  pose proof (lookup_lt_Some _ _ _ Hi) as Hlen1.
  pose proof (lookup_lt_Some _ _ _ Hj) as Hlen2.
  erewrite <- (list_insert_id l j) at 1; eauto.
  erewrite <- (list_insert_id l i) at 1; eauto.
  clear Hi Hj.
  revert x y i j Hlen1 Hlen2.
  induction l; intros x y i j Hlen1 Hlen2; auto.
  destruct i as [|i']; destruct j as [|j']; auto.
  - simpl; auto.
    simpl in Hlen2.
    rewrite insert_take_drop; [|lia].
    rewrite insert_take_drop; [|lia].
    rewrite Permutation_middle.
    rewrite Permutation_middle.
    rewrite Permutation_swap //.
  - simpl; auto.
    simpl in Hlen1.
    rewrite insert_take_drop; [|lia].
    rewrite insert_take_drop; [|lia].
    rewrite Permutation_middle.
    rewrite Permutation_middle.
    rewrite Permutation_swap //.
  - simpl.
    simpl in Hlen1.
    simpl in Hlen2.
    rewrite IHl; auto; lia.
Qed.

Lemma permutation_drop_one_eq {B : Type} (l lav : list B) :
  l ≡ₚ lav ->
  NoDup l ->
  0 < length l ->
  drop 1 l = drop 1 lav ->
  l = lav.
Proof.
  intros Hperm Hdup Hnonempty Hdrop.
  destruct l as [|x xs]; first (simpl in Hnonempty; lia).
  destruct lav as [|y ys].
  { pose proof (Permutation_length Hperm); simpl in *; lia. }
  simpl in Hdrop. unfold drop in Hdrop. subst ys.
  assert (x ∈ y :: xs) as Hmem.
  { rewrite -Hperm. constructor. }
  inversion Hdup as [|? ? Hnotin Hdupxs]; subst.
  simpl in Hmem.
  inversion Hmem ; subst ; first done.
  exfalso ; by apply Hnotin.
Qed.

Lemma lookup_before_equal_suffix {B : Type}
    (l lav : list B) (i k : nat) (a : B) :
  NoDup lav ->
  lav !! i = Some a ->
  l !! k = Some a ->
  drop (S i) l = drop (S i) lav ->
  k <= i.
Proof.
  intros Hdup Ha Hk Hsuffix.
  destruct (le_dec k i) as [Hle|Hnle]; first done.
  assert (S i <= k) as Hik by lia.
  assert (drop (S i) l !! (k - S i) = Some a) as Hdropk.
  {
    rewrite lookup_drop.
    replace (S i + (k - S i)) with k by lia.
    exact Hk.
  }
  rewrite Hsuffix in Hdropk.
  rewrite lookup_drop in Hdropk.
  replace (S i + (k - S i)) with k in Hdropk by lia.
  pose proof (NoDup_lookup lav i k a Hdup Ha Hdropk) as Heq.
  lia.
Qed.

Definition fy_miss_credit (n : nat) : R := / INR (fact n).
Definition fy_hit_credit (n : nat) : R := 1 - fy_miss_credit n.

Lemma fy_miss_credit_pos n :
  (0 < fy_miss_credit n)%R.
Proof.
  rewrite /fy_miss_credit.
  apply Rinv_0_lt_compat.
  apply lt_0_INR, Nat.neq_0_lt_0, fact_neq_0.
Qed.

Lemma fy_miss_credit_le_1 n :
  (fy_miss_credit n <= 1)%R.
Proof.
  assert (Hpos : (0 < INR (fact n))%R).
  { apply lt_0_INR, Nat.neq_0_lt_0, fact_neq_0. }
  apply (Rmult_le_reg_r (INR (fact n))); first exact Hpos.
  rewrite /fy_miss_credit Rinv_l; last lra.
  rewrite Rmult_1_l.
  change (INR 1 <= INR (fact n))%R.
  apply le_INR.
  pose proof (fact_neq_0 n).
  lia.
Qed.

Lemma fy_hit_credit_range n :
  (0 <= fy_hit_credit n <= 1)%R.
Proof.
  rewrite /fy_hit_credit.
  pose proof (fy_miss_credit_pos n).
  pose proof (fy_miss_credit_le_1 n).
  lra.
Qed.

Lemma fy_miss_credit_step n :
  (fy_miss_credit (S n) * INR (S n) = fy_miss_credit n)%R.
Proof.
  rewrite /fy_miss_credit.
  rewrite (fact_simpl n) mult_INR.
  rewrite Rinv_mult.
  rewrite Rmult_assoc.
  rewrite (Rmult_comm (/ INR (fact n)) (INR (S n))).
  rewrite -Rmult_assoc.
  rewrite Rinv_l.
  - by rewrite Rmult_1_l.
  - apply not_0_INR. lia.
Qed.

Lemma fy_hit_credit_step n :
  ((INR (S n) + fy_hit_credit (S n)) / INR (S (S n))
     = fy_hit_credit (S (S n)))%R.
Proof.
  rewrite /fy_hit_credit.
  assert (Hnz : (INR (S (S n)) ≠ 0%R)) by (apply not_0_INR; lia).
  field_simplify_eq ; last apply Hnz.
  rewrite Rmult_comm.
  rewrite -Rplus_minus_swap. replace (S n + 1)%R with (INR (S (S n))) by real_solver.
  field_simplify_eq.
  rewrite Rplus_comm. rewrite Rminus_def.
  apply Rplus_eq_compat_l. rewrite Rmult_comm.
  rewrite Ropp_mult_distr_r_reverse.
  rewrite fy_miss_credit_step.
  reflexivity.
Qed.


(* ========================================================================== *)
(* Fisher--Yates total avoid specification                                    *)
(* ========================================================================== *)

Section fisher_yates.
  Context `{!erisGS Σ}.
  Context `[!Inject A val].

  Lemma twp_fisher_yates_avoid_loop E l lav lv i:
    l ≡ₚ lav ->
      [[{ ⌜is_list l lv ⌝ ∗ ⌜i<length l⌝ ∗ ⌜ NoDup l ⌝ ∗
          (↯ (1/ fact (i+1)) ∨ ⌜drop (S i) l ≠ drop (S i) lav ⌝)  }]]
      fisher_yates_loop lv #i@E
      [[{ v, RET v; ∃ l', ⌜is_list l' v⌝ ∗ ⌜l' ≡ₚ l⌝ ∗ ⌜l' ≠ lav⌝ }]].
  Proof.
    iIntros (Hperm Φ) "(%Hl&%Hlen&%Hdup&Herr) HΦ".
    iInduction i as [|i'] "IH" forall (l lav lv Φ Hperm Hl Hlen Hdup) "Herr HΦ"; rewrite /fisher_yates_loop; wp_pures.
    {
      iModIntro. iApply "HΦ".
      iDestruct "Herr" as "[Herr | %Hdiff]".
      - iDestruct (ec_contradict with "[Herr]") as "?"; auto.
        simpl; lra.
      - iExists l.
        iSplit; auto.
        iSplit; auto.
        iPureIntro.
        by intros ->.
    }
    iDestruct "Herr" as "[Herr | %Hdiff]".

    - (* We have error credit.  Pick the position in [l] of the element
         that [lav] has at the position currently being fixed. *)
      pose proof (Permutation_length Hperm) as Hlenperm.
      assert (S i' < length lav) as Hlenlav by lia.
      destruct (lookup_lt_is_Some_2 lav (S i') Hlenlav) as [a Ha].
      assert (a ∈ l) as Hain.
      { rewrite Hperm. by eapply list_elem_of_lookup_2. }
      apply list_elem_of_lookup in Hain as [k Hk].
      wp_apply (twp_rand_err_amp_nat _ _ k); iFrame.
      iIntros (x) "(%Hnleq & [%Hneq | Herr])".
      + (* We did not draw [k].  Hence position [S i'] becomes different
           from the corresponding position of [lav]. *)
        wp_pures. wp_apply (gwp_list_swap (g := eris_twp_genwp)).
        { repeat iSplit; try done. iPureIntro. lia. }
        iIntros (lv') "(%xi & %xj & %H1 & %H2 & %Hlv')".
        do 3 wp_pure.
        replace (_-_)%Z with (Z.of_nat i'); last lia.
        wp_apply ("IH" $! (<[S i' := xj]> (<[x := xi]> l)) lav with "[][][][]").
        * iPureIntro. transitivity l; last exact Hperm.
          symmetry. by apply permutation_insert_swap.
        * iPureIntro. exact Hlv'.
        * iPureIntro. rewrite !length_insert. lia.
        * iPureIntro.
          eapply NoDup_ListNoDup, Permutation_NoDup ; last eapply NoDup_ListNoDup, Hdup.
          by apply permutation_insert_swap.
        * iRight. iPureIntro. intros Heq.
          (* Equality of the suffixes would in particular imply that the new value at [S i'] is [a]. *)
          assert (xj = a) as Hxja.
          {
            pose proof (f_equal (λ xs, xs !! 0) Heq) as Hlookup.
            rewrite !lookup_drop in Hlookup.
            simpl in Hlookup. rewrite Nat.add_0_r in Hlookup.
            rewrite list_lookup_insert_eq in Hlookup ; [|rewrite length_insert; lia].
            rewrite Ha in Hlookup. by simplify_eq.
          }

          (* But [xj] came from position [x], whereas [a] occurs at [k].
             NoDup therefore forces [x = k], contradicting [Hneq]. *)
          assert (l !! x = Some a) as Hxa by rewrite -Hxja => //.
          apply Hneq.
          exact (NoDup_lookup l x k a Hdup Hxa Hk).
        * iIntros (v) "(%l' & %Hl' & %Hperm' & %Hneq')".
          iApply "HΦ".
          iExists l'.
          iSplit.
          { iPureIntro. exact Hl'. }
          iSplit.
          { iPureIntro.
            transitivity (<[S i' := xj]> (<[x := xi]> l)); first exact Hperm'.
            symmetry. by apply permutation_insert_swap. }
          by iPureIntro.

      + (* Exceptional draw: retain the amplified credit and continue. *)
        wp_pures. wp_apply (gwp_list_swap (g := eris_twp_genwp)).
        { repeat iSplit; try done. iPureIntro. lia. }
        iIntros (lv') "(%xi & %xj & %H1 & %H2 & %Hlv')".
        do 3 wp_pure.
        replace (_-_)%Z with (Z.of_nat i'); last lia.
        wp_apply ("IH" $! (<[S i' := xj]> (<[x := xi]> l)) lav with "[][][][][Herr]").
        * iPureIntro. transitivity l; last exact Hperm. symmetry. by apply permutation_insert_swap.
        * iPureIntro. exact Hlv'.
        * iPureIntro. rewrite !length_insert. lia.
        * iPureIntro.
          eapply NoDup_ListNoDup, Permutation_NoDup; last eapply NoDup_ListNoDup, Hdup.
          by apply permutation_insert_swap.
        * iLeft. iApply (ec_eq with "Herr").
          (* (1/(i'+2)!) * (i'+2) = 1/(i'+1)! *)
          rewrite !Nat.add_1_r.
          rewrite -(S_INR (S i')).
          rewrite (fact_simpl (S i')) mult_INR.
          rewrite /Rdiv !Rmult_1_l Rinv_mult.
          rewrite (Rmult_comm (/ INR (S (S i'))) (/ INR (fact (S i')))).
          rewrite Rmult_assoc Rinv_l.
          { by rewrite Rmult_1_r. }
          apply not_0_INR. lia.
        * iIntros (v) "(%l' & %Hl' & %Hperm' & %Hneq')".
          iApply "HΦ".
          iExists l'.
          iSplit.
          { iPureIntro. exact Hl'. }
          iSplit.
          { iPureIntro. transitivity (<[S i' := xj]> (<[x := xi]> l)); first exact Hperm'.
            symmetry. by apply permutation_insert_swap. }
          by iPureIntro.

    - (* The already-fixed suffix differs from [lav].  Any swap performed
         at indices <= S i' leaves the still-later suffix unchanged. *)
      wp_apply twp_rand; auto.
      iIntros (n) "?". wp_pures. wp_apply (gwp_list_swap (g := eris_twp_genwp)).
      { repeat iSplit; try done. iPureIntro. pose proof (fin_to_nat_lt n). lia. }
      iIntros (lv') "(%xi & %xj & %H1 & %H2 & %Hlv')".
      do 3 wp_pure.
      replace (_-_)%Z with (Z.of_nat i'); last lia.

      wp_apply ("IH" $! (<[S i' := xj]> (<[fin_to_nat n := xi]> l)) lav with "[][][][]").
      * iPureIntro. transitivity l; last exact Hperm. symmetry. by apply permutation_insert_swap.
      * iPureIntro. exact Hlv'.
      * iPureIntro. rewrite !length_insert. lia.
      * iPureIntro.
        eapply NoDup_ListNoDup, Permutation_NoDup; last eapply NoDup_ListNoDup, Hdup.
        by apply permutation_insert_swap.
      * iRight. iPureIntro. intros Heq. apply Hdiff.

        (* Drop one more element from the alleged equal suffixes.
           Both swap positions are before that point, so the deeper
           suffix of the swapped list is exactly the deeper suffix of l. *)
        pose proof (f_equal (drop 1) Heq) as Heq'.
        rewrite !drop_drop in Heq'.
        rewrite !Nat.add_1_r in Heq'.
        rewrite drop_insert_lt in Heq'; [|lia].
        rewrite drop_insert_lt in Heq'; [|pose proof (fin_to_nat_lt n); lia].
        exact Heq'.
      * iIntros (v) "(%l' & %Hl' & %Hperm' & %Hneq')".
        iApply "HΦ".
        iExists l'.
        iSplit.
        { iPureIntro. exact Hl'. }
        iSplit.
        2: by iPureIntro.
        iPureIntro.
        transitivity (<[S i' := xj]> (<[fin_to_nat n := xi]> l)) => //.
        symmetry. by apply permutation_insert_swap.
  Qed.

  Lemma twp_fisher_yates_avoid E l lav lv:
    l ≡ₚ lav ->
    [[{ ⌜is_list l lv ⌝ ∗ ⌜NoDup l⌝ ∗ ↯ (1/ (fact (length l)))}]]
      fisher_yates lv @E
      [[{ v, RET v; ∃ l', ⌜is_list l' v⌝ ∗ ⌜l' ≡ₚ l⌝ ∗ ⌜l' ≠ lav⌝ }]].
  Proof.
    iIntros (Hperm Φ) "[% [% Hx]] HΦ".
    rewrite /fisher_yates.
    wp_pures.
    wp_apply (gwp_list_length (g := eris_twp_genwp)); first done.
    iIntros (? ->).
    wp_pures.
    destruct (decide (length l = 0)) as [->|].
    { rewrite /fisher_yates_loop. wp_pures.
      rewrite /= Rdiv_1_r.
      iDestruct (ec_contradict with "Hx") as "?"; auto.
      lra.
    }
    replace (_-_)%Z with (Z.of_nat (length l - 1)) by lia.
    wp_apply (twp_fisher_yates_avoid_loop with "[Hx]"); last done; auto.
    repeat iSplit; try done.
    { iPureIntro. lia. }
    iLeft.
    replace (length l - 1 + 1) with (length l) by lia.
    iFrame.
  Qed.


(* ========================================================================== *)
(* Total hit specification                                                    *)
(* ========================================================================== *)

Lemma twp_rand_force_nat E (N k : nat) (eps : R) :
  k <= N ->
  (0 <= eps <= 1)%R ->
  [[{ ↯ ((INR N + eps) / INR (S N)) }]]
    rand #N @ E
  [[{ v, RET v; ⌜v = #k⌝ ∗ ↯ eps }]].
Proof.
  iIntros (Hk [Heps0 Heps1] Φ) "Herr HΦ".
  assert (Hk' : k < S N) by lia.
  set (kf := Fin.of_nat_lt Hk' : fin (S N) ).
  set (ε2 := λ x : fin (S N), if bool_decide (x = kf) then eps else 1).
  (* First calculate the sum of the constant function [1] over [fin (S N)]. *)
  assert (Hones : SeriesC (λ _ : fin (S N), 1%R) = INR (S N)).
  {
    erewrite
      (SeriesC_ext _
        (λ x, if bool_decide (x ∈ enum (fin (S N))) then 1 else 0));
      last first.
    { intros x. rewrite bool_decide_eq_true_2; first done. apply elem_of_enum. }
    rewrite SeriesC_list_1.
    - rewrite -/(card (fin (S N))). by rewrite fin_card.
    - apply NoDup_enum.
  }
  (* There are [S N] outcomes altogether.  Start with one credit at
     every outcome, and change the distinguished outcome [kf] from
     [1] to [eps]:       sum ε2 = (N+1) + (eps-1) = N + eps. *)
  assert (Hsum : SeriesC ε2 = (INR N + eps)%R).
  {
    erewrite
      (SeriesC_ext _
        (λ x, (1 + (if bool_decide (x = kf) then eps - 1 else 0))%R));
      last first.
    { intros x. rewrite /ε2. case_bool_decide; real_solver. }

    rewrite SeriesC_plus.
    - rewrite Hones. rewrite (SeriesC_singleton kf (eps - 1)).
      rewrite S_INR. lra.
    - apply ex_seriesC_finite.
    - apply ex_seriesC_finite.
  }
  (* This is precisely the expectation required by [twp_rand_exp_fin1]. *)
  assert (Havg : SeriesC (λ x : fin (S N), (1 / (S N)) * ε2 x)%R = ((INR N + eps) / INR (S N))%R).
  1: rewrite SeriesC_scal_l Hsum /Rdiv Rmult_1_l ; apply Rmult_comm.
  assert (Hε2 : ∀ x, (0 <= ε2 x)%R)
    by (intros x ; rewrite /ε2 ; case_bool_decide ; real_solver).
  assert (HN : TCEq N (Z.to_nat (Z.of_nat N))) by by rewrite Nat2Z.id.
  wp_apply (twp_rand_exp_fin1 N (Z.of_nat N) E
              ((INR N + eps) / INR (S N)) ε2 HN Hε2 Havg with "Herr").
  iIntros (x) "Herr".
  rewrite /ε2. case_bool_decide as Hx.
  - (* The distinguished outcome. *)
    subst x. iApply "HΦ". iFrame. iPureIntro. f_equal.
    rewrite /kf. do 2 f_equal. apply fin_to_nat_to_fin.
  - (* Every other outcome has one full error credit. *)
    iExFalso. iApply (ec_contradict with "Herr"). real_solver.
Qed.


Lemma twp_fisher_yates_hit_loop E l lav lv i :
  l ≡ₚ lav ->
  [[{ ⌜is_list l lv⌝ ∗
      ⌜i < length l⌝ ∗
      ⌜NoDup l⌝ ∗
      ⌜drop (S i) l = drop (S i) lav⌝ ∗
      ↯ (fy_hit_credit (i + 1)) }]]
    fisher_yates_loop lv #i @ E
  [[{ v, RET v; ⌜is_list lav v⌝ }]].
Proof.
  iIntros (Hperm Φ) "(%Hl & %Hlen & %Hdup & %Hsuffix & Herr) HΦ".
  iInduction i as [|i'] "IH"
    forall (l lav lv Φ Hperm Hl Hlen Hdup Hsuffix)
    "Herr HΦ";
    rewrite /fisher_yates_loop; wp_pures.
  { assert (0 < length l) by lia.
    assert (l = lav) as -> by (eapply permutation_drop_one_eq; eauto).
    by iApply "HΦ". }

  pose proof (Permutation_length Hperm) as Hlenperm.
  assert (S i' < length lav) as Hlenlav by lia.
  destruct (lookup_lt_is_Some_2 lav (S i') Hlenlav) as [a Ha].
  assert (a ∈ l) as Hain.
  { rewrite Hperm. by eapply list_elem_of_lookup_2. }
  apply list_elem_of_lookup in Hain as [k Hk].

  assert (NoDup lav) as Hduplav.
  { eapply NoDup_ListNoDup, Permutation_NoDup.
    2: eapply NoDup_ListNoDup, Hdup. exact Hperm. }

  assert (k <= S i') as Hkbound by (eapply lookup_before_equal_suffix ; eauto).

  (* Convert the loop credit into exactly the force-one-outcome credit. *)
  assert (fy_hit_credit (S i' + 1) = ((INR (S i') + fy_hit_credit (S i')) /
             INR (S (S i')))%R) as ->.
  { rewrite /fy_hit_credit.
    replace (S i' + 1)%nat with (S (S i')) by lia.
    symmetry. apply fy_hit_credit_step. }

  wp_apply (twp_rand_force_nat _ _ k (fy_hit_credit (S i')) with "[Herr]") ;
    [lia| | iFrame "Herr" |].
  1: apply fy_hit_credit_range.

  iIntros (x) "(-> & Herr)". wp_pures. wp_apply gwp_list_swap.
  { repeat iSplit; try done. iPureIntro. lia. }
  iIntros (lv') "(%xi & %xj & %H1 & %H2 & %Hlv')".

  assert (xj = a) as Hxja.
  { rewrite Hk in H2. by simplify_eq. }
  do 3 wp_pure.
  replace (_ - _)%Z with (Z.of_nat i'); last lia.
  set (l' := <[S i' := xj]> (<[k := xi]> l)).
  assert (Hperm_swap : l' ≡ₚ l).
  { unfold l'. symmetry. by apply permutation_insert_swap. }

  assert (Hsuffix' : drop (S i') l' = drop (S i') lav).
  {
    apply list_eq.
    intros [|j].
    - rewrite !lookup_drop /= !Nat.add_0_r.
      unfold l'.
      rewrite list_lookup_insert_eq;
        [|rewrite length_insert; lia].
      rewrite Ha Hxja.
      done.
    - rewrite !lookup_drop.
      unfold l'.
      rewrite list_lookup_insert_ne; [|lia].
      rewrite list_lookup_insert_ne; [|lia].
      pose proof (f_equal (λ xs, xs !! j) Hsuffix) as Hj.
      rewrite !lookup_drop in Hj.
      replace (S (S i') + j)%nat with (S i' + S j)%nat in Hj by lia.
      exact Hj.
  }

  wp_apply ("IH" $! l' lav lv' with "[][][][][][Herr]").
  - iPureIntro.
    transitivity l; first exact Hperm_swap.
    exact Hperm.
  - iPureIntro. exact Hlv'.
  - iPureIntro.
    unfold l'. rewrite !length_insert. lia.
  - iPureIntro.
    eapply NoDup_ListNoDup, Permutation_NoDup;
      last eapply NoDup_ListNoDup, Hdup.
    symmetry. exact Hperm_swap.
  - iPureIntro. exact Hsuffix'.
  - replace (i'+1) with (S i') by lia. iFrame.
  - iIntros (v) "%Hv".
    by iApply "HΦ".
Qed.

Lemma twp_fisher_yates_hit E l lav lv :
  l ≡ₚ lav ->
  [[{ ⌜is_list l lv⌝ ∗
      ⌜NoDup l⌝ ∗
      ↯ (fy_hit_credit (length l)) }]]
    fisher_yates lv @ E
  [[{ v, RET v; ⌜is_list lav v⌝ }]].
Proof.
  iIntros (Hperm Φ) "(%Hl & %Hdup & Herr) HΦ".
  rewrite /fisher_yates.
  wp_pures.
  wp_apply (gwp_list_length (g := eris_twp_genwp)); first done.
  iIntros (? ->).
  wp_pures.

  destruct (decide (length l = 0)) as [Hnil|Hnonempty].
  - apply nil_length_inv in Hnil. subst l.
    pose proof (Permutation_length Hperm) as Hlav.
    simpl in Hlav. symmetry in Hlav.
    apply nil_length_inv in Hlav. subst lav.
    rewrite /fisher_yates_loop. wp_pures.
    iApply "HΦ". done.
  - replace (_ - _)%Z with (Z.of_nat (length l - 1)) by lia.
    wp_apply
      (twp_fisher_yates_hit_loop
         _ l lav lv (length l - 1)
         with "[Herr]"); [exact Hperm| |].
    + repeat iSplit; try done.
      * iPureIntro. lia.
      * iPureIntro.
        replace (S (length l - 1)) with (length l) by lia.
        rewrite {2}(Permutation_length Hperm).
        rewrite !drop_all.
        done.
      * replace (length l - 1 + 1)%nat with (length l) by lia.
        iFrame.
    + iIntros (v) "%".
      by iApply "HΦ".
Qed.


End fisher_yates.

(* ========================================================================== *)
(* Semantic adequacy: exact point masses                                      *)
(* ========================================================================== *)

Section fisher_yates_adequacy.

  Context `[!Inject A val].

  Local Instance fisher_yates_preG :
    adequacy.erisGpreS adequacy.erisΣ.
  Proof.
    apply adequacy.subG_erisGPreS.
    simpl. econstructor. reflexivity.
  Qed.

  Definition fy_returns (lav : list A) (v : val) : Prop :=
    is_list lav v.

  Lemma twp_prob_lim_exec
      (e : expr) (σ : state) (ε : R) (φ : val -> Prop) :
    (0 <= ε)%R ->
    (∀ `{!erisGS adequacy.erisΣ},
        ⊢ ↯ ε -∗ WP e [{ v, ⌜φ v⌝ }]) ->
    (1 - ε <=
       prob (lim_exec (e, σ))
         (λ v, bool_decide (φ v)))%R.
  Proof.
    intros Hε Hwp. exact (twp_tgl adequacy.erisΣ e σ ε φ Hε Hwp).
  Qed.

  Definition fy_uniform_mass (l lav : list A) : R :=
    if decide (l ≡ₚ lav) then / INR (fact (length l)) else 0.

  Theorem fisher_yates_uniform_point
      (l lav : list A) (lv : val) (σ : state) :
    NoDup l ->
    is_list l lv ->
    l ≡ₚ lav ->
    prob (lim_exec (fisher_yates lv, σ))
        (λ v, bool_decide (fy_returns lav v))
      = / INR (fact (length l)).
  Proof.
    intros Hdup Hl Hperm.

    assert (Hlower :
      (/ INR (fact (length l))
         <= prob (lim_exec (fisher_yates lv, σ))
              (λ v, bool_decide (fy_returns lav v)))%R).
    {
      pose proof (fy_hit_credit_range (length l)) as [Hcredit _].
      pose proof (twp_prob_lim_exec (fisher_yates lv) σ _ (fy_returns lav) Hcredit) as Hadequacy.

      assert (Htot :
               (1 - fy_hit_credit (length l)
                <= prob (lim_exec (fisher_yates lv, σ)) (λ v, bool_decide (fy_returns lav v)))%R).
      { apply Hadequacy. iIntros (HGS) "Herr". rewrite /fy_returns.
        iApply (twp_fisher_yates_hit _ l lav lv with "[$Herr]").
        1: exact Hperm.
        1,2: repeat iSplit; iPureIntro; intuition auto. }
      rewrite /fy_hit_credit /fy_miss_credit in Htot. lra.
    }

    assert ((prob (lim_exec (fisher_yates lv, σ)) (λ v, bool_decide (fy_returns lav v)) <= / INR (fact (length l)))%R)
      as Hupper.
    {
      assert (Heps : (0 <= / INR (fact (length l)))%R) by apply Rlt_le, fy_miss_credit_pos.

      (* [twp_pgl_lim] consumes the total avoid specification directly. *)
      assert (pgl (lim_exec (fisher_yates lv, σ)) (λ v, ∃ l', is_list l' v ∧ l' ≡ₚ l ∧ l' ≠ lav) (/ INR (fact (length l))))
        as Hpgl.
      {
        eapply (twp_pgl_lim adequacy.erisΣ).
        - exact Heps.
        - intros HGS.
          iIntros "Herr".
          iApply (twp_fisher_yates_avoid _ l lav lv with "[Herr]") => //.
          + rewrite /Rdiv Rmult_1_l. iFrame.
            repeat iSplit; done.
          + iIntros (v) "(%l' & %Hl' & %Hperm' & %Hneq)".
            iPureIntro. exists l'. naive_solver.
      }

      assert (pgl (lim_exec (fisher_yates lv, σ)) (λ v, ¬ fy_returns lav v) (/ INR (fact (length l))))
        as Hpgl_not.
      {
        eapply (pgl_mon_pred _ (λ v, ∃ l', is_list l' v ∧ l' ≡ₚ l ∧ l' ≠ lav)).
        - intros v (l' & Hl' & _ & Hneq).
          rewrite /fy_returns.
          intros Hlav.
          apply Hneq.
          by eapply is_list_inj.
        - exact Hpgl.
      }
      rewrite /pgl /prob in Hpgl_not |- *.
      etrans; last exact Hpgl_not.
      right.
      apply SeriesC_ext.
      intros v.
      repeat case_bool_decide; simpl; try done.
      all: exfalso; naive_solver.
    }
    lra.
  Qed.

  Corollary fisher_yates_is_uniform_over_permutations
      (l : list A) (lv : val) (σ : state) :
    NoDup l ->
    is_list l lv ->
    forall lav,
      l ≡ₚ lav ->
      prob (lim_exec (fisher_yates lv, σ))
        (λ v, bool_decide (fy_returns lav v))
      = fy_uniform_mass l lav.
  Proof.
    intros Hdup Hl lav Hperm.
    rewrite /fy_uniform_mass.
    destruct (decide (l ≡ₚ lav)) as [H|H]; last contradiction.
    by eapply fisher_yates_uniform_point.
  Qed.

End fisher_yates_adequacy.
