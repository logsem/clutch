From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia.
From clutch.eris Require Import eris.
From clutch.common Require Import inject.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling.fldr Require Import implementation model walk pure distribution list_total walk_spec round.
Import ListNotations.
#[local] Open Scope R.
Section Pos.
Context `{!erisGS Σ}.
Lemma prop_cond (ws : list nat) (i : nat) :
  admissible ws -> (i < length ws)%nat ->
  proposal_mass ws i =
    (INR (weight_sum ws) / INR (denominator ws)) * target_mass ws i.
Proof.
  intros Hadm Hi.
  rewrite <- (conditioned_original_mass ws i Hadm Hi).
  assert (Hw : ~ weight_sum ws = 0%nat) by
    (pose proof (admissible_weight_sum_pos ws Hadm) as Hpos; lia).
  assert (Hd : ~ denominator ws = 0%nat) by (pose proof (denominator_pos ws); lia).
  field; split; apply not_0_INR; assumption.
Qed.

Lemma proposal_split (ws : list nat) (D : nat -> R) (x : R) :
  admissible ws ->
  SeriesC (fun i => (proposal_mass ws i *
    (if i <? length ws then D i else x))%R) =
  ((INR (weight_sum ws) / INR (denominator ws)) *
    SeriesC (fun i => (target_mass ws i * D i)%R) +
    proposal_mass ws (length ws) * x)%R.
Proof.
  intros Hadm.
  rewrite (proposal_mass_expectation ws
    (fun i => (if i <? length ws then D i else x)%R)).
  assert (Hlen : length (extended_weights ws) = S (length ws)).
  { unfold extended_weights. rewrite app_length. simpl. lia. }
  rewrite Hlen.
  rewrite seq_S.
  rewrite map_app.
  rewrite fold_right_app.
  simpl.
  rewrite Rplus_0_r.
  assert (Hfirst :
      rsum (map (fun i => proposal_mass ws i *
          (if i <? length ws then D i else x)%R)
          (seq 0 (length ws))) =
      (INR (weight_sum ws) / INR (denominator ws)) *
        rsum (map (fun i => target_mass ws i * D i)%R
          (seq 0 (length ws)))).
  { rewrite <- (rsum_map_scal
      (INR (weight_sum ws) / INR (denominator ws))
      (fun i => target_mass ws i * D i)%R (seq 0 (length ws))).
    apply rsum_map_ext.
    intros i Hi.
    pose proof (proj1 (in_seq (length ws) 0 i) Hi) as Hbi.
    destruct Hbi as [_ Hlt]. simpl in Hlt.
    assert (Hif : (i <? length ws) = true).
    { apply Nat.ltb_lt. exact Hlt. }
    rewrite Hif.
    rewrite (prop_cond ws i Hadm Hlt). ring.
  }
  assert (HfirstFold :
      fold_right Rplus 0%R
        (map (fun i => proposal_mass ws i *
          (if i <? length ws then D i else x)%R)
          (seq 0 (length ws))) =
      (INR (weight_sum ws) / INR (denominator ws)) *
        fold_right Rplus 0%R
          (map (fun i => target_mass ws i * D i)%R
            (seq 0 (length ws)))) by exact Hfirst.
  assert (Hlast : (if length ws <? length ws then D (length ws) else x)%R = x).
  { rewrite Nat.ltb_irrefl. reflexivity. }
  rewrite Hlast.
  rewrite (fold_right_Rplus_acc
    (map (fun i => proposal_mass ws i *
      (if i <? length ws then D i else x)%R) (seq 0 (length ws)))
    (proposal_mass ws (length ws) * x)).
  rewrite HfirstFold.
  rewrite (target_mass_expectation ws D).
  reflexivity.
Qed.

Lemma pm_nonneg (ws : list nat) (i : nat) :
  (0 <= proposal_mass ws i)%R.
Proof.
  unfold proposal_mass.
  destruct (i <? length (extended_weights ws)); [|lra].
  apply Rcomplements.Rdiv_le_0_compat.
  - apply pos_INR.
  - change (INR 0 < INR (denominator ws))%R.
    apply lt_INR. pose proof (denominator_pos ws). lia.
Qed.

Lemma facts (ws:list nat) (Hadm: admissible ws) :
 let a := (INR (weight_sum ws) / INR (denominator ws))%R in
 let r := proposal_mass ws (length ws) in
 0 < a /\ a <= 1 /\ 0 <= r /\ r < 1 /\ a + r = 1.
Proof.
  intros a r.
  pose proof (denominator_bounds ws Hadm) as [Hle Hlt].
  assert (Hw : (0 < weight_sum ws)%nat).
  { exact (admissible_weight_sum_pos _ Hadm). }
  assert (Hd : (0 < denominator ws)%nat).
  { apply denominator_pos. }
  assert (Ha : (0 < a)%R).
  { unfold a. apply Rdiv_lt_0_compat.
    - change (INR 0 < INR (weight_sum ws))%R. apply lt_INR; exact Hw.
    - change (INR 0 < INR (denominator ws))%R. apply lt_INR; lia. }
  assert (Ha1 : (a <= 1)%R).
  { unfold a.
    rewrite (Rcomplements.Rle_div_l _ _ (INR (denominator ws))).
    - rewrite Rmult_1_l. apply le_INR. exact Hle.
     - change (INR 0 < INR (denominator ws))%R. apply lt_INR; lia. }
  assert (Hr : (0 <= r)%R).
  { unfold r. apply pm_nonneg. }
  assert (Har : (a = 1-r)%R).
  { unfold a, r. apply acceptance_mass. exact Hadm. }
  split; [exact Ha|]. split; [exact Ha1|]. split; [exact Hr|]. split; [lra|lra].
Qed.

Lemma round_bridge (ws : list nat) (D : nat -> R) (ε : R) :
  admissible ws -> nondegenerate ws ->
  SeriesC (fun i => proposal_mass ws i * D i)%R = ε ->
  ε = rsum (map (fun i => (INR (cnt (ddg_table ws) 0 i) /
    INR (2 ^ length (ddg_table ws)) * D i)%R)
    (seq 0 (length (extended_weights ws)))).
Proof.
  intros Hadm Hnd Hsum.
  rewrite (proposal_mass_expectation ws D) in Hsum.
  rewrite <- Hsum.
  apply rsum_map_ext.
  intros i Hi.
  pose proof (proj1 (in_seq (length (extended_weights ws)) 0 i) Hi) as Hboundi.
  destruct Hboundi as [_ HiN].
  simpl in HiN.
  pose proof (Hnd i HiN) as Hlt.
  assert (Hcnt : cnt (ddg_table ws) 0 i = nth i (extended_weights ws) 0%nat).
  { rewrite (cnt_naccept (ddg_table ws) 0 i).
    apply fldr_round_count_weight; assumption. }
  assert (Hden : Nat.pow 2 (length (ddg_table ws)) = denominator ws).
  { unfold denominator. assert (Hlen : length (ddg_table ws) = dyadic_width ws) by apply ddg_table_depth. rewrite Hlen. reflexivity. }
  rewrite Hcnt.
  rewrite Hden.
  unfold proposal_mass.
  assert (Hb : (i <? length (extended_weights ws)) = true).
  { apply Nat.ltb_lt. exact HiN. }
  rewrite Hb. reflexivity.
Qed.

Section TestRound.
  Context `{!erisGS Σ}.
  Lemma twp_fldr_round_adv_comp E (ws : list nat) (vrows : val) (D : nat -> R) (L ε : R) :
    admissible ws -> nondegenerate ws ->
    (forall i, (0 <= D i <= L)%R) ->
    SeriesC (fun i => proposal_mass ws i * D i)%R = ε ->
    [[{ ⌜is_list (ddg_table ws) vrows⌝ ∗ ↯ ε }]]
      fldr_walk #() vrows #0 @ E
    [[{ (i : nat), RET SOMEV #i; ↯ (D i) ∗ ⌜(i < length (extended_weights ws))%nat⌝ }]].
  Proof.
    intros Hadm Hnd HD HSum.
    assert (Hcap : cap_final (ddg_table ws) 1%nat = 0%nat).
    { apply ddg_table_cap_final; assumption. }
    assert (Hc : (0 < 1)%nat) by lia.
    assert (Hbound : forall row, In row (ddg_table ws) ->
      forall i, In i row -> (i < length (extended_weights ws))%nat).
    { intros row Hrow i Hi. exact (ddg_table_index_bound ws row i Hrow Hi). }
    assert (Heps : ε = rsum (map (fun i =>
      (INR (cnt (ddg_table ws) 0 i) /
       INR (2 ^ length (ddg_table ws)) * D i)%R)
      (seq 0 (length (extended_weights ws))))) .
    { apply round_bridge; assumption. }
    eapply (twp_fldr_walk_adv_comp E (ddg_table ws) vrows 0 1
      (length (extended_weights ws)) D L ε).
    - exact Hcap.
    - exact Hc.
    - exact Hbound.
    - exact HD.
    - exact Heps.
  Qed.
End TestRound.

Lemma twp_fldr_loop_adv_comp_pos E (ws:list nat) (vrows:val) (D:nat->R) (L ε:R) :
 admissible ws -> nondegenerate ws ->
 (forall i, (0 <= D i <= L)%R) ->
 SeriesC (fun i => target_mass ws i * D i)%R = ε ->
  ~ proposal_mass ws (length ws) = 0%R ->
 [[{ ⌜is_list (ddg_table ws) vrows⌝ ∗ ↯ ε }]]
   fldr_loop #() vrows #(length ws) @ E
 [[{ (i:nat), RET #i; ↯ (D i) ∗ ⌜(i < length ws)%nat⌝ }]].
Proof.
 intros Hadm Hnd HD HSum Hrne.
 set (n := length ws).
 set (a := (INR (weight_sum ws) / INR (denominator ws))%R).
 set (r := proposal_mass ws n).
 pose proof (facts ws Hadm) as Hfacts.
 simpl in Hfacts.
 destruct Hfacts as (Ha & Ha1 & Hr & Hr1 & Har).
 assert (Hrpos : (0 < r)%R).
 { unfold r, n. pose proof (pm_nonneg ws (length ws)) as Hnonneg. lra. }
 assert (Hr_inv : (1 < / r)%R).
 { replace 1%R with (/1)%R by apply Rinv_1.
   apply (Rinv_0_lt_contravar r 1 Hrpos). exact Hr1. }
 assert (HL0 : (0 <= L)%R).
 { pose proof (proj2 (HD 0%nat)) as HD0U. pose proof (proj1 (HD 0%nat)) as HD0. lra. }
 iIntros (Φ) "[Hlist Herr] HΦ".
 iApply twp_rand_err_pos; auto.
 iIntros (εterm Hεterm) "Hterm".
 iRevert (D ε HD HSum) "Herr HΦ Hlist".
 iApply (ec_ind_amp _ (/ r) with "[] Hterm"); try done.
 iModIntro.
 iIntros (ε' Hε') "IH Hterm".
 iIntros (D ε HD HSum) "Herr HΦ Hlist".
 assert (Heps0 : (0 <= ε)%R).
 { rewrite <- HSum. apply SeriesC_ge_0'. intros i.
   apply Rmult_le_pos; [apply target_mass_pos; exact Hadm|apply (proj1 (HD i))]. }
 set (q := (ε + (/ r) * ε')%R).
 set (D' := fun i => if i <? n then D i else q).
 assert (Hq0 : (0 <= q)%R).
 { unfold q. apply Rplus_le_le_0_compat; [exact Heps0|].
   apply Rmult_le_pos; [apply Rlt_le; apply Rinv_0_lt_compat; lra|lra]. }
 assert (HD' : forall i, (0 <= D' i <= L + q)%R).
 { intros i. unfold D'. destruct (i <? n).
   - destruct (HD i) as [HDi0 HDiL]. split; [exact HDi0|lra].
   - split; lra. }
 assert (Hsum' : SeriesC (fun i => proposal_mass ws i * D' i)%R = ε + ε').
 { unfold D'. rewrite (proposal_split ws D q Hadm).
   rewrite HSum.
   fold n. fold r. fold a.
   unfold q.
   rewrite Rmult_plus_distr_l.
   rewrite <- Rmult_assoc.
   rewrite Rmult_inv_r; [|lra].
   replace (a * ε + (r * ε + 1 * ε'))%R with ((a+r)*ε + ε')%R by ring.
   rewrite Har. ring. }
 iDestruct "Hlist" as %Hrows.
 rewrite /fldr_loop. wp_rec; wp_pures.
 iPoseProof (ec_combine with "[$Hterm $Herr]") as "Hec".
 iPoseProof (ec_eq (ε' + ε) (ε + ε') ltac:(ring) with "Hec") as "Hec2".
 wp_apply (twp_fldr_round_adv_comp E ws vrows D' (L+q) (ε+ε') Hadm Hnd HD' Hsum'
   with "[Hec2]") as (i) "[Hcredit %Hi]".
 - iSplit; [iPureIntro; exact Hrows|iFrame].
 - wp_pures; case_bool_decide as Hacc.
   + wp_if. iApply "HΦ".
     iSplitL "Hcredit".
   { iApply (ec_eq with "Hcredit"). unfold D'.
     assert (Hacc_nat : (i <? n) = true) by (apply Nat.ltb_lt; lia).
     rewrite Hacc_nat. reflexivity. }
   { iPureIntro. lia. }
 + wp_if.
   assert (Hlen : length (extended_weights ws) = S n).
   { unfold extended_weights. rewrite app_length. simpl. lia. }
   rewrite Hlen in Hi.
   assert (HiEq : i = n) by lia.
   assert (HDone : D' i = q).
   { unfold D'. rewrite HiEq. rewrite Nat.ltb_irrefl. reflexivity. }
   iPoseProof (ec_eq (D' i) q HDone with "Hcredit") as "Hrej".
   assert (Hamp0 : (0 <= (/ r * ε'))%R).
   { apply Rmult_le_pos; [apply Rlt_le; apply Rinv_0_lt_compat; lra|lra]. }
   iDestruct (ec_split with "Hrej") as "[HerrMain HerrAmp]"; [exact Heps0|exact Hamp0|].
   iSpecialize ("IH" with "HerrAmp").
   iApply ("IH" $! D ε with "[] [] HerrMain HΦ");
     try (iPureIntro; assumption).
Qed.

Lemma twp_fldr_loop_adv_comp E (ws : list nat) (vrows : val) (D : nat -> R) (L ε : R) :
  admissible ws -> nondegenerate ws ->
  (forall i, (0 <= D i <= L)%R) ->
  SeriesC (fun i => target_mass ws i * D i)%R = ε ->
  [[{ ⌜is_list (ddg_table ws) vrows⌝ ∗ ↯ ε }]]
    fldr_loop #() vrows #(length ws) @ E
  [[{ (i : nat), RET #i; ↯ (D i) ∗ ⌜(i < length ws)%nat⌝ }]].
Proof.
  intros Hadm Hnd HD HSum.
  set (n := length ws).
  set (a := (INR (weight_sum ws) / INR (denominator ws))%R).
  set (r := proposal_mass ws n).
  pose proof (facts ws Hadm) as Hfacts.
  simpl in Hfacts.
  destruct Hfacts as (Ha & Ha1 & Hr & Hr1 & Har).
  destruct (Req_dec r 0) as [Hr0|Hrne].
  - set (D' := fun i => if i <? n then D i else 1%R).
    assert (Hsum' : SeriesC (fun i => proposal_mass ws i * D' i)%R = ε).
    { unfold D'. rewrite (proposal_split ws D 1 Hadm).
      rewrite HSum.
      unfold r in Hr0.
      rewrite Hr0.
      unfold a, r in Har.
      rewrite Hr0 in Har.
      rewrite Rplus_0_r in Har.
      rewrite Har. ring. }
    assert (HL0 : (0 <= L)%R).
    { pose proof (proj2 (HD 0%nat)) as HD0U.
      pose proof (proj1 (HD 0%nat)) as HD0. lra. }
    assert (HD' : forall i, (0 <= D' i <= L + 1)%R).
    { intros i. unfold D'. destruct (i <? n) as [Hif|Hif].
      - destruct (HD i) as [HDi0 HDiL]. split; [exact HDi0|lra].
      - split; lra. }
    iIntros (Φ) "[Hlist Herr] HΦ".
    rewrite /fldr_loop. wp_rec; wp_pures.
    wp_apply (twp_fldr_round_adv_comp E ws vrows D' (L+1) ε
      Hadm Hnd HD' Hsum' with "[Hlist Herr]") as (i) "[Hcredit %Hi]".
    all: try (iFrame "Hlist Herr").
    wp_pures; case_bool_decide as Hacc.
    + wp_if. iApply "HΦ".
      iSplitL "Hcredit".
      { iApply (ec_eq with "Hcredit"). unfold D'.
        assert (Hacc_nat : (i <? n) = true) by (apply Nat.ltb_lt; lia).
        rewrite Hacc_nat. reflexivity. }
      { iPureIntro. lia. }
    + wp_if.
      assert (Hlen : length (extended_weights ws) = S n).
      { unfold extended_weights. rewrite app_length. simpl. lia. }
      rewrite Hlen in Hi.
      assert (HiEq : i = n) by lia.
      assert (HDone : D' i = 1%R).
      { unfold D'. rewrite HiEq. rewrite Nat.ltb_irrefl. reflexivity. }
      iPoseProof (ec_eq (D' i) 1%R HDone with "Hcredit") as "Hone".
      iDestruct (ec_contradict 1%R with "Hone") as "[]". lra.
  - unfold r, n in Hrne.
    eapply twp_fldr_loop_adv_comp_pos; eauto.
Qed.
End Pos.
