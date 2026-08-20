From Coq Require Import Arith.PeanoNat Lists.List Lia ZArith NArith.
From clutch.eris Require Import eris.
From clutch.common Require Import inject.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling.fldr Require Import model implementation list_total.

Import ListNotations.

Definition fldr_lit_nat (n : nat) : val := LitV (LitInt (Z.of_nat n)).

Lemma fldr_weight_sum_snoc (l : list nat) (a : nat) :
  weight_sum (l ++ [a]) = weight_sum l + a.
Proof.
  unfold weight_sum. rewrite fold_right_app. simpl.
  rewrite fold_right_add_acc. lia.
Qed.

Section FldrPreprocess.
  Context `{!erisGS Σ}.

  Lemma twp_fldr_weight_sum E (ws : list nat) (vws : val) :
    [[{ ⌜is_list ws vws⌝ }]]
      fldr_weight_sum vws @ E
    [[{ v, RET #v; ⌜v = weight_sum ws⌝ }]].
  Proof.
    iIntros (Φ) "%Hws HΦ".
    unfold fldr_weight_sum.
    wp_pures.
    iApply (twp_list_fold
      (fun lacc acc => ⌜acc = #(weight_sum lacc)⌝%I)
      (fun _ => True%I) (fun _ => True%I)
      E (λ: "acc" "w", "acc" + "w") ws #0 vws).
    - iIntros (a acc lacc lrem).
      iIntros (Φ') "!> Hpre Hcont".
      iDestruct "Hpre" as "[%Hsplit [%Hacc _]]".
      subst acc.
      wp_pures.
      iModIntro.
      iApply ("Hcont" $! _).
      iSplit.
      + iPureIntro. rewrite fldr_weight_sum_snoc. simpl. f_equal.
        rewrite Nat2Z.inj_add. reflexivity.
      + done.
    - iSplit.
      + done.
      + iSplit.
        * iPureIntro. simpl. reflexivity.
        * done.
    - iIntros (v) "[%Hacc _]".
      subst v.
      iApply ("HΦ" $! (weight_sum ws)).
      iPureIntro. reflexivity.
  Qed.

  Lemma twp_fldr_pow2_aux E (k d : nat) :
      d = k ->
      [[{ True }]]
        fldr_pow2 (fldr_lit_nat k) @ E
      [[{ v, RET #v; ⌜v = 2 ^ k⌝ }]].
  Proof.
    induction k as [|k IH] in d |- *.
    - intros Hd.
      iIntros (Φ) "_ HΦ".
      unfold fldr_pow2, fldr_lit_nat.
      wp_rec; wp_pures.
      iApply ("HΦ" $! (2 ^ 0)%nat).
      iPureIntro. simpl. reflexivity.
    - intros Hd.
      iIntros (Φ) "_ HΦ".
      unfold fldr_pow2, fldr_lit_nat.
      wp_rec; wp_pure _.
      wp_if.
      wp_op.
      assert (Hsub : #(Z.sub (Z.of_nat (S k)) 1) = #(k)%nat).
      { change (LitV (LitInt (Z.sub (Z.of_nat (S k)) 1)) =
                  LitV (LitInt (Z.of_nat k))).
        do 2 f_equal. rewrite Nat2Z.inj_succ. rewrite Z.sub_1_r. apply Z.pred_succ. }
      rewrite Hsub.
      fold fldr_pow2.
      wp_bind (fldr_pow2 (fldr_lit_nat k)).
      wp_apply (IH k eq_refl) as (v) "Hv"; [done|].
      wp_pures.
      iDestruct "Hv" as %Hv.
      subst v.
      iModIntro.
      assert (Hmul : LitV (LitInt (Z.mul (Z.of_nat 2) (Z.of_nat (2 ^ k))) ) =
                       LitV (LitInt (Z.of_nat (2 * 2 ^ k)))).
      { do 2 f_equal. rewrite Nat2Z.inj_mul. reflexivity. }
      rewrite Hmul.
      iApply ("HΦ" $! (2 * 2 ^ k)%nat).
      iPureIntro. simpl. lia.
  Qed.

  Lemma twp_fldr_pow2 E (k : nat) :
    [[{ True }]] fldr_pow2 (fldr_lit_nat k) @ E
    [[{ v, RET #v; ⌜v = 2 ^ k⌝ }]].
  Proof.
    iIntros (Φ) "H HΦ".
    iApply (twp_fldr_pow2_aux E k k eq_refl with "H HΦ").
  Qed.

  Lemma twp_fldr_width_aux E (m pow k d : nat) :
      pow = 2 ^ k -> k <= Nat.log2_up m -> d = Nat.log2_up m - k ->
      [[{ True }]]
        fldr_width (fldr_lit_nat m) (fldr_lit_nat pow) (fldr_lit_nat k) @ E
      [[{ v, RET #v; ⌜v = Nat.log2_up m⌝ }]].
  Proof.
    induction d as [|d IH] in m, pow, k |- *.
    - intros Hpow Hk Hd.
      iIntros (Φ) "_ HΦ".
      unfold fldr_lit_nat in *.
      unfold fldr_width.
      wp_rec; wp_pures.
      case_bool_decide as Hcmp.
      + wp_pures.
        assert (Hlog : Nat.log2_up m = k) by lia.
        iApply ("HΦ" $! k).
        iPureIntro. simpl. now rewrite Hlog.
      + exfalso.
        assert (Hmpos : 0 < m).
        { destruct (Nat.eq_dec m 0) as [->|Hm]; [lia|lia]. }
        pose proof (Nat.log2_log2_up_spec m Hmpos) as [_ Hupper].
        assert (Hlog : Nat.log2_up m = k) by lia.
        subst pow.
        assert (Hcmp_nat : ~ (m <= 2 ^ k)%nat).
        { intros H. apply Hcmp. lia. }
        exfalso. apply Hcmp_nat. now rewrite <- Hlog.
    - intros Hpow Hk Hd.
      iIntros (Φ) "_ HΦ".
      unfold fldr_lit_nat in *.
      unfold fldr_width.
      wp_rec; wp_pures.
      case_bool_decide as Hcmp.
      + wp_pures. exfalso.
        assert (Hlog_gt : k < Nat.log2_up m) by lia.
        assert (Hmgt1 : 1 < m).
        { destruct (le_lt_dec m 1) as [Hm|Hm].
          - pose proof (proj2 (Nat.log2_up_null m) Hm) as Hzero. lia.
          - exact Hm. }
        pose proof (Nat.log2_up_spec m Hmgt1) as [Hlower _].
        assert (Hpred : k <= Nat.pred (Nat.log2_up m)) by lia.
        pose proof (Nat.pow_le_mono_r 2 k (Nat.pred (Nat.log2_up m)) ltac:(lia) Hpred) as Hpowle.
        assert (Hcmp_nat : (m <= pow)%nat) by lia.
        rewrite Hpow in Hcmp_nat.
        lia.
      + wp_pure.
        fold fldr_width.
        assert (Hpow' : 2 * pow = 2 ^ (k + 1)).
        { rewrite Hpow. replace (k + 1)%nat with (S k) by lia.
          rewrite Nat.pow_succ_r'. lia. }
        assert (Hk' : k + 1 <= Nat.log2_up m) by lia.
        assert (Hd' : d = Nat.log2_up m - (k + 1)) by lia.
        wp_op.
        wp_op.
        fold fldr_width.
        assert (HpowZ : Z.mul (Z.of_nat 2) (Z.of_nat pow) = Z.of_nat (2 * pow)).
        { rewrite <- Nat2Z.inj_mul. reflexivity. }
        assert (HkZ : Z.add (Z.of_nat k) (Z.of_nat 1) = Z.of_nat (k + 1)).
        { rewrite <- Nat2Z.inj_add. reflexivity. }
        rewrite HpowZ HkZ.
        iApply (IH m (2 * pow) (k + 1) Hpow' Hk' Hd' with "[//] HΦ").
  Qed.
  Lemma twp_fldr_extend E (ws : list nat) (vws : val) (den m : nat) :
      m <= den ->
      [[{ ⌜is_list ws vws⌝ }]]
        fldr_extend vws (fldr_lit_nat den) (fldr_lit_nat m) @ E
      [[{ v, RET v; ⌜is_list (ws ++ [den - m]) v⌝ }]].
  Proof.
    intros Hle.
    iIntros (Φ) "%Hws HΦ".
    rewrite /fldr_extend.
    wp_pures.
    
    assert (Hsub : Z.sub (Z.of_nat den) (Z.of_nat m) = Z.of_nat (den - m)).
    { rewrite <- Nat2Z.inj_sub by lia. reflexivity. }
    rewrite Hsub.
    wp_bind (list_cons #(den - m)%nat (InjLV #())).
    wp_apply (twp_list_cons (den - m)%nat [] (InjLV #()) E) as (vone) "Vone"; [done|].
    iDestruct "Vone" as %Vone.
    wp_apply (twp_list_append E vws ws vone [den - m]) as (v) "Hv"; [iPureIntro; split; assumption|].
    iApply ("HΦ" $! v); iFrame.
  Qed.
  Lemma mapi_pair_indexed_aux (k : nat) (l : list nat) :
      mapi_loop (fun i w => (i, w)) k l = combine (seq k (length l)) l.
  Proof.
    induction l as [|a l IH] in k |- *; simpl.
    - reflexivity.
    - rewrite IH. simpl. reflexivity.
  Qed.

  Lemma mapi_pair_indexed (l : list nat) :
      mapi (fun i w => (i, w)) l = indexed_weights l.
  Proof.
    unfold mapi, indexed_weights.
    rewrite (mapi_pair_indexed_aux 0 l).
    reflexivity.
  Qed.


  Lemma twp_fldr_pair E (i x : nat) :
    [[{ True }]]
      (λ: "i" "w", ("i", "w"))%V #i (inject x) @ E
    [[{ fr, RET fr; ⌜fr = inject (i, x)⌝ ∗ True }]].
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_pures.
    iApply ("HΦ" $! (PairV (inject i) (inject x))).
    iModIntro. iSplit; [iPureIntro; reflexivity|done].
  Qed.

  Lemma twp_fldr_index E (l : list nat) (vl : val) :
    [[{ ⌜is_list l vl⌝ }]]
      fldr_index vl @ E
    [[{ v, RET v; ⌜is_list (indexed_weights l) v⌝ }]].
  Proof.
    iIntros (Φ) "%Hl HΦ".
    rewrite /fldr_index.
    wp_pures.
    wp_apply (twp_list_mapi (A := nat) (B := nat * nat)
      (fun i w => (i, w)) l
      (λ: "i" "w", ("i", "w")) vl
      (fun _ _ => True%I) (fun _ _ => True%I) E) as (v) "Hv".
    - iSplitR.
      + iModIntro. iIntros (i x).
        iIntros (Ψ) "!> _ HΨ".
        wp_pures.
        iApply ("HΨ" $! (PairV (inject i) (inject x))).
        iModIntro. iSplit; [iPureIntro; reflexivity|done].
      + iSplitL "".
        * iPureIntro; exact Hl.
        * iPureIntro. induction l; simpl; auto.
    - iApply ("HΦ" $! v).
      iDestruct "Hv" as "[%Hv _]".
      iPureIntro. rewrite mapi_pair_indexed in Hv. exact Hv.
  Qed.


  Definition fldr_row_pred (iw : nat * nat) : bool :=
    Nat.eqb (snd iw mod 2) 1.

  Lemma fldr_rem_nat (w : nat) :
      Z.rem (Z.of_nat w) (2%Z) = Z.of_nat (w mod 2).
  Proof.
    rewrite Z.rem_mod_nonneg; [|lia|lia].
    rewrite (Nat2Z.inj_mod w 2).
    reflexivity.
  Qed.

  Lemma fldr_row_bool (w : nat) :
      LitV (LitBool
        (bool_decide (LitV (LitInt (Z.of_nat (w mod 2))) = LitV (LitInt 1)))) =
      LitV (LitBool (Nat.eqb (w mod 2) 1)).
  Proof.
    do 2 f_equal.
    assert (Hequiv :
      (LitV (LitInt (Z.of_nat (w mod 2))) = LitV (LitInt 1)) <->
      (w mod 2 = 1)).
    { split.
      - intro H. injection H as H0.
        change (Z.of_nat (w mod 2) = Z.of_nat 1) in H0.
        apply Nat2Z.inj in H0. exact H0.
      - intro H. rewrite H. reflexivity. }
    assert (Hnat : bool_decide (w mod 2 = 1) = Nat.eqb (w mod 2) 1).
    { destruct (Nat.eq_dec (w mod 2) 1) as [Heq|Hne].
      - rewrite Heq. simpl. reflexivity.
      - rewrite (bool_decide_false _ Hne). symmetry. apply Nat.eqb_neq. exact Hne. }
    assert (Hval :
      bool_decide (LitV (LitInt (Z.of_nat (w mod 2))) = LitV (LitInt 1)) =
      bool_decide (w mod 2 = 1)).
    { apply bool_decide_ext. exact Hequiv. }
    rewrite Hval. exact Hnat.
  Qed.

  Lemma twp_fldr_row_pred E (iw : nat * nat) :
    [[{ True }]]
      (λ: "iw", (Snd "iw") `rem` #2 = #1)%V (inject iw) @ E
    [[{ v, RET v; ⌜v = inject (fldr_row_pred iw)⌝ }]].
  Proof.
    iIntros (Φ) "_ HΦ".
    destruct iw as [i w]. simpl [fldr_row_pred].
    wp_pures.
    assert (Hrem : #(Z.rem (Z.of_nat w) (2%Z)) = #(w mod 2)%nat).
    { change (LitV (LitInt (Z.rem (Z.of_nat w) (2%Z))) =
                LitV (LitInt (Z.of_nat (w mod 2)))).
      do 2 f_equal. apply fldr_rem_nat. }
    rewrite Hrem.
    assert (Hbool :
      LitV (LitBool
        (bool_decide (LitV (LitInt (Z.of_nat (w mod 2))) = LitV (LitInt 1)))) =
      LitV (LitBool (Nat.eqb (w mod 2) 1))) by apply fldr_row_bool.
    rewrite Hbool.
    iModIntro. iApply ("HΦ" $! (inject (fldr_row_pred (i,w)))).
    iPureIntro. reflexivity.
  Qed.

  Lemma twp_fldr_fst E (iw : nat * nat) :
    [[{ True }]]
      (λ: "iw", Fst "iw")%V (inject iw) @ E
    [[{ v, RET v; ⌜v = inject (fst iw)⌝ }]].
  Proof.
    iIntros (Φ) "_ HΦ". destruct iw as [i w].
    wp_pures. iApply ("HΦ" $! (inject i)).
    iModIntro. iPureIntro. reflexivity.
  Qed.

  Lemma twp_fldr_one_row E (iws : list (nat * nat)) (viws : val) :
    [[{ ⌜is_list iws viws⌝ }]]
      fldr_one_row viws @ E
    [[{ v, RET v; ⌜is_list (one_row iws) v⌝ }]].
  Proof.
    iIntros (Φ) "%Hiws HΦ".
    rewrite /fldr_one_row.
    wp_pures.
    wp_apply (twp_list_filter (A := nat * nat) iws fldr_row_pred
      (λ: "iw", (Snd "iw") `rem` #2 = #1)%V viws E) as (vf) "Hf".
    - iSplitR.
      + iIntros (iw).
        iIntros (Ψ) "!> _ HΨ".
        destruct iw as [i w]. simpl [fldr_row_pred].
        wp_pures.
        assert (Hrem : #(Z.rem (Z.of_nat w) (2%Z)) = #(w mod 2)%nat).
        { change (LitV (LitInt (Z.rem (Z.of_nat w) (2%Z))) =
                    LitV (LitInt (Z.of_nat (w mod 2)))).
          do 2 f_equal. apply fldr_rem_nat. }
        rewrite Hrem.
        rewrite fldr_row_bool.
        iApply ("HΨ" $! (inject (fldr_row_pred (i,w)))).
        iModIntro. iPureIntro. reflexivity.
      + done.
    - wp_bind (list_map (λ: "iw", Fst "iw")%E vf).
      iDestruct "Hf" as %Hf.
      wp_pures.
      wp_apply (twp_list_map_pure (A := nat * nat) (B := nat)
        (List.filter fldr_row_pred iws) (fun iw => fst iw)
        (λ: "iw", Fst "iw")%V vf E) as (v) "Hm".
      + iSplitR.
        * iIntros (iw).
          iIntros (Ψ) "!> _ HΨ".
          destruct iw as [i w]. wp_pures.
          iApply ("HΨ" $! (inject i)).
          iModIntro. iPureIntro. reflexivity.
        * done.
      + iApply ("HΦ" $! v).
        iDestruct "Hm" as %Hm.
        iPureIntro. exact Hm.
  Qed.

  Lemma twp_fldr_shift E (iws : list (nat * nat)) (viws : val) :
    [[{ ⌜is_list iws viws⌝ }]]
      fldr_shift viws @ E
    [[{ v, RET v; ⌜is_list (shift_weights iws) v⌝ }]].
  Proof.
    iIntros (Φ) "%Hiws HΦ".
    rewrite /fldr_shift.
    wp_pures.
    wp_apply (twp_list_map_pure (A := nat * nat) (B := nat * nat)
      iws (fun iw => (fst iw, snd iw / 2))
      (λ: "iw", (Fst "iw", (Snd "iw") `quot` #2))%V viws E) as (v) "Hm".
    - iSplitR.
      + iIntros (iw).
        iIntros (Ψ) "!> _ HΨ".
        destruct iw as [i w]. simpl.
        wp_pures.
        assert (Hq : #(Z.quot (Z.of_nat w) 2) = #(w / 2)%nat).
        { change (LitV (LitInt (Z.quot (Z.of_nat w) 2)) =
                    LitV (LitInt (Z.of_nat (w / 2)))).
          do 2 f_equal.
          rewrite <- (nat_N_Z w).
          replace (2%Z) with (Z.of_nat 2) by reflexivity.
          rewrite <- (nat_N_Z 2).
          rewrite <- (N2Z.inj_quot (N.of_nat w) (N.of_nat 2)).
          rewrite <- (nat_N_Z (w / 2)).
          rewrite <- (Nat2N.inj_div w 2).
          reflexivity. }
        rewrite Hq.
        iApply ("HΨ" $! (inject (i, w / 2))).
        iModIntro. iPureIntro. reflexivity.
      + done.
    - iApply ("HΦ" $! v).
      iDestruct "Hm" as %Hm.
      iPureIntro. exact Hm.
  Qed.

  Lemma twp_fldr_width E (m : nat) :
      0 < m ->
      [[{ True }]]
        fldr_width (fldr_lit_nat m) #1 #0 @ E
      [[{ v, RET #v; ⌜v = Nat.log2_up m⌝ }]].
  Proof.
    intros Hm.
    iIntros (Φ) "_ HΦ".
    iApply (twp_fldr_width_aux E m 1 0 (Nat.log2_up m)
      ltac:(simpl; lia) ltac:(lia) ltac:(lia) with "[//] HΦ").
  Qed.

  Lemma twp_fldr_rows_lsb E (fuel : nat) (iws : list (nat * nat)) (viws : val) :
    [[{ ⌜is_list iws viws⌝ }]]
      fldr_rows_lsb #fuel viws @ E
    [[{ v, RET v; ⌜is_list (rows_lsb fuel iws) v⌝ }]].
  Proof.
    induction fuel as [|fuel IH] in iws, viws |- *.
    - iIntros (Φ) "%Hiws HΦ".
      rewrite /fldr_rows_lsb.
      wp_rec; wp_pures.
      iModIntro.
      iApply ("HΦ" $! (InjLV #())).
      iPureIntro. reflexivity.
    - iIntros (Φ) "%Hiws HΦ".
      rewrite /fldr_rows_lsb.
      wp_rec; wp_pures.
      wp_bind (fldr_shift viws).
      wp_apply (twp_fldr_shift E iws viws) as (vs) "Hs"; [done|].
      wp_op.
      assert (Hsub : #(Z.sub (Z.of_nat (S fuel)) 1) = #(fuel)%nat).
      { change (LitV (LitInt (Z.sub (Z.of_nat (S fuel)) 1)) =
                  LitV (LitInt (Z.of_nat fuel))).
        do 2 f_equal. rewrite Nat2Z.inj_succ. rewrite Z.sub_1_r. apply Z.pred_succ. }
      rewrite Hsub.
      iDestruct "Hs" as %Hs.
      wp_bind (fldr_rows_lsb #fuel vs).
      fold fldr_rows_lsb.
      wp_apply (IH (shift_weights iws) vs) as (vt) "Ht"; [iPureIntro; exact Hs|].
      wp_bind (fldr_one_row viws)%E.
      wp_apply (twp_fldr_one_row E iws viws) as (vr) "Hrow"; [done|].
      rewrite /list_cons.
      wp_pures.
      iModIntro.
      iApply ("HΦ" $! (InjRV (PairV vr vt))).
      iDestruct "Hrow" as %Hrow.
      iDestruct "Ht" as %Ht.
      iPureIntro.
      apply (proj1 (is_list_inject _ _)) in Hrow.
      rewrite Hrow.
      exists vt. split; [reflexivity|exact Ht].
  Qed.

  Lemma reverse_eq_rev {A : Type} (l : list A) :
      reverse l = rev l.
  Proof. unfold reverse. symmetry. apply rev_alt. Qed.

  Lemma twp_fldr_table E (ws : list nat) (vws : val) :
    admissible ws ->
    [[{ ⌜is_list ws vws⌝ }]]
      fldr_table vws @ E
    [[{ v, RET v; ⌜is_list (ddg_table ws) v⌝ }]].
  Proof.
    intros Hadm.
    iIntros (Φ) "%Hws HΦ".
    rewrite /fldr_table.
    wp_pures.
    wp_bind (fldr_weight_sum vws).
    wp_apply (twp_fldr_weight_sum E ws vws) as (m) "Hm"; [done|].
    iDestruct "Hm" as %Hm.
    wp_let.
    wp_bind (fldr_width (fldr_lit_nat m) #1 #0).
    wp_apply (twp_fldr_width E m); [rewrite Hm; exact (admissible_weight_sum_pos _ Hadm)|done|].
    iIntros (k) "Hk".
    iDestruct "Hk" as %Hk.
    wp_let.
    wp_bind (fldr_pow2 (fldr_lit_nat k)).
    wp_apply (twp_fldr_pow2 E k) as (den) "Hden"; [done|].
    iDestruct "Hden" as %Hden.
    wp_let.
    rewrite Hden.
    wp_bind (fldr_extend vws (fldr_lit_nat (2 ^ k)) (fldr_lit_nat m)).
    assert (Hle : m <= 2 ^ k).
    { pose proof (proj1 (denominator_bounds ws Hadm)) as Hb.
      unfold denominator, dyadic_width in Hb.
      rewrite Hm in Hk.
      rewrite Hm. rewrite Hk. exact Hb. }
    wp_apply (twp_fldr_extend E ws vws (2 ^ k) m); [exact Hle|done|].
    iIntros (ext) "Hext".
    iDestruct "Hext" as %Hext.
    wp_let.
    assert (Hext' : is_list (extended_weights ws) ext).
    { unfold extended_weights, rejection_weight, denominator, dyadic_width.
      rewrite Hm in Hext.
      rewrite Hm in Hk.
      rewrite <- Hk. exact Hext. }
    wp_bind (fldr_index _).
    wp_apply (twp_fldr_index E (extended_weights ws) ext) as (viws) "Hiws"; [iPureIntro; exact Hext'|].
    iDestruct "Hiws" as %Hiws.
    wp_bind (fldr_rows_lsb (fldr_lit_nat k) viws).
    iApply (twp_fldr_rows_lsb E k (indexed_weights (extended_weights ws)) viws).
    - iPureIntro. exact Hiws.
    - iIntros (vr) "Hr".
      iDestruct "Hr" as %Hr.
      wp_bind (list_rev vr).
      wp_apply (twp_list_rev E vr (rows_lsb k (indexed_weights (extended_weights ws)))) as (v) "Hv"; [iPureIntro; exact Hr|].
      iApply ("HΦ" $! v).
      iDestruct "Hv" as %Hv.
      iPureIntro.
      rewrite reverse_eq_rev in Hv.
      unfold ddg_table.
      assert (Hdepth : k = dyadic_width ws).
      { unfold dyadic_width. rewrite Hm in Hk. exact Hk. }
      rewrite Hdepth in Hv.
      exact Hv.
  Qed.
End FldrPreprocess.
