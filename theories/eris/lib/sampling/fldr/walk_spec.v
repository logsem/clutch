From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia.
From clutch.eris Require Import eris.
From clutch.common Require Import inject.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling.fldr Require Import implementation model walk pure distribution list_total.

Import ListNotations.

(** * Instrumented finite walk and tape refinement.

    The counter records the number of bits consumed before a leaf is reached.
    This is intentionally separate from [walk], whose result forgets that
    consumption count. *)

Definition bit_of (n : fin 2) : bool := bool_decide (fin_to_nat n = 1%nat).

Fixpoint walkc (rows : list (list nat)) (c : nat) (bs : list bool) : option (nat * nat) :=
  match rows, bs with
  | row :: rest, b :: bs' =>
      let c' := 2 * c + (if b then 1 else 0) in
      if c' <? length row then Some (nth c' row 0, 1)
      else match walkc rest (c' - length row) bs' with
           | Some (i, n) => Some (i, S n)
           | None => None
           end
  | _, _ => None
  end.

Lemma walkc_walk rows c bs :
  option_map fst (walkc rows c bs) = walk rows c bs.
Proof.
  induction rows as [|row rest IH] in c, bs |- *.
  - reflexivity.
  - destruct bs as [|b bs]; [reflexivity|].
    simpl.
    set (c' := 2 * c + (if b then 1 else 0)).
    change (option_map fst
      (if c' <? length row then Some (nth c' row 0, 1)
       else match walkc rest (c' - length row) bs with
             | Some (j, n) => Some (j, S n)
             | None => None
             end) =
      if c' <? length row then Some (nth c' row 0)
      else walk rest (c' - length row) bs).
    destruct (c' <? length row) eqn:Hfit.
    + simpl. reflexivity.
    + simpl.
      destruct (walkc rest (c' - length row) bs) as [[j n]|] eqn:Hwalk.
      * simpl. pose proof (IH (c' - length row) bs) as Hih.
        rewrite Hwalk in Hih. simpl in Hih. exact Hih.
      * simpl. pose proof (IH (c' - length row) bs) as Hih.
        rewrite Hwalk in Hih. simpl in Hih. exact Hih.
Qed.

Lemma cnt_zero_above rows c i N :
  (forall row, In row rows -> forall j, In j row -> j < N) ->
  N <= i -> cnt rows c i = 0.
Proof.
  induction rows as [|row rest IH] in c |- *; intros Hbound Hi; simpl; [lia|].
  assert (Hrest : forall r, In r rest -> forall j, In j r -> j < N).
  { intros r Hr. apply (Hbound r); right; exact Hr. }
  assert (Hleaf : forall q, q < length row -> leafval row q i (length rest) = 0).
  { intros q Hq. unfold leafval.
    assert (Hnth : In (nth q row 0) row) by (apply nth_In; exact Hq).
    assert (Hlt : nth q row 0 < N) by
      apply (Hbound row (or_introl eq_refl) _ Hnth).
    assert (Hneq : ~ nth q row 0 = i) by lia.
    assert (Heq : Nat.eqb (nth q row 0) i = false) by
      (apply Nat.eqb_neq; exact Hneq).
    rewrite Heq. reflexivity. }
  destruct (2 * c <? length row) eqn:H0;
  destruct (2 * c + 1 <? length row) eqn:H1.
  all: replace (c + (c + 0)) with (2 * c) by lia.
  all: replace (c + (c + 0) + 1) with (2 * c + 1) by lia.
  all: rewrite H0; rewrite H1.
  - replace (c + (c + 0)) with (2 * c) by lia.
    replace (c + (c + 0) + 1) with (2 * c + 1) by lia.
    rewrite (Hleaf (2 * c) (proj1 (Nat.ltb_lt _ _) H0)).
    rewrite (Hleaf (2 * c + 1) (proj1 (Nat.ltb_lt _ _) H1)). lia.
  - replace (c + (c + 0) + 1) with (2 * c + 1) by lia.
    rewrite (Hleaf (2 * c) (proj1 (Nat.ltb_lt _ _) H0)).
    rewrite (IH (2 * c + 1 - length row) Hrest Hi). lia.
  - replace (c + (c + 0)) with (2 * c) by lia.
    rewrite (IH (2 * c - length row) Hrest Hi).
    rewrite (Hleaf (2 * c + 1) (proj1 (Nat.ltb_lt _ _) H1)). lia.
  - replace (c + (c + 0)) with (2 * c) by lia.
    replace (c + (c + 0) + 1) with (2 * c + 1) by lia.
    rewrite (IH (2 * c - length row) Hrest Hi).
    rewrite (IH (2 * c + 1 - length row) Hrest Hi). lia.
Qed.

Lemma bit_of_zero : bit_of 0%fin = false.
Proof. vm_compute. reflexivity. Qed.

Lemma bit_of_one : bit_of 1%fin = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bit_of_fin (b : fin 2) :
  bit_of b = bool_decide (fin_to_nat b = 1%nat).
Proof. reflexivity. Qed.
Lemma walkc_zero_tail rows row c bs i :
  length row <= 2 * c ->
  walkc (row :: rows) c (map bit_of (0%fin :: bs)) =
    Some (i, length (0%fin :: bs)) ->
  walkc rows (2 * c - length row) (map bit_of bs) = Some (i, length bs).
Proof.
  intros Hcap H.
  assert (Hmap : map bit_of (0%fin :: bs) = false :: map bit_of bs).
  { simpl. rewrite bit_of_zero. reflexivity. }
  rewrite Hmap in H. simpl in H.
  replace (c + (c + 0)) with (2 * c) in H by lia.
  replace (c + (c + 0) - length row) with (2 * c - length row) in H by lia.
  replace (2 * c + 0) with (2 * c) in H by lia.
  rewrite (proj2 (Nat.ltb_ge _ _) Hcap) in H.
  destruct (walkc rows (2 * c - length row) (map bit_of bs)) as [[j n]|] eqn:Hw.
  - inversion H. reflexivity.
  - discriminate.
Qed.

Lemma walkc_one_tail rows row c bs i :
  length row <= 2 * c + 1 ->
  walkc (row :: rows) c (map bit_of (1%fin :: bs)) =
    Some (i, length (1%fin :: bs)) ->
  walkc rows (2 * c + 1 - length row) (map bit_of bs) = Some (i, length bs).
Proof.
  intros Hcap H.
  assert (Hmap : map bit_of (1%fin :: bs) = true :: map bit_of bs).
  { simpl. rewrite bit_of_one. reflexivity. }
  rewrite Hmap in H. simpl in H.
  replace (c + (c + 0) + 1) with (2 * c + 1) in H by lia.
  replace (c + (c + 0) + 1 - length row) with (2 * c + 1 - length row) in H by lia.
  rewrite (proj2 (Nat.ltb_ge _ _) Hcap) in H.
  destruct (walkc rows (2 * c + 1 - length row) (map bit_of bs)) as [[j n]|] eqn:Hw.
  - inversion H. reflexivity.
  - discriminate.
Qed.

Section TapedWalk.
  Context `{!erisGS Σ}.

  Lemma twp_fldr_walk_tape E (rows : list (list nat)) (vrows : val)
        (c : nat) (α : loc) (bs : list (fin 2)) (rest : list (fin 2)) (i : nat) :
    walkc rows c (map bit_of bs) = Some (i, length bs) ->
    [[{ ⌜is_list rows vrows⌝ ∗ α ↪ (1; bs ++ rest) }]]
      fldr_walk #lbl:α vrows #c @ E
    [[{ RET SOMEV #i; α ↪ (1; rest) }]].
  Proof.
    induction rows as [|row rows IH] in c, vrows, bs, rest, i |- *.
    - intros Hwalk. simpl in Hwalk. discriminate.
    - destruct bs as [|b bs]; [intros Hwalk; simpl in Hwalk; discriminate|].
      assert (Hb_cases : b = 0%fin \/ b = 1%fin).
      { destruct (decide (b = 0%fin)) as [Hb|Hb].
        - left; exact Hb.
        - right. apply fin_to_nat_inj. pose proof (fin_to_nat_lt b) as Hlt.
          destruct (fin_to_nat b) as [|[|n]] eqn:Hbn.
          + exfalso. apply Hb. apply fin_to_nat_inj. simpl. exact Hbn.
          + reflexivity.
          + lia. }
      destruct Hb_cases as [Hb0|Hb1].
      * intros Hwalk. rewrite Hb0 in Hwalk. rewrite Hb0.
        iIntros (Φ) "[%Hrows Hα] HΦ".
        iAssert (⌜walkc (row :: rows) c (map bit_of (0%fin :: bs)) =
                  Some (i, length (0%fin :: bs))⌝%I) as "HwalkP".
        { iPureIntro. exact Hwalk. }
        simpl in Hrows.
        destruct Hrows as (vrow & -> & Hrows).
        rewrite /fldr_walk. wp_rec. wp_pures.
        wp_apply (twp_rand_tape with "Hα") as "Hα". wp_pures.
        wp_bind (list_length (inject_list row)).
        wp_apply (twp_list_length E row (inject_list row)).
        { iPureIntro. apply (is_list_inject row (inject_list row)). reflexivity. }
        iIntros (h) "%Hh"; simpl in Hh; subst h; wp_pures.
        case_bool_decide as Hfit.
        + assert (Hfit_nat : 2 * c < length row) by lia.
          iAssert (⌜nth (2 * c) row 0 = i ∧ length bs = 0⌝%I) as "Hfacts".
          { iPureIntro.
            simpl in Hwalk.
            replace (c + (c + 0)) with (2 * c) in Hwalk by lia.
            replace (2 * c + 0) with (2 * c) in Hwalk by lia.
            rewrite (proj2 (Nat.ltb_lt _ _) Hfit_nat) in Hwalk.
            inversion Hwalk. split; reflexivity. }
          assert (Hidx : #(Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 0)) = #(2 * c)%nat).
          { change (LitV (LitInt (Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 0))) =
                      LitV (LitInt (Z.of_nat (2 * c)))).
            do 2 f_equal. rewrite Nat2Z.inj_mul. lia. }
          rewrite Hidx.
          assert (Hrow : is_list row (inject_list row)).
          { apply (is_list_inject row (inject_list row)). reflexivity. }
          wp_pures.
          iApply (twp_list_nth E (2 * c) row (inject_list row) $! Hrow).
          iIntros (v [Hnone | (r & -> & Hlookup)]); first eauto with lia.
          iDestruct "Hfacts" as %Hfacts.
          destruct Hfacts as [Hslot Hlen].
          iAssert (⌜bs = []⌝%I) as %->.
          { iPureIntro. apply nil_length_inv. exact Hlen. }
          pose proof (nth_lookup_Some row (2 * c) 0 r Hlookup) as Hnth.
          iAssert (⌜r = i⌝%I) as %->.
          { iPureIntro. rewrite <- Hnth. exact Hslot. }
          by iApply "HΦ".
        + assert (Hrowcap : length row <= 2 * c) by lia.
          wp_if.
          wp_op.
          assert (Hsub :
            #(Z.sub (Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 0))
                    (Z.of_nat (length row))) =
            #(2 * c - length row)%nat).
          { change (LitV (LitInt (Z.sub (Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 0))
                                            (Z.of_nat (length row)))) =
                      LitV (LitInt (Z.of_nat (2 * c - length row)))).
            do 2 f_equal.
            replace (Z.of_nat 0) with 0%Z by lia.
            rewrite Z.add_0_r.
            rewrite <- Nat2Z.inj_mul.
            rewrite <- Nat2Z.inj_sub; lia. }
          rewrite Hsub.
          iAssert (⌜walkc rows (2 * c - length row) (map bit_of bs) =
                    Some (i, length bs)⌝%I) as "Hnext".
          { iDestruct "HwalkP" as %H; iPureIntro;
            exact (walkc_zero_tail rows row c bs i Hrowcap H). }
          iDestruct "Hnext" as %Hnext; iApply (IH vrow (2 * c - length row) bs rest i Hnext with "[Hα] HΦ").
          iSplit; [iPureIntro; exact Hrows | iFrame].
      * intros Hwalk. rewrite Hb1 in Hwalk. rewrite Hb1.
        iIntros (Φ) "[%Hrows Hα] HΦ".
        iAssert (⌜walkc (row :: rows) c (map bit_of (1%fin :: bs)) =
                  Some (i, length (1%fin :: bs))⌝%I) as "HwalkP".
        { iPureIntro. exact Hwalk. }
        simpl in Hrows.
        destruct Hrows as (vrow & -> & Hrows).
        rewrite /fldr_walk. wp_rec. wp_pures.
        wp_apply (twp_rand_tape with "Hα") as "Hα". wp_pures.
        wp_bind (list_length (inject_list row)).
        wp_apply (twp_list_length E row (inject_list row)).
        { iPureIntro. apply (is_list_inject row (inject_list row)). reflexivity. }
        iIntros (h) "%Hh"; simpl in Hh; subst h; wp_pures.
        case_bool_decide as Hfit.
        + assert (Hfit_nat : 2 * c + 1 < length row) by lia.
          iAssert (⌜nth (2 * c + 1) row 0 = i ∧ length bs = 0⌝%I) as "Hfacts".
          { iPureIntro.
            simpl in Hwalk.
            replace (c + (c + 0) + 1) with (2 * c + 1) in Hwalk by lia.
            rewrite (proj2 (Nat.ltb_lt _ _) Hfit_nat) in Hwalk.
            inversion Hwalk. split; reflexivity. }
          assert (Hidx : #(Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 1)) = #(2 * c + 1)%nat).
          { change (LitV (LitInt (Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 1))) =
                      LitV (LitInt (Z.of_nat (2 * c + 1)))).
            do 2 f_equal.
            rewrite <- Nat2Z.inj_mul.
            replace 1%Z with (Z.of_nat 1) by lia.
            rewrite <- Nat2Z.inj_add; lia. }
          rewrite Hidx.
          assert (Hrow : is_list row (inject_list row)).
          { apply (is_list_inject row (inject_list row)). reflexivity. }
          wp_pures.
          iApply (twp_list_nth E (2 * c + 1) row (inject_list row) $! Hrow).
          iIntros (v [Hnone | (r & -> & Hlookup)]); first eauto with lia.
          iDestruct "Hfacts" as %Hfacts.
          destruct Hfacts as [Hslot Hlen].
          iAssert (⌜bs = []⌝%I) as %->.
          { iPureIntro. apply nil_length_inv. exact Hlen. }
          pose proof (nth_lookup_Some row (2 * c + 1) 0 r Hlookup) as Hnth.
          iAssert (⌜r = i⌝%I) as %->.
          { iPureIntro. rewrite <- Hnth. exact Hslot. }
          by iApply "HΦ".
        + assert (Hrowcap : length row <= 2 * c + 1) by lia.
          wp_if.
          wp_op.
          assert (Hsub :
            #(Z.sub (Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 1))
                    (Z.of_nat (length row))) =
            #(2 * c + 1 - length row)%nat).
          { change (LitV (LitInt (Z.sub (Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 1))
                                            (Z.of_nat (length row)))) =
                      LitV (LitInt (Z.of_nat (2 * c + 1 - length row)))).
            do 2 f_equal.
            rewrite <- Nat2Z.inj_mul.
            replace 1%Z with (Z.of_nat 1) by lia.
            rewrite <- Nat2Z.inj_add.
            rewrite <- Nat2Z.inj_sub; lia. }
          rewrite Hsub.
          iAssert (⌜walkc rows (2 * c + 1 - length row) (map bit_of bs) =
                    Some (i, length bs)⌝%I) as "Hnext".
          { iDestruct "HwalkP" as %H; iPureIntro;
            exact (walkc_one_tail rows row c bs i Hrowcap H). }
          iDestruct "Hnext" as %Hnext; iApply (IH vrow (2 * c + 1 - length row) bs rest i Hnext with "[Hα] HΦ").
          iSplit; [iPureIntro; exact Hrows | iFrame].
  Qed.
End TapedWalk.
