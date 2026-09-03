From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia.
From clutch.eris Require Import eris.
From clutch.common Require Import inject.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling.fldr Require Import implementation model walk pure distribution list_total walk_spec.

Import ListNotations.
#[local] Open Scope R.

Definition rsum (l : list R) : R := fold_right Rplus 0%R l.

Lemma rsum_map_plus (f g : nat -> R) (l : list nat) :
  rsum (map (fun i => (f i + g i)%R) l) =
  (rsum (map f l) + rsum (map g l))%R.
Proof.
  unfold rsum. induction l as [|x l IH]; simpl; [lra|].
  rewrite IH. lra.
Qed.

Lemma rsum_map_scal (c : R) (f : nat -> R) (l : list nat) :
  rsum (map (fun i => (c * f i)%R) l) =
  (c * rsum (map f l))%R.
Proof.
  unfold rsum. induction l as [|x l IH]; simpl; [lra|].
  rewrite IH. lra.
Qed.

Lemma rsum_map_ext (f g : nat -> R) l :
  (forall i, In i l -> f i = g i) ->
  rsum (map f l) = rsum (map g l).
Proof.
  intros H. induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)).
  f_equal. apply IH. intros i Hi. apply H. right. exact Hi.
Qed.

Lemma rsum_map_nonneg (f : nat -> R) l :
  (forall i, In i l -> (0 <= f i)%R) ->
  (0 <= rsum (map f l))%R.
Proof.
  intros H. induction l as [|x l IH]; simpl; [lra|].
  specialize (IH (fun i Hi => H i (or_intror Hi))).
  specialize (H x (or_introl eq_refl)). lra.
Qed.

Lemma rsum_indicator (p : nat) (x : R) (n : nat) :
  (p < n)%nat ->
  rsum (map (fun i => if Nat.eqb p i then x else 0%R) (seq 0 n)) = x.
Proof.
  intros Hp. unfold rsum.
  remember (seq 0 n) as q eqn:Hq.
  assert (Hsplit : q = seq 0 p ++ p :: seq (S p) (n - S p)).
  { subst q.
     change (seq 0 n = seq 0 p ++ seq (0 + p) (S (n - S p))).
     rewrite <- (seq_app p (S (n - S p)) 0).
     simpl.
     set (q := (n - S p)%nat).
     assert (Hq : Nat.add q (S p) = n).
     { unfold q. exact (Nat.sub_add (S p) n ltac:(lia)). }
     assert (Harith : Nat.add p (S (n - S p)) = n).
     { unfold q in Hq. lia. }
     rewrite Harith. reflexivity.
   }
  rewrite Hsplit.
  rewrite map_app. simpl.
  rewrite fold_right_app.
  assert (Hpre : fold_right Rplus 0%R
      (map (fun i => if Nat.eqb p i then x else 0%R) (seq 0 p)) = 0%R).
  { change (rsum (map (fun i => if Nat.eqb p i then x else 0%R) (seq 0 p)) = 0%R).
    assert (Hzero : forall i, In i (seq 0 p) ->
      (if Nat.eqb p i then x else 0%R) = 0%R).
    { intros i Hi. destruct (Nat.eqb p i) eqn:Heq.
      - apply Nat.eqb_eq in Heq. subst i.
        exfalso. apply (Nat.lt_irrefl p). apply in_seq in Hi. lia.
      - reflexivity. }
    rewrite (rsum_map_ext
      (fun i => if Nat.eqb p i then x else 0%R)
      (fun _ => 0%R) (seq 0 p) Hzero).
    clear Hsplit Hq Hzero.
    induction (seq 0 p) as [|a l IH].
    - reflexivity.
    - simpl. lra.
    }
  assert (Hpost : fold_right Rplus 0%R
      (map (fun i => if Nat.eqb p i then x else 0%R)
        (seq (S p) (n - S p))) = 0%R).
  { change (rsum (map (fun i => if Nat.eqb p i then x else 0%R)
        (seq (S p) (n - S p))) = 0%R).
    assert (Hzero : forall i, In i (seq (S p) (n - S p)) ->
      (if Nat.eqb p i then x else 0%R) = 0%R).
    { intros i Hi. destruct (Nat.eqb p i) eqn:Heq.
      - apply Nat.eqb_eq in Heq. subst i.
        exfalso. apply (Nat.lt_irrefl p). apply in_seq in Hi. lia.
      - reflexivity. }
    rewrite (rsum_map_ext
      (fun i => if Nat.eqb p i then x else 0%R)
      (fun _ => 0%R) (seq (S p) (n - S p)) Hzero).
    clear Hsplit Hq Hzero.
    induction (seq (S p) (n - S p)) as [|a l IH].
    - reflexivity.
    - simpl. lra.
  }
  rewrite (fold_right_Rplus_acc
    (map (fun i => if Nat.eqb p i then x else 0%R) (seq 0 p))
    (fold_right Rplus 0%R
      ((if Nat.eqb p p then x else 0%R) ::
       map (fun i => if Nat.eqb p i then x else 0%R)
         (seq (S p) (n - S p))))).
  simpl.
   rewrite Hpre.
   rewrite Hpost. simpl.
  rewrite Nat.eqb_refl. lra.
Qed.

Lemma SeriesC_fin2_round (f : fin 2 -> R) :
  SeriesC f = f 0%fin + f 1%fin.
Proof. apply SeriesC_fin2. Qed.

Definition branch_counter (c : nat) (b : fin 2) : nat :=
  2 * c + fin_to_nat b.

Definition walk_branch_term (row : list nat) (rest : list (list nat)) (c : nat) (b : fin 2)
    (i : nat) (D : nat -> R) : R :=
  if branch_counter c b <? length row
  then (INR (leafval row (branch_counter c b) i (length rest)) /
        INR (2 ^ length rest) * D i)%R
  else (INR (cnt rest (branch_counter c b - length row) i) /
        INR (2 ^ length rest) * D i)%R.

Definition walk_branch_eps (row : list nat) (rest : list (list nat)) (c : nat) (b : fin 2)
    (N : nat) (D : nat -> R) : R :=
  rsum (map (fun i => walk_branch_term row rest c b i D) (seq 0 N)).

Lemma leaf_branch_eps (row : list nat) (rest : list (list nat)) c b N (D : nat -> R) :
  (branch_counter c b < length row)%nat ->
  (nth (branch_counter c b) row 0%nat < N)%nat ->
  walk_branch_eps row rest c b N D =
    D (nth (branch_counter c b) row 0%nat).
Proof.
  intros Hfit Hbound. unfold walk_branch_eps, walk_branch_term.
  assert (Hcase : (branch_counter c b <? length row) = true)
    by (apply Nat.ltb_lt; exact Hfit).
  rewrite Hcase.
  assert (Hpow : ~ INR (2 ^ length rest) = 0%R).
  { apply not_0_INR. apply Nat.pow_nonzero. lia. }
  assert (Hext : forall i, In i (seq 0 N) ->
      (INR (leafval row (branch_counter c b) i (length rest)) /
          INR (2 ^ length rest) * D i)%R =
      (if Nat.eqb (nth (branch_counter c b) row 0%nat) i
       then D (nth (branch_counter c b) row 0%nat) else 0%R)).
  { intros i Hi. unfold leafval.
    destruct (Nat.eqb (nth (branch_counter c b) row 0%nat) i) eqn:Heq.
    - apply Nat.eqb_eq in Heq. subst i. simpl.
      field; exact Hpow.
    - rewrite Rdiv_0_l. rewrite Rmult_0_l. reflexivity.
  }
  rewrite (rsum_map_ext
    (fun i => (INR (leafval row (branch_counter c b) i (length rest)) /
      INR (2 ^ length rest) * D i)%R)
    (fun i => if Nat.eqb (nth (branch_counter c b) row 0%nat) i
      then D (nth (branch_counter c b) row 0%nat) else 0%R)
    (seq 0 N) Hext).
  apply rsum_indicator. exact Hbound.
Qed.
Lemma round_term_split (row : list nat) (rest : list (list nat)) (c i : nat)
    (D : nat -> R) :
  (INR (cnt (row :: rest) c i) /
      INR (2 ^ length (row :: rest)) * D i)%R =
  ((1/2 * walk_branch_term row rest c 0%fin i D) +
   (1/2 * walk_branch_term row rest c 1%fin i D))%R.
Proof.
  unfold walk_branch_term, branch_counter.
  replace (Nat.add c (Nat.add c 0%nat)) with (Nat.mul 2 c) by lia.
  replace (Nat.add (Nat.add c (Nat.add c 0%nat)) 0%nat) with
    (Nat.mul 2 c) by lia.
  replace (Nat.add (Nat.add c (Nat.add c 0%nat)) 1%nat) with
    (Nat.add (Nat.mul 2 c) 1%nat) by lia.
  destruct (Nat.ltb (Nat.mul 2 c) (length row)) eqn:H0;
    destruct (Nat.ltb (Nat.add (Nat.mul 2 c) 1%nat) (length row)) eqn:H1;
    simpl.
  all: repeat rewrite Nat.add_0_r.
  all: try (replace (Nat.add c c) with (Nat.mul 2 c) by lia).
  all: rewrite H0.
  all: rewrite H1.
  all: rewrite plus_INR.
  all: repeat rewrite plus_INR.
  all: assert (Hpow : ~ (2 ^ length rest = 0)%nat) by
    (apply Nat.pow_nonzero; lia).
  all: field.
  all: split.
  all: try (apply not_0_INR; apply Nat.pow_nonzero; lia).
  all: apply Rgt_not_eq; apply Rplus_lt_0_compat;
    rewrite <- INR_0; apply lt_INR; lia.
Qed.

Lemma round_eps_split (row : list nat) (rest : list (list nat)) (c N : nat)
    (D : nat -> R) :
  rsum (map (fun i =>
      (INR (cnt (row :: rest) c i) /
       INR (2 ^ length (row :: rest)) * D i)%R) (seq 0 N)) =
  ((1/2 * walk_branch_eps row rest c 0%fin N D) +
   (1/2 * walk_branch_eps row rest c 1%fin N D))%R.
Proof.
  unfold walk_branch_eps.
  rewrite (rsum_map_ext
    (fun i => (INR (cnt (row :: rest) c i) /
      INR (2 ^ length (row :: rest)) * D i)%R)
    (fun i => (1/2 * walk_branch_term row rest c 0%fin i D +
      1/2 * walk_branch_term row rest c 1%fin i D)%R)
    (seq 0 N)).
  - unfold rsum.
    induction (seq 0 N) as [|a l IH]; simpl; [lra|].
    rewrite IH. lra.
  - intros i Hi. apply round_term_split.
Qed.


Lemma walk_branch_term_nonneg (row : list nat) (rest : list (list nat)) c b i
    (D : nat -> R) :
  (forall j, (0 <= D j)%R) ->
  (0 <= walk_branch_term row rest c b i D)%R.
Proof.
  intros HD. unfold walk_branch_term.
  destruct (branch_counter c b <? length row) eqn:Hfit.
  all: apply Rmult_le_pos; [|apply HD].
  all: apply Rcomplements.Rdiv_le_0_compat; [apply pos_INR|].
  all: rewrite <- INR_0; apply lt_INR.
  all: pose proof (Nat.pow_nonzero 2 (length rest) ltac:(lia)) as Hpow; lia.
Qed.

Lemma walk_branch_eps_nonneg (row : list nat) (rest : list (list nat)) c b N (D : nat -> R) :
  (forall i, (0 <= D i)%R) ->
  (forall i, In i (seq 0 N) ->
    (0 <= walk_branch_term row rest c b i D)%R) ->
  (0 <= walk_branch_eps row rest c b N D)%R.
Proof.
  intros HD H. unfold walk_branch_eps.
  apply rsum_map_nonneg. exact H.
Qed.

Section AdvComp.
  Context `{!erisGS Σ}.
  Lemma twp_fldr_walk_adv_comp E (rows : list (list nat)) (vrows : val)
        (c A N : nat) (D : nat -> R) (L ε : R) :
    cap_final rows A = 0%nat ->
    (c < A)%nat ->
    (forall row, In row rows -> forall i, In i row -> (i < N)%nat) ->
    (forall i, (0 <= D i <= L)%R) ->
    ε = rsum (map (fun i => (INR (cnt rows c i) /
      INR (2 ^ length rows) * D i)%R) (seq 0 N)) ->
    [[{ ⌜is_list rows vrows⌝ ∗ ↯ ε }]]
      fldr_walk #() vrows #c @ E
    [[{ (i : nat), RET SOMEV #i; ↯ (D i) ∗ ⌜(i < N)%nat⌝ }]].
  Proof.
    induction rows as [|row rest IH] in c, A, vrows, ε |- *.
    - intros Hcap Hc Hbound HD Heps. simpl in Hcap. lia.
    - intros Hcap Hc Hbound HD Heps.
      iIntros (Φ) "[%Hrows Herr] HΦ".
      simpl in Hrows.
      destruct Hrows as (vrow & -> & Hrows).
      pose proof Hrows as Hrest_list.
      rewrite /fldr_walk. wp_rec. wp_pures.
      set ε2 := (fun b : fin 2 => walk_branch_eps row rest c b N D).
      wp_apply (twp_rand_exp_fin 1 1 E ε ε2 with "Herr") as (b) "Herr".
      { intros n. unfold ε2. apply walk_branch_eps_nonneg.
        - intros i. exact (proj1 (HD i)).
        - intros i Hi. apply walk_branch_term_nonneg. intros j. exact (proj1 (HD j)). }
      { rewrite SeriesC_fin2_round. unfold ε2. rewrite Heps.
         rewrite round_eps_split.
         change ((1/2)%R * walk_branch_eps row rest c 0%fin N D +
           (1/2)%R * walk_branch_eps row rest c 1%fin N D =
           (1/2)%R * walk_branch_eps row rest c 0%fin N D +
           (1/2)%R * walk_branch_eps row rest c 1%fin N D).
         ring.
       }
      assert (Hb_cases : b = 0%fin \/ b = 1%fin).
      { destruct (decide (b = 0%fin)) as [Hb|Hb].
        - left; exact Hb.
        - right. apply fin_to_nat_inj. pose proof (fin_to_nat_lt b) as Hlt.
          destruct (fin_to_nat b) as [|[|n]] eqn:Hbn.
          + exfalso. apply Hb. apply fin_to_nat_inj. simpl. exact Hbn.
          + reflexivity.
          + lia. }
      destruct Hb_cases as [Hb0|Hb1].
       + subst b. wp_pures.
          assert (Hidx : #(Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 0)) = #(2 * c)%nat).
          { change (LitV (LitInt (Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 0))) =
                      LitV (LitInt (Z.of_nat (2 * c)))).
            do 2 f_equal. rewrite Nat2Z.inj_mul. lia. }
          rewrite Hidx.
         wp_bind (list_length (inject_list row)).
         wp_apply (twp_list_length E row (inject_list row)).
         { iPureIntro. apply (is_list_inject row (inject_list row)). reflexivity. }
         iIntros (h) "%Hh"; simpl in Hh; subst h; wp_pures.
         case_bool_decide as Hfit.
         { wp_if.
           assert (Hfit_nat : (2 * c < length row)%nat) by (lia).
           assert (Hlabel : (nth (2 * c) row 0%nat < N)%nat).
           { apply Hbound with (row := row); [left; reflexivity|].
             apply nth_In. exact Hfit_nat. }
           assert (Hε0 : walk_branch_eps row rest c 0%fin N D =
               D (nth (2 * c) row 0%nat)).
           { assert (Hb0 : branch_counter c 0%fin = (2 * c)%nat) by (unfold branch_counter; simpl; lia). rewrite <- Hb0. rewrite <- Hb0 in Hfit_nat, Hlabel. apply leaf_branch_eps; [exact Hfit_nat|exact Hlabel]. }
           iDestruct "Herr" as "HerrX".
           replace (Nat.add c (Nat.add c 0%nat)) with (Nat.mul 2 c) by lia.
           wp_pures.
           assert (Hrow : is_list row (inject_list row)).
           { apply (is_list_inject row (inject_list row)). reflexivity. }
           iApply (twp_list_nth E (2 * c) row (inject_list row) $! Hrow).
           iIntros (v [Hnone | (r & -> & Hlookup)]); first eauto with lia.
           pose proof (nth_lookup_Some row (2 * c) 0%nat r Hlookup) as Hnth.
             iAssert (⌜r = nth (2 * c) row 0%nat⌝%I) as %->.
             { iPureIntro. symmetry. exact Hnth. }
             iApply ("HΦ" $! (nth (2 * c) row 0%nat)).
             iSplitL.
             { iApply (ec_eq with "HerrX"). unfold ε2. exact Hε0. }
             { iPureIntro. exact Hlabel. }
         } { wp_if.
           assert (Hrowcap : (length row <= 2 * c)%nat) by lia.
           assert (Hcase0 : (2 * c <? length row) = false) by
             (apply Nat.ltb_ge; exact Hrowcap).
           assert (Hb0 : branch_counter c 0%fin = (2 * c)%nat) by
             (unfold branch_counter; simpl; lia).
           assert (Hεnext : walk_branch_eps row rest c 0%fin N D =
               rsum (map (fun i =>
                 (INR (cnt rest (2 * c - length row) i) /
                  INR (2 ^ length rest) * D i)%R) (seq 0 N))).
           { unfold walk_branch_eps.
             unfold walk_branch_term.
             rewrite Hb0. rewrite Hcase0. reflexivity. }
           assert (Hcap' : cap_final rest (2 * A - length row) = 0%nat) by
             exact Hcap.
           set (cnext := Nat.sub (Nat.mul 2 c) (length row)).
           assert (Hc' : (cnext < Nat.sub (Nat.mul 2 A) (length row))%nat). { unfold cnext. lia. }
           assert (Hbound' : forall r, In r rest -> forall j, In j r -> (j < N)%nat).
           { intros r Hr j Hj. apply Hbound with (row := r); [right; exact Hr|exact Hj]. }
           assert (Hεnext' : ε2 0%fin =
               rsum (map (fun i =>
                 (INR (cnt rest (2 * c - length row) i) /
                  INR (2 ^ length rest) * D i)%R) (seq 0 N))).
           { unfold ε2. exact Hεnext. }
           wp_op.
           assert (Hsub :
             #(Z.sub (Z.of_nat (Nat.mul 2 c)) (Z.of_nat (length row))) =
             #(Nat.sub (Nat.mul 2 c) (length row))%nat).
           { change (LitV (LitInt (Z.sub (Z.of_nat (Nat.mul 2 c))
                     (Z.of_nat (length row)))) =
                       LitV (LitInt (Z.of_nat (Nat.sub (Nat.mul 2 c) (length row))))).
             rewrite <- Nat2Z.inj_sub; [reflexivity|exact Hrowcap]. }
           rewrite Hsub.
           fold fldr_walk.
           pose proof (IH vrow cnext (Nat.sub (Nat.mul 2 A) (length row))
             (ε2 0%fin) Hcap' Hc' Hbound' HD Hεnext' Φ) as Hspec.
           iApply (Hspec with "[Herr] HΦ").
           iSplit; [iPureIntro; exact Hrest_list|iFrame].
         }
         + subst b. wp_pures.
         wp_bind (list_length (inject_list row)).
         wp_apply (twp_list_length E row (inject_list row)).
         { iPureIntro. apply (is_list_inject row (inject_list row)). reflexivity. }
         iIntros (h) "%Hh"; simpl in Hh; subst h; wp_pures.
         case_bool_decide as Hfit1.
         { wp_if.
           assert (Hfit1_nat : (2 * c + 1 < length row)%nat) by lia.
           assert (Hlabel1 : (nth (2 * c + 1) row 0%nat < N)%nat).
           { apply Hbound with (row := row); [left; reflexivity|].
             apply nth_In. exact Hfit1_nat. }
           assert (Hε1 : walk_branch_eps row rest c 1%fin N D =
               D (nth (2 * c + 1) row 0%nat)).
           { assert (Hb1 : branch_counter c 1%fin = (2 * c + 1)%nat) by (unfold branch_counter; simpl; lia).
             rewrite <- Hb1. rewrite <- Hb1 in Hfit1_nat, Hlabel1.
             apply leaf_branch_eps; [exact Hfit1_nat|exact Hlabel1]. }
           iDestruct "Herr" as "Herr1".
           replace (Nat.add (Nat.add c (Nat.add c 0%nat)) 1%nat)
             with (Nat.add (Nat.mul 2 c) 1%nat) by lia.
           wp_pures.
           assert (Hrow : is_list row (inject_list row)).
           { apply (is_list_inject row (inject_list row)). reflexivity. }
           assert (Hidx1 : #(Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 1)) = #(2 * c + 1)%nat).
           { change (LitV (LitInt (Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 1))) =
                       LitV (LitInt (Z.of_nat (2 * c + 1)))).
             do 2 f_equal. rewrite <- Nat2Z.inj_mul.
             replace 1%Z with (Z.of_nat 1) by lia.
             rewrite <- Nat2Z.inj_add; lia. }
           rewrite Hidx1.
           wp_bind (list_nth (inject_list row) #(Nat.add (Nat.mul 2 c) 1%nat)).
           wp_apply (twp_list_nth E (Nat.add (Nat.mul 2 c) 1%nat) row (inject_list row) $! Hrow).
           iIntros (v [Hnone | (r & -> & Hlookup)]); first eauto with lia.
           pose proof (nth_lookup_Some row (2 * c + 1%nat) 0%nat r Hlookup) as Hnth.
           iAssert (⌜r = nth (2 * c + 1%nat) row 0%nat⌝%I) as %->.
           { iPureIntro. symmetry. exact Hnth. }
           iApply ("HΦ" $! (nth (2 * c + 1%nat) row 0%nat)).
           iSplitL.
           { iApply (ec_eq with "Herr1"). unfold ε2.
             all: first [exact Hε1 | symmetry; exact Hε1]. }
           { iPureIntro. exact Hlabel1. }
         } { wp_if.
           assert (Hrowcap1 : (length row <= 2 * c + 1)%nat) by lia.
           assert (Hcase1 : (2 * c + 1 <? length row) = false) by
             (apply Nat.ltb_ge; exact Hrowcap1).
           assert (Hb1 : branch_counter c 1%fin = (2 * c + 1)%nat) by
             (unfold branch_counter; simpl; lia).
           assert (Hεnext1 : walk_branch_eps row rest c 1%fin N D =
               rsum (map (fun i =>
                 (INR (cnt rest (2 * c + 1 - length row) i) /
                  INR (2 ^ length rest) * D i)%R) (seq 0 N))).
           { unfold walk_branch_eps. unfold walk_branch_term.
             rewrite Hb1. rewrite Hcase1. reflexivity. }
           assert (Hcap1' : cap_final rest (2 * A - length row) = 0%nat) by exact Hcap.
           set (cnext1 := Nat.sub (Nat.add (Nat.mul 2 c) 1%nat) (length row)).
           assert (Hval1 : #(Nat.sub (Nat.add (Nat.mul 2 c) 1%nat) (length row)) = #cnext1) by (unfold cnext1; reflexivity).
           assert (Hc1' : (cnext1 < Nat.sub (Nat.mul 2 A) (length row))%nat).
           { unfold cnext1. lia. }
           assert (Hbound1' : forall r, In r rest -> forall j, In j r -> (j < N)%nat).
           { intros r Hr j Hj. apply Hbound with (row := r); [right; exact Hr|exact Hj]. }
           assert (Hεnext1' : ε2 1%fin =
               rsum (map (fun i =>
                 (INR (cnt rest (2 * c + 1 - length row) i) /
                  INR (2 ^ length rest) * D i)%R) (seq 0 N))).
           { unfold ε2. exact Hεnext1. }
           wp_op.
           assert (Hsub1 :
             #(Z.sub (Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 1))
                    (Z.of_nat (length row))) =
             #(Nat.sub (Nat.add (Nat.mul 2 c) 1%nat) (length row))%nat).
           { change (LitV (LitInt (Z.sub (Z.add (Z.mul (Z.of_nat 2) (Z.of_nat c)) (Z.of_nat 1))
                                           (Z.of_nat (length row)))) =
                       LitV (LitInt (Z.of_nat (Nat.sub (Nat.add (Nat.mul 2 c) 1%nat) (length row))))).
             rewrite <- Nat2Z.inj_mul.
             replace 1%Z with (Z.of_nat 1) by lia.
             rewrite <- Nat2Z.inj_add.
             rewrite <- Nat2Z.inj_sub; [reflexivity|exact Hrowcap1]. }
           rewrite Hsub1.
           rewrite Hval1.
           fold fldr_walk.
           pose proof (IH vrow cnext1 (Nat.sub (Nat.mul 2 A) (length row))
             (ε2 1%fin) Hcap1' Hc1' Hbound1' HD Hεnext1' Φ) as Hspec1.
           iAssert (⌜is_list rest vrow⌝ ∗ ↯ (ε2 1%fin))%I with "[Herr]" as "Hpre".
           { iSplit; [iPureIntro; exact Hrest_list|iFrame]. }
           wp_apply (Hspec1 with "[Hpre] HΦ").
           iExact "Hpre".
         }
  Qed.
End AdvComp.
Section FldrRound.
  Context `{!erisGS Σ}.
End FldrRound.
