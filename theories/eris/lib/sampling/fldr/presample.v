From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia.
From clutch.eris Require Import eris.
From clutch.common Require Import inject.
From clutch.eris.lib Require Import list.
From clutch.eris.lib.sampling Require Import utils.
From clutch.eris.lib.sampling.fldr Require Import implementation model walk pure distribution list_total walk_spec round tape.

Import ListNotations.
#[local] Open Scope R.

Lemma bit_of_fin_to_nat (b : fin 2) :
  (if bit_of b then 1 else 0)%nat = fin_to_nat b.
Proof.
  destruct (fin_to_nat b) as [|n] eqn:Hn.
  - unfold bit_of. rewrite Hn. reflexivity.
  - destruct n as [|n].
    + unfold bit_of. rewrite Hn. reflexivity.
    + exfalso. pose proof (fin_to_nat_lt b). lia.
Qed.

Lemma walkc_zero_cons (row : list nat) (rest : list (list nat)) (c : nat)
    (bs : list (fin 2)) (i n : nat) :
  (length row <= 2 * c)%nat ->
  walkc rest (2 * c - length row) (map bit_of bs) = Some (i, n) ->
  walkc (row :: rest) c (map bit_of (0%fin :: bs)) = Some (i, S n).
Proof.
  intros Hcap Hwalk.
  assert (Hmap : map bit_of (0%fin :: bs) = false :: map bit_of bs).
  { simpl. rewrite bit_of_zero. reflexivity. }
  rewrite Hmap. simpl. repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_succ_l in Hcap.
  rewrite Nat.mul_1_l in Hcap.
  assert (Hfalse : (c + c <? length row) = false).
  { apply Nat.ltb_ge. exact Hcap. }
  rewrite Hfalse.
  rewrite Nat.mul_succ_l in Hwalk.
  rewrite Nat.mul_1_l in Hwalk.
  rewrite Hwalk. reflexivity.
Qed.

Lemma walkc_one_cons (row : list nat) (rest : list (list nat)) (c : nat)
    (bs : list (fin 2)) (i n : nat) :
  (length row <= 2 * c + 1)%nat ->
  walkc rest (2 * c + 1 - length row) (map bit_of bs) = Some (i, n) ->
  walkc (row :: rest) c (map bit_of (1%fin :: bs)) = Some (i, S n).
Proof.
  intros Hcap Hwalk.
  assert (Hmap : map bit_of (1%fin :: bs) = true :: map bit_of bs).
  { simpl. rewrite bit_of_one. reflexivity. }
  rewrite Hmap. simpl. repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_succ_l in Hcap.
  rewrite Nat.mul_1_l in Hcap.
  assert (Hfalse : (c + c + 1 <? length row) = false).
  { apply Nat.ltb_ge. exact Hcap. }
  rewrite Hfalse.
  rewrite Nat.mul_succ_l in Hwalk.
  rewrite Nat.mul_1_l in Hwalk.
  rewrite Hwalk. reflexivity.
Qed.

Lemma walkc_zero_singleton (row : list nat) (rest : list (list nat)) (c : nat) :
  (2 * c < length row)%nat ->
  walkc (row :: rest) c (map bit_of [0%fin]) = Some (nth (2 * c) row 0%nat, 1%nat).
Proof.
  intros Hfit.
  assert (Hmap : map bit_of [0%fin] = [false]).
  { simpl. rewrite bit_of_zero. reflexivity. }
  rewrite Hmap. simpl.
  repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_succ_l in Hfit.
  rewrite Nat.mul_1_l in Hfit.
  rewrite (proj2 (Nat.ltb_lt _ _) Hfit). reflexivity.
Qed.

Lemma walkc_one_singleton (row : list nat) (rest : list (list nat)) (c : nat) :
  (2 * c + 1 < length row)%nat ->
  walkc (row :: rest) c (map bit_of [1%fin]) = Some (nth (2 * c + 1) row 0%nat, 1%nat).
Proof.
  intros Hfit.
  assert (Hmap : map bit_of [1%fin] = [true]).
  { simpl. rewrite bit_of_one. reflexivity. }
  rewrite Hmap. simpl.
  repeat rewrite Nat.add_0_r.
  rewrite Nat.mul_succ_l in Hfit.
  rewrite Nat.mul_1_l in Hfit.
  rewrite (proj2 (Nat.ltb_lt _ _) Hfit). reflexivity.
Qed.

Section FldrPresample.
  Context `{!erisGS Σ}.
  Lemma presample_cont_zero E (row : list nat) (rest : list (list nat))
      (c cnext N : nat) (α : loc) (raw : list (fin 2))
      (e : expr) (Φ : val -> iProp Σ) (D : nat -> R) :
    (length row <= 2 * c)%nat ->
    cnext = (2 * c - length row)%nat ->
    (∀ (i : nat) (bs : list (fin 2)),
       ⌜walkc (row :: rest) c (map bit_of bs) = Some (i, length bs)⌝ ∗
       ⌜(i < N)%nat⌝ ∗ α ↪ (1%nat; raw ++ bs) ∗ ↯ (D i) -∗ WP e @ E [{ Φ }]) -∗
    (∀ (i : nat) (bs : list (fin 2)),
       ⌜walkc rest cnext (map bit_of bs) = Some (i, length bs)⌝ ∗
       ⌜(i < N)%nat⌝ ∗ α ↪ (1%nat; (raw ++ [0%fin]) ++ bs) ∗ ↯ (D i) -∗ WP e @ E [{ Φ }]).
  Proof.
    iIntros (Hcap ->) "Hfull".
    iIntros (i bs) "Hpre".
    iDestruct "Hpre" as "(%Hwalk & Hrest)".
    iDestruct "Hrest" as "(%Hi & Hres)".
    iDestruct "Hres" as "[Htapex Hdx]".
    iApply ("Hfull" $! i (0%fin :: bs) with "[Htapex Hdx]").
    iSplitL "".
    - iPureIntro; apply walkc_zero_cons; [exact Hcap|exact Hwalk].
    - iSplitL "".
      + iPureIntro; exact Hi.
      + iSplitL "Htapex".
        * rewrite <- (app_assoc raw [0%fin] bs). iExact "Htapex".
        * iExact "Hdx".
  Qed.
  Lemma presample_cont_one E (row : list nat) (rest : list (list nat))
      (c cnext N : nat) (α : loc) (raw : list (fin 2))
      (e : expr) (Φ : val -> iProp Σ) (D : nat -> R) :
    (length row <= 2 * c + 1)%nat ->
    cnext = (2 * c + 1 - length row)%nat ->
    (∀ (i : nat) (bs : list (fin 2)),
       ⌜walkc (row :: rest) c (map bit_of bs) = Some (i, length bs)⌝ ∗
       ⌜(i < N)%nat⌝ ∗ α ↪ (1%nat; raw ++ bs) ∗ ↯ (D i) -∗ WP e @ E [{ Φ }]) -∗
    (∀ (i : nat) (bs : list (fin 2)),
       ⌜walkc rest cnext (map bit_of bs) = Some (i, length bs)⌝ ∗
       ⌜(i < N)%nat⌝ ∗ α ↪ (1%nat; (raw ++ [1%fin]) ++ bs) ∗ ↯ (D i) -∗ WP e @ E [{ Φ }]).
  Proof.
    iIntros (Hcap ->) "Hfull".
    iIntros (i bs) "Hpre".
    iDestruct "Hpre" as "(%Hwalk & Hrest)".
    iDestruct "Hrest" as "(%Hi & Hres)".
    iDestruct "Hres" as "[Htapex Hdx]".
    iApply ("Hfull" $! i (1%fin :: bs) with "[Htapex Hdx]").
    iSplitL "".
    - iPureIntro; apply walkc_one_cons; [exact Hcap|exact Hwalk].
    - iSplitL "".
      + iPureIntro; exact Hi.
      + iSplitL "Htapex".
        * rewrite <- (app_assoc raw [1%fin] bs). iExact "Htapex".
        * iExact "Hdx".
  Qed.
  Lemma twp_fldr_presample_walk E (rows : list (list nat))
        (c A N : nat) (α : loc) (raw : list (fin 2))
        (e : expr) (Φ : val -> iProp Σ) (D : nat -> R) (L ε : R) :
    cap_final rows A = 0%nat ->
    (c < A)%nat ->
    (forall row, In row rows -> forall i, In i row -> (i < N)%nat) ->
    (forall i, (0 <= D i <= L)%R) ->
    to_val e = None ->
    ε = rsum (map (fun i => (INR (cnt rows c i) / INR (2 ^ length rows) * D i)%R) (seq 0%nat N)) ->
    α ↪ (1%nat; raw) ∗ ↯ ε ∗
    (∀ (i : nat) (bs : list (fin 2)),
       ⌜walkc rows c (map bit_of bs) = Some (i, length bs)⌝ ∗ ⌜(i < N)%nat⌝ ∗
       α ↪ (1%nat; raw ++ bs) ∗ ↯ (D i) -∗ WP e @ E [{ Φ }])
    ⊢ WP e @ E [{ Φ }].
  Proof.
    induction rows as [|row rest IH] in c, A, raw, e, Φ, D, L, ε |- *.
    - intros Hcap Hc Hbound HD He Heps. simpl in Hcap. lia.
    - intros Hcap Hc Hbound HD He Heps.
      iIntros "(Htape & Herr & Hnext)".
      set (ε2 := (fun b : fin 2 => walk_branch_eps row rest c b N D)).
      unshelve wp_apply (twp_presample_adv_comp 1 1 E e α Φ raw ε ε2
        with "[$Htape $Herr Hnext]").
      { exact He. }
      { intros b. unfold ε2. apply walk_branch_eps_nonneg.
        - intros i. exact (proj1 (HD i)).
        - intros i Hi. apply walk_branch_term_nonneg. intros j. exact (proj1 (HD j)). }
      { rewrite SeriesC_fin2_round. unfold ε2. rewrite Heps.
        rewrite round_eps_split.
        change ((1/2)%R * walk_branch_eps row rest c 0%fin N D +
          (1/2)%R * walk_branch_eps row rest c 1%fin N D =
          (1/2)%R * walk_branch_eps row rest c 0%fin N D +
          (1/2)%R * walk_branch_eps row rest c 1%fin N D).
        ring. }
      iIntros (b) "[Herr Htape]".
      assert (Hb_cases : b = 0%fin \/ b = 1%fin).
      { destruct (decide (b = 0%fin)) as [Hb|Hb].
        - left; exact Hb.
        - right. apply fin_to_nat_inj. pose proof (fin_to_nat_lt b) as Hlt.
          destruct (fin_to_nat b) as [|[|n]] eqn:Hbn.
          + exfalso. apply Hb. apply fin_to_nat_inj. simpl. exact Hbn.
          + reflexivity.
          + lia. }
      destruct Hb_cases as [Hb0|Hb1].
      * subst b.
        destruct (Nat.lt_ge_cases (2 * c) (length row)) as [Hfit0|Hfit0].
        { assert (Hlabel0 : (nth (2 * c) row 0%nat < N)%nat).
          { apply Hbound with (row := row); [left; reflexivity|].
            apply nth_In. exact Hfit0. }
          assert (Hε0 : ε2 0%fin = D (nth (2 * c) row 0%nat)).
          { unfold ε2. assert (Hb0 : (branch_counter c 0%fin = 2 * c)%nat).
            { unfold branch_counter. simpl. rewrite Nat.add_0_r. reflexivity. }
            assert (Hfit0' : (branch_counter c 0%fin < length row)%nat) by (rewrite Hb0; exact Hfit0).
            assert (Hlabel0' : (nth (branch_counter c 0%fin) row 0%nat < N)%nat) by (rewrite Hb0; exact Hlabel0).
            rewrite <- Hb0. apply leaf_branch_eps; [exact Hfit0'|exact Hlabel0']. }
          iApply ("Hnext" $! (nth (2 * c) row 0%nat) [0%fin]).
          iSplitL "".
          - iPureIntro; apply walkc_zero_singleton; exact Hfit0.
          - iSplitL "".
            + iPureIntro; exact Hlabel0.
            + iSplitL "Htape".
              * iExact "Htape".
              * iApply (ec_eq with "Herr"). exact Hε0. }
        { assert (Hcase0 : (2 * c <? length row) = false).
          { apply Nat.ltb_ge. exact Hfit0. }
          assert (Hcap' : cap_final rest (2 * A - length row) = 0%nat) by exact Hcap.
          set (cnext := (2 * c - length row)%nat).
          assert (Hc' : (cnext < 2 * A - length row)%nat).
          { unfold cnext. lia. }
          assert (Hbound' : forall r, In r rest -> forall j, In j r -> (j < N)%nat).
          { intros r Hr j Hj. apply Hbound with (row := r); [right; exact Hr|exact Hj]. }
          assert (Hεnext : ε2 0%fin =
              rsum (map (fun i => (INR (cnt rest (2 * c - length row) i) /
                INR (2 ^ length rest) * D i)%R) (seq 0%nat N))).
          { unfold ε2, walk_branch_eps, walk_branch_term.
            assert (Hb0 : (branch_counter c 0%fin = 2 * c)%nat).
            { unfold branch_counter. simpl. rewrite Nat.add_0_r. reflexivity. }
            rewrite Hb0. rewrite Hcase0. reflexivity. }
          pose proof (IH cnext (2 * A - length row)%nat (raw ++ [0%fin]) e Φ D L (ε2 0%fin)
            Hcap' Hc' Hbound' HD He Hεnext) as Hspec.
          iPoseProof (presample_cont_zero E row rest c cnext N α raw e Φ D Hfit0
              ltac:(unfold cnext; reflexivity) with "[Hnext]") as "Hnext'".
          all: try iFrame.
          iApply (Hspec with "[Htape Herr Hnext']").
          iSplitL "Htape".
          - iExact "Htape".
          - iSplitL "Herr".
            + iExact "Herr".
            + iExact "Hnext'".
          }
      * subst b.
        destruct (Nat.lt_ge_cases (2 * c + 1) (length row)) as [Hfit1|Hfit1].
        { assert (Hlabel1 : (nth (2 * c + 1) row 0%nat < N)%nat).
          { apply Hbound with (row := row); [left; reflexivity|].
            apply nth_In. exact Hfit1. }
          assert (Hε1 : ε2 1%fin = D (nth (2 * c + 1) row 0%nat)).
          { unfold ε2. assert (Hb1 : (branch_counter c 1%fin = 2 * c + 1)%nat).
            { unfold branch_counter. simpl. reflexivity. }
            assert (Hfit1' : (branch_counter c 1%fin < length row)%nat) by (rewrite Hb1; exact Hfit1).
            assert (Hlabel1' : (nth (branch_counter c 1%fin) row 0%nat < N)%nat) by (rewrite Hb1; exact Hlabel1).
            rewrite <- Hb1. apply leaf_branch_eps; [exact Hfit1'|exact Hlabel1']. }
          iApply ("Hnext" $! (nth (2 * c + 1) row 0%nat) [1%fin]).
          iSplitL "".
          - iPureIntro; apply walkc_one_singleton; exact Hfit1.
          - iSplitL "".
            + iPureIntro; exact Hlabel1.
            + iSplitL "Htape".
              * iExact "Htape".
              * iApply (ec_eq with "Herr"). exact Hε1. }
        { assert (Hcase1 : (2 * c + 1 <? length row) = false).
          { apply Nat.ltb_ge. exact Hfit1. }
          assert (Hcap1' : cap_final rest (2 * A - length row) = 0%nat) by exact Hcap.
          set (cnext1 := (2 * c + 1 - length row)%nat).
          assert (Hc1' : (cnext1 < 2 * A - length row)%nat).
          { unfold cnext1. lia. }
          assert (Hbound1' : forall r, In r rest -> forall j, In j r -> (j < N)%nat).
          { intros r Hr j Hj. apply Hbound with (row := r); [right; exact Hr|exact Hj]. }
          assert (Hεnext1 : ε2 1%fin =
              rsum (map (fun i => (INR (cnt rest (2 * c + 1 - length row) i) /
                INR (2 ^ length rest) * D i)%R) (seq 0%nat N))).
          { unfold ε2, walk_branch_eps, walk_branch_term.
            assert (Hb1 : (branch_counter c 1%fin = 2 * c + 1)%nat).
            { unfold branch_counter. simpl. reflexivity. }
            rewrite Hb1. rewrite Hcase1. reflexivity. }
          pose proof (IH cnext1 (2 * A - length row)%nat (raw ++ [1%fin]) e Φ D L (ε2 1%fin)
            Hcap1' Hc1' Hbound1' HD He Hεnext1) as Hspec1.
          iPoseProof (presample_cont_one E row rest c cnext1 N α raw e Φ D Hfit1
              ltac:(unfold cnext1; reflexivity) with "[Hnext]") as "Hnext1'".
          all: try iFrame.
          iApply (Hspec1 with "[Htape Herr Hnext1']").
          iSplitL "Htape".
          - iExact "Htape".
          - iSplitL "Herr".
            + iExact "Herr".
            + iExact "Hnext1'".
          }
  Qed.

  Lemma twp_fldr_presample_round E (ws : list nat) (α : loc) (raw : list (fin 2))
        (e : expr) (Φ : val -> iProp Σ) (D : nat -> R) (L ε : R) :
    admissible ws -> nondegenerate ws -> to_val e = None ->
    (forall i, (0 <= D i <= L)%R) ->
    SeriesC (fun i => proposal_mass ws i * D i)%R = ε ->
    α ↪ (1%nat; raw) ∗ ↯ ε ∗
    (∀ (i : nat) (bs : list (fin 2)),
       ⌜round_ok ws bs i⌝ ∗ ⌜(i < length (extended_weights ws))%nat⌝ ∗
       α ↪ (1%nat; raw ++ bs) ∗ ↯ (D i) -∗ WP e @ E [{ Φ }])
    ⊢ WP e @ E [{ Φ }].
  Proof.
    intros Hadm Hnd He HD Heps.
    assert (Hcap : cap_final (ddg_table ws) 1 = 0%nat).
    { apply ddg_table_cap_final; assumption. }
    assert (Hbound : forall row, In row (ddg_table ws) -> forall i, In i row ->
      (i < length (extended_weights ws))%nat).
    { intros row Hrow i Hi. apply ddg_table_index_bound with (ws := ws) (row := row) (i := i); assumption. }
    assert (Heps' : ε =
      rsum (map (fun i => (INR (cnt (ddg_table ws) 0 i) /
        INR (2 ^ length (ddg_table ws)) * D i)%R)
        (seq 0%nat (length (extended_weights ws))))).
    { rewrite <- Heps.
      rewrite proposal_mass_expectation.
      apply rsum_map_ext.
      intros i Hi. apply in_seq in Hi as [_ HiN]. simpl in HiN.
      assert (Hlt : (nth i (extended_weights ws) 0%nat < denominator ws)%nat) by (exact (Hnd i HiN)).
      rewrite <- (ddg_mass_is_proposal_mass ws i HiN Hlt).
      unfold ddg_mass.
      rewrite <- (pure.fldr_round_count ws i Hadm).
      rewrite <- (pure.cnt_naccept (ddg_table ws) 0 i).
      unfold denominator.
      rewrite ddg_table_depth.
      reflexivity. }
    iIntros "(Htape & Herr & Hnext)".
    iApply (twp_fldr_presample_walk E (ddg_table ws) 0 1
      (length (extended_weights ws)) α raw e Φ D L ε Hcap ltac:(lia)
      Hbound HD He Heps').
    iSplitL "Htape".
    - iExact "Htape".
    - iSplitL "Herr".
      + iExact "Herr".
      + iIntros (i bs) "(%Hwalk & %Hi & Htape' & HDi)".
        iApply ("Hnext" $! i bs).
        iSplitL "".
        * iPureIntro. exact Hwalk.
        * iSplitL "".
          -- iPureIntro. exact Hi.
          -- iSplitL "Htape'".
             ++ iExact "Htape'".
             ++ iExact "HDi".
  Qed.
End FldrPresample.
