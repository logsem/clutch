From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia.
From Coquelicot Require Import Hierarchy.
From clutch.prob Require Import distribution.
From clutch.eris.lib.sampling.utils Require Import lemmas.
From clutch.eris.lib.sampling.fldr Require Import model walk pure.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(** * Nondegenerate FLDR tables *)

Definition nondegenerate (ws : list nat) : Prop :=
  forall i, i < length (extended_weights ws) ->
            nth i (extended_weights ws) 0 < denominator ws.

Lemma nondegenerate_forallb ws :
  forallb (fun w => Nat.ltb w (denominator ws)) (extended_weights ws) = true ->
  nondegenerate ws.
Proof.
  intros H i Hi.
  apply Nat.ltb_lt.
  pose proof (proj1 (forallb_forall
    (fun w => Nat.ltb w (denominator ws)) (extended_weights ws)) H) as Hforall.
  apply Hforall. apply nth_In. exact Hi.
Qed.

Example nondegenerate_not_one : ~ nondegenerate [1].
Proof.
  intro H.
  assert (Hi : 0 < length (extended_weights [1])) by (vm_compute; lia).
  specialize (H 0 Hi).
  vm_compute in H; lia.
Qed.

Example nondegenerate_not_eight : ~ nondegenerate [8].
Proof.
  intro H.
  assert (Hi : 0 < length (extended_weights [8])) by (vm_compute; lia).
  specialize (H 0 Hi).
  vm_compute in H; lia.
Qed.

Example nondegenerate_321 : nondegenerate [3; 2; 1].
Proof. apply nondegenerate_forallb; vm_compute; reflexivity. Qed.

Example nondegenerate_5 : nondegenerate [5].
Proof. apply nondegenerate_forallb; vm_compute; reflexivity. Qed.

Example nondegenerate_22 : nondegenerate [2; 2].
Proof. apply nondegenerate_forallb; vm_compute; reflexivity. Qed.

Example nondegenerate_201 : nondegenerate [2; 0; 1].
Proof. apply nondegenerate_forallb; vm_compute; reflexivity. Qed.

Lemma nondegenerate_mod ws i :
  nondegenerate ws ->
  i < length (extended_weights ws) ->
  nth i (extended_weights ws) 0 mod denominator ws =
  nth i (extended_weights ws) 0.
Proof.
  intros H Hi. apply Nat.mod_small. exact (H i Hi).
Qed.

(** * Totality of the finite table walk *)

Lemma walk_total rows A c bs :
  cap_final rows A = 0 -> c < A -> length bs = length rows ->
  exists i, walk rows c bs = Some i.
Proof.
  induction rows as [|row rest IH] in A, c, bs |- *.
  - intros Hcap Hc Hlen. exfalso. simpl in Hcap. lia.
  - intros Hcap Hc Hlen.
    destruct bs as [|b bs]; [simpl in Hlen; lia|].
    simpl in Hlen.
    simpl in Hcap.
    set (c' := 2 * c + (if b then 1 else 0)).
    assert (Hc' : c' < 2 * A).
    { subst c'. destruct b; lia. }
    destruct (c' <? length row) eqn:Hfit.
    + exists (nth c' row 0).
      unfold walk. fold c'. rewrite Hfit. reflexivity.
    + assert (Hrow : length row <= c') by
        (apply Nat.ltb_ge; exact Hfit).
      assert (Hnext : c' - length row < 2 * A - length row) by lia.
      assert (Hrest : length bs = length rest) by lia.
      specialize (IH (2 * A - length row) (c' - length row) bs
        Hcap Hnext Hrest) as [i Hi].
      exists i. unfold walk. fold c'. rewrite Hfit. exact Hi.
Qed.

Lemma extended_weights_in_nth ws w :
  In w (extended_weights ws) ->
  exists i, i < length (extended_weights ws) /\
            nth i (extended_weights ws) 0 = w.
Proof.
  intro Hw. now apply In_nth.
Qed.

Lemma modsum_indexed_denominator ws :
  admissible ws -> nondegenerate ws ->
  modsum (dyadic_width ws)
    (indexed_weights (extended_weights ws)) = denominator ws.
Proof.
  intros Hadm Hnd.
  unfold modsum.
  assert (Hmod :
    map (fun iw => snd iw mod 2 ^ dyadic_width ws)
      (indexed_weights (extended_weights ws)) =
    map snd (indexed_weights (extended_weights ws))).
  { apply map_ext_in. intros [i w] Hiw.
    assert (Hsnd : map snd (indexed_weights (extended_weights ws)) =
        extended_weights ws).
    { unfold indexed_weights. apply map_snd_combine. rewrite seq_length. reflexivity. }
    assert (Hwmap : In w (map snd (indexed_weights (extended_weights ws)))).
    { apply in_map_iff. exists (i, w). split; [reflexivity|exact Hiw]. }
    rewrite Hsnd in Hwmap.
    destruct (extended_weights_in_nth ws w Hwmap) as [j [Hj Hjth]].
    change (w mod 2 ^ dyadic_width ws = w).
    rewrite <- Hjth.
    apply Nat.mod_small. exact (Hnd j Hj).
  }
  rewrite Hmod.
  rewrite (nsum_indexed_snd (extended_weights ws)).
  rewrite (extended_weight_sum ws Hadm).
  unfold denominator. reflexivity.
Qed.

Lemma ddg_table_cap_final ws :
  admissible ws -> nondegenerate ws ->
  cap_final (ddg_table ws) 1 = 0.
Proof.
  intros Hadm Hnd.
  unfold ddg_table.
  pose proof (rows_lsb_capacity (dyadic_width ws)
    (indexed_weights (extended_weights ws)) 1) as Hcap.
  assert (Hbound :
    modsum (dyadic_width ws) (indexed_weights (extended_weights ws)) <=
    1 * 2 ^ dyadic_width ws).
  { rewrite Nat.mul_1_l.
    rewrite (modsum_indexed_denominator ws Hadm Hnd).
    reflexivity. }
  destruct (Hcap Hbound) as [_ Hfinal].
  rewrite Hfinal.
  rewrite (modsum_indexed_denominator ws Hadm Hnd).
  unfold denominator.
  lia.
Qed.

Theorem walk_total_table ws bs :
  admissible ws -> nondegenerate ws ->
  length bs = dyadic_width ws ->
  exists i, walk (ddg_table ws) 0 bs = Some i.
Proof.
  intros Hadm Hnd Hlen.
  apply walk_total with (A := 1) (c := 0).
  - apply ddg_table_cap_final; assumption.
  - lia.
  - rewrite ddg_table_depth. exact Hlen.
Qed.

Lemma walk_some_in rows c bs i :
  walk rows c bs = Some i ->
  exists row, In row rows /\ In i row.
Proof.
  induction rows as [|row rest IH] in c, bs |- *.
  - simpl. discriminate.
  - destruct bs as [|b bs]; simpl; try discriminate.
    set (c' := 2 * c + (if b then 1 else 0)).
    destruct (c' <? length row) eqn:Hfit.
    + intros H.
      unfold walk in H. fold c' in H. rewrite Hfit in H.
      inversion H.
      exists row. split; [now left|]. apply nth_In.
      apply Nat.ltb_lt. exact Hfit.
    + intros H.
      unfold walk in H. fold c' in H. rewrite Hfit in H.
      apply IH in H as [r [Hr Hi]].
      exists r. split; [now right|exact Hi].
Qed.

Corollary walk_table_index_bound ws bs i :
  walk (ddg_table ws) 0 bs = Some i ->
  i < length (extended_weights ws).
Proof.
  intro Hwalk.
  destruct (walk_some_in _ _ _ _ Hwalk) as [row [Hrow Hi]].
  eapply ddg_table_index_bound; eauto.
Qed.

(** * The finite target distribution *)

Lemma target_mass_pos ws (Hws : admissible ws) i :
  (0 <= target_mass ws i)%R.
Proof.
  pose proof (admissible_weight_sum_pos ws Hws) as Hsum.
  unfold target_mass.
  destruct (i <? length ws) eqn:Hi; [|lra].
  apply Rcomplements.Rdiv_le_0_compat.
  - apply pos_INR.
  - rewrite <- INR_0. apply lt_INR. exact Hsum.
Qed.

Lemma target_mass_ex_seriesC ws :
  ex_seriesC (target_mass ws).
Proof.
  apply ex_seriesC_ex_bounded with (n := length ws).
  intros k Hk. apply target_mass_invalid. exact Hk.
Qed.

Lemma fold_right_Rplus_acc xs z :
  fold_right Rplus z xs = (fold_right Rplus 0%R xs + z)%R.
Proof.
  induction xs as [|x xs IH]; simpl; [lra|]. rewrite IH. lra.
Qed.
Lemma sum_n_seq (f : nat -> R) (n : nat) :
  (@Hierarchy.sum_n R_AbelianMonoid f n) =
  fold_right Rplus 0%R (map f (seq 0 (S n))).
Proof.
  induction n as [|n IH].
  - rewrite (@Hierarchy.sum_O R_AbelianMonoid f). simpl. rewrite Rplus_0_r. reflexivity.
  - rewrite (@Hierarchy.sum_Sn R_AbelianMonoid f n).
    replace (S (S n)) with (S n + 1) by lia.
    rewrite (seq_app (S n) 1 0).
    rewrite map_app.
    rewrite Nat.add_0_l.
    assert (Htail : map f (seq (S n) 1) = [f (S n)]) by reflexivity.
    rewrite Htail.
    rewrite fold_right_app.
    assert (Hsingle : fold_right Rplus 0%R [f (S n)] = f (S n)).
    { simpl. rewrite Rplus_0_r. reflexivity. }
    rewrite Hsingle.
    rewrite (fold_right_Rplus_acc (map f (seq 0 (S n))) (f (S n))).
    rewrite IH. reflexivity.

Qed.
Lemma fldr_series_finite (f : nat -> R) (n : nat) :
  (forall k, n <= k -> f k = 0%R) ->
  SeriesC f = fold_right Rplus 0%R (map f (seq 0 n)).
Proof.
  intros Hzero.
  destruct n as [|n].
  - assert (Hf0 : forall k, f k = 0%R).
    { intros k. apply Hzero. lia. }
    rewrite (SeriesC_ext f (fun _ => 0%R) Hf0).
    assert (Hzero0 : forall k : nat, (fun _ => 0%R) k = 0%R) by reflexivity.
    rewrite (SeriesC_0 (fun _ : nat => 0%R) Hzero0).
    reflexivity.
  - assert (Hext : forall k,
        f k = if bool_decide (k <= n) then f k else 0%R).
    { intros k. case_bool_decide as Hk; [reflexivity|].
      assert (Hkn : S n <= k) by lia.
      rewrite (Hzero k Hkn). reflexivity. }
    rewrite (SeriesC_ext f
      (fun k => if bool_decide (k <= n) then f k else 0%R) Hext).
    rewrite SeriesC_nat_bounded.
    apply sum_n_seq.
Qed.

Program Definition fldr_distr (ws : list nat) (Hws : admissible ws) : distr nat :=
  MkDistr (target_mass ws) (target_mass_pos ws Hws) _ _.
Next Obligation.
  intros ws Hws. exact (target_mass_ex_seriesC ws).
Qed.
Next Obligation.
  intros ws Hws.
  rewrite (fldr_series_finite (target_mass ws) (length ws)).
  - rewrite (target_mass_normalized ws Hws). apply Rle_refl.
  - intros k Hk. apply target_mass_invalid. exact Hk.
Qed.

Theorem fldr_distr_mass ws (Hws : admissible ws) :
  SeriesC (fldr_distr ws Hws) = 1%R.
Proof.
  rewrite (fldr_series_finite (target_mass ws) (length ws)).
  - apply target_mass_normalized. exact Hws.
  - intros k Hk. apply target_mass_invalid. exact Hk.
Qed.

Lemma proposal_mass_invalid ws i :
  length (extended_weights ws) <= i -> proposal_mass ws i = 0%R.
Proof.
  intros Hi. apply Nat.ltb_ge in Hi. unfold proposal_mass. rewrite Hi. reflexivity.
Qed.

Lemma target_mass_expectation ws (D : nat -> R) :
  SeriesC (fun i => target_mass ws i * D i)%R =
  fold_right Rplus 0%R
    (map (fun i => (target_mass ws i * D i)%R) (seq 0 (length ws))).
Proof.
  apply fldr_series_finite.
  intros k Hk. rewrite (target_mass_invalid ws k Hk). lra.
Qed.

Lemma proposal_mass_expectation ws (D : nat -> R) :
  SeriesC (fun i => proposal_mass ws i * D i)%R =
  fold_right Rplus 0%R
    (map (fun i => (proposal_mass ws i * D i)%R)
      (seq 0 (length (extended_weights ws)))).
Proof.
  apply fldr_series_finite.
  intros k Hk. rewrite (proposal_mass_invalid ws k Hk). lra.
Qed.

Lemma target_mass_expectation_ex_seriesC ws (D : nat -> R) :
  ex_seriesC (fun i => target_mass ws i * D i)%R.
Proof.
  apply ex_seriesC_ex_bounded with (n := length ws).
  intros k Hk. rewrite (target_mass_invalid ws k Hk). lra.
Qed.

Lemma proposal_mass_expectation_ex_seriesC ws (D : nat -> R) :
  ex_seriesC (fun i => proposal_mass ws i * D i)%R.
Proof.
  apply ex_seriesC_ex_bounded with (n := length (extended_weights ws)).
  intros k Hk. rewrite (proposal_mass_invalid ws k Hk). lra.
Qed.
