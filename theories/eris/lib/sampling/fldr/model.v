From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia.
Import ListNotations.

(** A small, executable pure model of the arithmetic half of FLDR.  Labels are
    zero based.  The last extended label is the rejection label. *)

Definition weight_sum (ws : list nat) : nat := fold_right Nat.add 0%nat ws.
Definition admissible (ws : list nat) : Prop := ws <> [] /\ 0 < weight_sum ws.
Definition dyadic_width (ws : list nat) : nat := Nat.log2_up (weight_sum ws).
Definition denominator (ws : list nat) : nat := 2 ^ dyadic_width ws.
Definition rejection_weight (ws : list nat) : nat := denominator ws - weight_sum ws.
Definition extended_weights (ws : list nat) : list nat := ws ++ [rejection_weight ws].

Lemma denominator_bounds ws :
  admissible ws ->
  weight_sum ws <= denominator ws /\ denominator ws < 2 * weight_sum ws.
Proof.
  intros [_ Hpos].
  unfold denominator, dyadic_width.
  destruct (Nat.eq_dec (weight_sum ws) 1) as [->|Hne].
  - rewrite Nat.log2_up_1. simpl. lia.
  - assert (1 < weight_sum ws) by lia.
    pose proof (Nat.log2_up_spec _ H) as [Hlo Hhi].
    split; [exact Hhi|].
    pose proof (Nat.log2_up_pos _ H) as Hk.
    replace (Nat.log2_up (weight_sum ws)) with
      (S (Nat.pred (Nat.log2_up (weight_sum ws)))) by lia.
    rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma denominator_pos ws : 0 < denominator ws.
Proof.
  unfold denominator.
  assert (2 ^ dyadic_width ws <> 0) by (apply Nat.pow_nonzero; lia).
  lia.
Qed.

Lemma rejection_weight_nonnegative ws :
  admissible ws -> weight_sum ws + rejection_weight ws = denominator ws.
Proof.
  intros H. unfold rejection_weight.
  pose proof (denominator_bounds ws H) as [Hle _]. lia.
Qed.

Lemma fold_right_add_acc xs z :
  fold_right Nat.add z xs = fold_right Nat.add 0%nat xs + z.
Proof. induction xs; simpl; lia. Qed.

Lemma extended_weight_sum ws :
  admissible ws -> weight_sum (extended_weights ws) = denominator ws.
Proof.
  intros H. unfold extended_weights, weight_sum.
  rewrite fold_right_app. simpl. rewrite fold_right_add_acc, Nat.add_0_r.
  change (weight_sum ws + rejection_weight ws = denominator ws).
  apply rejection_weight_nonnegative; exact H.
Qed.

(** The executable table constructor.  It emits the labels whose current
    least-significant bit is one, shifts every weight, and repeats.  Reversing
    the rows gives FLDR's most-significant-bit-first table. *)
Definition indexed_weights (ws : list nat) : list (nat * nat) :=
  combine (seq 0 (length ws)) ws.

Definition one_row (iws : list (nat * nat)) : list nat :=
  map fst (filter (fun iw => Nat.eqb (snd iw mod 2) 1) iws).

Definition shift_weights (iws : list (nat * nat)) : list (nat * nat) :=
  map (fun iw => (fst iw, snd iw / 2)) iws.

Fixpoint rows_lsb (fuel : nat) (iws : list (nat * nat)) : list (list nat) :=
  match fuel with
  | 0 => []
  | S fuel' => one_row iws :: rows_lsb fuel' (shift_weights iws)
  end.

Definition ddg_table (ws : list nat) : list (list nat) :=
  rev (rows_lsb (dyadic_width ws) (indexed_weights (extended_weights ws))).

Lemma rows_lsb_length fuel iws : length (rows_lsb fuel iws) = fuel.
Proof. induction fuel as [|fuel IH] in iws |- *; simpl; auto. Qed.

Lemma ddg_table_depth ws : length (ddg_table ws) = dyadic_width ws.
Proof. unfold ddg_table. rewrite rev_length, rows_lsb_length. reflexivity. Qed.

Lemma in_shift_weights_label i iws :
  In i (map fst (shift_weights iws)) <-> In i (map fst iws).
Proof.
  unfold shift_weights. induction iws as [|[j w] iws IH]; simpl; [tauto|].
  rewrite IH. tauto.
Qed.

Lemma one_row_labels i iws : In i (one_row iws) -> In i (map fst iws).
Proof.
  unfold one_row. intros Hin.
  apply in_map_iff in Hin as [[j w] [<- Hin]]. simpl in *.
  apply filter_In in Hin as [Hin _].
  apply in_map_iff. exists (j, w). simpl. auto.
Qed.

Lemma rows_lsb_labels fuel iws row i :
  In row (rows_lsb fuel iws) -> In i row -> In i (map fst iws).
Proof.
  induction fuel as [|fuel IH] in iws, row |- *; simpl; [tauto|].
  intros [<-|Hin] Hi.
  - now apply one_row_labels.
  - apply IH with (iws := shift_weights iws) (row := row) in Hin; auto.
    rewrite <- in_shift_weights_label. exact Hin.
Qed.

Lemma map_fst_combine {A B} (xs : list A) (ys : list B) :
  length xs = length ys -> map fst (combine xs ys) = xs.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] H; simpl in *;
    try discriminate; [reflexivity|].
  f_equal. apply IH. now injection H.
Qed.

Lemma indexed_weights_labels ws :
  map fst (indexed_weights ws) = seq 0 (length ws).
Proof.
  unfold indexed_weights.
  apply map_fst_combine. rewrite seq_length. reflexivity.
Qed.

Lemma ddg_table_index_bound ws row i :
  In row (ddg_table ws) -> In i row -> i < length (extended_weights ws).
Proof.
  unfold ddg_table. intros Hrow Hi.
  apply in_rev in Hrow.
  eapply rows_lsb_labels in Hrow; [|exact Hi].
  rewrite indexed_weights_labels in Hrow.
  apply in_seq in Hrow. lia.
Qed.

(** [leaf_numerator w k] is the number of depth-[k] equiprobable bit
    strings represented by the leaves emitted for [w].  The recurrence is
    exactly the recurrence used by [rows_lsb]. *)
Fixpoint leaf_numerator (w k : nat) : nat :=
  match k with
  | 0 => w
  | S k' => (w mod 2) + 2 * leaf_numerator (w / 2) k'
  end.

Lemma leaf_numerator_exact w k : leaf_numerator w k = w.
Proof.
  induction k as [|k IH] in w |- *.
  - reflexivity.
  - change ((w mod 2) + 2 * leaf_numerator (w / 2) k = w).
    rewrite IH.
    pose proof (Nat.div_mod w 2 ltac:(lia)) as Hdiv.
    lia.
Qed.

Definition table_leaf_mass (ws : list nat) (i : nat) : R :=
  INR (leaf_numerator (nth i (extended_weights ws) 0) (dyadic_width ws)) /
  INR (denominator ws).

Lemma in_le_weight_sum x ws : In x ws -> x <= weight_sum ws.
Proof.
  unfold weight_sum. induction ws as [|w ws IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [<-|Hin]; [lia|]. specialize (IH Hin). lia.
Qed.

Lemma extended_weight_bound ws i :
  admissible ws -> i < length (extended_weights ws) ->
  nth i (extended_weights ws) 0 < denominator ws \/
  nth i (extended_weights ws) 0 = denominator ws.
Proof.
  intros H Hi.
  assert (Hin : In (nth i (extended_weights ws) 0) (extended_weights ws)).
  { apply nth_In. exact Hi. }
  unfold extended_weights in Hin.
  apply in_app_or in Hin as [Hin|Hin].
  unfold extended_weights.
  - pose proof (denominator_bounds ws H) as [Hsum _].
    pose proof (in_le_weight_sum _ _ Hin) as Hweight.
    lia.
  - simpl in Hin. destruct Hin as [Hin|[]].
    unfold extended_weights. rewrite <- Hin. unfold rejection_weight.
    pose proof (denominator_bounds ws H) as [Hsum _]. lia.
Qed.

Lemma table_leaf_mass_eq ws i :
  table_leaf_mass ws i =
    (INR (nth i (extended_weights ws) 0%nat) / INR (denominator ws))%R.
Proof. unfold table_leaf_mass. now rewrite leaf_numerator_exact. Qed.

Lemma table_leaf_mass_invalid ws i :
  length (extended_weights ws) <= i -> table_leaf_mass ws i = 0%R.
Proof.
  intros Hi. unfold table_leaf_mass.
  rewrite nth_overflow by exact Hi. rewrite leaf_numerator_exact. simpl.
  field. apply not_0_INR. pose proof (denominator_pos ws). lia.
Qed.

Lemma table_leaf_mass_zero ws i :
  nth i (extended_weights ws) 0 = 0 -> table_leaf_mass ws i = 0%R.
Proof.
  intros Hz. unfold table_leaf_mass. rewrite Hz, leaf_numerator_exact. simpl.
  field. apply not_0_INR. pose proof (denominator_pos ws). lia.
Qed.

(** Finite target mass and proposal mass. *)
Definition target_mass (ws : list nat) (i : nat) : R :=
  if i <? length ws then INR (nth i ws 0) / INR (weight_sum ws) else 0.

Definition proposal_mass (ws : list nat) (i : nat) : R :=
  if i <? length (extended_weights ws)
  then INR (nth i (extended_weights ws) 0) / INR (denominator ws)
  else 0.

Lemma target_mass_invalid ws i : length ws <= i -> target_mass ws i = 0%R.
Proof. intros Hi. apply Nat.ltb_ge in Hi. unfold target_mass. rewrite Hi. reflexivity. Qed.

Lemma target_mass_zero ws i :
  i < length ws -> nth i ws 0 = 0 -> target_mass ws i = 0%R.
Proof.
  intros Hi Hz. apply Nat.ltb_lt in Hi. unfold target_mass.
  rewrite Hi, Hz, INR_0, Rdiv_0_l. reflexivity.
Qed.

Lemma sum_nth_seq ws :
  fold_right Nat.add 0 (map (fun i => nth i ws 0) (seq 0 (length ws))) = weight_sum ws.
Proof.
  unfold weight_sum. induction ws as [|w ws IH]; simpl; [reflexivity|].
  rewrite <- seq_shift, map_map. simpl. f_equal.
  replace (map (fun x : nat => nth (S x) (w :: ws) 0) (seq 0 (length ws)))
    with (map (fun x : nat => nth x ws 0) (seq 0 (length ws))).
  - exact IH.
  - apply map_ext. intros x. reflexivity.
Qed.

Lemma sum_INR_div xs m :
  m <> 0 ->
  fold_right Rplus 0%R (map (fun n => (INR n / INR m)%R) xs) =
  (INR (fold_right Nat.add 0%nat xs) / INR m)%R.
Proof.
  intros Hm. induction xs as [|x xs IH]; simpl.
  - field. now apply not_0_INR.
  - rewrite IH, plus_INR. field. now apply not_0_INR.
Qed.

Lemma target_mass_normalized ws :
  admissible ws ->
  fold_right Rplus 0%R (map (target_mass ws) (seq 0 (length ws))) = 1%R.
Proof.
  intros [_ Hsum].
  unfold target_mass.
  assert (Hmap :
    map (fun i : nat =>
      if i <? length ws then (INR (nth i ws 0%nat) / INR (weight_sum ws))%R else 0%R)
      (seq 0 (length ws)) =
    map (fun i => (INR (nth i ws 0%nat) / INR (weight_sum ws))%R)
      (seq 0 (length ws))).
  { apply map_ext_in. intros i Hi. apply in_seq in Hi.
    assert (Hb : (i <? length ws) = true) by (apply Nat.ltb_lt; lia).
    rewrite Hb. reflexivity. }
  rewrite Hmap.
  assert (Hcompose :
    map (fun n => (INR n / INR (weight_sum ws))%R)
      (map (fun i => nth i ws 0%nat) (seq 0 (length ws))) =
    map (fun i => (INR (nth i ws 0%nat) / INR (weight_sum ws))%R)
      (seq 0 (length ws))).
  { rewrite map_map. reflexivity. }
  rewrite <- Hcompose. rewrite sum_INR_div by lia. rewrite sum_nth_seq.
  field. apply not_0_INR. lia.
Qed.

Lemma proposal_original_mass ws i :
  i < length ws -> proposal_mass ws i =
  (INR (nth i ws 0%nat) / INR (denominator ws))%R.
Proof.
  intros Hi. unfold proposal_mass, extended_weights.
  rewrite app_length. simpl.
  assert (Hb : (i <? length ws + 1) = true) by (apply Nat.ltb_lt; lia).
  rewrite Hb. rewrite app_nth1 by exact Hi. reflexivity.
Qed.

Lemma proposal_rejection_mass ws :
  proposal_mass ws (length ws) =
  (INR (rejection_weight ws) / INR (denominator ws))%R.
Proof.
  unfold proposal_mass, extended_weights. rewrite app_length. simpl.
  assert (Hb : (length ws <? length ws + 1) = true) by (apply Nat.ltb_lt; lia).
  rewrite Hb, nth_middle. reflexivity.
Qed.

Lemma acceptance_mass ws :
  admissible ws ->
  (INR (weight_sum ws) / INR (denominator ws))%R =
  (1 - proposal_mass ws (length ws))%R.
Proof.
  intros H. rewrite proposal_rejection_mass.
  pose proof (rejection_weight_nonnegative ws H) as Hsum.
  assert (HsumR :
    (INR (weight_sum ws) + INR (rejection_weight ws))%R = INR (denominator ws)).
  { rewrite <- plus_INR. now rewrite Hsum. }
  rewrite <- HsumR. field. rewrite HsumR. apply not_0_INR.
  pose proof (denominator_pos ws). lia.
Qed.

Lemma conditioned_original_mass ws i :
  admissible ws -> i < length ws ->
  ((proposal_mass ws i) /
    (INR (weight_sum ws) / INR (denominator ws)))%R = target_mass ws i.
Proof.
  intros [_ Hsum] Hi. rewrite proposal_original_mass by exact Hi.
  unfold target_mass.
  assert (Hb : (i <? length ws) = true) by (apply Nat.ltb_lt; exact Hi).
  rewrite Hb. field; split; apply not_0_INR; try lia.
  pose proof (denominator_pos ws). lia.
Qed.

Example check_321 : ddg_table [3; 2; 1] = [[]; [0; 1; 3]; [0; 2]].
Proof. vm_compute. reflexivity. Qed.

Example check_singleton : ddg_table [5] = [[0]; [1]; [0; 1]].
Proof. vm_compute. reflexivity. Qed.

Example check_power_two : ddg_table [2; 2] = [[0; 1]; []].
Proof. vm_compute. reflexivity. Qed.

Example check_internal_zero : ddg_table [2; 0; 1] = [[0]; [2; 3]].
Proof. vm_compute. reflexivity. Qed.

(** * Bridge: the constructed table really carries the claimed leaf mass.

    Everything above relates [leaf_numerator] to a weight but nothing relates
    it to [ddg_table].  Note that [leaf_numerator w k = w] holds
    unconditionally, so it cannot by itself describe a depth-[k] table: such a
    table can only carry the low [k] bits of [w].  The correct row count is
    [w mod 2 ^ k], and the side condition [w < 2 ^ k] is what turns it back
    into [w]. *)

Definition ind (P : Prop) (d : {P} + {~ P}) : nat := if d then 1 else 0.

Definition occ (i : nat) (row : list nat) : nat :=
  ind (In i row) (in_dec Nat.eq_dec i row).

Lemma pair_unique_by_fst i w w' (iws : list (nat * nat)) :
  NoDup (map fst iws) -> In (i, w) iws -> In (i, w') iws -> w = w'.
Proof.
  induction iws as [|[j v] iws IH]; intros Hnd Hin Hin'; [contradiction|].
  simpl in Hnd. inversion Hnd as [|? ? Hnotin Hnd']; subst.
  destruct Hin as [Heq1|Hin1]; destruct Hin' as [Heq2|Hin2].
  - inversion Heq1; inversion Heq2; congruence.
  - inversion Heq1; subst. exfalso. apply Hnotin.
    apply in_map_iff. exists (i, w'). split; [reflexivity|exact Hin2].
  - inversion Heq2; subst. exfalso. apply Hnotin.
    apply in_map_iff. exists (i, w). split; [reflexivity|exact Hin1].
  - apply IH; assumption.
Qed.

(** A label occupies a row exactly when the current bit of its weight is set. *)
Lemma one_row_spec i w iws :
  NoDup (map fst iws) -> In (i, w) iws ->
  (In i (one_row iws) <-> w mod 2 = 1).
Proof.
  intros Hnd Hin. unfold one_row. split.
  - intros Hrow. apply in_map_iff in Hrow as [[i' w'] [Heq Hfil]].
    simpl in Heq. subst i'.
    apply filter_In in Hfil as [Hin' Hbit]. simpl in Hbit.
    apply Nat.eqb_eq in Hbit.
    now rewrite (pair_unique_by_fst i w w' iws Hnd Hin Hin').
  - intros Hbit. apply in_map_iff. exists (i, w). split; [reflexivity|].
    apply filter_In. split; [exact Hin|]. simpl. now apply Nat.eqb_eq.
Qed.

Lemma occ_one_row i w iws :
  NoDup (map fst iws) -> In (i, w) iws -> occ i (one_row iws) = w mod 2.
Proof.
  intros Hnd Hin. unfold occ, ind.
  destruct (in_dec Nat.eq_dec i (one_row iws)) as [Hyes|Hno].
  - symmetry. now apply (one_row_spec i w iws).
  - destruct (Nat.eq_dec (w mod 2) 1) as [Heq|Hne].
    + exfalso. apply Hno. apply (one_row_spec i w iws); assumption.
    + pose proof (Nat.mod_upper_bound w 2 ltac:(lia)). lia.
Qed.

Lemma shift_weights_in i w iws :
  In (i, w) iws -> In (i, w / 2) (shift_weights iws).
Proof.
  intros Hin. unfold shift_weights. apply in_map_iff.
  exists (i, w). split; [reflexivity|exact Hin].
Qed.

Lemma shift_weights_fst iws : map fst (shift_weights iws) = map fst iws.
Proof.
  unfold shift_weights. rewrite map_map. apply map_ext. now intros [i w].
Qed.

(** Weighted occurrence count of a label across the LSB-first rows. *)
Fixpoint tcount (fuel : nat) (iws : list (nat * nat)) (i : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f => occ i (one_row iws) + 2 * tcount f (shift_weights iws) i
  end.

(** The step that was previously only a comment: the row-occupancy count of
    the constructed table is the low-[fuel]-bit value of the label's weight. *)
Lemma tcount_spec fuel iws i w :
  NoDup (map fst iws) -> In (i, w) iws ->
  tcount fuel iws i = w mod 2 ^ fuel.
Proof.
  induction fuel as [|fuel IH] in iws, w |- *; intros Hnd Hin.
  - simpl tcount. now rewrite Nat.pow_0_r, Nat.mod_1_r.
  - simpl tcount.
    rewrite (occ_one_row i w iws Hnd Hin).
    rewrite (IH (shift_weights iws) (w / 2));
      [|rewrite shift_weights_fst; exact Hnd|now apply shift_weights_in].
    replace (2 ^ S fuel) with (2 * 2 ^ fuel) by (simpl; lia).
    rewrite (Nat.mod_mul_r w 2 (2 ^ fuel)); [lia|lia|].
    pose proof (Nat.pow_nonzero 2 fuel ltac:(lia)). lia.
Qed.

(** * Sum plumbing *)

Definition nsum (l : list nat) : nat := fold_right Nat.add 0 l.

Lemma nsum_app l1 l2 : nsum (l1 ++ l2) = nsum l1 + nsum l2.
Proof. induction l1 as [|x l1 IH]; simpl; [reflexivity|]. unfold nsum in *; simpl; lia. Qed.

Lemma nsum_rev l : nsum (rev l) = nsum l.
Proof.
  induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite nsum_app, IH. unfold nsum; simpl; lia.
Qed.

Lemma nsum_scale c l : nsum (map (fun x => c * x) l) = c * nsum l.
Proof. induction l as [|x l IH]; simpl; [lia|]. unfold nsum in *; simpl; lia. Qed.

(** * From row occupancy to leaf mass on the real table.

    [msum] sums a label's occurrences over the MSB-first rows of [ddg_table],
    weighting a row of residual depth [d] by [2 ^ d].  Summing over the row
    list rather than over row indices avoids all reindexing. *)

Fixpoint msum (i : nat) (rows : list (list nat)) : nat :=
  match rows with
  | [] => 0
  | r :: rest => occ i r * 2 ^ length rest + msum i rest
  end.

Lemma msum_app i a b :
  msum i (a ++ b) = msum i a * 2 ^ length b + msum i b.
Proof.
  induction a as [|r a IH]; simpl; [lia|].
  rewrite IH, app_length, Nat.pow_add_r. lia.
Qed.

Lemma msum_rev_tcount fuel iws i :
  msum i (rev (rows_lsb fuel iws)) = tcount fuel iws i.
Proof.
  induction fuel as [|fuel IH] in iws |- *; [reflexivity|].
  simpl rows_lsb. simpl rev. rewrite msum_app. simpl.
  rewrite IH, Nat.mul_1_r. lia.
Qed.

Lemma indexed_weights_nth ws i :
  i < length ws -> In (i, nth i ws 0) (indexed_weights ws).
Proof.
  intros Hi. unfold indexed_weights.
  assert (Hlen : length (seq 0 (length ws)) = length ws) by apply seq_length.
  assert (Hcomb : nth i (combine (seq 0 (length ws)) ws) (0, 0) =
                  (nth i (seq 0 (length ws)) 0, nth i ws 0)).
  { apply combine_nth. exact Hlen. }
  rewrite seq_nth in Hcomb by exact Hi. simpl in Hcomb.
  rewrite <- Hcomb. apply nth_In.
  rewrite combine_length, Hlen. lia.
Qed.

Lemma indexed_weights_nodup ws : NoDup (map fst (indexed_weights ws)).
Proof.
  rewrite indexed_weights_labels. apply seq_NoDup.
Qed.

(** ** The bridge theorem.

    The occupancy of the table that [ddg_table] actually builds carries
    exactly the label's weight, provided the weight fits in the table depth. *)
Theorem ddg_table_occupancy ws i :
  i < length (extended_weights ws) ->
  msum i (ddg_table ws) =
  nth i (extended_weights ws) 0 mod denominator ws.
Proof.
  intros Hi. unfold ddg_table, denominator.
  rewrite msum_rev_tcount.
  apply (tcount_spec _ _ _ (nth i (extended_weights ws) 0)).
  - apply indexed_weights_nodup.
  - now apply indexed_weights_nth.
Qed.

Corollary ddg_table_occupancy_exact ws i :
  i < length (extended_weights ws) ->
  nth i (extended_weights ws) 0 < denominator ws ->
  msum i (ddg_table ws) = nth i (extended_weights ws) 0.
Proof.
  intros Hi Hlt. rewrite ddg_table_occupancy by exact Hi.
  now apply Nat.mod_small.
Qed.

(** The leaf mass of the constructed table equals the dyadic proposal mass. *)
Definition ddg_mass (ws : list nat) (i : nat) : R :=
  INR (msum i (ddg_table ws)) / INR (denominator ws).

Theorem ddg_mass_is_proposal_mass ws i :
  i < length (extended_weights ws) ->
  nth i (extended_weights ws) 0 < denominator ws ->
  ddg_mass ws i = proposal_mass ws i.
Proof.
  intros Hi Hlt. unfold ddg_mass, proposal_mass.
  rewrite ddg_table_occupancy_exact by assumption.
  assert (Hb : (i <? length (extended_weights ws)) = true)
    by (apply Nat.ltb_lt; exact Hi).
  now rewrite Hb.
Qed.

(** Composed with [conditioned_original_mass], the table therefore yields the
    normalized input weights after rejection. *)
Theorem ddg_mass_conditioned ws i :
  admissible ws -> i < length ws ->
  nth i (extended_weights ws) 0 < denominator ws ->
  (ddg_mass ws i / (INR (weight_sum ws) / INR (denominator ws)))%R =
  target_mass ws i.
Proof.
  intros Hadm Hi Hlt.
  rewrite ddg_mass_is_proposal_mass;
    [| unfold extended_weights; rewrite app_length; simpl; lia | exact Hlt].
  now apply conditioned_original_mass.
Qed.

(** ** The side condition is necessary.

    When one label carries the whole denominator the depth-[k] table is empty,
    so it carries no mass.  These are exactly the degenerate [n=1], [m=2^k]
    inputs, which the sampler must branch on rather than table-drive. *)
Example degenerate_one : ddg_table [1] = [] /\ msum 0 (ddg_table [1]) = 0.
Proof. split; vm_compute; reflexivity. Qed.

Example degenerate_eight : ddg_table [8] = [[]; []; []] /\ msum 0 (ddg_table [8]) = 0.
Proof. split; vm_compute; reflexivity. Qed.

Example nondegenerate_321 : msum 0 (ddg_table [3;2;1]) = 3 /\
                            msum 1 (ddg_table [3;2;1]) = 2 /\
                            msum 2 (ddg_table [3;2;1]) = 1 /\
                            msum 3 (ddg_table [3;2;1]) = 2.
Proof. repeat split; vm_compute; reflexivity. Qed.
