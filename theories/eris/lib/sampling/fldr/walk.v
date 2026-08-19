From Coq Require Import Arith.PeanoNat Lists.List Reals Psatz Lia.
From clutch.eris.lib.sampling.fldr Require Import model.
Import ListNotations.

(** * The FLDR online walk over the constructed table.

    [model.v] proves that the table built from the weights carries the right
    occupancy.  This file gives the walk that consumes fair bits, and proves
    the one-round law: the number of length-[k] bit strings that return label
    [i] is exactly the occupancy [msum i rows].

    Rows are MSB first, as produced by [ddg_table].  Entering a row the walk
    holds a counter [c]; it reads one bit, sets [c' := 2c + b], returns the
    leaf [nth c' row] when [c' < length row], and otherwise carries
    [c' - length row] into the next row. *)

Fixpoint walk (rows : list (list nat)) (c : nat) (bs : list bool) : option nat :=
  match rows, bs with
  | row :: rest, b :: bs' =>
      let c' := 2 * c + (if b then 1 else 0) in
      if c' <? length row then Some (nth c' row 0)
      else walk rest (c' - length row) bs'
  | _, _ => None
  end.

(** ** Counting accepting bit strings *)

Definition leafval (row : list nat) (c' i rest : nat) : nat :=
  if Nat.eqb (nth c' row 0) i then 2 ^ rest else 0.

Fixpoint cnt (rows : list (list nat)) (c i : nat) : nat :=
  match rows with
  | [] => 0
  | row :: rest =>
      (if 2 * c <? length row
       then leafval row (2 * c) i (length rest)
       else cnt rest (2 * c - length row) i)
      +
      (if 2 * c + 1 <? length row
       then leafval row (2 * c + 1) i (length rest)
       else cnt rest (2 * c + 1 - length row) i)
  end.

(** ** The row-capacity invariant.

    [A] is the number of live counters entering a row.  A row may hold at most
    [2 * A] leaves; whatever is left is carried forward. *)

Fixpoint capacity_ok (rows : list (list nat)) (A : nat) : Prop :=
  match rows with
  | [] => True
  | row :: rest => length row <= 2 * A /\ capacity_ok rest (2 * A - length row)
  end.

(** ** Sum plumbing over [seq] *)

Lemma nsum_zero l : (forall x, In x l -> x = 0) -> nsum l = 0.
Proof.
  induction l as [|x l IH]; [reflexivity|]. intros H.
  unfold nsum in *; simpl. rewrite (H x) by now left.
  rewrite IH; [lia|]. intros y Hy. apply H. now right.
Qed.

Lemma nsum_seq_pair A g :
  nsum (map (fun c => g (2 * c) + g (2 * c + 1)) (seq 0 A)) =
  nsum (map g (seq 0 (2 * A))).
Proof.
  induction A as [|A IH]; [reflexivity|].
  rewrite seq_S, map_app, nsum_app, IH.
  replace (2 * S A) with (S (S (2 * A))) by lia.
  rewrite seq_S, map_app, nsum_app.
  rewrite seq_S, map_app, nsum_app.
  unfold nsum; simpl; rewrite Nat.add_1_r; lia.
Qed.

Lemma map_shift_seq k m :
  map (fun c => k + c) (seq 0 m) = seq k m.
Proof.
  induction m as [|m IH] in k |- *; [reflexivity|].
  simpl. rewrite Nat.add_0_r. f_equal.
  change (seq 1 m) with (seq (S 0) m).
  rewrite <- seq_shift, map_map.
  rewrite <- (IH (S k)). apply map_ext. intros a. lia.
Qed.

Lemma nsum_seq_split g n m :
  nsum (map g (seq 0 (n + m))) =
  nsum (map g (seq 0 n)) + nsum (map (fun c => g (n + c)) (seq 0 m)).
Proof.
  rewrite seq_app, map_app, nsum_app. f_equal.
  rewrite <- map_shift_seq, map_map. reflexivity.
Qed.

(** A label occupies at most one slot of a row, so summing the leaf value over
    the row's slots returns the occupancy indicator. *)
Lemma sum_leafval_row row i rest :
  NoDup row ->
  nsum (map (fun c => leafval row c i rest) (seq 0 (length row))) =
  occ i row * 2 ^ rest.
Proof.
  intros Hnd. unfold occ, ind.
  destruct (in_dec Nat.eq_dec i row) as [Hin|Hout].
  - (* exactly one slot carries [i] *)
    destruct (In_nth row i 0 Hin) as [p [Hp Hnth]].
    replace (length row) with (p + (1 + (length row - S p))) by lia.
    rewrite nsum_seq_split, nsum_seq_split.
    assert (Hzero : forall q, q < p ->
              leafval row q i rest = 0).
    { intros q Hq. unfold leafval.
      destruct (Nat.eqb_spec (nth q row 0) i) as [Heq|]; [|reflexivity].
      exfalso. assert (q = p); [|lia].
      apply (proj1 (NoDup_nth row 0) Hnd q p); try lia; congruence. }
    assert (Hzero2 : forall q, q < length row - S p ->
              leafval row (p + (1 + q)) i rest = 0).
    { intros q Hq. unfold leafval.
      destruct (Nat.eqb_spec (nth (p + (1 + q)) row 0) i) as [Heq|]; [|reflexivity].
      exfalso. assert (p + (1 + q) = p); [|lia].
      apply (proj1 (NoDup_nth row 0) Hnd _ p); try lia; congruence. }
    assert (H1 : nsum (map (fun c => leafval row c i rest) (seq 0 p)) = 0).
    { apply nsum_zero. intros x Hx. apply in_map_iff in Hx as [q [<- Hq]].
      apply in_seq in Hq. apply Hzero. lia. }
    assert (H3 : nsum (map (fun c => leafval row (p + (1 + c)) i rest)
                           (seq 0 (length row - S p))) = 0).
    { apply nsum_zero. intros x Hx. apply in_map_iff in Hx as [q [<- Hq]].
      apply in_seq in Hq. apply Hzero2. lia. }
    rewrite H1, H3. unfold nsum. simpl.
    replace (p + 0) with p by lia.
    unfold leafval. rewrite Hnth, Nat.eqb_refl. lia.
  - (* no slot carries [i] *)
    rewrite Nat.mul_0_l. apply nsum_zero. intros x Hx.
    apply in_map_iff in Hx as [q [<- Hq]]. apply in_seq in Hq.
    unfold leafval. destruct (Nat.eqb_spec (nth q row 0) i) as [Heq|]; [|reflexivity].
    exfalso. apply Hout. rewrite <- Heq. apply nth_In. lia.
Qed.

(** ** The one-round law.

    Summed over the [A] live counters entering the table, the number of
    accepting bit strings for label [i] is its table occupancy. *)
Theorem walk_count rows i A :
  capacity_ok rows A ->
  (forall row, In row rows -> NoDup row) ->
  nsum (map (fun c => cnt rows c i) (seq 0 A)) = msum i rows.
Proof.
  induction rows as [|row rest IH] in A |- *; intros Hcap Hnd.
  - simpl msum. apply nsum_zero. intros x Hx.
    apply in_map_iff in Hx as [q [<- _]]. reflexivity.
  - destruct Hcap as [Hrow Hcap].
    set (g := fun c' => if c' <? length row
                        then leafval row c' i (length rest)
                        else cnt rest (c' - length row) i).
    unfold nsum.
    rewrite (map_ext (fun c => cnt (row :: rest) c i)
                     (fun c => g (2 * c) + g (2 * c + 1)))
      by (intros c; subst g; reflexivity).
    fold (nsum (map (fun c => g (2 * c) + g (2 * c + 1)) (seq 0 A))).
    rewrite (nsum_seq_pair A g).
    replace (2 * A) with (length row + (2 * A - length row)) by lia.
    rewrite nsum_seq_split.
    assert (Hleft :
      nsum (map g (seq 0 (length row))) = occ i row * 2 ^ length rest).
    { rewrite <- (sum_leafval_row row i (length rest)) by (apply Hnd; now left).
      unfold nsum. f_equal. apply map_ext_in. intros c Hc.
      apply in_seq in Hc. subst g. simpl.
      assert (Hb : (c <? length row) = true) by (apply Nat.ltb_lt; lia).
      now rewrite Hb. }
    assert (Hright :
      nsum (map (fun c => g (length row + c))
                (seq 0 (2 * A - length row))) =
      nsum (map (fun c => cnt rest c i) (seq 0 (2 * A - length row)))).
    { unfold nsum. f_equal. apply map_ext_in. intros c Hc.
      subst g. simpl.
      assert (Hb : (length row + c <? length row) = false)
        by (apply Nat.ltb_ge; lia).
      rewrite Hb. f_equal. lia. }
    rewrite Hleft, Hright.
    rewrite (IH (2 * A - length row) Hcap); [|intros r Hr; apply Hnd; now right].
    simpl msum. lia.
Qed.
