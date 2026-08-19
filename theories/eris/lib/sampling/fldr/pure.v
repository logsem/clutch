From Coq Require Import Arith.PeanoNat Lists.List Psatz Lia.
From clutch.eris.lib.sampling.fldr Require Import model walk.
Import ListNotations.

(** * Counting the finite bit strings accepted by one table walk. *)

Fixpoint all_bits (k : nat) : list (list bool) :=
  match k with
  | 0 => [[]]
  | S k' => map (cons true) (all_bits k') ++ map (cons false) (all_bits k')
  end.

Lemma all_bits_length k : length (all_bits k) = 2 ^ k.
Proof.
  induction k as [|k IH]; simpl; [reflexivity|].
  rewrite app_length, !map_length, IH.
  lia.
Qed.

Lemma all_bits_spec k bs : In bs (all_bits k) <-> length bs = k.
Proof.
  induction k as [|k IH] in bs |- *.
  - change (In bs [[]] <-> length bs = 0).
    split.
    + intros [H|H]; [subst; reflexivity|contradiction].
    + intros H. destruct bs as [|b bs]; [left; reflexivity|simpl in H; lia].
  - change (In bs (map (cons true) (all_bits k) ++
        map (cons false) (all_bits k)) <-> length bs = S k).
    rewrite in_app_iff, !in_map_iff.
    split.
    + intros [[x [<- Hx]]|[x [<- Hx]]].
      * simpl. rewrite (proj1 (IH x) Hx). reflexivity.
      * simpl. rewrite (proj1 (IH x) Hx). reflexivity.
    + intros Hlen. destruct bs as [|b bs]; [simpl in Hlen; lia|].
      destruct b.
      * left. exists bs. split.
        { reflexivity. }
        { apply (proj2 (IH bs)). simpl in Hlen. lia. }
      * right. exists bs. split.
        { reflexivity. }
        { apply (proj2 (IH bs)). simpl in Hlen. lia. }
Qed.


Definition accepts (rows : list (list nat)) (c i : nat) (bs : list bool) : bool :=
  match walk rows c bs with Some j => Nat.eqb j i | None => false end.

Definition naccept (rows : list (list nat)) (c i : nat) : nat :=
  length (filter (accepts rows c i) (all_bits (length rows))).

Lemma filter_map_cons_length {B : Type} (p : list B -> bool)
    (b : B) (xs : list (list B)) :
  length (filter p (map (cons b) xs)) =
  length (filter (fun bs => p (b :: bs)) xs).
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity|].
  destruct (p (b :: x)); simpl; rewrite IH; reflexivity.
Qed.

Lemma filter_length_constant {A : Type} (p : A -> bool) (xs : list A) (q : bool) :
  (forall x, p x = q) ->
  length (filter p xs) = if q then length xs else 0.
Proof.
  intros Hp. destruct q.
  - induction xs as [|x xs IH]; simpl; [reflexivity|].
    destruct (p x) eqn:Hx.
    * simpl. rewrite IH. reflexivity.
    * exfalso. congruence.
  - induction xs as [|x xs IH]; simpl; [reflexivity|].
    destruct (p x) eqn:Hx.
    * exfalso. congruence.
    * simpl. rewrite IH. reflexivity.
Qed.

Theorem cnt_naccept rows c i : cnt rows c i = naccept rows c i.
Proof.
  induction rows as [|row rest IH] in c |- *.
  - unfold cnt, naccept, all_bits. simpl. reflexivity.
  - unfold cnt, naccept.
    simpl (length (row :: rest)).
    unfold all_bits.
    change (cnt (row :: rest) c i = length (filter (accepts (row :: rest) c i)
      (map (cons true) (all_bits (length rest)) ++
       map (cons false) (all_bits (length rest))))).
    rewrite filter_app, app_length.
    rewrite (filter_map_cons_length (accepts (row :: rest) c i) true
      (all_bits (length rest))).
    rewrite (filter_map_cons_length (accepts (row :: rest) c i) false
      (all_bits (length rest))).
    unfold cnt.
    set (ct := 2 * c).
    set (h := length row).
    assert (Htrue : forall bs,
      accepts (row :: rest) c i (true :: bs) =
      if (ct + 1 <? h) then Nat.eqb (nth (ct + 1) row 0) i
      else accepts rest (ct + 1 - h) i bs).
    { intros bs. subst ct h. unfold accepts, walk. simpl.
      replace (c + (c + 0) + 1) with (2 * c + 1) by lia.
      destruct (2 * c + 1 <? length row); reflexivity. }
    assert (Hfalse : forall bs,
      accepts (row :: rest) c i (false :: bs) =
      if (ct <? h) then Nat.eqb (nth ct row 0) i
      else accepts rest (ct - h) i bs).
    { intros bs. subst ct h. unfold accepts, walk. simpl.
      rewrite Nat.add_0_r.
      replace (c + (c + 0)) with (2 * c) by lia.
      destruct (2 * c <? length row); reflexivity. }
    destruct (ct <? h) eqn:Hf.
    + assert (Hf' : forall bs,
          accepts (row :: rest) c i (false :: bs) = Nat.eqb (nth ct row 0) i)
        by (intros bs; rewrite Hfalse; reflexivity).
      destruct (ct + 1 <? h) eqn:Ht.
      * assert (Ht' : forall bs,
            accepts (row :: rest) c i (true :: bs) = Nat.eqb (nth (ct + 1) row 0) i)
          by (intros bs; rewrite Htrue; reflexivity).
        rewrite (filter_length_constant _ _ _ Ht').
        rewrite (filter_length_constant _ _ _ Hf').
        rewrite !all_bits_length.
        unfold leafval.
        lia.
      * assert (Ht' : forall bs,
            accepts (row :: rest) c i (true :: bs) =
              accepts rest (ct + 1 - h) i bs)
          by (intros bs; rewrite Htrue; reflexivity).
        rewrite (filter_length_constant _ _ _ Hf').
        assert (Hfilter :
          filter (fun bs => accepts (row :: rest) c i (true :: bs))
            (all_bits (length rest)) =
          filter (accepts rest (ct + 1 - h) i) (all_bits (length rest))).
        { apply filter_ext. intros bs. apply Ht'. }
        rewrite Hfilter. unfold naccept in IH.
        change (leafval row ct i (length rest) + cnt rest (ct + 1 - h) i =
          length (filter (accepts rest (ct + 1 - h) i) (all_bits (length rest))) +
          (if Nat.eqb (nth ct row 0) i then length (all_bits (length rest)) else 0)).
        rewrite (IH (ct + 1 - h)).
        unfold leafval.
        rewrite all_bits_length.
        lia.
    + assert (Hf' : forall bs,
          accepts (row :: rest) c i (false :: bs) = accepts rest (ct - h) i bs)
        by (intros bs; rewrite Hfalse; reflexivity).
      destruct (ct + 1 <? h) eqn:Ht.
      * assert (Ht' : forall bs,
            accepts (row :: rest) c i (true :: bs) = Nat.eqb (nth (ct + 1) row 0) i)
          by (intros bs; rewrite Htrue; reflexivity).
        rewrite (filter_length_constant _ _ _ Ht').
        assert (Hfilter :
          filter (fun bs => accepts (row :: rest) c i (false :: bs))
            (all_bits (length rest)) =
          filter (accepts rest (ct - h) i) (all_bits (length rest))).
        { apply filter_ext. intros bs. apply Hf'. }
        rewrite Hfilter. unfold naccept in IH.
        change (cnt rest (ct - h) i + leafval row (ct + 1) i (length rest) =
          (if Nat.eqb (nth (ct + 1) row 0) i then length (all_bits (length rest)) else 0) +
          length (filter (accepts rest (ct - h) i) (all_bits (length rest)))).
        rewrite (IH (ct - h)).
        unfold leafval.
        rewrite all_bits_length.
        lia.
      * assert (Ht' : forall bs,
            accepts (row :: rest) c i (true :: bs) = accepts rest (ct + 1 - h) i bs)
          by (intros bs; rewrite Htrue; reflexivity).
        assert (Hfiltert :
          filter (fun bs => accepts (row :: rest) c i (true :: bs))
            (all_bits (length rest)) =
          filter (accepts rest (ct + 1 - h) i) (all_bits (length rest))).
        { apply filter_ext. intros bs. apply Ht'. }
        rewrite Hfiltert.
        assert (Hfilterf :
          filter (fun bs => accepts (row :: rest) c i (false :: bs))
            (all_bits (length rest)) =
          filter (accepts rest (ct - h) i) (all_bits (length rest))).
        { apply filter_ext. intros bs. apply Hf'. }
        rewrite Hfilterf.
        unfold naccept in IH.
        change (cnt rest (ct - h) i + cnt rest (ct + 1 - h) i =
          length (filter (accepts rest (ct + 1 - h) i) (all_bits (length rest))) +
          length (filter (accepts rest (ct - h) i) (all_bits (length rest)))).
        rewrite (IH (ct - h)), (IH (ct + 1 - h)).
        lia.
Qed.


(** * Capacity of the constructed table. *)

Fixpoint cap_final (rows : list (list nat)) (A : nat) : nat :=
  match rows with
  | [] => A
  | row :: rest => cap_final rest (2 * A - length row)
  end.

Lemma cap_final_app r1 r2 A :
  cap_final (r1 ++ r2) A = cap_final r2 (cap_final r1 A).
Proof.
  induction r1 as [|row r1 IH] in A |- *; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma capacity_ok_app r1 r2 A :
  capacity_ok (r1 ++ r2) A <->
  capacity_ok r1 A /\ capacity_ok r2 (cap_final r1 A).
Proof.
  induction r1 as [|row r1 IH] in A |- *; simpl.
  - tauto.
  - rewrite IH. tauto.
Qed.

Definition modsum (f : nat) (iws : list (nat * nat)) : nat :=
  nsum (map (fun iw => snd iw mod 2 ^ f) iws).

Lemma mod_succ_shift w f :
  w mod 2 ^ (S f) = w mod 2 + 2 * ((w / 2) mod 2 ^ f).
Proof.
  replace (2 ^ S f) with (2 * 2 ^ f) by (simpl; lia).
  rewrite (Nat.mod_mul_r w 2 (2 ^ f)); [lia|lia|].
  pose proof (Nat.pow_nonzero 2 f ltac:(lia)). lia.
Qed.

Lemma modsum_succ_shift f iws :
  modsum (S f) iws =
    nsum (map (fun iw => snd iw mod 2) iws) +
    2 * modsum f (shift_weights iws).
Proof.
  unfold modsum.
  induction iws as [|[i w] iws IH].
  - reflexivity.
  - change (w mod 2 ^ (S f) +
      nsum (map (fun iw : nat * nat => snd iw mod 2 ^ S f) iws) =
      w mod 2 + nsum (map (fun iw : nat * nat => snd iw mod 2) iws) +
      2 * ((w / 2) mod 2 ^ f +
        nsum (map (fun iw : nat * nat => snd iw mod 2 ^ f) (shift_weights iws)))).
    rewrite mod_succ_shift, IH.
    lia.
Qed.

Lemma one_row_length iws :
  length (one_row iws) =
  nsum (map (fun iw => snd iw mod 2) iws).
Proof.
  induction iws as [|[i w] iws IH].
  - reflexivity.
  - unfold one_row.
    assert (Hbit : w mod 2 = 0 \/ w mod 2 = 1).
    { pose proof (Nat.mod_upper_bound w 2 ltac:(lia)). lia. }
    unfold one_row in IH.
    rewrite map_length in IH.
    rewrite map_length.
    change (length (filter (fun iw : nat * nat => snd iw mod 2 =? 1)
      ((i, w) :: iws)) =
      w mod 2 + nsum (map (fun iw : nat * nat => snd iw mod 2) iws)).
    change (length (if w mod 2 =? 1
      then (i, w) :: filter (fun iw : nat * nat => snd iw mod 2 =? 1) iws
      else filter (fun iw : nat * nat => snd iw mod 2 =? 1) iws) =
      w mod 2 + nsum (map (fun iw : nat * nat => snd iw mod 2) iws)).
    destruct Hbit as [Hzero|Hone].
    + rewrite Hzero.
      change (length (filter (fun iw : nat * nat => snd iw mod 2 =? 1) iws) =
        nsum (map (fun iw : nat * nat => snd iw mod 2) iws)).
      exact IH.
    + rewrite Hone.
      change (S (length (filter (fun iw : nat * nat => snd iw mod 2 =? 1) iws)) =
        S (nsum (map (fun iw : nat * nat => snd iw mod 2) iws))).
      f_equal. exact IH.
Qed.

Lemma modsum_le_sum f iws :
  modsum f iws <= nsum (map snd iws).
Proof.
  unfold modsum.
  induction iws as [|[i w] iws IH]; simpl; [lia|].
  pose proof (Nat.mod_le w (2 ^ f)) as Hmod.
  pose proof (Nat.pow_nonzero 2 f ltac:(lia)) as Hpow.
  lia.
Qed.

Lemma map_snd_combine {A B : Type} (xs : list A) (ys : list B) :
  length xs = length ys -> map snd (combine xs ys) = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] H; simpl in *;
    try discriminate; [reflexivity|].
  f_equal. apply IH. now injection H.
Qed.

Lemma nsum_indexed_snd ws :
  nsum (map snd (indexed_weights ws)) = weight_sum ws.
Proof.
  unfold indexed_weights.
  rewrite (map_snd_combine (seq 0 (length ws)) ws).
  - unfold weight_sum. reflexivity.
  - rewrite seq_length. reflexivity.
Qed.

Lemma rows_lsb_capacity f iws A :
  modsum f iws <= A * 2 ^ f ->
  capacity_ok (rev (rows_lsb f iws)) A /\
  cap_final (rev (rows_lsb f iws)) A = A * 2 ^ f - modsum f iws.
Proof.
  induction f as [|f IH] in iws, A |- *.
  - assert (Hzero : modsum 0 iws = 0).
    { unfold modsum. induction iws as [|[i w] iws IH].
      - reflexivity.
      - change (w mod 1 + nsum (map (fun iw : nat * nat => snd iw mod 1) iws) = 0).
        rewrite Nat.mod_1_r.
        replace (2 ^ 0) with 1 in IH by reflexivity.
        rewrite IH. lia. }
    simpl. rewrite Hzero. lia.
  - intros Hbound.
    rewrite Nat.pow_succ_r' in Hbound |- *.
    rewrite (modsum_succ_shift f iws) in Hbound.
    simpl rows_lsb. simpl rev.
    simpl.
    set (rest_rows := rev (rows_lsb f (shift_weights iws))).
    set (bits := length (one_row iws)).
    assert (Hbits : bits = nsum (map (fun iw => snd iw mod 2) iws))
      by (subst bits; apply one_row_length).
    assert (Hshift : modsum f (shift_weights iws) <= A * 2 ^ f).
    { rewrite Nat.mul_assoc in Hbound.
      rewrite (Nat.mul_comm A 2) in Hbound.
      rewrite <- Nat.mul_assoc in Hbound.
      assert (Htwice : 2 * modsum f (shift_weights iws) <=
          2 * (A * 2 ^ f)) by lia.
      lia. }
    assert (HIH := IH (shift_weights iws) A Hshift).
    destruct HIH as [Hcap Hfinal].
    assert (Hnontrunc : modsum f (shift_weights iws) <= A * 2 ^ f) by exact Hshift.
    assert (Hcapbit : bits <= 2 * (A * 2 ^ f - modsum f (shift_weights iws))).
    { rewrite Hbits.
      lia. }
    split.
    + apply (proj2 (capacity_ok_app rest_rows [one_row iws] A)).
      split; [exact Hcap|].
      simpl. split; [unfold bits, rest_rows; rewrite Hfinal; lia|exact I].
    + rewrite cap_final_app.
      simpl.
      unfold rest_rows.
      rewrite Hfinal.
      rewrite (modsum_succ_shift f iws).
      unfold bits in Hcapbit.
      lia.
Qed.

Theorem ddg_table_capacity ws :
  admissible ws -> capacity_ok (ddg_table ws) 1.
Proof.
  intros Hadm.
  unfold ddg_table.
  assert (Hmass :
    modsum (dyadic_width ws) (indexed_weights (extended_weights ws)) <=
    1 * 2 ^ dyadic_width ws).
  { rewrite Nat.mul_1_l.
    apply Nat.le_trans with (nsum (map snd (indexed_weights (extended_weights ws)))).
    - apply modsum_le_sum.
    - rewrite nsum_indexed_snd.
      rewrite extended_weight_sum by exact Hadm.
      reflexivity. }
  exact (proj1 (rows_lsb_capacity (dyadic_width ws)
    (indexed_weights (extended_weights ws)) 1 Hmass)).
Qed.

(** * Distinct labels in every generated row. *)

Lemma one_row_nodup iws :
  NoDup (map fst iws) -> NoDup (one_row iws).
Proof.
  induction iws as [|[i w] iws IH]; intros Hnd.
  - simpl. constructor.
  - simpl in Hnd. inversion Hnd as [|? ? Hnotin Htail]. subst.
    unfold one_row.
    change (NoDup (map fst
      (if w mod 2 =? 1
       then (i, w) :: filter (fun iw : nat * nat => snd iw mod 2 =? 1) iws
       else filter (fun iw : nat * nat => snd iw mod 2 =? 1) iws))).
    destruct (w mod 2 =? 1) eqn:Hbit.
    + constructor.
      * intros Hin.
        apply Hnotin.
        apply one_row_labels.
        exact Hin.
      * apply IH. exact Htail.
    + apply IH. exact Htail.
Qed.

Lemma rows_lsb_rows_nodup fuel iws :
  NoDup (map fst iws) ->
  forall row, In row (rows_lsb fuel iws) -> NoDup row.
Proof.
  induction fuel as [|fuel IH] in iws |- *; intros Hnd row Hrow.
  - simpl in Hrow. contradiction.
  - simpl in Hrow. destruct Hrow as [<-|Hrow].
    + apply one_row_nodup. exact Hnd.
    + apply IH with (iws := shift_weights iws).
      * rewrite shift_weights_fst. exact Hnd.
      * exact Hrow.
Qed.

Theorem ddg_table_rows_nodup ws :
  forall row, In row (ddg_table ws) -> NoDup row.
Proof.
  intros row Hrow.
  unfold ddg_table in Hrow.
  eapply rows_lsb_rows_nodup.
  - apply indexed_weights_nodup.
  - apply in_rev. exact Hrow.
Qed.

Corollary fldr_round_count ws i :
  admissible ws ->
  naccept (ddg_table ws) 0 i = msum i (ddg_table ws).
Proof.
  intros Hadm.
  rewrite <- (cnt_naccept (ddg_table ws) 0 i).
  pose proof (walk_count (ddg_table ws) i 1
    (ddg_table_capacity ws Hadm)
    (fun row Hrow => ddg_table_rows_nodup ws row Hrow)) as Hwalk.
  simpl in Hwalk.
  lia.
Qed.

Corollary fldr_round_count_weight ws i :
  admissible ws -> i < length (extended_weights ws) ->
  nth i (extended_weights ws) 0 < denominator ws ->
  naccept (ddg_table ws) 0 i = nth i (extended_weights ws) 0.
Proof.
  intros Hadm Hi Hlt.
  rewrite fldr_round_count by exact Hadm.
  apply ddg_table_occupancy_exact; assumption.
Qed.

Example capacity_degenerate_one : capacity_ok (ddg_table [1]) 1.
Proof. vm_compute. exact I. Qed.

Example capacity_321 : capacity_ok (ddg_table [3; 2; 1]) 1.
Proof. vm_compute. repeat split; lia. Qed.

Example capacity_singleton : capacity_ok (ddg_table [5]) 1.
Proof. vm_compute. repeat split; lia. Qed.

Example capacity_power_two : capacity_ok (ddg_table [2; 2]) 1.
Proof. vm_compute. repeat split; lia. Qed.

Example capacity_internal_zero : capacity_ok (ddg_table [2; 0; 1]) 1.
Proof. vm_compute. repeat split; lia. Qed.
