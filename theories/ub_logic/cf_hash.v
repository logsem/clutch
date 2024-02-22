From clutch.ub_logic Require Export ub_clutch hash lib.map.
From stdpp Require Import fin_maps.
Import Hierarchy.

Section coll_free_hash.

  Context `{!ub_clutchGS Σ}.

  (*

     A module implementing a "collision-free hash" with constant amortized
     error. The hash keeps track of a threshold R, a current
     hash size S such that (S < R) and a size of value space VS. On every
     query on a new element, it samples uniformly from (0,...,VS-1). Once S
     reaches R, the hash is resized, so that L becomes R, R becomes 2R
     and S becomes 2S (e.g., we could sample one extra bit to keep uniformity).
     This guarantees a constant amortized error cost of 3*R0/4*VS0 assuming
     on initialization S = 0, R = R0 and VS = VS0. This is not a tight bound,
     it is chosen to work nicely with powers of 2, so there is some extra
     unused error credits
  *)

  Variable init_val_size : nat.
  Variable init_r : nat.


  Definition compute_cf_hash : val :=
    λ: "hf" "v",
      let, ("hm" , "vsval", "sval", "rval" ) := "hf" in
      match: get "hm" "v" with
      | SOME "b" => ("b", "hf")
      | NONE =>
          let: "b" := rand ("vsval" - #1) in
          set "hm" "v" "b";;
          if: "sval" + #1 = "rval" then
            ("b", ("hm", #2 * "vsval", "sval" + #1, #2*"rval"))
          else ("b", ("hm", "vsval", "sval" + #1, "rval"))
      end.

  Definition compute_cf_hash_specialized hm vs s r : val :=
    λ: "v",
      match: get hm "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "val_size" := !vs in
          let: "b" := rand ("val_size" - #1) in
          set hm "v" "b";;
          s <- !s+#1;;
          if: !s = !r then
            r <- #2 * !r;;
            vs <- #2 * "val_size" ;;
            "b"
         else "b"
      end.

  Definition init_cf_hash_state : val := init_map.

  Definition init_cf_hash : val :=
    λ: "_",
      let: "hm" := init_cf_hash_state #() in
      let: "vs" := ref (#init_val_size) in
      let: "s" := ref (#0) in
      let: "r" := ref (#init_r) in
      compute_cf_hash "hm" "vs" "s" "r".




  (* A hash function is collision free if the partial map it
     implements is an injective function *)
  Definition coll_free (m : gmap nat nat) :=
    forall k1 k2,
      is_Some (m !! k1) ->
      is_Some (m !! k2) ->
      m !!! k1 = m !!! k2 ->
      k1 = k2.

  Definition is_bounded_prf (m : gmap nat nat) (size : nat) :=
    coll_free m /\
    (forall x : nat, (elem_of x (@map_img _ _ _ _ (gset nat) _ _ _ m)) -> x < size).

  Lemma coll_free_insert (m : gmap nat nat) (n : nat) (z : nat) :
    m !! n = None ->
    coll_free m ->
    Forall (λ x, z ≠ snd x) (map_to_list m) ->
    coll_free (<[ n := z ]>m).
  Proof.
    intros Hnone Hcoll HForall.
    intros k1 k2 Hk1 Hk2 Heq.
    apply lookup_insert_is_Some' in Hk1.
    apply lookup_insert_is_Some' in Hk2.
    destruct (decide (n = k1)).
    - destruct (decide (n = k2)); simplify_eq; auto.
      destruct Hk2 as [|Hk2]; auto.
      rewrite lookup_total_insert in Heq.
      rewrite lookup_total_insert_ne // in Heq.
      apply lookup_lookup_total in Hk2.
      rewrite -Heq in Hk2.
      eapply (Forall_iff (uncurry ((λ (k : nat) (v : nat), z ≠ v)))) in HForall; last first.
      { intros (?&?); eauto. }
      eapply map_Forall_to_list in HForall.
      rewrite /map_Forall in HForall.
      eapply HForall in Hk2; congruence.
    - destruct (decide (n = k2)); simplify_eq; auto.
      {
        destruct Hk1 as [|Hk1]; auto.
        rewrite lookup_total_insert in Heq.
        rewrite lookup_total_insert_ne // in Heq.
        apply lookup_lookup_total in Hk1.
        rewrite Heq in Hk1.
        eapply (Forall_iff (uncurry ((λ (k : nat) (v : nat), z ≠ v)))) in HForall; last first.
        { intros (?&?); eauto. }
        eapply map_Forall_to_list in HForall.
        rewrite /map_Forall in HForall.
        eapply HForall in Hk1; congruence.
      }
      rewrite ?lookup_total_insert_ne // in Heq.
      destruct Hk1 as [|Hk1]; try congruence; [].
      destruct Hk2 as [|Hk2]; try congruence; [].
      apply Hcoll; eauto.
  Qed.


  (*
     The representation predicate stores, alongside the
     values for all the variables keeping track of the
     hash size and threshold, a reserve of error credits,
     such that when the actual error becomes larger than
     the constant amortized amount of error credits we
     get on every insertion, we are still able to pay
     for the totalerror
  *)

  Definition cf_hashfun_raw hf m (vsval sval rval : nat) : iProp Σ :=
    ∃ (lm : loc) (ε : nonnegreal),
      (* The current internals of the hash function *)
      ⌜ hf = (#lm, #vsval, #sval, #rval)%V ⌝ ∗
      (* The reserve of error credits *)
      € ε ∗
      ⌜ 0 < vsval ⌝ ∗
      (* The ratio between the threshold and the size of the sample space
         is kept constant *)
      ⌜ (rval / vsval = init_r/ init_val_size)%R ⌝ ∗
      (* The internal list-based map represents the exposed abstract map *)
      map_list lm ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗
      ⌜ sval < rval ⌝ ∗
      ⌜ sval = (length (map_to_list m)) ⌝ ∗
      (* The current reserve plus the amortized cost times the number of insertions
         until the next resize is enough to pay for all the error *)
      ⌜(ε + (rval - sval)*(3 * init_r)/(4 * init_val_size) >=
          sum_n_m (λ x, x/vsval) sval (rval-1) )%R ⌝ ∗
      ⌜ is_bounded_prf m vsval ⌝.

  Lemma cf_hashfun_bounded_prf f m vsval sval rval :
    cf_hashfun_raw f m vsval sval rval -∗ ⌜ is_bounded_prf m vsval ⌝ ∗ cf_hashfun_raw f m vsval sval rval.
  Proof.
    iIntros "Hhash".
    rewrite /cf_hashfun_raw.
    iDestruct "Hhash" as (hm ε) "(?&?&?&?&?&?&?&?&?)".
    iSplit; auto.
    iExists _,_. iFrame.
  Qed.

  Definition cf_hashfun f m : iProp Σ :=
    ∃ (vsval sval rval : nat),
      cf_hashfun_raw f m vsval sval rval.

  Lemma sum_n_m_le_cond (a b : nat → R) (n m : nat) :
    (n <= m)%nat ->
    (∀ k : nat, n ≤ k ≤ m -> a k <= b k) →
    sum_n_m a n m <= sum_n_m b n m.
  Proof.
    intros Hnm.
    induction Hnm; intros Hleq.
    - do 2 rewrite sum_n_n.
      apply Hleq. auto.
    - rewrite sum_n_Sm; [ | apply le_S; auto].
      rewrite sum_n_Sm ; [ | apply le_S; auto].
      etrans; last first.
      + apply Rplus_le_compat_l.
        apply Hleq; split; auto.
      + apply Rplus_le_compat_r.
        apply IHHnm.
        intros ? [].
        apply Hleq.
        split; auto.
  Qed.

  Lemma sum_n_INR (n : nat) :
    sum_n INR n = (n / 2) * (n + 1).
  Proof.
    induction n.
    - rewrite sum_O /=. lra.
    - rewrite sum_Sn IHn.
      rewrite S_INR /=.
      rewrite /plus/=. lra.
  Qed.

  Lemma sum_n_m_INR (n : nat) :
    sum_n_m INR n (2 * n - 1) = (n / 2) * (3 * n - 1).
  Proof.
    destruct n.
    - simpl.
      rewrite sum_n_n /=.
      lra.
    - rewrite sum_n_m_sum_n; last first.
      {
        simpl.
        rewrite Nat.sub_0_r.
        rewrite Nat.add_0_r.
        auto with arith.
      }
      rewrite S_INR /=.
      rewrite /minus/=/plus/=/opp/=.
      rewrite Nat.sub_0_r.
      rewrite Nat.add_0_r.
      rewrite sum_n_INR /=.
      rewrite sum_n_INR /=.
      rewrite plus_INR.
      rewrite S_INR /=. lra.
  Qed.


   (*
     Auxiliary lemma for updating our error resources in the non-resizing cases.
     This is mostly "straightforward" since, by assumption, the representation
     predicate already states that we have all the error credits that we will need,
     so this is mostly moving around the credits associated to the first insertion.
     Most of the proof is showing that the credit reserve we are left with is still
     non-negative.
   *)


  Lemma cf_update_potential_aux (vsval sval rval : nat) (ε : R) :
    (0 <= ε) ->
    (0 < vsval) ->
    (sval + 1 < rval) ->
    (ε + (rval - sval)*(3 * init_r)/(4 * init_val_size) >=
          sum_n_m (λ x, x/vsval) sval (rval - 1))%R ->
    exists ε',
    (0 <= ε') /\ (ε' + (sval / vsval) <= ε + (3 * init_r)/(4 * init_val_size)) /\ (ε' + (rval - (sval + 1))*(3 * init_r)/(4 * init_val_size) >=
          sum_n_m (λ x, x/vsval) (sval + 1) (rval - 1)).
   Proof.
     intros Hpos Hvs Hcomp Hsum.
     assert (sval ≤ rval - 1) as Hcomp'.
     {
       destruct rval.
       - simpl in Hcomp.
         pose proof (pos_INR sval). lra.
       - simpl.
         rewrite Nat.sub_0_r.
         apply INR_le.
         rewrite S_INR in Hcomp. lra.
     }
     exists (ε + ((3 * init_r) / (4 * init_val_size)) - (sval / vsval)).
     split; [ | split].
     - apply (Rmult_le_reg_l (rval - sval)); [lra |].
       rewrite Rmult_0_r {2}/Rminus Rplus_assoc Rmult_plus_distr_l.
       replace ((rval - sval) * ε) with (ε + ((rval - sval - 1) * ε)) by lra.
       apply Rge_le in Hsum.
       apply Rcomplements.Rle_minus_l in Hsum.
       rewrite Rplus_assoc.
       apply Rcomplements.Rle_minus_l.
       etrans; eauto.
       replace
         (0 - ((rval - sval - 1) * ε + (rval - sval) * (3 * init_r / ( 4 * init_val_size) + - (sval / vsval)))) with
         (((rval - sval) * (sval / vsval) - (rval - sval - 1) * ε) + - ((rval - sval) * (3 * init_r) / (4 * init_val_size))) by lra.
       rewrite {6}/Rminus.
       apply Rplus_le_compat_r.
       apply Rcomplements.Rle_minus_l.
       etrans; last first.
       {
         eapply Rle_plus_l; [apply Rle_refl |].
         nra.
       }
       replace ((rval - sval) * (sval / vsval)) with (sum_n_m (λ x : nat, sval / vsval) sval (rval - 1)); last first.
       {
         rewrite sum_n_m_const.
         rewrite minus_INR.
         - rewrite S_INR.
           rewrite minus_INR.
           + simpl. f_equal. lra.
           + simpl in Hcomp.
             apply INR_le.
             rewrite S_INR /=.
             left.
             eapply Rle_lt_trans; eauto.
             eapply Rplus_le_compat_r.
             apply pos_INR.
         - apply INR_le.
           rewrite S_INR /=.
           rewrite minus_INR.
           + simpl. lra.
           + simpl in Hcomp.
             apply INR_le.
             rewrite S_INR /=.
             left.
             eapply Rle_lt_trans; eauto.
             eapply Rplus_le_compat_r.
             apply pos_INR.
       }
       apply sum_n_m_le_cond; auto.
       intros k H.
       rewrite /Rdiv.
       apply Rmult_le_compat_r.
       + left. by apply Rinv_0_lt_compat.
       + apply le_INR, H.
     - lra.
     - replace
         (ε + 3 * init_r / (4 * init_val_size) - sval / vsval + (rval - (sval + 1)) * (3 * init_r) / (4 * init_val_size)) with
         (ε - sval / vsval + (rval - sval) * (3 * init_r / (4 * init_val_size))) by lra.
       rewrite Rplus_comm.
       rewrite -Rplus_assoc.
       apply Rle_ge.
       apply Rcomplements.Rle_minus_r.
       apply Rge_le in Hsum.
       rewrite Rplus_comm in Hsum.
       rewrite {2}/Rdiv in Hsum.
       rewrite Rmult_assoc in Hsum.
       etrans; eauto.
       replace (Init.Nat.add sval (S O)) with (S sval);
         [ | by rewrite Nat.add_1_r].
       rewrite (sum_Sn_m _ sval); [rewrite /plus/=; lra|]; auto.
  Qed.

   (*
     Auxiliary lemma for updating our error resources in the resizing case.
     This is more interesting, since when updating the bounds and the sampling space
     size we need to re-establish the representation predicate. Most of the actual
     math is used in here.
   *)

  Lemma cf_update_potential_resize_aux (vsval sval rval : nat) (ε : R) :
    (0 <= ε) ->
    ( 0 < vsval) ->
    (sval + 1 = rval) ->
    (rval / vsval =  init_r / init_val_size)%R ->
    (ε + (3 * init_r)/(4 * init_val_size) >= ((rval - 1)/vsval)%R) ->
    ((sval / vsval) <= ε + (3 * init_r)/(4 * init_val_size)) /\
      ((2 * rval - (sval + 1))*(3 * init_r)/(4 * init_val_size) >=
          sum_n_m (λ x, x/(2*vsval)) (sval + 1) (2*rval - 1)).
  Proof.
    intros Hpos Hvsval Heq Hratio Hsum.
    split.
    - nra.
    - rewrite (sum_n_m_ext _ (λ x, x * (1 / (2 * vsval)))); last first.
      {
        intros. rewrite /Rdiv. lra.
      }
      replace
        (sum_n_m (λ x : nat, x * (1 / (2 * vsval))) (sval + 1) (2 * rval - 1)) with
        ((1 / (2 * vsval)) * (rval / 2) * (3 * rval - 1)); last first.
      {
        replace (Init.Nat.add sval (S O)) with rval; last first.
        - apply INR_eq.
          by rewrite plus_INR.
        - erewrite sum_n_m_ext; [ | by intro; rewrite Rmult_comm].
          rewrite sum_n_m_scal_l.
          rewrite sum_n_m_INR.
          rewrite /scal/=/mult/=.
          lra.
      }
      rewrite Heq.
      replace (2*rval - rval) with (INR rval) by lra.
      replace (rval * (3 * init_r) / (4 * init_val_size)) with (rval * (3 * rval) / (4 * vsval)); last first.
      {
        rewrite /Rdiv.
        rewrite /Rdiv in Hratio.
        do 2 rewrite (Rmult_assoc rval).
        replace (3 * rval * / (4 * vsval)) with ((3 / 4) * (rval / vsval)); last first.
        - rewrite /Rdiv Rinv_mult. lra.
        - rewrite /Rdiv Hratio Rinv_mult. lra.
      }
      transitivity (rval * (3 * rval - 1) / (4 * vsval)).
      + apply Rle_ge.
        rewrite /Rdiv.
        do 2 rewrite Rmult_assoc.
        apply Rmult_le_compat_l; [ apply pos_INR |].
        apply Rmult_le_compat_r; [ | lra ].
        left.
        apply Rinv_0_lt_compat. lra.
      + right.
        rewrite -Rmult_assoc.
        rewrite -(Rmult_comm rval (1 / (2 * vsval))).
        rewrite /Rdiv.
        do 3 rewrite (Rmult_assoc rval).
        f_equal.
        rewrite Rmult_1_l.
        rewrite -(Rmult_comm (3 * rval - 1)).
        f_equal.
        rewrite -Rinv_mult.
        f_equal.
        lra.
  Qed.


  (*
    The management of the potential is kept abstract by the following
    two lemmas. These allow us to update our error resources after every
    insertion while ensuring that what we get afterwards is still a valid
    collision-free hash.  *)


  Lemma cf_update_potential (vsval sval rval : nat) ε :
    (sval + 1 < rval)%nat ->
    ( 0 < vsval) ->
      € ε -∗
      ⌜ (ε + (rval - sval)*(3 * init_r)/(4 * init_val_size) >=
          sum_n_m (λ x, x/vsval) sval (rval - 1))%R ⌝%I -∗
      € (nnreal_div (nnreal_nat (3 * init_r)) (nnreal_nat(4 * init_val_size))) -∗
      ∃ (ε' : nonnegreal),
      (€ ε' ∗
      € (nnreal_div (nnreal_nat sval) (nnreal_nat vsval))) ∗
      ⌜(ε' + (rval - (sval + 1))*(3 * init_r)/(4 *init_val_size) >=
          sum_n_m (λ x, x/vsval) (sval + 1) (rval - 1))%R ⌝.
  Proof.
    intros Hsval Hvsval.
    iIntros "Herr1".
    iIntros "%Hsum".
    iIntros "Herr2".
    epose proof (cf_update_potential_aux vsval sval rval ε (cond_nonneg ε) Hvsval _ Hsum) as (ε' & Hε'pos & Hupd & Hsum').
    Unshelve.
    2:{
      apply lt_INR in Hsval.
      rewrite plus_INR /= in Hsval.
      lra.
      }
    iExists (mknonnegreal ε' Hε'pos). simpl.
    iSplitL.
    - iApply ec_split.
      simpl.
      iApply (ec_weaken); last first.
      + iApply ec_split; iFrame.
      + simpl.
        rewrite /Rdiv in Hupd.
        rewrite -(Rplus_comm ε).
        do 2 rewrite Nat.add_0_r.
        etrans; eauto.
        apply Rplus_le_compat; [lra |].
        do 5 rewrite plus_INR. right.
        f_equal; [lra |].
        f_equal. lra.
    - iPureIntro.
      auto.
  Qed.




  Lemma cf_update_potential_resize (vsval sval rval : nat) ε :
    (sval + 1 = rval)%nat ->
    ( 0 < vsval) ->
      € ε -∗
      ⌜ (rval / vsval = init_r / init_val_size)%R ⌝ -∗
      ⌜ (ε + (3 * init_r)/(4 * init_val_size) >= ((rval - 1)/vsval))%R ⌝%I -∗
      € (nnreal_div (nnreal_nat (3 * init_r)) (nnreal_nat(4 * init_val_size))) -∗
      (€ nnreal_zero ∗
      € (nnreal_div (nnreal_nat sval) (nnreal_nat vsval))) ∗
      ⌜((2 * rval - (sval + 1))*(3 * init_r)/(4 * init_val_size) >=
          sum_n_m (λ x, x/(2*vsval)) (sval + 1) (2*rval - 1))%R ⌝.
  Proof.
    intros Hsval Hvsval.
    iIntros "Herr1".
    iIntros "%Hratio".
    iIntros "%Hsum".
    iIntros "Herr2".
    epose proof (cf_update_potential_resize_aux vsval sval rval ε (cond_nonneg ε) Hvsval _ Hratio Hsum) as (Hupd & Hsum').
    Unshelve.
    2:{
        apply (f_equal INR) in Hsval.
        rewrite plus_INR /= in Hsval.
        lra.
      }
    iSplitL.
    - iApply ec_split.
      iApply (ec_weaken); last first.
      + iApply ec_split; iFrame.
      + simpl.
        rewrite Rplus_0_l.
        rewrite /Rdiv in Hupd.
        rewrite -(Rplus_comm ε).
        etrans; eauto.
        apply Rplus_le_compat; [lra |].
        do 7 rewrite plus_INR. right.
        simpl.
        do 2 rewrite Rplus_0_r.
        f_equal; [lra |].
        f_equal. lra.
    - iPureIntro.
      auto.
  Qed.


  (* The spec for a non-resizing insertion.
     If we have a collision free hash, and we get € (3 * init_r) / (4 * init_val_size)
     then we return a collision free hash, with enough credits in the reserve to pay
     for future insertions *)


  Lemma wp_insert_no_coll E f m (vsval sval rval: nat) (n : nat) :
    m !! n = None →
    0 < vsval ->
    (sval + 1 < rval)%nat ->
    {{{ cf_hashfun_raw f m vsval sval rval ∗
          € (nnreal_div (nnreal_nat (3 * init_r)) (nnreal_nat(4 * init_val_size))) }}}
      compute_cf_hash f #n @ E
    {{{ (v : nat) (f' : val), RET (#v, f')%V;
        ⌜ v < vsval ⌝ ∗ ⌜ v ∉ (@map_img _ _ _ _ (gset nat) _ _ _ m) ⌝ ∗
          cf_hashfun_raw f' (<[ n := v ]>m) vsval (sval+1) rval }}}.
  Proof.
    iIntros (Hlookup Hvsval_pos Hineq Φ) "(Hhash & Herr) HΦ".
    iDestruct "Hhash" as (hm ε)
                           "(-> & Herr2 & %Hvspos & Hratio & Hmap & %Hlsr & %Hlen & Htot_err & (%Hcf & %Himg))".
    rewrite /compute_cf_hash.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_rand_err_list_nat _ (vsval - 1) (map (λ p, snd p) (map_to_list m))); auto.
    rewrite map_length -Hlen.
    iPoseProof (cf_update_potential _ _ _ _ _ _
                 with "[Herr2 //] [Htot_err //] [Herr //]")
      as (ε') "((Herr3 & Herr4) & %Hupdp)".
    Unshelve.
    2:{ auto. }
    2:{ auto. }
    replace (nnreal_nat ((Z.to_nat (vsval - 1)) + 1)) with
              (nnreal_nat vsval); last first.
    { f_equal.
      destruct vsval; [ |lia].
      simpl in Hvsval_pos.
      lra.
    }
    iFrame.
    iIntros "%x %HForall".
    wp_pures.
    wp_apply (wp_set with "Hhash").
    iIntros "Hlist".
    wp_pures.
    rewrite bool_decide_eq_false_2; last first.
    {
      intro H.
      inversion H.
      lia.
    }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iSplit.
    {
      iPureIntro.
      eapply (Rlt_le_trans _ (S (Z.to_nat (Z.sub (Z.of_nat vsval) (Zpos xH))))); eauto.
      { apply lt_INR. apply fin_to_nat_lt. }
      right.
      f_equal.
      destruct vsval; [simpl in Hvsval_pos; lra |].
      rewrite Z2Nat.inj_sub; last by lia.
      rewrite Nat2Z.id /=. lia.
    }
    iSplit.
    {
      iPureIntro.
      intro Hx.
      apply (Forall_map (λ p : nat * nat, p.2)) in HForall; auto.
      apply elem_of_map_img_1 in Hx as (i & Hi).
      apply elem_of_map_to_list in Hi.
      eapply Forall_forall in HForall; eauto.
      done.
    }
    rewrite /cf_hashfun_raw.
    iExists hm, ε'.
    (* Is there a way to avoid having to apply this coercion? *)
    assert (#(sval + 1)%nat = #(sval + 1)) as Hsval.
    {
      do 2 f_equal. lia.
    }
    rewrite Hsval.
    iFrame.
    iSplit; auto.
    iSplitR; [ done |].
    iSplit.
    - rewrite fmap_insert //.
    - iSplit.
      + iPureIntro.
        apply lt_INR in Hineq.
        lra.
      + iSplit.
        * iPureIntro.
           etrans; last first.
           ** eapply Permutation_length.
              symmetry.
              (* FIXME : Why can it not infer typeclassses ? *)
              eapply (@map_to_list_insert _ _ _ _ _ _ _ _ _ _
                        (gmap_finmap)); eauto.
           ** simpl.
              rewrite -Hlen. lia.
        * iSplit.
           ** iPureIntro.
              rewrite plus_INR /= //.
           ** iPureIntro.
              split.
              *** apply coll_free_insert; auto.
                 apply (Forall_map (λ p : nat * nat, p.2)) in HForall; auto.
              *** intros y Hy.
                 assert (S (Z.to_nat (Z.sub (Z.of_nat vsval) (Zpos xH))) = vsval) as Hfin.
                 {
                   destruct vsval; [simpl in Hvsval_pos; lra |].
                   rewrite Z2Nat.inj_sub; last by lia.
                   rewrite Nat2Z.id /=. lia.
                 }
                 apply elem_of_map_img_1 in Hy as (i & Hi).
                 destruct (decide(n = i)) as [-> | Hneq].
                 **** rewrite lookup_insert in Hi. inversion Hi.
                     eapply (Rlt_le_trans _ (S (Z.to_nat (Z.sub (Z.of_nat vsval) (Zpos xH))))); eauto.
                     { apply lt_INR. apply fin_to_nat_lt. }
                     right. f_equal.
                     destruct vsval; [simpl in Hvsval_pos; lra |].
                     rewrite Z2Nat.inj_sub; last by lia.
                     rewrite Nat2Z.id /=. lia.

                 **** rewrite lookup_insert_ne in Hi; auto.
                     apply Himg.
                     eapply elem_of_map_img_2; eauto.
  Qed.


  (* The spec for a resizing insertion.
     If we have a collision free hash that is one insertion away from the threshold,
     and we get € (3 * init_r) / (4 * init_val_size) then we return a collision free hash
     with updated sizes and threshold, and an empty credit reserve  *)

  Lemma wp_insert_no_coll_resize E f m (vsval sval rval: nat) (n : nat) :
    m !! n = None →
    0 < vsval ->
    (sval + 1 = rval)%nat ->
    {{{ cf_hashfun_raw f m vsval sval rval ∗
          € (nnreal_div (nnreal_nat (3 * init_r)) (nnreal_nat(4 * init_val_size))) }}}
      compute_cf_hash f #n @ E
    {{{ (v : nat) (f' : val), RET (#v, f');
        ⌜ v < vsval ⌝ ∗ ⌜ v ∉ (@map_img _ _ _ _ (gset nat) _ _ _ m) ⌝ ∗
          cf_hashfun_raw f' (<[ n := v ]>m) (Nat.mul 2 vsval) rval (Nat.mul 2 rval) }}}.
  Proof.
    iIntros (Hlookup Hvsval_pos Heq Φ) "(Hhash & Herr) HΦ".
    iDestruct "Hhash" as (hm ε)
                           "(-> & Herr2 & %Hvspos & %Hratio & Hmap & %Hlsr & %Hlen & %Htot_err & (%Hcf & %Himg))".
    rewrite /compute_cf_hash.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup. wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_rand_err_list_nat _ (vsval - 1) (map (λ p, snd p) (map_to_list m))); auto.

    rewrite map_length -Hlen.
    iPoseProof (cf_update_potential_resize vsval sval rval _ _ Hvspos
                 with "[Herr2 //] [//] [] [Herr //]")
      as "((Herr3 & Herr4) & %Hupdp)".
    Unshelve.
    {
      iPureIntro.
      rewrite -Heq plus_INR /= in Htot_err.
      rewrite Nat.add_sub sum_n_n in Htot_err.
      rewrite -Heq /=.
      rewrite plus_INR /=.
      rewrite /Rminus Rplus_assoc Rplus_minus Rmult_1_l in Htot_err.
      setoid_rewrite Htot_err.
      lra.
    }
    2:{ auto. }
    replace (nnreal_nat ((Z.to_nat (vsval - 1)) + 1)) with
              (nnreal_nat vsval); last first.
    { f_equal.
      destruct vsval; [ |lia].
      simpl in Hvsval_pos.
      lra.
    }
    iFrame.
    iIntros "%x %HForall".
    wp_pures.
    wp_apply (wp_set with "Hhash").
    iIntros "Hlist".
    wp_pures.
    rewrite bool_decide_eq_true_2; last first.
    {
      do 2 f_equal.
      lia.
    }
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iSplit.
    {
      iPureIntro.
      eapply (Rlt_le_trans _ (S (Z.to_nat (Z.sub (Z.of_nat vsval) (Zpos xH))))); eauto.
      { apply lt_INR. apply fin_to_nat_lt. }
      right.
      f_equal.
      destruct vsval; [simpl in Hvsval_pos; lra |].
      rewrite Z2Nat.inj_sub; last by lia.
      rewrite Nat2Z.id /=. lia.
    }
    iSplit.
    {
      iPureIntro.
      intro Hx.
      apply (Forall_map (λ p : nat * nat, p.2)) in HForall; auto.
      apply elem_of_map_img_1 in Hx as (i & Hi).
      apply elem_of_map_to_list in Hi.
      eapply Forall_forall in HForall; eauto.
      done.
    }
    rewrite /cf_hashfun_raw.
    iExists hm, nnreal_zero.
    (* Is there a way to avoid having to apply this coercion? *)
    assert (#(sval + 1)%nat = #(sval + 1)) as Hsval.
    {
      do 2 f_equal. lia.
    }
    iFrame.
    iSplit; auto.
    {
      replace (#(2 * vsval)%nat) with (#(2 * vsval)); [ |do 2 f_equal; lia ].
      replace (#(rval)) with (#(sval+1)); [ |do 2 f_equal; lia ].
      replace (#(2 * rval)%nat) with (#(2 * rval)); [ |do 2 f_equal; lia ].
      auto.
    }
    iSplit.
    {
      iPureIntro.
      rewrite mult_INR /=.
      lra.
    }
    iSplit.
    { iPureIntro.
      do 2 rewrite mult_INR.
      rewrite -Hratio.
      rewrite /Rdiv Rinv_mult /=.
      lra.
    }
    iSplit.
    + rewrite fmap_insert //.
    + iSplit.
      * iPureIntro.
        rewrite mult_INR.
        rewrite <- (Rmult_1_l rval) at 1.
        apply Rmult_lt_compat_r.
        ** eapply Rle_lt_trans; eauto.
           apply pos_INR.
        ** simpl. lra.
      * iSplit.
        ** iPureIntro.
           etrans; last first.
           *** eapply Permutation_length.
              symmetry.
              (* FIXME : Why can it not infer typeclassses ? *)
              eapply (@map_to_list_insert _ _ _ _ _ _ _ _ _ _
                        (gmap_finmap)); eauto.
           *** simpl.
              rewrite -Hlen. lia.
        ** iSplit.
           *** iPureIntro.
              rewrite <- Heq at 3.
              etrans; last first.
              {
                erewrite sum_n_m_ext; [ apply Hupdp |].
                intro. rewrite mult_INR /= //.
              }
              right.
              rewrite -Heq /=.
              rewrite Rplus_0_l.
              do 2 f_equal.
              do 4 rewrite plus_INR /=.
              lra.
           *** iPureIntro.
              split.
              -- apply coll_free_insert; auto.
                 apply (Forall_map (λ p : nat * nat, p.2)) in HForall; auto.
              -- intros y Hy.
                 assert (S (Z.to_nat (Z.sub (Z.of_nat vsval) (Zpos xH))) = vsval) as Hfin.
                 {
                   destruct vsval; [simpl in Hvsval_pos; lra |].
                   rewrite Z2Nat.inj_sub; last by lia.
                   rewrite Nat2Z.id /=. lia.
                 }
                 apply elem_of_map_img_1 in Hy as (i & Hi).
                 destruct (decide(n = i)) as [-> | Hneq].
                 ++ rewrite lookup_insert in Hi. inversion Hi.
                     eapply (Rlt_le_trans _ (S (Z.to_nat (Z.sub (Z.of_nat vsval) (Zpos xH))))); eauto.
                     { apply lt_INR. apply fin_to_nat_lt. }
                     transitivity vsval.
                     { right. f_equal.
                     destruct vsval; [simpl in Hvsval_pos; lra |].
                     rewrite Z2Nat.inj_sub; last by lia.
                     rewrite Nat2Z.id /=. lia. }
                     rewrite mult_INR /=. lra.
                 ++ rewrite lookup_insert_ne in Hi; auto.
                     transitivity vsval.
                     { apply Himg.
                       eapply elem_of_map_img_2; eauto. }
                     rewrite mult_INR /= //. lra.
  Qed.


  Lemma wp_lookup_no_coll E f m (vsval sval rval: nat) (n : nat) x :
    m !! n = Some x →
    {{{ cf_hashfun_raw f m vsval sval rval }}}
      compute_cf_hash f #n @ E
      {{{ (v : nat) (f' : val), RET (#v, f') ; ⌜ v = x ⌝ ∗ cf_hashfun_raw f' m vsval sval rval }}}.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (hm ε)
                           "(-> & Herr2 & %Hvspos & Hratio & Hmap & %Hlsr & %Hlen & Htot_err & %Hcf)".
    rewrite /compute_cf_hash.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup. wp_pures.
    iModIntro.
    iApply "HΦ".
    rewrite /cf_hashfun_raw.
    iSplit; auto.
    iExists hm, ε.
    iFrame.
    iSplit; auto.
  Qed.


  Lemma wp_hf_lookup_none E f m (n : nat) :
    m !! n = None →
    {{{ cf_hashfun f m ∗
          € (nnreal_div (nnreal_nat (3 * init_r)) (nnreal_nat(4 * init_val_size)))}}}
      compute_cf_hash f #n @ E
      {{{ (v : nat) (f' : val), RET (#v, f'); cf_hashfun f' (<[ n := v ]>m)  }}}.
  Proof.
    iIntros (Hlookup Φ) "[Hhash Herr] HΦ".
    iDestruct "Hhash" as (vsval sval rval) "Hhash".
    iDestruct "Hhash" as (hm ε)
                           "(-> &  Herr2 & %Hvspos & Hratio & Hmap & %Hlsr & %Hlen & Htot_err & %Hcf)".
    assert ((sval + 1 < rval)%nat \/ (sval + 1 = rval)%nat) as [Hleq | Heq].
    {
      apply INR_lt in Hlsr.
      inversion Hlsr.
      - right. lia.
      - left. lia.
    }
    - wp_apply (wp_insert_no_coll with "[-HΦ]"); eauto.
      + iFrame.
        iExists _,_. by iFrame.
      + iIntros (v f') "(?&?&Hhash)".
        iApply "HΦ".
        rewrite /cf_hashfun.
        iExists _,_,_. done.
    - wp_apply (wp_insert_no_coll_resize with "[-HΦ]"); eauto.
      + iFrame.
        iExists _,_. by iFrame.
      + iIntros (v f') "(?&?&Hhash)".
        iApply "HΦ".
        rewrite /cf_hashfun.
        iExists _,_,_. done.
  Qed.


  Lemma wp_hf_lookup_some E f m (n : nat) x :
    m !! n = Some x →
    {{{ cf_hashfun f m }}}
      compute_cf_hash f #n @ E
    {{{ (v : nat) (f' : val), RET (#v, f'); ⌜v = x⌝ ∗ cf_hashfun f' m  }}}.
  Proof.
    iIntros (Hlookup Φ) "Hhash HΦ".
    iDestruct "Hhash" as (vsval sval rval) "Hhash".
    iDestruct "Hhash" as (hm ε)
                           "(-> & Herr2 & %Hvspos & Hratio & Hmap & %Hlsr & %Hlen & Htot_err & %Hcf)".
    wp_apply (wp_lookup_no_coll with "[-HΦ]"); eauto.
      + iExists _,_. by iFrame.
      + iIntros (v f') "[? Hhash]".
        iApply "HΦ". iFrame.
        rewrite /cf_hashfun.
        iExists _,_,_. done.
  Qed.




End coll_free_hash.
