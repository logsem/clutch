From clutch.ub_logic Require Export ub_clutch hash lib.map.
Import Hierarchy.

Module coll_free_hash.

  Context `{!ub_clutchGS Σ}.

  (*

     A module implementing a "collision-free hash" with constant amortized
     error. The hash keeps track of a threshold R, a current
     hash size S such that (S < R) and a size of value space VS. On every
     query on a new element, it samples uniformly from (0,...,VS-1). Once S
     reaches R, the hash is resized, so that L becomes R, R becomes 2R
     and S becomes 2S (e.g., we could sample one extra bit to keep uniformity).
     This guarantees a constant amortized error cost of R0/VS0 assuming
     on initialization S = 0, R = R0 and VS = VS0. This is not a tight bound,
     it is chosen to work nicely with powers of 2, so there is some extra
     unused error credits
  *)

  Variable init_val_size : nat.
  Variable init_r : nat.

  Definition compute_cf_hash : val :=
    λ: "hm" "vs" "s" "r" "v",
      match: get "hm" "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "val_size" := !"vs" in
          let: "b" := rand ("val_size" - #1) in
          set "hm" "v" "b";;
          "s" <- !"s"+#1;;
          if: !"s" = !"r" then
            "r" <- #2 * !"r";;
            "vs" <- #2 * !"val_size";;
            "b"
         else "b"
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


  Definition coll_free (m : gmap nat Z) :=
    forall k1 k2,
      is_Some (m !! k1) ->
      is_Some (m !! k2) ->
      m !!! k1 = m !!! k2 ->
      k1 = k2.

  Lemma coll_free_insert (m : gmap nat Z) (n : nat) (z : Z) :
    m !! n = None ->
    coll_free m ->
    Forall (λ x, z ≠ snd x) (gmap_to_list m) ->
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
      eapply (Forall_iff (uncurry ((λ (k : nat) (v : Z), z ≠ v)))) in HForall; last first.
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
        eapply (Forall_iff (uncurry ((λ (k : nat) (v : Z), z ≠ v)))) in HForall; last first.
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

  Definition cf_hashfun f m (vsval sval rval : nat) ε: iProp Σ :=
    ∃ (hm vs s r : loc),
      € ε ∗
      vs ↦ #vsval ∗ s ↦ #sval ∗ r ↦ #rval ∗
      ⌜ 0 < vsval ⌝ ∗
      ⌜ (rval * init_val_size = init_r *  vsval)%R ⌝ ∗
      ⌜ f = compute_cf_hash_specialized #hm #vs #s #r⌝ ∗
      map_list hm ((λ b, LitV (LitInt b)) <$> m) ∗
      ⌜ sval < rval ⌝ ∗
      ⌜ sval = (length (gmap_to_list m)) ⌝ ∗
      ⌜(ε + (rval - sval)*(init_r)/(init_val_size) >=
          sum_n_m (λ x, x/vsval) sval (rval-1) )%R ⌝ ∗
      ⌜ coll_free m ⌝.

  (*
    The management of the potential is kept abstract by the following
    two lemmas. These allow us to update our error resources after every
    insertion while ensuring that what we get afterwards is still a valid
    collision-free hash. The actual math is in here, after proving these
    the proof of the specifications is straightforward
  *)

  Lemma sum_n_m_le_cond (a b : nat → R) (n m : nat) :
    (∀ k : nat, n ≤ k ≤ m -> a k <= b k) →
    sum_n_m a n m <= sum_n_m b n m.
  Admitted.

  Lemma sum_n_m_INR (n : nat) :
    sum_n_m INR n (2 * n - 1) = (n / 2) * (3 * n - 1).
  Admitted.

  Lemma cf_update_potential_aux (vsval sval rval : nat) (ε : R) :
    (0 <= ε) ->
    (0 < vsval) ->
    (sval + 1 < rval) ->
    (ε + (rval - sval)*(init_r)/(init_val_size) >=
          sum_n_m (λ x, x/vsval) sval (rval - 1))%R ->
    exists ε',
    (0 <= ε') /\ (ε' + (sval / vsval) <= ε + (init_r)/(init_val_size)) /\ (ε' + (rval - (sval + 1))*(init_r)/(init_val_size) >=
          sum_n_m (λ x, x/vsval) (sval + 1) (rval - 1)).
   Proof.
     intros Hpos Hvs Hcomp Hsum.
     exists (ε + (init_r / init_val_size) - (sval / vsval)).
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
         (0 - ((rval - sval - 1) * ε + (rval - sval) * (init_r / init_val_size + - (sval / vsval)))) with
         (((rval - sval) * (sval / vsval) - (rval - sval - 1) * ε) + - ((rval - sval) * init_r / init_val_size) ) by lra.
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
       apply sum_n_m_le_cond.
       intros k H.
       rewrite /Rdiv.
       apply Rmult_le_compat_r.
       + left. by apply Rinv_0_lt_compat.
       + apply le_INR, H.
     - lra.
     - replace
         (ε + init_r / init_val_size - sval / vsval + (rval - (sval + 1)) * init_r / init_val_size) with
         (ε - sval / vsval + (rval - sval) * (init_r / init_val_size)) by lra.
       rewrite Rplus_comm.
       rewrite -Rplus_assoc.
       apply Rle_ge.
       apply Rcomplements.Rle_minus_r.
       apply Rge_le in Hsum.
       rewrite Rplus_comm in Hsum.
       rewrite {2}/Rdiv in Hsum.
       rewrite Rmult_assoc in Hsum.
       etrans; eauto.
       admit.
  Admitted.


  Lemma cf_update_potential (vsval sval rval : nat) ε :
    (sval + 1 < rval)%nat ->
    ( 0 < vsval) ->
      € ε -∗
      ⌜ (ε + (rval - sval)*(init_r)/(init_val_size) >=
          sum_n_m (λ x, x/vsval) sval (rval - 1))%R ⌝%I -∗
      € (nnreal_div (nnreal_nat (init_r)) (nnreal_nat(init_val_size))) -∗
      ∃ (ε' : nonnegreal),
      (€ ε' ∗
      € (nnreal_div (nnreal_nat sval) (nnreal_nat vsval))) ∗
      ⌜(ε' + (rval - (sval + 1))*init_r/(init_val_size) >=
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
      }.
    iExists (mknonnegreal ε' Hε'pos). simpl.
    iSplitL.
    - iApply ec_split.
      simpl.
      iApply (ec_weaken); last first.
      + iApply ec_split; iFrame.
      + simpl.
        rewrite /Rdiv in Hupd.
        rewrite -(Rplus_comm ε).
        auto.
    - iPureIntro.
      auto.
  Qed.


  Lemma cf_update_potential_resize_aux (vsval sval rval : nat) (ε : R) :
    (0 <= ε) ->
    (sval + 1 = rval) ->
    (rval * init_val_size = init_r *  vsval)%R ->
    (ε + (init_r)/(init_val_size) >= ((rval - 1)/vsval)%R) ->
    ((sval / vsval) <= ε + (init_r)/(init_val_size)) /\
      ((2 * rval - (sval + 1))*(init_r)/(init_val_size) >=
          sum_n_m (λ x, x/(2*vsval)) (sval + 1) (2*rval - 1)).
  Proof.
    intros Hpos Heq Hratio Hsum.
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
        admit.
      }
      rewrite Heq.
      replace (2*rval - rval) with (INR rval) by lra.
      replace (rval * init_r / init_val_size) with (rval * rval / vsval); last first.
      {
        rewrite /Rdiv.
        do 2 rewrite (Rmult_assoc rval).
        f_equal.
        admit.
      }
      transitivity (rval * (3 * rval - 1) / (4 * vsval)).
      + admit.
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
  Admitted.


  Lemma cf_update_potential_resize (vsval sval rval : nat) ε :
    (sval + 1 = rval)%nat ->
      € ε -∗
      ⌜ (rval * init_val_size = init_r *  vsval)%R ⌝ -∗
      ⌜ (ε + (init_r)/(init_val_size) >= ((rval - 1)/vsval))%R ⌝%I -∗
      € (nnreal_div (nnreal_nat (init_r)) (nnreal_nat(init_val_size))) -∗
      (€ nnreal_zero ∗
      € (nnreal_div (nnreal_nat sval) (nnreal_nat vsval))) ∗
      ⌜((2 * rval - (sval + 1))*(init_r)/(init_val_size) >=
          sum_n_m (λ x, x/(2*vsval)) (sval + 1) (2*rval - 1))%R ⌝.
  Proof.
    intro Hsval.
    iIntros "Herr1".
    iIntros "%Hratio".
    iIntros "%Hsum".
    iIntros "Herr2".
    epose proof (cf_update_potential_resize_aux vsval sval rval ε (cond_nonneg ε) _ Hratio Hsum) as (Hupd & Hsum').
    Unshelve.
    2:{
        apply (f_equal INR) in Hsval.
        rewrite plus_INR /= in Hsval.
        lra.
      }.
    iSplitL.
    - iApply ec_split.
      iApply (ec_weaken); last first.
      + iApply ec_split; iFrame.
      + simpl.
        rewrite Rplus_0_l.
        rewrite /Rdiv in Hupd.
        rewrite -(Rplus_comm ε).
        auto.
    - iPureIntro.
      auto.
  Qed.


  Lemma wp_insert_no_coll E f m (vsval sval rval: nat) ε (n : nat) :
    m !! n = None →
    0 < vsval ->
    (sval + 1 < rval)%nat ->
    {{{ cf_hashfun f m vsval sval rval ε ∗
          € (nnreal_div (nnreal_nat (init_r)) (nnreal_nat(init_val_size))) }}}
      f #n @ E
    {{{ (v : Z), RET #v;
        ∃ ε',
          cf_hashfun f (<[ n := v ]>m) vsval (sval+1) rval ε' }}}.
  Proof.
    iIntros (Hlookup Hvsval_pos Hineq Φ) "(Hhash & Herr) HΦ".
    iDestruct "Hhash" as (hm vs s r)
                           "(Herr2 & Hvs & Hs & Hr & %Hvspos & Hratio & -> & Hmap & %Hlsr & %Hlen & Htot_err & %Hcf)".
    rewrite /compute_cf_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures.
    wp_load. wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_rand_err_list_int _ (vsval - 1) (map (λ p, snd p) (gmap_to_list m))); auto.
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
    wp_load.
    wp_pures.
    wp_store.
    wp_load.
    wp_load.
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
    iExists ε'.
    rewrite /cf_hashfun.
    iExists hm, vs, s, r.
    (* Is there a way to avoid having to apply this coercion? *)
    assert (#(sval + 1)%nat = #(sval + 1)) as Hsval.
    {
      do 2 f_equal. lia.
    }
    rewrite Hsval.
    iFrame.
    iSplitR; [ done |].
    iSplit.
    - auto.
    - iSplit.
      + rewrite fmap_insert //.
      + iSplit.
        * iPureIntro.
          apply lt_INR in Hineq.
          lra.
        * iSplit.
          -- iPureIntro.
             etrans; last first.
             ** eapply Permutation_length.
                symmetry.
                (* FIXME : Why can it not infer typeclassses ? *)
                eapply (@map_to_list_insert _ _ _ _ _ _ _ _ _ _
                          (gmap_finmap)); eauto.
             ** simpl.
                rewrite -Hlen. lia.
          -- iSplit.
             ++ iPureIntro.
                rewrite plus_INR /= //.
             ++ iPureIntro.
                apply coll_free_insert; auto.
                apply (Forall_map (λ p : nat * Z, p.2)) in HForall; auto.
 Qed.


  Lemma wp_insert_no_coll_resize E f m (vsval sval rval: nat) ε (n : nat) :
    m !! n = None →
    0 < vsval ->
    (sval + 1 = rval)%nat ->
    {{{ cf_hashfun f m vsval sval rval ε ∗
          € (nnreal_div (nnreal_nat (init_r)) (nnreal_nat(init_val_size))) }}}
      f #n @ E
    {{{ (v : Z), RET #v;
          cf_hashfun f (<[ n := v ]>m) (Nat.mul 2 vsval) rval (Nat.mul 2 rval) nnreal_zero }}}.
  Proof.
    iIntros (Hlookup Hvsval_pos Heq Φ) "(Hhash & Herr) HΦ".
    iDestruct "Hhash" as (hm vs s r)
                           "(Herr2 & Hvs & Hs & Hr & %Hvspos & %Hratio & -> & Hmap & %Hlsr & %Hlen & %Htot_err & %Hcf)".
    rewrite /compute_cf_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup. wp_pures.
    wp_load. wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_rand_err_list_int _ (vsval - 1) (map (λ p, snd p) (gmap_to_list m))); auto.
    rewrite map_length -Hlen.
    iPoseProof (cf_update_potential_resize vsval sval rval _ _
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
    wp_load.
    wp_pures.
    wp_store.
    wp_load.
    wp_load.
    wp_pures.
    rewrite bool_decide_eq_true_2; last first.
    {
      do 2 f_equal.
      lia.
    }
    wp_pures.
    wp_load.
    wp_pures.
    wp_store.
    wp_pures.
    wp_store.
    iModIntro.
    iApply "HΦ".
    rewrite /cf_hashfun.
    iExists hm, vs, s, r.
    (* Is there a way to avoid having to apply this coercion? *)
    assert (#(sval + 1)%nat = #(sval + 1)) as Hsval.
    {
      do 2 f_equal. lia.
    }
    iFrame.
    iSplitL "Hvs".
    {
      replace (#(2 * vsval)%nat) with (#(2 * vsval)); auto.
      do 2 f_equal; lia.
    }
    iSplitL "Hs".
    {
      replace (#(rval)) with (#(sval+1)); auto.
      do 2 f_equal; lia.
    }
    iSplitL "Hr".
    {
      replace (#(2 * rval)%nat) with (#(2 * rval)); auto.
      do 2 f_equal; lia.
    }
    iSplitR.
    {
      iPureIntro.
      rewrite mult_INR /=.
      lra.
    }
    iSplitR.
    { iPureIntro.
      do 2 rewrite mult_INR.
      rewrite Rmult_assoc Hratio.
      lra.
    }
    iSplit.
    - auto.
    - iSplit.
      + rewrite fmap_insert //.
      + iSplit.
        * iPureIntro.
          rewrite mult_INR.
          rewrite <- (Rmult_1_l rval) at 1.
          apply Rmult_lt_compat_r.
          -- eapply Rle_lt_trans; eauto.
             apply pos_INR.
          -- simpl. lra.
        * iSplit.
          -- iPureIntro.
             etrans; last first.
             ** eapply Permutation_length.
                symmetry.
                (* FIXME : Why can it not infer typeclassses ? *)
                eapply (@map_to_list_insert _ _ _ _ _ _ _ _ _ _
                          (gmap_finmap)); eauto.
             ** simpl.
                rewrite -Hlen. lia.
          -- iSplit.
             ++ iPureIntro.
                rewrite <- Heq at 3.
                (* This is true, should follow from Hupdp, just annoying to prove *)
                etrans; last first.
                {
                  erewrite sum_n_m_ext; [ apply Hupdp |].
                  intro. rewrite mult_INR /= //.
                }
                right.
                rewrite mult_INR -Heq /Rdiv /=.
                rewrite Rplus_0_l.
                do 2 rewrite Rmult_assoc.
                f_equal.
                rewrite plus_INR /= //.
             ++ iPureIntro.
                apply coll_free_insert; auto.
                apply (Forall_map (λ p : nat * Z, p.2)) in HForall; auto.
 Qed.

End coll_free_hash.
