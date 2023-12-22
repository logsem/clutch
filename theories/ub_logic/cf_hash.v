From clutch.ub_logic Require Export ub_clutch hash lib.map.
Import Hierarchy.

Module coll_free_hash.

  Context `{!ub_clutchGS Σ}.

  (*

     A module implementing a "collision-free hash" with constant amortized
     error. The hash keeps track of a threshold R, a current
     hash size S such that (S < R) and a size of value space VS. On every
     query on a new element, it samples uniformly from (0,...,VS-1). Once S
     reaches R, the hash is resized, so that L becomes R, R becomes 4R
     and S becomes 4S (e.g., we could sample two extra bits to keep uniformity).
     This guarantees a constant amortized error cost of (2*R0)/VS0 assuming
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
            "r" <- #4 * !"r";;
            "vs" <- #4 * !"val_size";;
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
            r <- #4 * !r;;
            vs <- #4 * "val_size" ;;
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
      ⌜ f = compute_cf_hash_specialized #hm #vs #s #r⌝ ∗
      map_list hm ((λ b, LitV (LitInt b)) <$> m) ∗
      ⌜ sval < rval ⌝ ∗
      ⌜ sval = (length (gmap_to_list m)) ⌝ ∗
      ⌜(ε + (rval - sval)*(2*init_r)/(init_val_size) >=
          sum_n_m (λ x, x/vsval) sval (rval-1) )%R ⌝ ∗
      ⌜ coll_free m ⌝.

  (*
    The management of the potential is kept abstract by the following
    two lemmas. These allow us to update our error resources after every
    insertion while ensuring that what we get afterwards is still a valid
    collision-free hash. The actual math is in here, after proving these
    the proof of the specifications is straightforward
  *)

  Lemma cf_update_potential (vsval sval rval : nat) ε :
    (sval + 1 < rval)%nat ->
      € ε -∗
      ⌜ (ε + (rval - sval)*(2*init_r)/(init_val_size) >=
          sum_n_m (λ x, x/vsval) sval (rval - 1))%R ⌝%I -∗
      € (nnreal_div (nnreal_nat (2*init_r)) (nnreal_nat(init_val_size))) -∗
      ∃ (ε' : nonnegreal),
      € ε' ∗
      € (nnreal_div (nnreal_nat sval) (nnreal_nat vsval)) ∗
      ⌜(ε' + (rval - (sval + 1))*(2*init_r)/(init_val_size) >=
          sum_n_m (λ x, x/vsval) (sval + 1) (rval - 1))%R ⌝.
  Proof.
    intro Hsval.
    iIntros "Herr1".
    iIntros "%Hsum".
    iIntros "Herr2".
  Admitted.


  Lemma cf_update_potential_resize (vsval sval rval : nat) ε :
    (sval + 1 = rval)%nat ->
      € ε -∗
      ⌜ (ε + (2*init_r)/(init_val_size) >= ((rval - 1)/vsval))%R ⌝%I -∗
      € (nnreal_div (nnreal_nat (2*init_r)) (nnreal_nat(init_val_size))) -∗
      € nnreal_zero ∗
      € (nnreal_div (nnreal_nat sval) (nnreal_nat vsval)) ∗
      ⌜((4 * rval - (sval + 1))*(2*init_r)/(init_val_size) >=
          sum_n_m (λ x, x/4*vsval) (sval + 1) (4*rval - 1))%R ⌝.
  Admitted.


  Lemma wp_insert_no_coll E f m (vsval sval rval: nat) ε (n : nat) :
    m !! n = None →
    0 < vsval ->
    (sval + 1 < rval)%nat ->
    {{{ cf_hashfun f m vsval sval rval ε ∗
          € (nnreal_div (nnreal_nat (2*init_r)) (nnreal_nat(init_val_size))) }}}
      f #n @ E
    {{{ (v : Z), RET #v;
        ∃ ε',
          cf_hashfun f (<[ n := v ]>m) vsval (sval+1) rval ε' }}}.
  Proof.
    iIntros (Hlookup Hvsval_pos Hineq Φ) "(Hhash & Herr) HΦ".
    iDestruct "Hhash" as (hm vs s r)
                           "(Herr2 & Hvs & Hs & Hr & -> & Hmap & %Hlsr & %Hlen & Htot_err & %Hcf)".
    rewrite /compute_cf_hash_specialized.
    wp_pures.
    wp_apply (wp_get with "[$]").
    iIntros (vret) "(Hhash&->)".
    rewrite lookup_fmap Hlookup /=. wp_pures.
    wp_load. wp_pures.
    wp_bind (rand _)%E.
    wp_apply (wp_rand_err_list_int _ (vsval - 1) (map (λ p, snd p) (gmap_to_list m))); auto.
    rewrite map_length -Hlen.
    iPoseProof (cf_update_potential _ _ _ _ _
                 with "[Herr2 //] [Htot_err //] [Herr //]")
      as (ε') "(Herr3 & Herr4 & %Hupdp)".
    Unshelve.
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
          € (nnreal_div (nnreal_nat (2*init_r)) (nnreal_nat(init_val_size))) }}}
      f #n @ E
    {{{ (v : Z), RET #v;
          cf_hashfun f (<[ n := v ]>m) (Nat.mul 4 vsval) rval (Nat.mul 4 rval) nnreal_zero }}}.
  Proof.
    iIntros (Hlookup Hvsval_pos Heq Φ) "(Hhash & Herr) HΦ".
    iDestruct "Hhash" as (hm vs s r)
                           "(Herr2 & Hvs & Hs & Hr & -> & Hmap & %Hlsr & %Hlen & %Htot_err & %Hcf)".
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
                 with "[Herr2 //] [] [Herr //]")
      as "(Herr3 & Herr4 & %Hupdp)".
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
      replace (#(4 * vsval)%nat) with (#(4 * vsval)); auto.
      do 2 f_equal; lia.
    }
    iSplitL "Hs".
    {
      replace (#(rval)) with (#(sval+1)); auto.
      do 2 f_equal; lia.
    }
    iSplitL "Hr".
    {
      replace (#(4 * rval)%nat) with (#(4 * rval)); auto.
      do 2 f_equal; lia.
    }
    iSplit.
    - auto.
    - iSplit.
      + rewrite fmap_insert //.
      + iSplit.
        * iPureIntro.
          rewrite mult_INR.
          Search Rlt.
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
                (* This is true, just annoying to prove *)
                admit.
             ++ iPureIntro.
                apply coll_free_insert; auto.
                apply (Forall_map (λ p : nat * Z, p.2)) in HForall; auto.
 Admitted.

End coll_free_hash.
