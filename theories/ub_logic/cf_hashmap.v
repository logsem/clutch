From clutch.ub_logic Require Export ub_clutch hash lib.map lib.array cf_hash.
From stdpp Require Import gmap.

Import Hierarchy.

Section coll_free_hashmap.

  Context `{!ub_clutchGS Σ}.

  (*

     A module implementing a "collision-free" hashmap with constant amortized
     insertion error and 0 lookup error. As in the hash function, we keep track
     of a threshold R, a current hashmap size S such that (S < R) and total
     size of hashmap VS. Insertions to this map are done through the use of a
     collision free hash function to ensure that no collisions happen.
  *)

  Variable init_val_size : nat.
  Variable init_r : nat.


  Definition insert_elem : val :=
    λ: "l" "hf" "s" "r" "val_size" "v",
      let: "off" := "hf" "v" in
      let: "w" := !("l" +ₗ "off") in
      if: "w" = #() then
        ("l" +ₗ "off") <- "v" ;;
        "s" <- !"s" + #1 ;;
         if: !"s" = !"r" then
           let: "l'" := array_resize "l" !"val_size" !"val_size" in
           "r" <- #2 * !"r";;
           "val_size" <- #2 * !"val_size";;
           "l'"
         else "l"
      else "l".


  Definition filter_units (vs : list val) :=
    filter (λ v, ¬(v = #())) vs.


  Lemma list_filter_insert_True {A : Type} (P : A -> Prop) (H : ∀ x : A, Decision (P x))
                                (l : list A) (i : nat) (v w : A) :
    i < length l ->
    l !! i = Some w ->
    ¬ (P w) ->
    (P v) ->
    filter P (<[i:=v]> l) ≡ₚ  (cons v (filter P l)).
  Proof.
    revert i.
    induction l; intros i Hlen Hi Hw Hv; apply INR_lt in Hlen.
    - simpl in Hlen.
      inversion Hlen.
    - destruct i.
      + simpl.
        simpl in Hi; inversion Hi; simplify_eq.
        do 2 rewrite filter_cons.
        rewrite decide_True; auto.
        rewrite decide_False; auto.
      + simpl.
        do 2 rewrite filter_cons.
        destruct (decide (P a)).
        * rewrite IHl; auto.
          ** apply Permutation_swap.
          ** simpl in Hlen.
             apply lt_INR. lia.
        * apply IHl; auto.
          simpl in Hlen.
          apply lt_INR. lia.
  Qed.



  Definition cf_hashmap_raw (l : loc) (ns : gset nat) f (vs s r : loc) : iProp Σ :=
    ∃ (vsval sval rval : nat) (m : gmap nat nat) (img : list val),
      (* The reserve of error credits *)
        vs ↦ #vsval ∗ s ↦ #sval ∗ r ↦ #rval ∗
        l ↦∗ img ∗
        ⌜ 0 < vsval ⌝ ∗
        ⌜ sval < rval ⌝ ∗
        ⌜ length img = vsval ⌝ ∗
      (cf_hashfun_raw init_val_size init_r f m vsval sval rval ) ∗
      ⌜ (filter_units img) ≡ₚ (λ b, LitV (LitInt (Z.of_nat b))) <$> (elements ns) ⌝ ∗
      ⌜ forall (i v : nat), m !! v = Some i <-> img !! i = Some #v ⌝ ∗
      ⌜ forall (i : nat), (i < vsval) ->
                    i ∉ (@map_img _ _ _ _ (gset nat) _ _ _ m) ->
                    img !! i = Some #() ⌝ ∗
      ⌜ dom m = ns ⌝.


  Lemma wp_hm_insert E l ns f (vs s r : loc) (n : nat) :
    {{{ cf_hashmap_raw l ns f vs s r ∗
          € (nnreal_div (nnreal_nat (3 * init_r)) (nnreal_nat(4 * init_val_size))) }}}
      insert_elem #l f #s #r #vs #n  @ E
    {{{ l', RET #l';
          cf_hashmap_raw l' (ns ∪ {[n]}) f vs s r }}}.
  Proof.
    iIntros (Φ) "(Htable & Herr) HΦ".
    iDestruct "Htable" as (vsval sval rval m img)
                            " (Hvs & Hs & Hr & Hl & %Hvspos & %Hineq & %Hlen & Hhash & %Hperm & %HimgN & %HimgU & %Hdom)".
    (*
    iDestruct "Hhash" as (hm vs' s' r' ε)
                           "(Herr2 & Hvs' & Hs' & Hr' & %Hvspos' & Hratio & -> & Hmap & %Hlsr & %Hlen & Htot_err & %Hcf)".
    *)
    assert (#(sval + 1)%nat = #(sval + 1)) as Hsval.
    {
      do 2 f_equal. lia.
    }
    rewrite /insert_elem.
    wp_pures.
    destruct (m !! n) as [v |] eqn:Hlu.
    - wp_apply (wp_lookup_no_coll with "[Hhash]"); eauto.
      iIntros (?) "(-> & Hhf)".
      wp_pures.
      wp_apply (wp_load_offset with "[Hl //]").
      { by apply HimgN.  }
      iIntros "Hl".
      wp_pures.
      iApply "HΦ".
      iModIntro.
      rewrite /cf_hashmap_raw.
      iExists vsval, sval, rval, m, img.
      rewrite /cf_hashfun_raw.
      iDestruct "Hhf" as (?????) "(?&?&?&?&?&?&?&?&?&?&?& %Hprf)".
      iFrame.
      (* TODO: Notation *)
      iSplitL "Hl"; [done| ].
      iSplit; [done|].
      iSplit; [iExists _,_,_,_,_; by iFrame |].
      iPureIntro.
      destruct Hprf as (Hcf & Himg). split.
      + assert ((ns ∪ {[n]}) = ns) as ->; auto.
        assert (n ∈ ns); [ | set_solver].
        rewrite -Hdom.
        by apply elem_of_dom.
      + rewrite Hdom.
        assert (n ∈ ns); [ | set_solver].
        rewrite -Hdom.
        by apply elem_of_dom.
    - assert ((sval + 1 < rval)%nat \/ (sval + 1 = rval)%nat) as [Hleq | Heq].
      {
        apply INR_lt in Hineq.
        inversion Hineq.
        - right. lia.
        - left. lia.
      }
      + wp_apply (wp_insert_no_coll _ _ _ _ _ vsval sval rval with "[$Hhash $Herr]"); eauto.
        iIntros (k) "(%Hklt & %Hkimg & Hhash)".
        wp_pures.
        wp_apply (wp_load_offset with "[Hl //]"); auto.
        iIntros "Hl".
        wp_pures.
        wp_apply (wp_store_offset with "[Hl //]").
        { apply lookup_lt_is_Some_2.
          rewrite Hlen.
          by apply INR_lt.
        }
        iIntros "Hl".
        wp_pures.
        wp_load.
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
        iApply "HΦ".
        iModIntro.
        rewrite /cf_hashmap_raw.
        iExists _, (sval + 1)%nat, _, _, (<[k:=#n]> img).
        rewrite /cf_hashfun_raw.
        iDestruct "Hhash" as (?????) "(?&?&?&?&?&?&?&?&?&?&?& %Hprf)".
        iFrame.
        iSplitL "Hs"; [by rewrite Hsval |].
        iSplitL "Hl"; [done | ].
        iSplit.
        { iPureIntro.
          rewrite insert_length //.
        }
        iSplit.
        { iExists _,_,_,_,_.
          iFrame.
          iSplit; [ done |].
          iSplit; [| done].
          iPureIntro.
          by apply lt_INR.
        }
        iPureIntro.
        destruct Hprf as (Hcf & Himg). split; [| split; [|split]].
        * rewrite /filter_units /=.
          rewrite list_filter_insert_True; auto.
          2:{ rewrite Hlen //. }
          rewrite union_comm.
          rewrite elements_union_singleton /=; last first.
          {
            intros H.
            assert (#n ∈ filter_units img) as H2.
            {
              rewrite Hperm.
              apply (elem_of_list_fmap).
              eexists; split; eauto.
              set_solver.
            }
            rewrite /filter_units in H2.
            apply elem_of_list_filter in H2 as (H3 & H4).
            apply elem_of_list_lookup_1 in H4 as (i & Hi).
            apply HimgN in Hi. simplify_eq.
          }
          by apply perm_skip.
        * intros i v; split; intros H.
          ** destruct (decide (k = i)) as [-> | Hneqki].
             *** rewrite list_lookup_insert; [ | apply INR_lt; rewrite Hlen // ].
                 destruct (decide (n = v)) as [-> | Hneqnv]; auto.
                 rewrite lookup_insert_ne in H; auto.
                 exfalso. apply Hkimg.
                 by eapply elem_of_map_img_2.
             *** rewrite list_lookup_insert_ne; auto.
                 apply HimgN.
                 destruct (decide (n = v)) as [-> | Hneqnv]; auto.
                 **** rewrite lookup_insert in H.
                      inversion H; done.
                 **** rewrite lookup_insert_ne in H; auto.
          ** destruct (decide (n = v)) as [-> | Hneqnv].
             *** rewrite lookup_insert.
                 destruct (decide (k = i)) as [-> | Hneqki]; auto.
                 rewrite list_lookup_insert_ne in H; auto.
                 exfalso. apply Hkimg.
                 set_solver.
             *** rewrite lookup_insert_ne; auto.
                 apply HimgN.
                 destruct (decide (k = i)) as [-> | Hneqki]; auto.
                 **** rewrite list_lookup_insert in H; [inversion H; simplify_eq | ].
                      rewrite Hlen. apply INR_lt; auto.
                 **** rewrite list_lookup_insert_ne in H; auto.
        * intros i Hi Hiimg.
          destruct (decide (k = i)) as [-> | Hneqki].
          ** exfalso.
             apply Hiimg.
             eapply elem_of_map_img.
             exists n. rewrite lookup_insert //.
          ** rewrite list_lookup_insert_ne; eauto.
             apply HimgU; auto.
             intro Him.
             apply Hiimg.
             rewrite map_img_insert_notin; auto.
             set_solver.

        * rewrite dom_insert_L.
          rewrite Hdom. set_solver.

      + iPoseProof (cf_hashfun_bounded_prf with "[Hhash //]") as "(%Hprf_pre & Hhash)".
        wp_apply (wp_insert_no_coll_resize _ _ _ _ _ vsval sval rval with "[$Hhash $Herr]"); eauto.
        iIntros (k) "(%Hklt & %Hkimg & Hhash)".
        wp_pures.
        wp_apply (wp_load_offset with "[Hl //]"); auto.
        iIntros "Hl".
        wp_pures.
        wp_apply (wp_store_offset with "[Hl //]").
        { apply lookup_lt_is_Some_2.
          rewrite Hlen.
          by apply INR_lt.
        }
        iIntros "Hl".
        wp_pures.
        wp_load.
        wp_store.
        wp_load.
        wp_load.
        wp_pures.
        rewrite bool_decide_eq_true_2; last first.
        { do 2 f_equal. lia. }
        wp_pures.
        wp_load.
        wp_load.
        wp_bind (array_resize _ _ _).
        rewrite -Hsval.
        wp_apply (wp_array_resize _ l _ (<[k:=#n]> img) _ _ with "[Hl]"); auto; try lia.
        { rewrite insert_length. lia. }
        { by apply INR_lt. }
        { by apply INR_lt. }
        iIntros (l') "(Hl & Hl')".
        wp_pures.
        wp_load.
        wp_store.
        wp_load.
        wp_store.
        iApply "HΦ".
        iModIntro.
        replace (#(2 * rval)) with (#(2 * rval)%nat); last first.
        { do 2 f_equal. lia. }
        replace (#(2 * vsval)) with (#(2 * vsval)%nat); last first.
        { do 2 f_equal. lia. }
        rewrite /cf_hashmap_raw.
        iExists (2 * vsval)%nat, (sval + 1)%nat, (2 * rval)%nat, _,(<[k:=#n]> img ++ replicate (vsval) #()).
        rewrite /cf_hashfun_raw.
        iDestruct "Hhash" as (?????) "(?&?&?&?&?&?&?&?&?&?&?& %Hprf)".
        iFrame.
        iSplit.
        {
          iPureIntro.
          apply lt_INR.
          lia.
        }
        iSplit.
        {
          iPureIntro.
          rewrite app_length insert_length replicate_length.
          lia.
        }
        iSplit.
        {
          iExists _,_,s0,_,_.
          rewrite Heq.
          iFrame.
          iSplit.
          { iPureIntro. rewrite mult_INR /=. lra. }
          done.
        }
        iPureIntro.
        destruct Hprf as (Hcf & Himg). split; [| split; [|split]].
        * rewrite /filter_units.
          simpl.
          rewrite filter_app.
          rewrite list_filter_insert_True; auto.
          2:{ rewrite Hlen //. }
          rewrite union_comm.
          rewrite elements_union_singleton /=; last first.
          {
            intros H.
            assert (#n ∈ filter_units img) as H2.
            {
              rewrite Hperm.
              apply (elem_of_list_fmap).
              eexists; split; eauto.
              set_solver.
            }
            rewrite /filter_units in H2.
            apply elem_of_list_filter in H2 as (H3 & H4).
            apply elem_of_list_lookup_1 in H4 as (i & Hi).
            apply HimgN in Hi. simplify_eq.
          }
          (* TODO: Move outside *)
          assert (forall N, filter (λ v : val, v ≠ #()) (replicate N #()) = []) as ->.
          {
            induction N.
            - simpl.
              rewrite filter_nil //.
            - simpl.
              rewrite filter_cons /=.
              apply IHN.
          }
          rewrite app_nil_r.
          by apply perm_skip.

        * intros i v. split; intros H.
          ** destruct (decide (k = i)) as [-> | Hneqki].
             *** rewrite lookup_app_l; last first.
                 { rewrite insert_length. apply INR_lt. rewrite Hlen //. }
                 rewrite list_lookup_insert; [ | apply INR_lt; rewrite Hlen // ].
                 destruct (decide (n = v)) as [-> | Hneqnv]; auto.
                 rewrite lookup_insert_ne in H; auto.
                 exfalso. apply Hkimg.
                 by eapply elem_of_map_img_2.
             *** destruct (decide (n = v)) as [-> | Hneqnv]; auto.
                 **** rewrite lookup_insert in H.
                      inversion H; done.
                 **** rewrite lookup_insert_ne in H; auto.
                      rewrite lookup_app_l; last first.
                      {
                       rewrite insert_length. apply INR_lt.
                       rewrite /is_bounded_prf in Hprf_pre.
                       destruct Hprf_pre as (H3 & H4).
                       rewrite Hlen.
                       apply H4.
                       apply elem_of_map_img; eauto.
                     }
                     rewrite list_lookup_insert_ne; auto.
                     by apply HimgN.

          ** destruct (decide (n = v)) as [-> | Hneqnv].
             *** rewrite lookup_insert.
                 destruct (decide (k = i)) as [-> | Hneqki]; auto.
                 assert ((i < length img \/ length img <= i)%nat) as [?|?] by lia.
                 **** rewrite lookup_app_l in H; [ | rewrite insert_length // ].
                      rewrite list_lookup_insert_ne in H; auto.
                      exfalso. apply Hkimg.
                      set_solver.
                 **** rewrite lookup_app_r in H; [ | rewrite insert_length // ].
                      rewrite lookup_replicate in H.
                      destruct H as (?&?).
                      simplify_eq.

             *** rewrite lookup_insert_ne; auto.
                 apply HimgN.
                 assert ((i < length img \/ length img <= i)%nat) as [?|?] by lia.
                 **** rewrite lookup_app_l in H; [ | rewrite insert_length // ].
                      destruct (decide (k = i)) as [-> | Hneqki]; auto.
                      ***** rewrite list_lookup_insert in H; [inversion H; simplify_eq | ].
                      rewrite Hlen. apply INR_lt; auto.
                      ***** rewrite list_lookup_insert_ne in H; auto.
                 **** rewrite lookup_app_r in H; [ | rewrite insert_length // ].
                      rewrite lookup_replicate in H.
                      destruct H as (?&?).
                      simplify_eq.

        * intros i Hi Hiimg.
          destruct (decide (k = i)) as [-> | Hneqki].
          ** exfalso.
             apply Hiimg.
             eapply elem_of_map_img.
             exists n. rewrite lookup_insert //.
          ** assert ((i < length img \/ length img <= i)%nat) as [?|?] by lia.
             *** rewrite lookup_app_l; [ | rewrite insert_length // ].
                 rewrite list_lookup_insert_ne; eauto.
                 apply HimgU; auto.
                 { apply lt_INR. lia. }
                 intro Him.
                 apply Hiimg.
                 rewrite map_img_insert_notin; auto.
                 set_solver.
             *** rewrite lookup_app_r; [ | rewrite insert_length // ].
                 rewrite lookup_replicate; split; auto.
                 rewrite insert_length -Hlen.
                 apply INR_lt in Hi.
                 lia.
        * rewrite dom_insert_L.
          rewrite Hdom. set_solver.
 Qed.


End coll_free_hashmap.
