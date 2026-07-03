From clutch.common Require Import inject.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list.

Section subsampling_code.

  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  Definition subsample : val :=
    rec: "subsample" "l" :=
      match: "l" with
        SOME "a" =>
        let: "hd" := Fst "a" in
        let: "tl" := Snd "a" in
        let: "b" := rand #1 in
        let: "rest" := "subsample" "tl" in
        (if: "b" = #1
         then  SOME ("hd", "rest")
         else  "rest")
      | NONE => NONE
      end.

   Lemma neighbour_split_l {A : Type} (x y : list A) :
     neighbour x y -> (length x > length y)%nat ->
       (exists a xs, x = a :: xs /\ xs = y) \/
       (exists a xs ys, x = a :: xs /\ y = a :: ys /\ neighbour xs ys).
   Proof.
     intros Hn Hlen.
     destruct Hn as [a b n Hx Hy | a b n Hx Hy]; subst.
     - destruct a as [|a0 a'].
       + left. exists n, b. split; done.
       + right. exists a0, (a' ++ [n] ++ b), (a' ++ b).
         repeat split.
         eapply neighbour_add_l; done.
     - exfalso. rewrite !length_app /= in Hlen. lia.
   Qed.

   Lemma neighbour_cons {A : Type} (a : A) (xs ys : list A) :
     neighbour xs ys -> neighbour (a :: xs) (a :: ys).
   Proof.
     destruct 1 as [pfx sfx n Hx Hy | pfx sfx n Hx Hy]; subst.
     - eapply (neighbour_add_l _ _ (a::pfx) sfx n); by simpl.
     - eapply (neighbour_add_r _ _ (a::pfx) sfx n); by simpl.
   Qed.

   (* Running the exact same [subsample] call on both the implementation and
      spec side (on the same underlying list) always yields the same value:
      couple every [rand #1] via the identity bijection. *)
   Lemma subsample_refl (l : list val) (lv : val) K :
     is_list l lv ->
     {{{ ⤇ fill K (subsample lv) }}}
       subsample lv
     {{{ v, RET v; ∃ vs, ⌜is_list vs v⌝ ∗ ⤇ fill K (of_val v) }}}.
   Proof.
     iIntros (Hl Φ) "Hspec HΦ".
     iInduction l as [|a l'] "IH" forall (lv Hl K Φ).
     - simpl in Hl; subst.
       tp_rec. tp_pures.
       wp_rec. wp_pures.
       iApply "HΦ". iExists []. iModIntro. iSplit; [done|]. done.
     - destruct Hl as [lv' [-> Hl']].
       tp_rec. tp_pures.
       wp_rec. wp_pures.
       tp_bind (rand _)%E.
       wp_bind (rand _)%E.
       wp_apply (wp_couple_rand_rand 1 (fun n : nat => n) 1%Z with "Hspec"); [lia|].
       iIntros (n) "[%Hn Hspec]".
       simpl.
       tp_pures. wp_pures.
       tp_bind (subsample _)%E.
       wp_bind (subsample _)%E.
       wp_apply ("IH" $! lv' Hl' with "Hspec").
       iIntros (v) "(%vs & %Hvs & Hspec)".
       simpl.
       tp_pures. wp_pures.
       case_bool_decide as Hb.
       + tp_pures. wp_pures. iApply "HΦ". iExists (a :: vs). iModIntro.
         iSplit; [|done]. iPureIntro. simpl. eexists. split; [done|]. done.
       + tp_pures. wp_pures. iApply "HΦ". iExists vs. iModIntro.
         iSplit; [|done]. done.
   Qed.

   Lemma subsampling_diffpriv_aux (ε δ : R) (xs ys : list val) (xsv ysv : val) K :
        0 <= ε -> 0 <= δ <= 0.5 ->
        {{{ ↯m (ε) ∗ ↯ (δ) ∗
            ⤇ fill K (subsample ysv) ∗
            ⌜is_list xs xsv ⌝ ∗
            ⌜is_list ys ysv ⌝ ∗
            ⌜ neighbour xs ys ⌝ ∗
            ⌜ (length xs > length ys) ⌝
        }}}
            subsample (of_val xsv)
        {{{ v vs vs', RET v ; ∃ (v' : val),
            ⤇ fill K v' ∗
            ⌜is_list vs v ⌝ ∗
            ⌜is_list vs' v' ⌝ ∗
            ((⌜ vs  = vs' ⌝ ∗ ↯m ( ln (2*(exp ε)-1) ) ∗ ↯ (2*δ) ) ∨
               (⌜ neighbour vs vs' ⌝ ))
        }}}.
  Proof.
    iIntros (Hε Hδ). iLöb as "IH" forall (ε δ xs ys xsv ysv K Hε Hδ).
    iIntros (Φ) "(Hεm & Hδ' & Hspec & %Hxs & %Hys & %Hnb & %Hlen) HΦ".
    assert (length xs > length ys)%nat as Hlennat by (apply INR_lt; lra).
    destruct (neighbour_split_l xs ys Hnb Hlennat)
      as [(a & xs' & Hxeq & Hxys) | (a & xs' & ys' & Hxeq & Hyeq & Hnb')].
    { (* Case 1: [xs] has one extra element at the front, [xs' = ys]. *)
      subst xs. subst ys.
      destruct Hxs as [xsv' [-> Hxs']].
      assert (xsv' = ysv) as -> by (eapply is_list_eq; eauto).
      wp_rec. wp_pures.
      wp_bind (rand _)%E.
      wp_apply (hoare_couple_rand_l_adv 1
                  (fun n => if bool_decide (n = 0)%nat then ln (2*(exp ε)-1) else 0)
                  (fun n => if bool_decide (n = 0)%nat then 2*δ else 0)
                  1%Z ⊤ ε δ with "[$Hεm $Hδ']").
      - intros n. case_bool_decide; [|lra].
        have Hexp1 : 1 <= exp ε.
        { have := exp_ineq1_le ε. lra. }
        assert (1 <= 2*(exp ε)-1) as Hge by lra.
        destruct (Rle_lt_or_eq_dec 1 (2*(exp ε)-1) Hge) as [Hlt|Heq].
        + rewrite -ln_1. apply Rlt_le, ln_increasing; lra.
        + rewrite -Heq. rewrite ln_1. lra.
      - intros n. case_bool_decide; lra.
      - have Hdunif : dunifP 1 = dmap bool_to_fin fair_coin.
        { apply distr_ext => n.
          rewrite /pmf /= /dbind_pmf SeriesC_bool.
          rewrite /pmf /= /fair_coin_pmf /dret_pmf.
          inv_fin n; [simpl; lra | intros n].
          inv_fin n; [simpl; lra | intros n].
          inversion n. }
        rewrite Hdunif.
        rewrite Expval_dmap; [ | intros []; apply Rlt_le, exp_pos | apply ex_seriesC_finite].
        rewrite Expval_fair_coin.
        rewrite /compose /=.
        have Hexp1 : 1 <= exp ε.
        { have := exp_ineq1_le ε. lra. }
        rewrite exp_ln; [|lra]. rewrite exp_0. lra.
      - have Hdunif : dunifP 1 = dmap bool_to_fin fair_coin.
        { apply distr_ext => n.
          rewrite /pmf /= /dbind_pmf SeriesC_bool.
          rewrite /pmf /= /fair_coin_pmf /dret_pmf.
          inv_fin n; [simpl; lra | intros n].
          inv_fin n; [simpl; lra | intros n].
          inversion n. }
        rewrite Hdunif.
        rewrite Expval_dmap; [ | intros a0; case_bool_decide; lra | apply ex_seriesC_finite].
        rewrite Expval_fair_coin.
        rewrite /compose /=.
        lra.
      - iIntros (n) "(%Hn & Hεm' & Hδ')".
        wp_pures.
        wp_bind (subsample _)%E.
        wp_apply (subsample_refl xs' ysv K with "Hspec"); [exact Hxs'|].
        iIntros (v) "(%vs & %Hvs & Hspec)".
        wp_pures.
        destruct n as [|[|n]].
        + (* coin = 0: the extra element is dropped, so both sides agree. *)
          wp_pures.
          iApply ("HΦ" $! v vs vs).
          iModIntro. iExists v. iFrame "Hspec". iSplit; [done|]. iSplit; [done|].
          iLeft. iSplit; [done|]. iFrame.
        + (* coin = 1: the extra element is kept, so the results are neighbours. *)
          wp_pures.
          iApply ("HΦ" $! (SOMEV (inject a, v)) (a :: vs) vs).
          iModIntro. iExists v. iFrame "Hspec".
          iSplit.
          { iPureIntro. simpl. eexists. split; [done|]. exact Hvs. }
          iSplit; [done|].
          iRight. iPureIntro. eapply (neighbour_add_l _ _ [] vs a); by simpl.
        + exfalso. apply INR_le in Hn. lia. }
    { (* Case 2: [xs] and [ys] share a common head [a]. *)
      subst xs. subst ys.
      destruct Hxs as [xsv' [-> Hxs']].
      destruct Hys as [ysv2 [-> Hys']].
      tp_rec. tp_pures.
      wp_rec. wp_pures.
      tp_bind (rand _)%E.
      wp_bind (rand _)%E.
      wp_apply (wp_couple_rand_rand 1 (fun n : nat => n) 1%Z with "Hspec"); [lia|].
      iIntros (n) "[%Hn Hspec]".
      simpl.
      tp_pures. wp_pures.
      tp_bind (subsample _)%E.
      wp_bind (subsample _)%E.
      assert (length xs' > length ys') as Hlen'
          by (simpl in Hlennat; apply lt_INR; lia).
      wp_apply ("IH" $! ε δ xs' ys' xsv' ysv2 _ with "[//] [//] [$Hεm $Hδ' $Hspec //]").
      iIntros (v vs vs') "(%v' & Hspec & %Hvs & %Hvs' & Hdisj)".
      tp_pures.
      wp_pures.
      destruct n as [|[|n]].
      - (* coin = 0: the common head is dropped on both sides. *)
        tp_bind (App _ _)%E. do 3 tp_pure. tp_pures.
        wp_pures.
        iApply ("HΦ" $! v vs vs').
        iModIntro. iExists v'. iFrame "Hspec". iSplit; [done|]. iSplit; [done|].
        iExact "Hdisj".
      - (* coin = 1: the common head is kept on both sides. *)
        tp_bind (App _ _)%E. do 3 tp_pure. tp_pures.
        wp_pures.
        iApply ("HΦ" $! (InjRV (a, v)) (a :: vs) (a :: vs')).
        iModIntro. iExists (InjRV (a, v')). iFrame "Hspec".
        iSplit.
        { iPureIntro. simpl. eexists. split; [done|]. exact Hvs. }
        iSplit.
        { iPureIntro. simpl. eexists. split; [done|]. exact Hvs'. }
        iDestruct "Hdisj" as "[(%Heq & Hεm' & Hδ') | %Hnbd]".
        + iLeft. iFrame. iPureIntro. by rewrite Heq.
        + iRight. iPureIntro. by apply neighbour_cons.
      - exfalso. lia. }
  Qed.



End subsampling_code.


