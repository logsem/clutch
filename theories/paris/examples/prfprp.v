From clutch.paris Require Export paris map list prf prp.
Set Default Proof Using "Type*".

Section prf_prp.

  (* This is the same as the simple hash *)

  Context `{!parisGS Σ}.

  Variable val_size : nat.

  (*
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
*)

  Definition is_sprp := is_sprp val_size.
  Definition init_prp := init_prp val_size.
  Definition is_random_function := is_random_function val_size.
  Definition random_function := random_function val_size.

 Lemma wp_prf_prp_couple_eq_Some E K (k:Z) (f : val) (m : gmap nat Z) (sf : val) (sr : list Z) (n : nat) :
   m !! n = Some k →
   n <= val_size ->
   {{{ ⤇ fill K (sf #n) ∗ is_random_function f m ∗ is_sprp sf m sr}}}
     f #n @ E
     {{{ RET #k;
         ⤇ fill K (of_val #k) ∗ is_random_function f m ∗ is_sprp sf m sr }}}.
 Proof.
   iIntros (Hsome Hrange Φ) "(HK&Hf&Hg) HΦ".
   iMod (spec_prp_prev with "[$]") as "[HK Hg]"; [done|].
   wp_apply (wp_random_function_prev with "[$]"); first done.
   iIntros "Hf".
   iApply "HΦ"; iFrame.
 Qed.

 Lemma wp_prf_prp_couple_eq_err E K (f : val) (m : gmap nat Z) (sf : val) (sr : list Z) (n : nat) (ε : R):
    m !! n = None →
    n <= val_size ->
    (∀ n' : nat, val_size < n' → m !! n' = None) ->
    length sr <= S val_size ->
    (((S val_size - (length sr)) / S val_size)%R <= ε)%R ->
    {{{ ⤇ fill K (sf #n) ∗ is_random_function f m ∗ is_sprp sf m sr ∗ ↯ ε }}}
      f #n @ E
    {{{ (z: Z), RET #z;
        ⤇ fill K (of_val #z) ∗ is_random_function f (<[ n := z ]>m) ∗
          ∃ l1 l2,
                ⌜ sr = l1 ++ z :: l2 ⌝ ∗
          is_sprp sf (<[n := z]>m) (l1 ++ l2) }}}.
 Proof.
    iIntros (Hnone Hrange Hdom Hineq Hε Φ) "(HK & Hprf & Hprp & Herr) HΦ".
    iDestruct "Hprf" as (hm ->) "Hm".
    iDestruct "Hprp" as (lsm lsr) "(-> & Hsm & Hlsr & %Hperm)".
    rewrite /compute_rf_specialized.
    rewrite /query_prp_specialized.
    wp_pures.
    tp_pures.

    (* Some helper lemmas *)
    assert (Forall (λ z: Z , (Z.of_nat (Z.to_nat z)) = z) sr) as HZsr.
    {
      eapply (Forall_app _ ((map_to_list m).*2) sr).
      rewrite Hperm.
      apply Forall_fmap.
      apply Forall_seq.
      intros j Hj. simpl.
      lia.
    }

    edestruct (prp_None_non_full val_size) as (vl & Hvl); eauto.


    (* spec get *)
    tp_bind (get _ _).
    iMod (spec_get with "[$] [$]") as "(HK&Hsm)".
    rewrite lookup_fmap Hnone /=.
    tp_pures.

    (* impl get *)
    wp_apply (wp_get with "[$]").
    iIntros (res) "(Hm&->)".
    rewrite lookup_fmap Hnone /=.
    wp_pures.

    iDestruct "Hlsr" as (lf) "(Hlsr & %Hlf)".

    tp_load.
    tp_bind (list_length _).
    iMod (spec_list_length with "[% //] HK") as (len) "(HK&->)".
    rewrite Hvl. simpl.
    tp_pure.
    tp_pure.
    tp_pure.
    assert (#(S vl - 1) = #vl) as ->.
    {
     do 3 f_equal; lia.
    }

    tp_bind (rand _)%E.
    iDestruct (ec_weaken with "[$]") as "Hε".
    { split; [|done].
      apply Rcomplements.Rdiv_le_0_compat; [|real_solver].
      apply Rle_0_le_minus. real_solver. }
    set f := (λ n : nat, if (n <=? vl) then Z.to_nat (nth n sr 0) else n + val_size).
    wp_apply (wp_couple_rand_rand_rev_inj val_size vl f val_size vl with "[$]").
    {
      intros x Hx.
      rewrite /f.
      rewrite leb_correct; [ | lia].
      apply Forall_nth; [ | lia].
      eapply (Forall_app _ ((map_to_list m).*2) sr).
      rewrite Hperm.
      apply Forall_fmap.
      apply Forall_seq.
      intros j Hj. simpl.
      rewrite Nat2Z.id.
      lia.
    }
    {
      rewrite /f.
      intros x y Hx Hy Hxy.
      rewrite leb_correct in Hxy; [ | lia].
      rewrite leb_correct in Hxy; [ | lia].
      eapply (NoDup_nth sr 0); try lia.
      + apply (NoDup_remove_pref ((map_to_list m).*2)).
        rewrite Hperm.
        rewrite seq_to_seqZ.
        apply NoDup_ListNoDup.
        apply NoDup_seqZ.
      + pose proof (Forall_nth (λ z : Z, Z.of_nat (Z.to_nat z) = z) 0 sr ) as [Haux ?].
        specialize (Haux HZsr).
        rewrite -Haux; [ |lia].
        rewrite -(Haux y); [ |lia].
        by rewrite Hxy.
    }
    {
      apply Permutation_length in Hperm.
      rewrite app_length in Hperm.
      do 2 rewrite fmap_length in Hperm.
      rewrite seq_length Hvl in Hperm.
      lia.
    }
    { rewrite -Hvl. done. }
    iIntros (x) "HK".
    simpl.
    wp_pures.
    tp_pures.
    pose proof (fin_to_nat_lt x).
    tp_load.
    tp_bind (list_remove_nth _ _).
    unshelve iMod (spec_remove_nth _ _ sr _ with "[#] HK")
      as (v) "(HK & (%e & %v' & %l1 & %l2 & (%Hsr & %Hlen & -> & %Hil)))".
    {
      iPureIntro; split; auto.
      lia.
    }
    tp_pures.


    assert (#(f x) = # e) as ->.
    {
      do 3 f_equal.
      rewrite /f.
      rewrite Hsr -Hlen nth_middle leb_correct; [ | lia].
      rewrite Hsr in HZsr.
      eapply (Forall_elt _ _ _ HZsr).
    }
    wp_pures.
    simpl. tp_pures.
    tp_bind (set _ _ _).
    iMod (spec_set with "[$] [$]") as "(HK&Hsm)".
    simpl.
    tp_pures.
    tp_store.
    tp_pures.

    wp_apply (wp_set with "[$]").
    iIntros "Hm". wp_pures. iApply "HΦ".
    iModIntro. iFrame.
    iSplitL "Hm".
    { iExists _. iSplit; first auto. rewrite fmap_insert //. }
    iExists _, _. iSplit; first auto.
    rewrite /is_sprp.
    iExists _.
    iSplit; first auto.
    rewrite fmap_insert.
    iFrame "%∗".
    iPureIntro.
    etrans; [ | apply Hperm ].
    rewrite Hsr.
    rewrite map_to_list_insert; auto.
    replace (((n, e) :: map_to_list m).*2) with (e :: (map_to_list m).*2); [ | auto].
    rewrite Permutation_app_rot.
    rewrite (Permutation_app_rot ((map_to_list m).*2) l1 (e :: l2)).
    apply Permutation_app_head.
    rewrite Permutation_app_comm.
    simpl.
    apply perm_skip.
    by rewrite Permutation_app_comm.
 Qed.


Definition test_prf: val :=
  λ: "n",
    let: "f" := random_function #() in
  letrec: "aux" "f" "i" :=
    (if: "i" ≤ #0
     then  "f"
     else let: "x" := rand #val_size in
          "f" "x";;
          "aux" "f" ("i" - #1)) in
      "aux" "f" "n".


Definition test_prp: val :=
  λ: "n",
    let: "f" := init_prp #() in
    letrec: "aux" "f" "i" :=
    (if: "i" ≤ #0
     then  "f"
     else let: "x" := rand #val_size in
          "f" "x";;
          "aux" "f" ("i" - #1)) in
      "aux" "f" "n".



Lemma wp_prf_prp_test_err_ind E K (f g:val) (m : gmap nat Z) (n k : nat) (l:list Z) (ε : R):
  (0<=k<=n)%nat ->
  ((S val_size) - (n-k))%nat <= length l ->
  NoDup l ->
  l⊆(Z.of_nat <$> seq 0 (S val_size)) ->
  (forall x:Z, x∈ ((map_img m):gset _) -> x ∈ l -> False) ->
  (dom m ⊆ set_seq 0 (S val_size))->
  ((INR(fold_left (Nat.add) (seq (n-k) k) 0%nat) / INR (S val_size))%R <= ε)%R ->
  {{{ ↯ ε ∗
      is_random_function f m ∗
      ⤇ fill K
        ((rec: "aux" "f" "i" :=
            if: "i" ≤ #0 then "f"
            else let: "x" := rand #val_size in "f" "x";; "aux" "f" ("i" - #1))%V g #k) ∗
      is_sprp g m l }}}
    (rec: "aux" "f" "i" :=
       if: "i" ≤ #0 then "f" else let: "x" := rand #val_size in "f" "x";; "aux" "f" ("i" - #1))%V f
    #k
    @ E
    {{{ f, RET f;
        ∃ g m l, ⤇ fill K (of_val g) ∗ is_random_function f m∗
                 is_sprp g m l }}}.
Proof.
  iInduction k as [|k'] "IH" forall (m l ε).
   - iIntros (Hn Hlen HNoDup Hsubseteq Hdom Hdom' Hε Φ) "(Hε & Hf & HK & Hg) HΦ".
     tp_pures. wp_pures.
     iModIntro.
     iApply "HΦ".
     iExists _,_,_. iFrame.

   - iIntros (Hn Hlen HNoDup Hsubseteq Hdom Hdom' Hε Φ) "(Hε & Hf & HK & Hg) HΦ".
     wp_pures.
     wp_bind (rand _)%E.

     tp_pures.
     tp_bind (rand _)%E.
     iMod (ec_zero) as "H0".
     wp_apply (wp_couple_rand_rand_leq val_size val_size val_size val_size _ _ 0
              with "[$]").
     { done. }
     { rewrite Rminus_diag /Rdiv Rmult_0_l /=//. }
     iIntros (n2 m2) "[-> HK]".
     iSimpl in "HK".
     wp_pures.
     wp_bind (f _).

     tp_pures.
     tp_bind (g _).
     iAssert (↯ _ ∗ ↯ _)%I with "[Hε]" as "[Hε Hε']".
     { iApply ec_split; last first.
       - iApply ec_weaken; last done.
         split; last first.
         { etrans; last exact. rewrite <-cons_seq. rewrite fold_symmetric; [|lia|lia].
           rewrite [foldr _ _ _]/=.
           rewrite plus_INR Rdiv_plus_distr. done. }
         apply Rplus_le_le_0_compat; apply Rcomplements.Rdiv_le_0_compat; real_solver.
       - apply Rcomplements.Rdiv_le_0_compat; real_solver.
       - apply Rcomplements.Rdiv_le_0_compat; real_solver. }
     iAssert (⌜(n-S k')<S val_size⌝)%I with "[Hε]" as "%".
     { pose proof Nat.lt_ge_cases (n-S k') (S val_size) as [|]; first done.
       iExFalso. iApply ec_contradict; last done. simpl.
       apply Rcomplements.Rle_div_r.
       - pose proof pos_INR_S val_size. apply Rlt_gt. exact.
       - rewrite Rmult_1_l. replace (_)%R with (INR (S val_size)); last by simpl. apply le_INR. lia. }
     destruct (m!!fin_to_nat m2) eqn:Hm'.
     + wp_apply (wp_prf_prp_couple_eq_Some with "[$]"); try done.
       * apply elem_of_dom_2 in Hm'.
         eapply elem_of_weaken in Hm'; last done.
         rewrite elem_of_set_seq in Hm'. lia.
       * iIntros "(HK & Hf & Hg)".
         do 3 wp_pure. simpl.
         do 3 tp_pure.
         replace (Z.of_nat _ - 1)%Z with (Z.of_nat k')%Z; last lia.
         iApply ("IH" with "[][][][][][][][$]"); try done.
         -- iPureIntro. lia.
         -- iPureIntro. lia.
         -- simpl. iPureIntro. apply Req_le. rewrite fold_symmetric; try (intros; lia).
            replace (S _)  with (n-k'); first done. lia.
     + wp_apply (wp_prf_prp_couple_eq_err _ _ _ _ _ _ m2
                  with "[$Hε $Hg $Hf $HK]"); [done|pose proof(fin_to_nat_lt m2); lia|..].
       * intros. apply not_elem_of_dom_1. intro.
         eassert (n' ∈ (set_seq 0 (S val_size))).
         { eapply elem_of_weaken; exact. }
         rewrite elem_of_set_seq in H2. lia.
       * pose proof list_pigeonhole _ _ Hsubseteq as H0.
         pose proof Nat.lt_ge_cases  (S val_size) (length l) as [H1|H1]; try lia.
         rewrite fmap_length seq_length in H0.
         specialize (H0 H1).
         destruct H0 as (?&?&?&?&?&?).
         eapply NoDup_lookup in HNoDup; [|exact H2|exact H3].
         subst. lia.
       * simpl. rewrite Rdiv_def. f_equal. rewrite minus_INR; last lia.
         rewrite Rdiv_def. apply Rmult_le_compat_r; first pose proof pos_INR_S val_size as H0.
         { rewrite -Rdiv_1_l. apply Rcomplements.Rdiv_le_0_compat; try lra. done. }
         rewrite Rcomplements.Rle_minus_l.
         trans (INR n - INR (S k') + INR (S val_size - (n - S k')))%R; last first.
         { apply Rplus_le_compat_l. apply le_INR. lia. }
         rewrite minus_INR; last lia.
         assert (0<=INR n - INR (S k') - INR (n-S k'))%R; last first.
         { replace (match val_size with | _ => _  end) with (INR (S val_size)); last by simpl.
           lra. }
         rewrite minus_INR; last lia.
         lra.
       * iIntros (z) "(HK & Hf & (%l1 & %l2 & %Hperm & Hg))".
         do 3 wp_pure.
         simpl.
         do 3 tp_pure.
         assert (#(S k' - 1) = #k') as ->.
         {
           do 3 f_equal. lia.
         }
         iApply ("IH" with "[][][][][][][][$Hε' $Hf $HK $Hg][HΦ]").
         -- iPureIntro; lia.
         -- iPureIntro.
            apply le_S_n.
            replace (S (S _ - _)) with (S val_size - (n - S k')) by lia.
            trans (length l); try done.
            subst. rewrite !app_length cons_length. lia.
         -- iPureIntro. subst. apply NoDup_app. apply NoDup_app in HNoDup.
            destruct HNoDup as [?[? HNoDup]]. apply NoDup_cons in HNoDup. set_solver.
         -- iPureIntro. rewrite list_subseteq_app_iff_l. split; set_solver.
         -- iPureIntro. intro. subst. rewrite map_img_insert_notin; last done.
            rewrite elem_of_union elem_of_app. intros [|] [|]; subst.
            ++ set_unfold. subst. apply NoDup_app in HNoDup. set_solver.
            ++ set_unfold. subst. apply NoDup_app in HNoDup.
               destruct HNoDup as [?[? HNoDup]]. apply NoDup_cons in HNoDup.
               set_solver.
            ++ eapply Hdom; set_solver.
            ++ eapply Hdom; set_solver.
         -- iPureIntro. intros. subst.
            rewrite dom_insert_L.
            apply union_least; last done.
            rewrite singleton_subseteq_l.
            rewrite <-set_seq_S_start.
            rewrite elem_of_set_seq.
            pose proof (fin_to_nat_lt m2).
            lia.
         -- simpl. rewrite Rdiv_def. iPureIntro. repeat f_equal. rewrite fold_symmetric; try (intros; lia).
            apply Req_le. replace (S _)  with (n-k'); first done. lia.
         -- iModIntro; done.
            Unshelve.
            ++ apply gset_semi_set.
  Qed.

  Lemma wp_prf_prp_test_err E K (n : nat) (ε : R):
    (INR (fold_left (Nat.add) (seq 0 n) 0%nat) / INR (S val_size))%R = ε ->
    {{{ ⤇ fill K (test_prp #n) ∗ ↯ ε }}}
      test_prf #n @ E
    {{{ f, RET f;
        ∃ g m l, ⤇ fill K (of_val g) ∗ is_random_function f m∗
          is_sprp g m l }}}.
 Proof.
   iIntros (Hε Φ) "(HK & Herr) HΦ ".

   rewrite /test_prf.
   wp_pure.
   wp_bind (random_function _).
   wp_apply (wp_random_function); first done.
   iIntros (f) "Hf".
   do 2 wp_pure.

   rewrite /test_prp.
   tp_pure.
   tp_bind (init_prp _).
   iMod (spec_init_prp with "HK") as (g) "(HK & Hg)".
   iSimpl in "HK".
   do 5 tp_pure.
   do 3 wp_pure.
   wp_apply (wp_prf_prp_test_err_ind with "[$Herr $Hf $HK $Hg]"); [..|done].
   - split; first lia. done.
   - simpl. rewrite fmap_length seq_length. lia.
   - intros. apply NoDup_fmap_2; last apply NoDup_seq. apply Nat2Z.inj'.
   - intros; set_solver.
   - set_solver.
   - set_solver.
   - replace (_-_) with 0; try lia. rewrite <-Hε. done.
 Qed.


End prf_prp.
