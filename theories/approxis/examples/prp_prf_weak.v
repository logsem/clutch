From clutch.approxis Require Export approxis map list prf prp sum_seq.
Set Default Proof Using "Type*".

Section prp_prf.

  (* The weak PRP/PRF Switching Lemma.

     We prove that (up to error) the idealized PRP and PRF are
     indistinguishable in Q queries by calling each function Q times and
     showing that both produce the same list of results.

   *)

  Variable val_size : nat.

  Definition wPRP := wPRP val_size.
  Definition wPRF := wPRF val_size val_size.
  Definition random_permutation := random_permutation val_size.
  Definition random_function := random_function val_size.

Section Approxis.
  (* We derive the logical refinement in Approxis, in order to then conclude
     via adequacy. *)

  Context `{!approxisGS Σ}.

  
  Definition is_prp := is_prp val_size.
  Definition is_sprp := is_sprp val_size.
  Definition is_random_function := is_random_function val_size.
  Definition is_srandom_function := is_srandom_function val_size.


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

  Lemma wp_prp_prf_couple_eq_Some E K (k:Z) (f : val) (m : gmap nat Z) (sf : val) (sr : list Z) (n : nat) :
    m !! n = Some k →
    n <= val_size ->
    {{{ ⤇ fill K (sf #n) ∗ is_srandom_function sf m ∗ is_prp f m sr}}}
      f #n @ E
      {{{ RET #k;
          ⤇ fill K (of_val #k) ∗ is_srandom_function sf m ∗ is_prp f m sr }}}.
  Proof.
    iIntros (Hsome Hrange Φ) "(HK&Hf&Hg) HΦ".
    iMod (spec_random_function_prev with "[$][$]") as "[??]"; first done.
    wp_apply (wp_prp_prev with "[$]"); first done. 
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
    assert (#(S vl - 1) = #vl) as ->. { do 3 f_equal; lia. }

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


  (* Variable names might be inverted as copied from above *)
  Lemma wp_prp_prf_couple_eq_err E K (f : val) (m : gmap nat Z) (sf : val) (r : list Z) (n : nat) (ε : R):
    m !! n = None →
    n <= val_size ->
    (∀ n' : nat, val_size < n' → m !! n' = None) ->
    length r <= S val_size ->
    (((S val_size - (length r)) / S val_size)%R <= ε)%R ->
    {{{ ⤇ fill K (sf #n) ∗ is_srandom_function sf m ∗ is_prp f m r ∗ ↯ ε }}}
      f #n @ E
      {{{ (z: Z), RET #z;
          ⤇ fill K (of_val #z) ∗ is_srandom_function sf (<[ n := z ]>m) ∗
          ∃ l1 l2,
            ⌜ r = l1 ++ z :: l2 ⌝ ∗
            is_prp f (<[n := z]>m) (l1 ++ l2) }}}.
  Proof.
    iIntros (Hnone Hrange Hdom Hineq Hε Φ) "(HK & Hprf & Hprp & Herr) HΦ".
    iDestruct "Hprf" as (hm ->) "Hm".
    iDestruct "Hprp" as (lsm lsr) "(-> & Hsm & Hlsr & %Hperm)".
    rewrite /compute_rf_specialized.
    rewrite /query_prp_specialized.
    wp_pures.
    tp_pures.

    (* Some helper lemmas *)
    assert (Forall (λ z: Z , (Z.of_nat (Z.to_nat z)) = z) r) as HZsr.
    {
      eapply (Forall_app _ ((map_to_list m).*2) r).
      rewrite Hperm.
      apply Forall_fmap.
      apply Forall_seq.
      intros j Hj. simpl.
      lia.
    }

    edestruct (prp_None_non_full val_size) as (vl & Hvl); eauto.

    (* spec get *)
    tp_bind (get _ _).
    wp_apply (wp_get with " [$]"). iIntros (res) "[Hsm ->]".
    rewrite lookup_fmap Hnone /=.
    wp_pures.

    (* impl get *)
    tp_bind (get _ _).
    iMod (spec_get with "[$][$]") as "[HK Hm]".
    simpl.
    rewrite lookup_fmap Hnone /=.
    tp_pures.

    iDestruct "Hlsr" as (lf) "(Hlsr & %Hlf)".

    wp_load.
    wp_apply (wp_list_length); first done.
    iIntros (?) "->".
    rewrite Hvl. simpl.
    wp_pure.
    wp_pure.
    wp_pure.
    assert (#(S vl - 1) = #vl) as ->. { do 3 f_equal; lia. }

    tp_bind (rand _)%E.
    iDestruct (ec_weaken with "[$]") as "Hε".
    { split; [|done].
      apply Rcomplements.Rdiv_le_0_compat; [|real_solver].
      apply Rle_0_le_minus. real_solver. }
    set f := (λ n : nat, if (n <=? vl) then Z.to_nat (nth n r 0) else n + val_size).
    wp_apply (wp_couple_rand_rand_inj vl val_size f vl val_size with "[$]").
    {
      intros x Hx.
      rewrite /f.
      rewrite leb_correct; [ | lia].
      apply Forall_nth; [ | lia].
      eapply (Forall_app _ ((map_to_list m).*2) r).
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
      eapply (NoDup_nth r 0); try lia.
      + apply (NoDup_remove_pref ((map_to_list m).*2)).
        rewrite Hperm.
        rewrite seq_to_seqZ.
        apply NoDup_ListNoDup.
        apply NoDup_seqZ.
      + pose proof (Forall_nth (λ z : Z, Z.of_nat (Z.to_nat z) = z) 0 r ) as [Haux ?].
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
    wp_load.
    wp_apply (wp_remove_nth).
    { iPureIntro; split; try done. lia. }
    iIntros (?) "(%e & %v' & %l1 & %l2 & (%Hsr & %Hlen & -> & %Hil))".
    wp_pures.


    assert (#(f x) = # e) as ->.
    {
      do 3 f_equal.
      rewrite /f.
      rewrite Hsr -Hlen nth_middle leb_correct; [ | lia].
      rewrite Hsr in HZsr.
      eapply (Forall_elt _ _ _ HZsr).
    }
    tp_bind (set _ _ _).
    iMod (spec_set with "[$][$]") as "[HK Hm]".
    simpl.
    tp_pures.
    wp_apply (wp_set with " [$]").
    iIntros "Hsm".
    simpl.
    wp_pures.
    wp_store.
    wp_pures.
    iApply "HΦ".
    iModIntro. iFrame.
    iSplitL "Hm".
    { iExists _. iSplit; first auto. rewrite fmap_insert //. }
    iExists _, _. iSplit; first auto.
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

 Definition loop (f : val) (res : loc) :=
   (rec: "loop" "i" :=
      if: "i" = #0 then #()
      else let: "x" := rand #val_size in
           let: "y" := f "x" in
           #res <- list_cons ("x", "y") ! #res;;
           "loop" ("i" - #1))%V.

  Lemma wp_wPRF_wPRP_err_ind E K (rf rp : val) (res res' : loc ) (m : gmap nat Z) (n k : nat) (l:list Z) (ε : R):
    (0<=k<=n)%nat ->
    ((S val_size) - (n-k))%nat <= length l ->
    NoDup l ->
    l⊆(Z.of_nat <$> seq 0 (S val_size)) ->
    (forall x:Z, x∈ ((map_img m):gset _) -> x ∈ l -> False) ->
    (dom m ⊆ set_seq 0 (S val_size))->
    ((INR(fold_left (Nat.add) (seq (n-k) k) 0%nat) / INR (S val_size))%R <= ε)%R ->
    {{{ ↯ ε ∗
        is_random_function rf m ∗
        ⤇ fill K (loop rp res' #k) ∗
        is_sprp rp m l ∗
        ∃ lres, ∃ vres : val, ⌜is_list lres vres⌝ ∗ res ↦ vres ∗ res' ↦ₛ vres
    }}}
      loop rf res #k
      @ E
      {{{ RET #();
          ∃ m l,
            ⤇ fill K #() ∗
            is_random_function rf m ∗
            is_sprp rp m l ∗
            ∃ lres, ∃ vres : val, ⌜is_list lres vres⌝ ∗ res ↦ vres ∗ res' ↦ₛ vres
      }}}.
  Proof with (wp_pures ; tp_pures).
    iInduction k as [|Q'] "IH" forall (ε m l).
    - iIntros (Hn Hlen HNoDup Hsubseteq Hdom Hdom' Hε Φ)
        "(ε & rf & spec & rp & %lres & %vres & %list_vres & res & res') HΦ".
      rewrite /loop.
      tp_pures.
      1: by (simpl ; auto).
      wp_pures. iApply "HΦ". iModIntro. iExists _,_. iFrame "rf rp".
      iFrame. by iExists _.
    - iIntros (Hn Hlen HNoDup Hsubseteq Hdom Hdom' Hε Φ)
        "(ε & rf & spec & rp & %lres & %vres & %list_vres & res & res') HΦ".
      rewrite /loop.
      wp_pures.
      tp_pures.
      1: by (simpl ; auto).
      rewrite -/(loop rf res) -/(loop rp res').
      iMod (ec_zero) as "H0".
      wp_apply (wp_couple_rand_rand_leq val_size val_size val_size val_size with "[spec H0]") => //.
      { iSplitL "spec".
        - tp_bind (rand _)%E. done.
        - rewrite Rminus_diag /Rdiv Rmult_0_l /=//.
      }
      iIntros (n2 m2) "[-> spec]".
      iSimpl in "spec"...
      wp_pures. wp_bind (rf _).
      tp_pures. tp_bind (rp _).
      iAssert (↯ _ ∗ ↯ _)%I with "[ε]" as "[Hε Hε']".
      { iApply ec_split; last first.
        - iApply ec_weaken; last done.
          split; last first.
          { etrans; last exact. rewrite <-cons_seq. rewrite fold_symmetric; [|lia|lia].
            rewrite [foldr _ _ _]/=.
            rewrite plus_INR Rdiv_plus_distr. done. }
          apply Rplus_le_le_0_compat; apply Rcomplements.Rdiv_le_0_compat; real_solver.
        - apply Rcomplements.Rdiv_le_0_compat; real_solver.
        - apply Rcomplements.Rdiv_le_0_compat; real_solver. }
      iAssert (⌜(n-S Q')<S val_size⌝)%I with "[Hε]" as "%".
      { pose proof Nat.lt_ge_cases (n-S Q') (S val_size) as [|]; first done.
        iExFalso. iApply ec_contradict; last done. simpl.
        apply Rcomplements.Rle_div_r.
        - pose proof pos_INR_S val_size. apply Rlt_gt. exact.
        - rewrite Rmult_1_l. replace (_)%R with (INR (S val_size)); last by simpl. apply le_INR. lia. }

      destruct (m!!fin_to_nat m2) eqn:Hm'.
      + iApply (wp_prf_prp_couple_eq_Some
                  _ _ _ _ _ _ _ _ Hm' with "[$spec $rf $rp]").
        * apply elem_of_dom_2 in Hm'.
          eapply elem_of_weaken in Hm'; last done.
          rewrite elem_of_set_seq in Hm'. lia.
        * iNext. iIntros " (spec & Hf & Hg)".
          wp_pures. wp_load.
          wp_pure.
          wp_bind (list_cons (#m2, #z)%V vres).
          iApply (wp_list_cons $! list_vres).
          iNext. iIntros (cons_vres) "%list_vres_cons".
          iSimpl in "spec". tp_pure. tp_pure. tp_load. tp_pure.
          tp_bind (list_cons (#m2, #z)%V vres)%E.
          iMod (spec_list_cons $! list_vres with "spec") as "[%vres_cons' [spec %list_vres_cons']]" => // ; iSimpl in "spec".
          wp_store. tp_store. tp_pure. tp_pure.
          wp_pures. tp_pures.
          replace #(S Q' - 1) with (#Q') by (do 2 f_equal ; lia).
          iApply ("IH" $! (foldr Nat.add 0%nat (seq (S (n - S Q')) Q') / S val_size)%R
                   with "[][][][][][][][-HΦ][HΦ]"); try done ; try by (iPureIntro ; lia).
          { simpl. iPureIntro. apply Req_le. rewrite fold_symmetric; try (intros; lia).
            replace (S _)  with (n-Q'); first done. lia. }
          iFrame "Hf Hg spec Hε'".
          pose proof (is_list_eq _ _ _ list_vres_cons list_vres_cons') as eq_vres ; rewrite -eq_vres.
          iExists _,_. by iFrame.
      + wp_apply (wp_prf_prp_couple_eq_err _ _ _ _ _ _ m2
                   with "[$Hε $rp $rf $spec]"); [done|pose proof(fin_to_nat_lt m2); lia|..].
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
          trans (INR n - INR (S Q') + INR (S val_size - (n - S Q')))%R; last first.
          { apply Rplus_le_compat_l. apply le_INR. lia. }
          rewrite minus_INR; last lia.
          assert (0<=INR n - INR (S Q') - INR (n-S Q'))%R; last first.
          { replace (match val_size with | _ => _  end) with (INR (S val_size)); last by simpl.
            lra. }
          rewrite minus_INR; last lia.
          lra.
        * iIntros (z) "(HK & Hf & (%l1 & %l2 & %Hperm & Hg))".
          wp_pures. wp_load.
          wp_pure.
          wp_bind (list_cons (#m2, #z)%V vres).
          iApply (wp_list_cons $! list_vres).
          iNext. iIntros (cons_vres) "%list_vres_cons".
          iSimpl in "HK". tp_pure. tp_pure. tp_load. tp_pure.
          tp_bind (list_cons (#m2, #z)%V vres)%E.
          iMod (spec_list_cons $! list_vres with "HK") as "[%vres_cons' [spec %list_vres_cons']]" => // ; iSimpl in "spec".
          wp_store. tp_store. tp_pure. tp_pure.
          wp_pures. tp_pures.
          replace #(S Q' - 1) with (#Q') by (do 2 f_equal ; lia).
          iApply ("IH" $! (foldr Nat.add 0%nat (seq (S (n - S Q')) Q') / S val_size)%R
                   with "[][][][][][][][-HΦ $Hf $Hg $spec $Hε'][HΦ]"); try done ; try by (iPureIntro ; lia).
          -- iPureIntro.
             apply le_S_n.
             replace (S (S _ - _)) with (S val_size - (n - S Q')) by lia.
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
          -- iPureIntro. intros. subst. simpl.
             rewrite dom_insert_L.
             apply union_least; last done.
             rewrite singleton_subseteq_l.
             rewrite <-set_seq_S_start.
             rewrite elem_of_set_seq.
             pose proof (fin_to_nat_lt m2).
             lia.
          -- simpl. rewrite Rdiv_def. iPureIntro. repeat f_equal. rewrite fold_symmetric; try (intros; lia).
             apply Req_le. replace (S _)  with (n-Q'); first done. lia.
          -- pose proof (is_list_eq _ _ _ list_vres_cons list_vres_cons') as eq_vres ; rewrite -eq_vres.
             iExists _,_ ; by iFrame "res res'".
             Unshelve.
             ++ apply gset_semi_set.
  Qed.


  Lemma wp_wPRP_wPRF_err_ind E K (rf rp : val) (res res' : loc ) (m : gmap nat Z) (n k : nat) (l:list Z) (ε : R):
    (0<=k<=n)%nat ->
    ((S val_size) - (n-k))%nat <= length l ->
    NoDup l ->
    l⊆(Z.of_nat <$> seq 0 (S val_size)) ->
    (forall x:Z, x∈ ((map_img m):gset _) -> x ∈ l -> False) ->
    (dom m ⊆ set_seq 0 (S val_size))->
    ((INR(fold_left (Nat.add) (seq (n-k) k) 0%nat) / INR (S val_size))%R <= ε)%R ->
    {{{ ↯ ε ∗
        is_srandom_function rf m ∗
        ⤇ fill K (loop rf res' #k) ∗
        is_prp rp m l ∗
        ∃ lres, ∃ vres : val, ⌜is_list lres vres⌝ ∗ res ↦ vres ∗ res' ↦ₛ vres
    }}}
      loop rp res #k
      @ E
      {{{ RET #();
          ∃ m l,
            ⤇ fill K #() ∗
            is_srandom_function rf m ∗
            is_prp rp m l ∗
            ∃ lres, ∃ vres : val, ⌜is_list lres vres⌝ ∗ res ↦ vres ∗ res' ↦ₛ vres
      }}}.
  Proof with (wp_pures ; tp_pures).
    iInduction k as [|Q'] "IH" forall (ε m l).
    - iIntros (Hn Hlen HNoDup Hsubseteq Hdom Hdom' Hε Φ)
        "(ε & rf & spec & rp & %lres & %vres & %list_vres & res & res') HΦ".
      rewrite /loop.
      tp_pures.
      1: by (simpl ; auto).
      wp_pures. iApply "HΦ". iModIntro. iExists _,_. iFrame "rf rp".
      iFrame. by iExists _.
    - iIntros (Hn Hlen HNoDup Hsubseteq Hdom Hdom' Hε Φ)
        "(ε & rf & spec & rp & %lres & %vres & %list_vres & res & res') HΦ".
      rewrite /loop.
      wp_pures.
      tp_pures.
      1: by (simpl ; auto).
      rewrite -/(loop rf res) -/(loop rp res').
      iMod (ec_zero) as "H0".
      wp_apply (wp_couple_rand_rand_leq val_size val_size val_size val_size with "[spec H0]") => //.
      { iSplitL "spec".
        - tp_bind (rand _)%E. done.
        - rewrite Rminus_diag /Rdiv Rmult_0_l /=//.
      }
      iIntros (n2 m2) "[-> spec]".
      iSimpl in "spec"...
      wp_pures. wp_bind (rp _).
      tp_pures. tp_bind (rf _).
      iAssert (↯ _ ∗ ↯ _)%I with "[ε]" as "[Hε Hε']".
      { iApply ec_split; last first.
        - iApply ec_weaken; last done.
          split; last first.
          { etrans; last exact. rewrite <-cons_seq. rewrite fold_symmetric; [|lia|lia].
            rewrite [foldr _ _ _]/=.
            rewrite plus_INR Rdiv_plus_distr. done. }
          apply Rplus_le_le_0_compat; apply Rcomplements.Rdiv_le_0_compat; real_solver.
        - apply Rcomplements.Rdiv_le_0_compat; real_solver.
        - apply Rcomplements.Rdiv_le_0_compat; real_solver. }
      iAssert (⌜(n-S Q')<S val_size⌝)%I with "[Hε]" as "%".
      { pose proof Nat.lt_ge_cases (n-S Q') (S val_size) as [|]; first done.
        iExFalso. iApply ec_contradict; last done. simpl.
        apply Rcomplements.Rle_div_r.
        - pose proof pos_INR_S val_size. apply Rlt_gt. exact.
        - rewrite Rmult_1_l. replace (_)%R with (INR (S val_size)); last by simpl. apply le_INR. lia. }

      destruct (m!!fin_to_nat m2) eqn:Hm'.
      + iApply (wp_prp_prf_couple_eq_Some
                  _ _ _ _ _ _ _ _ Hm' with "[$spec $rf $rp]").
        * apply elem_of_dom_2 in Hm'.
          eapply elem_of_weaken in Hm'; last done.
          rewrite elem_of_set_seq in Hm'. lia.
        * iNext. iIntros " (spec & Hf & Hg)".
          wp_pures. wp_load.
          wp_pure.
          wp_bind (list_cons (#m2, #z)%V vres).
          iApply (wp_list_cons $! list_vres).
          iNext. iIntros (cons_vres) "%list_vres_cons".
          iSimpl in "spec". tp_pure. tp_pure. tp_load. tp_pure.
          tp_bind (list_cons (#m2, #z)%V vres)%E.
          iMod (spec_list_cons $! list_vres with "spec") as "[%vres_cons' [spec %list_vres_cons']]" => // ; iSimpl in "spec".
          wp_store. tp_store. wp_pure.
          tp_pure. tp_pure. tp_pure.
          replace #(S Q' - 1) with (#Q') by (do 2 f_equal ; lia).
          iApply ("IH" $! (foldr Nat.add 0%nat (seq (S (n - S Q')) Q') / S val_size)%R
                   with "[][][][][][][][-HΦ][HΦ]"); try done ; try by (iPureIntro ; lia).
          { simpl. iPureIntro. apply Req_le. rewrite fold_symmetric; try (intros; lia).
            replace (S _)  with (n-Q'); first done. lia. }
          iFrame "Hf Hg spec Hε'".
          pose proof (is_list_eq _ _ _ list_vres_cons list_vres_cons') as eq_vres ; rewrite -eq_vres.
          iExists _,_. by iFrame.
      + wp_apply (wp_prp_prf_couple_eq_err _ _ _ _ _ _ m2
                   with "[$Hε $rp $rf $spec]"); [done|pose proof(fin_to_nat_lt m2); lia|..].
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
          trans (INR n - INR (S Q') + INR (S val_size - (n - S Q')))%R; last first.
          { apply Rplus_le_compat_l. apply le_INR. lia. }
          rewrite minus_INR; last lia.
          assert (0<=INR n - INR (S Q') - INR (n-S Q'))%R; last first.
          { replace (match val_size with | _ => _  end) with (INR (S val_size)); last by simpl.
            lra. }
          rewrite minus_INR; last lia.
          lra.
        * iIntros (z) "(HK & Hf & (%l1 & %l2 & %Hperm & Hg))".
          wp_pures. wp_load.
          wp_pure.
          wp_bind (list_cons (#m2, #z)%V vres).
          iApply (wp_list_cons $! list_vres).
          iNext. iIntros (cons_vres) "%list_vres_cons".
          iSimpl in "HK". tp_pure. tp_pure. tp_load. tp_pure.
          tp_bind (list_cons (#m2, #z)%V vres)%E.
          iMod (spec_list_cons $! list_vres with "HK") as "[%vres_cons' [spec %list_vres_cons']]" => // ; iSimpl in "spec".
          wp_store. tp_store. tp_pure. tp_pure. tp_pure.
          wp_pure.
          replace #(S Q' - 1) with (#Q') by (do 2 f_equal ; lia).
          iApply ("IH" $! (foldr Nat.add 0%nat (seq (S (n - S Q')) Q') / S val_size)%R
                   with "[][][][][][][][-HΦ $Hf $Hg $spec $Hε'][HΦ]"); try done ; try by (iPureIntro ; lia).
          -- iPureIntro.
             apply le_S_n.
             replace (S (S _ - _)) with (S val_size - (n - S Q')) by lia.
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
          -- iPureIntro. intros. subst. simpl.
             rewrite dom_insert_L.
             apply union_least; last done.
             rewrite singleton_subseteq_l.
             rewrite <-set_seq_S_start.
             rewrite elem_of_set_seq.
             pose proof (fin_to_nat_lt m2).
             lia.
          -- simpl. rewrite Rdiv_def. iPureIntro. repeat f_equal. rewrite fold_symmetric; try (intros; lia).
             apply Req_le. replace (S _)  with (n-Q'); first done. lia.
          -- pose proof (is_list_eq _ _ _ list_vres_cons list_vres_cons') as eq_vres ; rewrite -eq_vres.
             iExists _,_ ; by iFrame "res res'".
             Unshelve.
             ++ apply gset_semi_set.
  Qed.

  
  (* We compare the "ideal" wPRP and wPRF games (as indicated by the #false
     argument below); to ignore the "real" games (wPRP #true and wPRF #true),
     we provide a dummy scheme. *)
  Definition dummy_scheme : val := ((λ: "_", #()),#()).

  Lemma wp_wPRF_wPRP
    E K (Q : nat) (ε : R) :
    ((fold_left Nat.add (seq 0 Q) 0%nat / S val_size)%R = ε) →
    {{{ ↯ ε ∗ ⤇ fill K (wPRP #false dummy_scheme #Q) }}}
      wPRF #false dummy_scheme #Q @ E
      {{{ (vres : val), RET vres; ⤇ fill K vres }}}.
  Proof with (wp_pures ; tp_pures).
    rewrite /wPRF/wPRP/prf.wPRF/prp.wPRP. iIntros (Hε) "%Φ (ε & spec) HΦ"...
    tp_bind (prp.random_permutation _ #()).
    iMod (spec_random_permutation with "spec") as (rp) "(spec & rp)".
    wp_bind (random_function _).
    wp_apply (wp_random_function); first done.
    iIntros (rf) "rf" ; simpl. wp_pure. wp_pure.
    wp_apply wp_list_nil => //.
    iIntros (vres) "%list_vres".
    wp_alloc res as "res".
    tp_pure. tp_pure.
    tp_bind list_nil.
    iMod (spec_list_nil with "[spec]") as "[%vres' [spec %list_vres']]" => // ; iSimpl in "spec".
    pose proof (is_list_eq _ _ _ list_vres list_vres') as eq_vres ; rewrite -eq_vres.
    tp_alloc as res' "res'".
    do 2 wp_pure. do 2 tp_pure.
    wp_pure. wp_pure. wp_pure.
    wp_bind ((rec: "loop" _ := _) _)%V.
    tp_pure. tp_pure. tp_pure.
    tp_bind ((rec: "loop" _ := _) _)%V.
    iAssert (∃ l vres, ⌜is_list l vres⌝ ∗ res ↦ vres ∗ res' ↦ₛ vres)%I
      with "[res res']" as "res". 1: (iExists _,_ ; by iFrame).
    fold (loop rf res).
    fold (loop rp res').

    iApply (wp_wPRF_wPRP_err_ind with "[-HΦ $ε $rf $rp $spec]").
    - split; first lia. done.
    - simpl. rewrite fmap_length seq_length. lia.
    - intros.
      replace (Z.of_nat 0 :: list_fmap nat Z Z.of_nat (seq 1 val_size)) with (Z.of_nat <$> seq 0 (S val_size)) by easy.
      apply NoDup_fmap_2; last apply NoDup_seq. apply Nat2Z.inj'.
    - intros; set_solver.
    - set_solver.
    - set_solver.
    - replace (_-_) with 0; try lia. rewrite <-Hε. done.
    - easy.
    - iNext. iIntros "(%m & %l & spec & rf & rp & %vlist & %vres'' & %is_res & hres & hres')". wp_pures.
      simpl. tp_pures. tp_load.
      wp_load.
      by iApply "HΦ".
  Qed.


  Lemma wp_wPRP_wPRF
    E K (Q : nat) (ε : R) :
    ((fold_left Nat.add (seq 0 Q) 0%nat / S val_size)%R = ε) →
    {{{ ↯ ε ∗ ⤇ fill K (wPRF #false dummy_scheme #Q) }}}
      (wPRP #false dummy_scheme #Q) @ E
      {{{ (vres : val), RET vres; ⤇ fill K vres }}}.
  Proof with (wp_pures ; tp_pures).
    rewrite /wPRF/wPRP/prf.wPRF/prp.wPRP. iIntros (Hε) "%Φ (ε & spec) HΦ"...
    tp_bind (prf.random_function _ #()).
    iMod (spec_random_function with "spec") as (rf) "(spec & rf)".
    wp_bind (random_permutation _).
    wp_apply (wp_random_permutation); first done.
    iIntros (rp) "rp" ; simpl. wp_pure. wp_pure.
    wp_apply wp_list_nil => //.
    iIntros (vres) "%list_vres".
    wp_alloc res as "res".
    tp_pure. tp_pure.
    tp_bind list_nil.
    iMod (spec_list_nil with "[spec]") as "[%vres' [spec %list_vres']]" => // ; iSimpl in "spec".
    pose proof (is_list_eq _ _ _ list_vres list_vres') as eq_vres ; rewrite -eq_vres.
    tp_alloc as res' "res'".
    do 2 wp_pure. do 2 tp_pure.
    wp_pure. wp_pure. wp_pure.
    wp_bind ((rec: "loop" _ := _) _)%V.
    tp_pure. tp_pure. tp_pure.
    tp_bind ((rec: "loop" _ := _) _)%V.
    iAssert (∃ l vres, ⌜is_list l vres⌝ ∗ res ↦ vres ∗ res' ↦ₛ vres)%I
      with "[res res']" as "res". 1: (iExists _,_ ; by iFrame).
    fold (loop rf res).
    fold (loop rp res').

    iApply (wp_wPRP_wPRF_err_ind with "[-HΦ $ε $rf $rp $spec]").
    - split; first lia. done.
    - simpl. rewrite fmap_length seq_length. lia.
    - intros.
      replace (Z.of_nat 0 :: list_fmap nat Z Z.of_nat (seq 1 val_size)) with (Z.of_nat <$> seq 0 (S val_size)) by easy.
      apply NoDup_fmap_2; last apply NoDup_seq. apply Nat2Z.inj'.
    - intros; set_solver.
    - set_solver.
    - set_solver.
    - replace (_-_) with 0; try lia. rewrite <-Hε. done.
    - easy.
    - iNext. iIntros "(%m & %l & spec & rf & rp & %vlist & %vres'' & %is_res & hres & hres')". wp_pures.
      simpl. tp_pures. tp_load.
      wp_load.
      by iApply "HΦ".
  Qed.

End Approxis.

  Lemma ARC_wPRF_wPRP Σ `{approxisGpreS Σ}
    σ σ' (Q : nat) (ε : R) :
    ((fold_left Nat.add (seq 0 Q) 0%nat / S val_size)%R = ε) →
    ARcoupl
      (lim_exec ((wPRF #false dummy_scheme #Q), σ))
      (lim_exec ((wPRP #false dummy_scheme #Q), σ'))
      (=) ε.
  Proof.
    intros <-. unshelve eapply adequacy.wp_adequacy ; eauto.
    1: apply Rcomplements.Rdiv_le_0_compat; real_solver.
    iIntros (?) "spec ε".
    iApply (wp_wPRF_wPRP _ [] with "[spec $ε]") => //.
    iNext ; iIntros. iExists _. iFrame. done.
  Qed.

  Lemma ARC_wPRP_wPRF Σ `{approxisGpreS Σ}
    σ σ' (Q : nat) (ε : R) :
    ((fold_left Nat.add (seq 0 Q) 0%nat / S val_size)%R = ε) →
    ARcoupl
      (lim_exec ((wPRP #false dummy_scheme #Q), σ))
      (lim_exec ((wPRF #false dummy_scheme #Q), σ'))
      (=) ε.
  Proof.
    intros <-.
    unshelve eapply adequacy.wp_adequacy ; eauto.
    1: apply Rcomplements.Rdiv_le_0_compat; real_solver.
    iIntros (?) "spec ε".
    iApply (wp_wPRP_wPRF _ [] with "[spec $ε]") => //.
    iNext ; iIntros. iExists _. iFrame. done.
  Qed.

  Corollary wPRF_wPRP_bound Σ `{approxisGpreS Σ} σ σ' (Q : nat) ε vres :
    ((((Q - 1) * Q) / (2 * S val_size)) = ε)%R →
    ((lim_exec ((wPRF #false dummy_scheme #Q), σ) vres)
     <=
       ((lim_exec ((wPRP #false dummy_scheme #Q), σ')) vres) + ε)%R.
  Proof.
    intros hε; apply ARcoupl_eq_elim.
    pose proof (sum_seq Q).
    rewrite Rdiv_mult_distr in hε.
    rewrite (sum_seq Q) in hε.
    eapply ARC_wPRF_wPRP => //.
  Qed.

  Corollary wPRP_wPRF_bound Σ `{approxisGpreS Σ} σ σ' (Q : nat) ε vres :
    ((((Q - 1) * Q) / (2 * S val_size)) = ε)%R →
    ((lim_exec ((wPRP #false dummy_scheme #Q), σ) vres)
     <=
       ((lim_exec ((wPRF #false dummy_scheme #Q), σ')) vres) + ε)%R.
  Proof.
    intros hε; apply ARcoupl_eq_elim.
    pose proof (sum_seq Q).
    rewrite Rdiv_mult_distr in hε.
    rewrite (sum_seq Q) in hε.
    eapply ARC_wPRP_wPRF => //.
  Qed.

  Lemma weak_switching_lemma σ σ' (Q : nat) vres :
    (Rabs ((lim_exec (wPRP #false dummy_scheme #Q, σ ) vres) -
           (lim_exec (wPRF #false dummy_scheme #Q, σ') vres))
     <= ((Q - 1) * Q / (2 * S val_size)))%R.
  Proof.
    apply Rabs_le.
    set (ε := ((Q - 1) * Q / (2 * S val_size))%R).
    opose proof (wPRP_wPRF_bound _ σ σ' Q ε vres _) ; eauto.
    { apply subG_approxisRGPreS. apply subG_refl. }
    opose proof (wPRF_wPRP_bound _ σ' σ Q ε vres _) ; eauto.
    { apply subG_approxisRGPreS. apply subG_refl. }
    split ; lra.
  Qed.

End prp_prf.
