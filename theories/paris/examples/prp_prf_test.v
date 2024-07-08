From clutch.paris Require Export paris map list prf prp prp_prf_weak.
Set Default Proof Using "Type*".

Section prp_prf_test.

  (* Alternative specification for the weak PRP/PRF Switching Lemma.

     We prove that (up to error) the PRP and PRF are indistinguishable in Q
     queries by calling each function Q times and proving that they both track
     the same finite map in the representation predicate [is_sprp] and
     [is_random_function].

   *)

  Context `{!parisGS Σ}.

  Variable val_size : nat.

  Definition is_sprp := is_sprp val_size.
  Definition random_permutation := random_permutation val_size.
  Definition is_random_function := is_random_function val_size.
  Definition random_function := random_function val_size.

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
      let: "f" := random_permutation #() in
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
      + wp_apply (wp_prf_prp_couple_eq_err _ _ _ _ _ _ _ m2
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
    tp_bind (random_permutation _).
    iMod (spec_random_permutation with "HK") as (g) "(HK & Hg)".
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


End prp_prf_test.
