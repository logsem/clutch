From iris.base_logic.lib Require Import invariants.
From clutch.coneris Require Import coneris par spawn spin_lock hash atomic lock concurrent_hash.
From clutch.coneris.lib Require Import list array.

Set Default Proof Using "Type*".

Section bloom_filter.

  Variable filter_size : nat.
  Variable num_hash : nat.
  Variable insert_num : nat.
  Variable max_hash_size : nat.
  Hypothesis max_hash_size_pos: (0<max_hash_size)%nat.

  Context `{!conerisGS Σ}.

  Fixpoint fp_error (m l b : nat) : R :=
      (match m with
      | 0 => let fix fp_error_Z (l b : nat) : R :=
              match l with
              | 0 => pow (b/(filter_size + 1)) num_hash
              | S l' => (b / (filter_size + 1)) * fp_error_Z l' b + ((filter_size + 1 - b) / (filter_size + 1)) * fp_error_Z l' (S b)
              end
              in fp_error_Z l b
      | S m' => let fix fp_error_m (l b : nat) : R :=
                 match l with
                 | 0 => fp_error m' num_hash b
                 | S l' => (b / (filter_size + 1)) * fp_error_m l' b + ((filter_size + 1 - b) / (filter_size + 1)) * fp_error_m l' (S b)
                 end
               in fp_error_m l b
       end)%R.


  Lemma fp_error_Z_Z (m b : nat) : fp_error 0 0 b = pow (b/(filter_size + 1)) num_hash.
  Proof.
    done.
  Qed.

  Lemma fp_error_S_Z (m b : nat) : fp_error (S m) 0 b = fp_error m num_hash b.
  Proof.
    done.
  Qed.

  Lemma fp_error_m_S (m l b : nat) :
    fp_error m (S l) b = ((b / (filter_size + 1)) * fp_error m l b + ((filter_size + 1 - b) / (filter_size + 1)) * fp_error m l (S b))%R.
  Proof.
    destruct m; done.
  Qed.

  Lemma fp_error_nonneg (m l b : nat) :
    (0 <= fp_error m l b)%R.
  Admitted.



  Definition init_bloom_filter : expr :=
    λ: "_" ,
      let: "h1" := init_hash filter_size #() in
      let: "h2" := init_hash filter_size #() in
      let: "arr" := array_init #(S filter_size) (λ: "x", #false)%E in
      let: "l" := ref ("h1", "h2", "arr") in
      "l".

  Definition insert_bloom_filter : expr :=
    λ: "l" "v" ,
      let, ("h1", "h2", "arr") := !"l" in
      let: "i1" := "h1" "v" in
      let: "i2" := "h2" "v" in
      "arr" +ₗ "i1" <- #true ;;
      "arr" +ₗ "i2" <- #true ;;
      #().



  Definition is_bloom_filter (l : loc) (els : gset nat) (bs : nat) : iProp Σ :=
    ∃ h1 h2 m1 m2 a arr (idxs : gset nat),
      l ↦ (h1, h2, LitV (LitLoc a))%V ∗
        hashfun filter_size h1 m1 ∗ hashfun filter_size h2 m2 ∗
        ⌜ length arr = S filter_size ⌝ ∗
        (a ↦∗ arr) ∗
        ⌜ els = dom m1 ⌝ ∗ ⌜ els = dom m2 ⌝ ∗
        ⌜ forall e, e ∈ els -> (m1 !!! e) ∈ idxs  ⌝ ∗
        ⌜ forall e, e ∈ els -> (m2 !!! e) ∈ idxs  ⌝ ∗
        ⌜ forall i, i ∈ idxs -> arr !! i = Some #true  ⌝ ∗
        ⌜ forall i, i ∈ idxs -> (i < S filter_size)%nat  ⌝ ∗
        ⌜ forall i, i < S filter_size -> i ∉ idxs -> arr !! i = Some #false  ⌝ ∗
        ⌜ bs = size idxs ⌝.



  Lemma bloom_filter_init_spec :
    {{{ True }}}
      init_bloom_filter #()
      {{{ (l:loc), RET #l ; is_bloom_filter l ∅ 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /init_bloom_filter.
    wp_pures.
    wp_apply (wp_init_hash); auto.
    iIntros (h1) "(%γ1 & Hh1)".
    wp_pures.
    wp_apply (wp_init_hash); auto.
    iIntros (h2) "(%γ2 & Hh2)".
    wp_pures.
    wp_apply (wp_array_init (λ _ v, ⌜ v = #false ⌝%I)).
    - admit.
    - iApply big_sepL_intro.
      iModIntro.
      iIntros (??) "?".
      wp_pures.
      done.
    - iIntros (a arr) "(%Hlen & Ha & %Harr)".
      wp_pures.
      wp_alloc l as "Hl".
      wp_pures.
      iMod "Hh1" as "(Hh1h & Hh1a)".
      iMod "Hh2" as "(Hh2h & Hh2a)".
      iModIntro.
      iApply "HΦ".
      rewrite /is_bloom_filter.
      iExists h1, h2, ∅, ∅, a, arr, ∅.
      iFrame.
      iSplit.
      {
        iPureIntro.
        set_solver.
      }
      iSplit.
      {
        iPureIntro.
        set_solver.
      }
      iPureIntro.
      split; [set_solver |].
      split; [set_solver |].
      split; [set_solver |].
      split; [set_solver |].
      split; [set_solver |].
      split; [|set_solver].
      intros i ??.
      apply Nat2Z.inj' in Hlen.
      rewrite <- Hlen in H.
      pose proof (lookup_lt_is_Some_2 arr i H) as [x Hx].
      specialize (Harr i x Hx).
      rewrite Hx Harr //.
  Admitted.


  Lemma bloom_filter_insert_spec (l : loc) (s : gset nat) (bs x m c : nat) :
    {{{ is_bloom_filter l s bs ∗ ⌜ x ∉ s ⌝ ∗
         ↯ (fp_error m (S (S c)) bs)
    }}}
      insert_bloom_filter #l #x
      {{{ RET #() ;
          ∃ (i: nat),
            is_bloom_filter l (s ∪ {[x]}) (bs + i) ∗
              ↯ (fp_error m c (bs + i))
      }}}.
  Proof.
    iIntros (Φ) "(Hbf & %Hx & Herr) HΦ".
    rewrite /insert_bloom_filter /is_bloom_filter.
    wp_pures.
    iDestruct "Hbf" as (h1 h2 m1 m2 a arr idxs) "(Hl & Hh1 & Hh2 & %HlenA & Ha & %Hm1 & %Hm2 & %Hidxs1 & %Hidxs2 & %Htrue & %Hbd & %Hfalse & %Hbs)".
    wp_load.
    wp_pures.
    wp_bind (h1 _).
    wp_apply (wp_insert_avoid_set_adv filter_size _ _ m1 _ idxs
                (mknonnegreal (fp_error m (S (S c)) bs) (fp_error_nonneg m (S (S c)) bs))
                (mknonnegreal (fp_error m (S c) bs) (fp_error_nonneg m (S c) bs))
                (mknonnegreal (fp_error m (S c) (S bs)) (fp_error_nonneg m (S c) (S bs)))
               with
             "[$]").
    - apply not_elem_of_dom_1.
      set_solver.
    - auto.
    - simpl.
      rewrite fp_error_m_S -Hbs /=.
      lra.
    - iIntros (v1) "(%Hv1 & Hh1 & [(%HOut1 & Herr)|(%HIn1 & Herr )])".
      + simpl.
        wp_pures.
        wp_bind (h2 _).
        wp_apply (wp_insert_avoid_set_adv filter_size _ _ m2 _ (idxs ∪ {[v1]})
                    (mknonnegreal (fp_error m (S c) (S bs)) (fp_error_nonneg m (S c) (S bs)))
                    (mknonnegreal (fp_error m c (S bs)) (fp_error_nonneg m c (S bs)))
                    (mknonnegreal (fp_error m c (S (S bs))) (fp_error_nonneg m c (S (S bs))))
                   with
                   "[$]").
        * apply not_elem_of_dom_1; set_solver.
        * intros i Hi.
          apply elem_of_union in Hi as [?|Hs]; auto.
          apply elem_of_singleton in Hs as ->.
          auto.
        * simpl.
          rewrite size_union; [|set_solver].
          rewrite size_singleton.
          rewrite fp_error_m_S -Hbs.
          rewrite !S_INR.
          rewrite plus_INR /=.
          lra.
        * iIntros (v2) "(%Hv2 & Hh2 & [(%HOut2 & Herr)|(%HIn2 & Herr )])".
          ** wp_pures.
             wp_apply (wp_store_offset with "[$Ha]").
             {
               apply lookup_lt_is_Some_2.
               rewrite HlenA //.
             }
             iIntros "Ha".
             wp_pures.
             wp_apply (wp_store_offset with "[$Ha]").
             {
               apply lookup_lt_is_Some_2.
               rewrite insert_length HlenA //.
             }
             iIntros "Ha".
             wp_pures.
             simpl.
             iModIntro.
             iApply "HΦ".
             iExists 2.
             iSplitR "Herr"; last first.
             {
               rewrite !Nat.add_succ_r Nat.add_0_r.
               iFrame.
             }
             iExists h1, h2, (<[x:=v1]> m1), (<[x:=v2]> m2).
             iFrame.
             iExists ((idxs ∪ {[v1]}) ∪ {[v2]}).
             iPureIntro.
             repeat split.
             *** rewrite !insert_length //.
             *** set_solver.
             *** set_solver.
             *** intros e He.
                 apply elem_of_union in He as [? | ?].
                 **** apply Hidxs1 in H.
                      admit.
                 **** admit.
             *** admit.
             *** admit.
             *** admit.
             *** admit.
             *** rewrite size_union; [|set_solver].
                 rewrite size_union; [|set_solver].
                 rewrite !size_singleton. real_solver.
 Admitted.

End bloom_filter.
