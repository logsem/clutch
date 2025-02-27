From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import gset_bij auth excl frac agree numbers.
From coneris.coneris Require Import
  coneris par spawn spin_lock hash atomic lock
  con_hash_interface4 bloom_filter.
From coneris.coneris.lib Require Import list array.

Set Default Proof Using "Type*".

Section conc_bloom_filter.
  Variables filter_size max_key num_hash : nat.
  Context `{!conerisGS Σ, !spawnG Σ,
      c : con_hash4 Σ,
      !inG Σ (excl_authR boolO), !inG Σ (prodR fracR val0) }.

  Definition init_bloom_filter : val :=
    λ: "_" ,
      let: "hfuns" := list_seq_fun #0 #num_hash (λ: "_", init_con_hash #filter_size #max_key) in
      let: "arr" := array_init #(S filter_size) (λ: "x", #false)%E in
      let: "l" := ref ("hfuns", "arr") in
      "l".

  Definition insert_bloom_filter : val :=
    λ: "l" "v" ,
      let, ("hfuns", "arr") := !"l" in
      list_iter (λ: "h",
          let: "i" := "h" "v" in
          "arr" +ₗ "i" <- #true) "hfuns".

  Definition lookup_bloom_filter : val :=
    λ: "l" "v" ,
      let, ("hfuns", "arr") := !"l" in
      let: "res" := ref #true in
      list_iter (λ: "h",
          let: "i" := "h" "v" in
          if: !("arr" +ₗ "i") then #() else "res" <- #false) "hfuns" ;;
      !"res".

  Definition insert_bloom_filter_loop : val :=
    (rec: "aux" "bfl" "ks" :=
       match: "ks" with
         NONE => #()
       | SOME "p" =>
           let: "h" := Fst "p" in
           let: "t" := Snd "p" in
           (insert_bloom_filter "bfl" "h") ||| ("aux" "bfl" "t")
       end).

  Definition main_bloom_filter (ksv ktest : val) : expr :=
      let: "bfl" := init_bloom_filter #() in
      insert_bloom_filter_loop "bfl" ksv ;;
      lookup_bloom_filter "bfl" ktest.


  Definition insert_bloom_filter_loop_seq : val :=
    (rec: "aux" "bfl" "ks" :=
       match: "ks" with
         NONE => #()
       | SOME "p" =>
           let: "h" := Fst "p" in
           let: "t" := Snd "p" in
           (insert_bloom_filter "bfl" "h") ;; ("aux" "bfl" "t")
       end).

  Definition main_bloom_filter_seq (ksv ktest : val) : expr :=
      let: "bfl" := init_bloom_filter #() in
      insert_bloom_filter_loop_seq "bfl" ksv ;;
      lookup_bloom_filter "bfl" ktest.


  Definition con_hash_inv_list hfs hnames ks (s : gset nat) :=
    ([∗ list] i ↦f;γ ∈ hfs;hnames,
       conhashfun γ filter_size f ∗
       ([∗ list] k ∈ ks, ∃ n, ⌜ n ∈ s ⌝ ∗ hashkey γ k (Some n)))%I.

  Lemma con_hash_inv_list_cons f fs2 hnames ks s :
    con_hash_inv_list ((f :: fs2)) hnames ks s -∗
    (∃ γ hnames2,
        ⌜ hnames = γ :: hnames2 ⌝ ∗
        conhashfun γ filter_size f∗
        ([∗ list] k ∈ ks, ∃ n, ⌜ n ∈ s ⌝ ∗ hashkey γ k (Some n)) ∗
        con_hash_inv_list fs2 hnames2 ks s).
  Proof.
    iIntros "Hinv_list".
    rewrite /con_hash_inv_list.
    destruct hnames as [| γ hnames2]; auto.
    iDestruct "Hinv_list" as "(? & ?)".
    by iFrame.
  Qed.

  Definition bloom_filter_inv_aux bfl hfuns a
    hnames ks (s : gset nat) : iPropI Σ :=
        (∃ hfs,
            (bfl ↦ (hfuns, LitV (LitLoc a))%V ∗
            ⌜ is_list_HO hfs hfuns ⌝ ∗
            ⌜ length hfs = num_hash ⌝ ∗
            con_hash_inv_list hfs hnames ks s ∗
            ⌜ forall i, i ∈ s -> (i < S filter_size)%nat  ⌝ ∗
            (∃ (arr : list val),
                 (a ↦∗ arr) ∗
                 ⌜ length arr = S filter_size ⌝ ∗
                 ⌜ forall i, i < S filter_size -> arr !! i = Some #true \/ arr !! i = Some #false⌝ ∗
                 ⌜ forall i, i < S filter_size -> arr !! i = Some #true -> i ∈ s  ⌝)))%I.

  Definition bloom_filter_inv N bfl hfuns a hnames ks (s : gset nat) : iPropI Σ :=
    inv (N.@"bf") (bloom_filter_inv_aux bfl hfuns a hnames ks s).

  Lemma hash_preview_list rem (ks : list nat) f γs (bad : gset nat) :
     (forall x : nat, x ∈ bad -> (x < S filter_size)%nat) ->
     conhashfun γs filter_size f -∗
     ⌜ NoDup ks ⌝ -∗
     ([∗ list] k ∈ ks, hashkey γs k None) -∗
     ↯ (fp_error filter_size num_hash (rem + length ks) (size bad)) -∗
     state_update ⊤ ⊤ (∃ (res : gset nat),
          ⌜ forall x : nat, x ∈ (bad ∪ res) -> (x < S filter_size)%nat ⌝ ∗
          ↯ (fp_error filter_size num_hash rem (size (bad ∪ res))) ∗
          ([∗ list] k ∈ ks, ∃ n, ⌜ n ∈ (bad ∪ res) ⌝ ∗ hashkey γs k (Some n) )).
  Proof.
    iIntros (Hbound) "#Hhinv".
    iInduction ks as [|k ks] "IH" forall (bad Hbound).
    - iIntros "Hndup Hnone Herr".
      rewrite /= Nat.add_0_r.
      iModIntro.
      iExists bad.
      replace (bad ∪ bad) with bad by set_solver.
      iSplit; auto.
    - iIntros "%Hndup (Hknone & Hksnone) Herr".
      pose proof (NoDup_cons_1_1 k ks Hndup) as Hdup1.
      pose proof (NoDup_cons_1_2 k ks Hndup) as Hdup2.
      replace (rem + length (k :: ks)) with (S rem + (length ks));
        [|simpl; lia].
      assert (forall m b, 0 <= fp_error filter_size num_hash m b)%R as Hfp.
      {
        intros; apply fp_error_bounded.
      }
      iPoseProof (hashkey_presample k bad
                      (mknonnegreal (fp_error filter_size num_hash (S rem + length ks) (size bad))
                         (Hfp _ _))
                      (mknonnegreal (fp_error filter_size num_hash (rem + length ks) (size bad))
                         (Hfp _ _))
                      (mknonnegreal (fp_error filter_size num_hash (rem + length ks) (S (size bad)))
                         (Hfp _ _))
                      γs with "Hhinv [Hknone] [Herr]") as "Hcur"; auto; try done.
       + simpl.
         case_bool_decide.
         * rewrite fp_error_max /=; auto.
           rewrite fp_error_max /=; auto.
           rewrite !Rmult_1_l.
           lra.
         * right.
           rewrite (Rmult_comm (size bad / (filter_size + 1))).
           rewrite (Rmult_comm ((filter_size + 1 - size bad) / (filter_size + 1))).
           rewrite Rmult_plus_distr_r.
           rewrite !(Rmult_assoc _ _ (filter_size + 1)).
           rewrite !Rinv_l; [lra|].
           real_solver.
       + iMod ("Hcur") as "(%v & [(%Hnotbad & Herr)|(%Hbad & Herr)] & Hhauth)"; last first.
         ** simpl.
            iMod ("IH" $! bad with "[] [] [Hksnone] [Herr]") as "(%res&?&?&?)"; auto.
            iModIntro.
            iExists (bad ∪ res).
            replace (bad ∪ (bad ∪ res)) with (bad ∪ res) by set_solver.
            iFrame.
            iPureIntro.
            set_solver.
         ** simpl.
            iMod ("IH" $! (bad ∪ {[fin_to_nat v]}) with "[] [] [Hksnone] [Herr]") as "(%res&?&?&?)"; auto.
            *** iPureIntro.
                intros x Hx.
                apply elem_of_union in Hx as [Hx|Hx]; auto.
                apply elem_of_singleton in Hx as ->.
                apply fin_to_nat_lt.
            *** rewrite size_union; [|set_solver].
                rewrite size_singleton.
                replace (size bad + 1) with (S (size bad)) by lia.
                iFrame.
            *** iModIntro.
                iExists ((bad ∪ {[fin_to_nat v]}) ∪ res).
                replace (bad ∪ (bad ∪ {[fin_to_nat v]} ∪ res)) with ((bad ∪ {[fin_to_nat v]}) ∪ res) by set_solver.
                iFrame.
                iPureIntro.
                set_solver.
  Qed.

  Lemma bloom_filter_init_spec N (ks : list nat) :
    NoDup ks ->
    ([∗ list] k ∈ ks, ⌜ (k ≤ max_key)%nat ⌝) -∗
    {{{ ↯ (fp_error filter_size num_hash (num_hash * length ks) 0) }}}
      init_bloom_filter #()
   {{{ (bfl:loc), RET #bfl ;
         ∃ hfuns a hnames s,
           ↯ (fp_error filter_size num_hash 0 (size s)) ∗
             ([∗ list] γ ∈ hnames,
               ([∗ set] k ∈ (set_seq 0 (S max_key) ∖ list_to_set ks), hashkey γ k (None) )) ∗
             bloom_filter_inv N bfl hfuns a hnames ks s
   }}}.
   Proof.
    iIntros (Hndup) "%Hks".
    iIntros (Φ).
    iModIntro.
    iIntros "Herr HΦ".
    rewrite /init_bloom_filter.
    wp_pures.
    set (Ψ := (λ l, ⌜ num_hash < length l ⌝ ∨
                (∃ (s : gset nat),
                      ↯(fp_error filter_size num_hash ((num_hash - length l) * length ks) (size s)) ∗
                      ⌜ ∀ x : nat, x ∈ s → x < S filter_size ⌝ ∗
                      ([∗ list] f ∈ l,
                        (∃ γ,
                            conhashfun γ filter_size f ∗
                            ([∗ set] k ∈ (set_seq 0 (S max_key) ∖ list_to_set ks), hashkey γ k (None) ) ∗
                            ([∗ list] k ∈ ks, ∃ v, ⌜ v ∈ s ⌝ ∗ hashkey γ k (Some v))))))%I).
    wp_apply (wp_list_seq_fun_HO_invariant _ Ψ
                0 num_hash _ (λ _ _, True)%I with "[] [Herr] [HΦ]").
    - iIntros (i l Ξ).
      iModIntro.
      iIntros "HΨ HΞ".
      wp_pures.
      iApply pgl_wp_state_update.
      wp_apply conhash_init; auto.
      iIntros (γ f) "(#Hhinv&Hkeys)".
      iPoseProof (big_sepS_subseteq with "Hkeys") as "Hkeys".
      {
        erewrite (union_difference (list_to_set ks)); [reflexivity|].
        apply elem_of_subseteq.
        intros k Hk.
        apply elem_of_set_seq.
        split; [lia |].
        simpl.
        apply Nat.lt_succ_r.
        apply elem_of_list_to_set, elem_of_list_lookup in Hk as [? ?].
        by eapply Hks.
      }
      iPoseProof (big_sepS_union with "Hkeys") as "(Hks&Hrest)"; [set_solver|].
      iPoseProof (big_sepS_list_to_set with "Hks") as "Hks"; auto.
      iApply "HΞ".
      iSplitL; auto.
      rewrite /Ψ cons_length.
      assert (num_hash ≤ length l \/ num_hash > length l) as [Haux|?] by lia.
      {
        iModIntro.
        iDestruct "HΨ" as "[%|HΨ]"; [iLeft; iPureIntro; lia |].
        iLeft. iPureIntro. lia.
      }
      iDestruct "HΨ" as "[%|HΨ]"; [iModIntro; iLeft; iPureIntro; lia |].
      iDestruct "HΨ" as "(%s & Herr & %Hbound & Hl)".
      replace ((num_hash - length l) * length ks) with ((num_hash - S (length l)) * length ks + length ks);
        last first.
      {
        rewrite -{2}(Nat.mul_1_l (length ks)).
        rewrite -Nat.mul_add_distr_r.
        f_equal.
        lia.
      }
      iMod (hash_preview_list _ ks _ _ s with "[$][//] Hks Herr") as "Hupd"; auto.
      iModIntro.
      iRight.
      iDestruct "Hupd" as "(%res & ? & Herr & ?)".
      iExists (s ∪ res).
      iSplitL "Herr"; auto.
      iSplit; auto.
      iApply big_sepL_cons.
      iFrame.
      iSplit; auto.
      iApply (big_sepL_mono with "Hl").
      iIntros (k v Hkv) "(%γ'&?&?&?)".
      iExists γ'.
      iFrame.
      iApply (big_sepL_mono with "[$]").
      iIntros (???) "(%&%&?)".
      iExists _; iFrame.
      iPureIntro. set_solver.
   - rewrite /Ψ.
     iRight.
     iExists ∅.
     rewrite size_empty nil_length Nat.sub_0_r.
     iFrame.
     iSplit; [iPureIntro; set_solver |].
     done.
   - iModIntro.
     iIntros (hfuns fαs) "(%Hhfuns & %Hlen & HΨ & _)".
      wp_pures.
      wp_apply (wp_array_init (λ _ v, ⌜ v = #false ⌝%I)).
      + real_solver.
      + iApply big_sepL_intro.
        iModIntro.
        iIntros (??) "?".
        wp_pures.
        done.
      + iIntros (a arr) "(%HlenA & Ha & %Harr)".
        wp_pures.
        wp_alloc l as "Hl".
        wp_pures.
        rewrite /Ψ.
        iDestruct "HΨ" as "[%|(%s & Herr & %Hbound & Hfs)]";
          [lia |].
        iPoseProof (array.big_sepL_exists with "Hfs") as "(%hnames & Hfs)"; eauto.
        iApply "HΦ".
        rewrite Hlen Nat.sub_diag Nat.mul_0_l.
        iExists hfuns, a, hnames, s.
        iAssert (([∗ list] v;x ∈ fαs;hnames, conhashfun x filter_size v ∗
                ([∗ list] k ∈ ks, ∃ v0 : nat, ⌜v0 ∈ s⌝ ∗ hashkey x k (Some v0))) ∗
                [∗ list] γ ∈ hnames, ([∗ set] k ∈ (set_seq 0 (S max_key) ∖ list_to_set ks),
                  hashkey γ k None))%I with "[Hfs]" as "(?&?)".
        { iApply (big_sepL2_sep_sepL_r _ _ fαs hnames).
          iApply (big_sepL2_mono with "[$]").
          iIntros (?????) "(?&?&?)".
          iFrame. }
        iFrame.
        iMod (inv_alloc _ _ (bloom_filter_inv_aux l hfuns a hnames ks s) with "[-]") as "#Hinv";
          [| iApply "Hinv"].
        rewrite /bloom_filter_inv_aux.
        iModIntro.
        iExists fαs.
        iFrame.
        iPureIntro.
        repeat split; auto.
        ** lia.
        ** intros i Hi.
           right.
           pose proof (lookup_lt_is_Some_2 arr i) as [b Hb]; [lia |].
           rewrite Hb.
           apply Harr in Hb; auto.
           by simplify_eq.
        ** intros i Hi1 Hi2.
           specialize (Harr i #true Hi2).
           simplify_eq.
 Qed.

  Lemma bloom_filter_insert_thread_spec N bfl hfuns a hnames (k : nat) (ks : list nat) s :
    (k ∈ ks) ->
    ([∗ list] k ∈ ks, ⌜ (k ≤ max_key)%nat ⌝) -∗
    {{{ bloom_filter_inv N bfl hfuns a hnames ks s }}}
      insert_bloom_filter #bfl #k
    {{{ RET #(); True  }}}.
  Proof.
    iIntros (Hk Hleq Φ) "!# #Hinv HΦ".
    rewrite /insert_bloom_filter.
    wp_pures.
    wp_bind (! _)%E.
    iInv "Hinv" as "(%hfs&>Hbfl&>%Hhfs&>%Hlen&#Hhinv&>%Hbound&?)" "Hclose".
    wp_load.
    iMod ("Hclose" with "[-HΦ]").
    {
      iModIntro.
      iExists hfs.
      iFrame.
      repeat iSplit; auto.
    }
    iModIntro.
    wp_pures.
    wp_apply (wp_list_iter_invariant_HO
                (λ fs1 fs2,
                   ∃ hnames2,
                    con_hash_inv_list fs2 hnames2 ks s)%I with "[][][HΦ]"); auto.
    - iIntros (fs1 f fs2 Ψ) "!# (%hnames2 & Hiter) HΨ".
      wp_pures.
      rewrite /con_hash_inv_list.
      iPoseProof (con_hash_inv_list_cons with "Hiter")
        as "(%γ&%hnames3&->&#Hinvf&Hfrags&Htail)".
      wp_bind (f _).
      iPoseProof (big_sepL_elem_of _ _ k with "Hfrags") as "(%v&%Hv&#Hfrag)"; auto.
      wp_apply (wp_conhashfun_prev with "[$Hfrag //]").
      iIntros "_".
      wp_pures.
      iInv "Hinv" as "(%&?&?&?&?&?&%arr&Harr&>%HlenA&>%Htf&>%Htrue)" "Hclose".
      wp_apply (wp_store_offset with "[$Harr]").
      {
        apply lookup_lt_is_Some_2.
        rewrite HlenA //.
        by apply Hbound.
      }
      iIntros "Harr".
      iMod ("Hclose" with "[-HΨ Htail]").
      {
        iModIntro.
        iFrame.
        iPureIntro.
        repeat split.
        - rewrite insert_length //.
        - intros i Hi.
          destruct (decide (i = v)) as [-> | Hneq]; auto.
          + rewrite list_lookup_insert; [auto|lia].
          + rewrite list_lookup_insert_ne; auto.
        - intros i Hi Hlookup.
          destruct (decide (i = v)) as [-> | Hneq]; auto.
          apply Htrue; auto.
          by rewrite list_lookup_insert_ne in Hlookup.
      }
      iApply "HΨ".
      iModIntro.
      rewrite /con_hash_inv_list.
      iExists hnames3.
      iFrame.
   - iModIntro.
     iIntros "?".
     by iApply "HΦ".
 Qed.

 Lemma bloom_filter_lookup_spec N bfl hfuns a hnames (k : nat) (ks : list nat) s :
    (k ∉ ks) ->
    (k ≤ max_key)%nat ->
    ([∗ list] k ∈ ks, ⌜ (k ≤ max_key)%nat ⌝) -∗
    {{{ ↯ (fp_error filter_size num_hash 0 (size s)) ∗
         ([∗ list] γ ∈ hnames, hashkey γ k None) ∗
        bloom_filter_inv N bfl hfuns a hnames ks s }}}
           lookup_bloom_filter #bfl #k
      {{{ v, RET v; ⌜ v = #false ⌝ }}}.
 Proof.
   iIntros (Hk Hkleq Hksleq Φ) "!# (Herr & Hfrags & #Hinv) HΦ".
   rewrite /lookup_bloom_filter.
   wp_pures.
   wp_bind (!_)%E.
   iInv "Hinv" as "(%hfs&>Hbfl&>%Hhfs&>%Hlen&#Hhinv&>%Hbound&?)" "Hclose".
   wp_load.
   iMod ("Hclose" with "[-HΦ Herr Hfrags]").
   {
     iModIntro.
     iExists hfs.
     iFrame.
     repeat iSplit; auto.
   }
   iModIntro.
   wp_pures.
   wp_alloc res as "Hres".
   wp_pures.
   wp_apply (wp_list_iter_invariant_HO
               (λ fs1 fs2,
                 (∃ hnames2,
                     ([∗ list] γ ∈ hnames2, hashkey γ k None) ∗
                     con_hash_inv_list fs2 hnames2 ks s) ∗
                 (res ↦ #false ∨
                 (res ↦ #true ∗
                          ↯ ((size s / (filter_size + 1)) ^ (length fs2))%R)))%I
              with "[][Hfrags Herr Hres][HΦ]").
   - iIntros (fs1 f fs2 Ψ) "!# ((%γ2 & Hfrags & Hiter) & [Hr | (Hr & Herr)]) HΨ".
     + wp_pures.
       wp_bind (f _).
       iPoseProof (con_hash_inv_list_cons with "Hiter")
         as "(%γ&%hnames3&->&#Hinvf&HSome&Htail)".
       iPoseProof (big_sepL_cons with "Hfrags") as "(?&Hfrags)".
       wp_apply (wp_hash_lookup_safe with "[$]").
       iIntros (v) "(%&#?)".
       wp_pures.
       wp_bind (!_)%E.
       iInv "Hinv" as "(%&?&?&?&?&?&%arr&Harr&>%HlenA&>%Htf&>%Htrue)" "Hclose".
       pose proof (lookup_lt_is_Some_2 arr v) as [x Hx]; [lia|].
       wp_apply (wp_load_offset with "Harr"); eauto.
       iIntros "Harr".
       iMod ("Hclose" with "[- Hr HΨ Hfrags Htail]").
       {
         iModIntro.
         iExists hfs.
         iFrame.
         repeat iSplit; auto.
       }
       iModIntro.
       pose proof (Htf v) as [?|?]; [lia | |]; simplify_eq.
       * wp_pures.
         iModIntro.
         iApply "HΨ".
         iFrame.
       * wp_pures.
         wp_store.
         iModIntro.
         iApply "HΨ".
         iFrame.

     + wp_pures.
       wp_bind (f _).
       iPoseProof (con_hash_inv_list_cons with "Hiter")
         as "(%γ&%hnames3&->&#Hinvf&HSome&Htail)".

       iPoseProof (big_sepL_cons with "Hfrags") as "(Hknone&Hfrags)".
       assert
         (forall z, (0 <= (size s / (filter_size + 1))^z)%R) as Haux.
       {
         intro z.
         apply pow_le.
         apply Rcomplements.Rdiv_le_0_compat; real_solver.
       }
       wp_apply (wp_hash_lookup_avoid_set _ _ _ s
                     (mknonnegreal _ (Haux (length (f :: fs2) )))
                     (mknonnegreal _ (Haux (length fs2 )))
                     0%NNR with "[$Herr $Hknone]"); auto.
       {
         simpl. rewrite Rmult_0_l Rplus_0_r.
         rewrite -(Rmult_comm (filter_size + 1))
            -Rmult_assoc
            Rmult_div_assoc
            Rmult_div_r; [lra |].
         real_solver.
       }
       simpl.
       iIntros (v) "(%Hv & [(%Hin & Herr) | (%Hout & Herr)] & Hksome)".
       * wp_pures.
         wp_bind (!_)%E.
         iInv "Hinv" as "(%&?&?&?&?&?&%arr&Harr&>%HlenA&>%Htf&>%Htrue)" "Hclose".
         pose proof (lookup_lt_is_Some_2 arr v) as [x Hx]; [lia|].
         wp_apply (wp_load_offset with "Harr"); eauto.
         iIntros "Harr".
         iMod ("Hclose" with "[- Hr HΨ Hfrags Htail Herr]").
         {
           iModIntro.
           iExists hfs.
           iFrame.
           repeat iSplit; auto.
         }
         iModIntro.
         pose proof (Htf v) as [?|?]; [lia | |]; simplify_eq.
         ** wp_pures.
            iModIntro.
            iApply "HΨ".
            iFrame.
            iRight; iFrame.
         ** wp_pures.
            wp_store.
            iModIntro.
            iApply "HΨ".
            iFrame.
       * wp_pures.
         wp_bind (!_)%E.
         iInv "Hinv" as "(%&?&?&?&?&?&%arr&Harr&>%HlenA&>%Htf&>%Htrue)" "Hclose".
         assert (arr !! v = Some #false) as Hlookup.
         {
           pose proof (Htf v) as [H1 | H2]; [lia| |auto].
           exfalso.
           apply Hout, Htrue; auto.
           lia.
         }
         wp_apply (wp_load_offset with "Harr"); eauto.
         iIntros "Harr".
         iMod ("Hclose" with "[- Hr HΨ Hfrags Htail]").
         {
           iModIntro.
           iExists hfs.
           iFrame.
           repeat iSplit; auto.
         }
         iModIntro.
         wp_pures.
         wp_store.
         iModIntro.
         iApply "HΨ".
         iFrame.

  - iSplit; auto.
    iSplitR "Hres Herr".
    + iExists hnames.
      auto.
    + iRight.
      iFrame.
      rewrite /fp_error Hlen.
      case_bool_decide; [|iFrame].
      iPoseProof (ec_contradict with "Herr") as "?"; auto.
      simpl; lra.
  - iModIntro.
    iIntros "((%hnames2 & ? & ?)&[Hres | (Hres & Herr)])".
    * wp_pures.
      wp_load.
      by iApply "HΦ".
    * simpl.
      iPoseProof (ec_contradict with "Herr") as "?"; auto; lra.
 Qed.


  Lemma insert_bloom_filter_loop_spec N bfl hfuns a hnames s
          (ns ks : list nat) (ksv : val) :
    is_list ks ksv ->
    {{{ bloom_filter_inv N bfl hfuns a hnames ns s ∗
        ([∗ list] k ∈ ks, ⌜k ∈ ns ⌝) ∗
        ([∗ list] k ∈ ns, ⌜ (k ≤ max_key)%nat ⌝)
    }}}
      insert_bloom_filter_loop #bfl ksv
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Hksv Φ) "(#Hinv & %Hks & %Hns) HΦ".
    rewrite /insert_bloom_filter_loop.
    iInduction ks as [|k ks'] "IH" forall (ksv Hksv Φ).
    - simpl in Hksv.
      simplify_eq.
      wp_pures.
      by iApply "HΦ".
    - destruct Hksv as [kv [-> Htail]].
      wp_pures.
      simpl.
      wp_apply (wp_par (λ _, True)%I (λ _, True)%I).
      + wp_apply (bloom_filter_insert_thread_spec _ _ _ _ _ _ ns); auto.
        apply (Hks 0); auto.
      + iSpecialize ("IH" with "[]").
        {
          iPureIntro.
          intros i ? ?.
          apply (Hks (S i)).
          auto.
        }
        iApply "IH"; auto.
      + iIntros (? ?) "? !>".
        by iApply "HΦ".
  Qed.


  Lemma insert_bloom_filter_loop_seq_spec N bfl hfuns a hnames s
          (ns ks : list nat) (ksv : val) :
    is_list ks ksv ->
    {{{ bloom_filter_inv N bfl hfuns a hnames ns s ∗
        ([∗ list] k ∈ ks, ⌜k ∈ ns ⌝) ∗
        ([∗ list] k ∈ ns, ⌜ (k ≤ max_key)%nat ⌝)
    }}}
      insert_bloom_filter_loop_seq #bfl ksv
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Hksv Φ) "(#Hinv & %Hks & %Hns) HΦ".
    rewrite /insert_bloom_filter_loop_seq.
    iInduction ks as [|k ks'] "IH" forall (ksv Hksv Φ).
    - simpl in Hksv.
      simplify_eq.
      wp_pures.
      by iApply "HΦ".
    - destruct Hksv as [kv [-> Htail]].
      wp_pures.
      simpl.
      wp_bind (insert_bloom_filter _ _).
      wp_apply (bloom_filter_insert_thread_spec _ _ _ _ _ _ ns); auto.
      { apply (Hks 0); auto. }
      iIntros "_".
      do 2 wp_pure.
      iSpecialize ("IH" with "[]").
      {
        iPureIntro.
        intros i ? ?.
        apply (Hks (S i)).
        auto.
      }
      iApply "IH"; auto.
  Qed.

 Lemma main_bloom_filter_seq_spec (N : namespace) (ks : list nat) (ksv : val) (ktest : nat) :
      NoDup ks ->
      is_list ks ksv ->
      ktest ∉ ks ->
      (ktest ≤ max_key)%nat ->
      {{{ ([∗ list] k ∈ ks, ⌜ (k ≤ max_key)%nat ⌝) ∗
           ↯ (fp_error filter_size num_hash (num_hash * length ks) 0) }}}
        main_bloom_filter_seq ksv #ktest
      {{{ v, RET v; ⌜ v = #false ⌝ }}}.
 Proof.
   iIntros (Hndup Hksv Hktest Htestvalid Φ) "(#Hks & Herr) HΦ".
   rewrite /main_bloom_filter_seq.
   wp_apply (bloom_filter_init_spec N ks with "[//] Herr"); auto.
   iIntros (bfl) "(%hfuns & %a & %hnames & %s & Herr & Hauths & #Hinv)".
   wp_pures.
   wp_apply (insert_bloom_filter_loop_seq_spec N _ _ _ _ _ ks ks); auto.
   {
     repeat iSplit; auto.
     iPureIntro.
     intros ? ? ?.
     simpl.
     eapply elem_of_list_lookup_2; eauto.
   }
   iIntros (?) "_".
   wp_pures.
   wp_apply (bloom_filter_lookup_spec N _ _ _ hnames _ ks s with "[][Herr Hauths]"); auto.
   iFrame.
   iSplit; auto.
   iApply (big_sepL_mono with "Hauths").
   iIntros (k γ Hk) "Hnones".
   iApply (big_sepS_elem_of with "Hnones").
   apply elem_of_difference; split.
   - apply elem_of_set_seq; split; lia.
   - by apply not_elem_of_list_to_set.
 Qed.

End conc_bloom_filter.
