From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import gset_bij auth excl frac agree numbers.
From clutch.coneris Require Import coneris par spawn spin_lock hash atomic lock concurrent_hash con_hash_interface4 bloom_filter.
From clutch.coneris.lib Require Import list array.

Set Default Proof Using "Type*".



Section conc_bloom_filter.



  Variables filter_size max_key num_hash num_threads : nat.
  Context `{!conerisGS Σ, !spawnG Σ, c:con_hash4 Σ filter_size, !inG Σ (excl_authR boolO), !inG Σ (prodR fracR val0) }.


  Definition init_bloom_filter : expr :=
    λ: "_" ,
      let: "hfuns" := list_seq_fun #0 #num_hash (λ: "_", init_hash4 #()) in
      let: "arr" := array_init #(S filter_size) (λ: "x", #false)%E in
      let: "l" := ref ("hfuns", "arr") in
      "l".

  Definition insert_bloom_filter : expr :=
    λ: "l" "v" ,
      let, ("hfuns", "arr") := !"l" in
      list_iter (λ: "h",
          let: "i" := "h" "v" in
          "arr" +ₗ "i" <- #true) "hfuns".


  Definition lookup_bloom_filter : expr :=
    λ: "l" "v" ,
      let, ("hfuns", "arr") := !"l" in
      let: "res" := ref #true in
      list_iter (λ: "h",
          let: "i" := "h" "v" in
          if: !("arr" +ₗ "i") then #() else "res" <- #false) "hfuns" ;;
      !"res".

(*
  (*
     The invariant of the case study keeps track of three sets, s1, s2, and s3, whose union s is always constant.
       - s1 represents the set of elements that are in the tape of some hash
       - s2 represents the set of indices that have been read from the hash, but are still waiting to be written to
       the array
       - s3 represents the set of indices of the array that have been set to 1

     After the initialization, s1 will contain all elements in the hash sets, while s2 and s3 are empty. The deterministic
     part of the program will just advance the physical state of the bloom filter so that at the end s1 and s2 are empty.

     Additionally, the invariant ensures that every thread reading from a hash will find a non-empty tape (and therefore there
     is no more sampling happening).
   *)
  Definition bloom_filter_inv (s : gset nat) (a : loc) (arr lbls : list val) (snames : list hash_set_gname) (tnames : list hash_tape_gname): iProp Σ :=
    ∃ (s1 s2 s3 : gset nat),
      ⌜ s1 ∪ s2 ∪ s3 = s ⌝ ∗
      (* Every element in s1 is in the tape of some hash *)
      ([∗ list] x ∈ (zip lbls (zip snames tnames)),
           ∃ (sx : list nat), hash_tape1 (fst x) sx (fst (snd x)) (snd (snd x)) ∗ ⌜ subseteq (list_to_set sx) s1 ⌝) ∗
      (* Every element in s2 is waiting to be written *)
      (* Every element in s3 is an index set to 1 in the array *)
      (a ↦∗ arr) ∗
      ⌜ forall i, arr !! i = Some #true -> i ∈ s3  ⌝ ∗
      ⌜ forall i, i ∈ s3 -> (i < S filter_size)%nat  ⌝ ∗
      ([∗ set] x ∈ s3, ∃ γ, (hash_set_frag1 x γ)).
 *)


  Definition con_hash_inv_list N hfs hnames ks (s : gset nat) :=
    ([∗ list] i ↦f;γ ∈ hfs;hnames,
       ∃ lk hm,
         con_hash_inv4 N f lk hm (λ _, True) γ.1 γ.2 ∗
         ([∗ list] k ∈ ks, ∃ v, ⌜ v ∈ s ⌝ ∗ hash_frag4 k v γ.1))%I.


  Lemma con_hash_inv_list_cons N f fs2 hnames ks s :
    con_hash_inv_list N ((f :: fs2)) hnames ks s -∗
    (∃ lk hm γ hnames2,
        ⌜ hnames = γ :: hnames2 ⌝ ∗
        con_hash_inv4 N f lk hm (λ _, True) γ.1 γ.2 ∗
        ([∗ list] k ∈ ks, ∃ v, ⌜ v ∈ s ⌝ ∗ hash_frag4 k v γ.1) ∗
        con_hash_inv_list N fs2 hnames2 ks s
    ).
  Admitted.

  Definition bloom_filter_inv_aux N bfl hfuns a
    (hnames : list (hash_view_gname * hash_lock_gname)) ks (s : gset nat) : iPropI Σ :=
        (∃ hfs,
            (bfl ↦ (hfuns, LitV (LitLoc a))%V ∗
            ⌜ is_list_HO hfs hfuns ⌝ ∗
            ⌜ length hfs = num_hash ⌝ ∗
            con_hash_inv_list N hfs hnames ks s ∗
            ⌜ forall i, i ∈ s -> (i < S filter_size)%nat  ⌝ ∗
            (∃ (arr : list val),
                 (a ↦∗ arr) ∗
                 ⌜ length arr = S filter_size ⌝ ∗
                 ⌜ forall i, i < S filter_size -> arr !! i = Some #true -> i ∈ s  ⌝)))%I.

  Definition bloom_filter_inv N bfl hfuns a
    (hnames : list (hash_view_gname * hash_lock_gname)) ks (s : gset nat) : iPropI Σ :=
      (inv (N.@"bf") (bloom_filter_inv_aux N bfl hfuns a hnames ks s)).

  Definition hash_auth_list (hnames : list (hash_view_gname * hash_lock_gname)) (ks : list nat) :=
    ([∗ list] γ ∈ hnames, ∃ m, hash_auth4 m γ.1 ∗ [∗ list] k ∈ ks, ⌜ k ∈ dom m ⌝)%I.

(*
  Definition con_hash_inv_list N hfs hnames :=
      ([∗ list] k↦hf;γ ∈ hfs;hnames,
        ∃ f α lk hm ns,
          ⌜ hf = (f, α)%V ⌝ ∗
          hash_tape1 α ns γ.2.1 γ.2.2.1 ∗
        con_hash_inv1 N f lk hm (λ _, True) γ.1 γ.2.1 γ.2.2.1 γ.2.2.2)%I.



*)


  Lemma hash_preview_list N rem (ks : list nat) f l hm R {HR: ∀ m, Timeless (R m )} m γ_hv γ_lock (bad : gset nat) E:
     ↑(N) ⊆ E ->
     (forall x : nat, x ∈ bad -> (x < S filter_size)%nat) ->
     hash_auth4 m γ_hv -∗
     con_hash_inv4 N f l hm R γ_hv γ_lock -∗
     ⌜ NoDup ks ⌝ -∗
     ([∗ list] k ∈ ks,  ⌜ m !! k = None ⌝) -∗
     ↯ (fp_error filter_size num_hash (rem + length ks) (size bad)) -∗
     state_update E E (∃ (res : gset nat) (m' : gmap nat nat),
          ⌜ forall x : nat, x ∈ (bad ∪ res) -> (x < S filter_size)%nat ⌝ ∗
          ↯ (fp_error filter_size num_hash rem (size (bad ∪ res))) ∗
          hash_auth4 m' γ_hv ∗
          ⌜ m ⊆ m' ⌝ ∗
          ([∗ list] k ∈ ks, ⌜ k ∈ dom m' ⌝) ∗
          ([∗ list] k ∈ ks, ∃ v, ⌜ v ∈ (bad ∪ res) ⌝ ∗ hash_frag4 k v γ_hv )).
  Proof.
    iIntros (Hsubset Hbound) "Hhauth #Hhinv".
    iInduction ks as [|k ks] "IH" forall (m bad Hbound).
    - iIntros "Hndup Hnone Herr".
      rewrite /= Nat.add_0_r.
      iModIntro.
      iExists bad, m.
      replace (bad ∪ bad) with bad by set_solver.
      iSplit; auto.
      by iFrame.
    - iIntros "%Hndup ( Hknone & Hksnone) Herr".
      iDestruct "Hknone" as "%Hknone".
      pose proof (NoDup_cons_1_1 k ks Hndup) as Hdup1.
      pose proof (NoDup_cons_1_2 k ks Hndup) as Hdup2.
      replace (rem + length (k :: ks)) with (S rem + (length ks));
        [|simpl; lia].
      assert (forall m b, 0 <= fp_error filter_size num_hash m b)%R as Hfp.
      {
        intros; apply fp_error_bounded.
      }
      iPoseProof (hash_preview4 N k _ _ _ _ _ _ _ bad
                      (mknonnegreal (fp_error filter_size num_hash (S rem + length ks) (size bad))
                         (Hfp _ _))
                      (mknonnegreal (fp_error filter_size num_hash (rem + length ks) (size bad))
                         (Hfp _ _))
                      (mknonnegreal (fp_error filter_size num_hash (rem + length ks) (S (size bad)))
                         (Hfp _ _))
                      E with "Hhauth Hhinv [//] [Herr]") as "Hcur"; auto; try done.
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
       + iMod ("Hcur") as "(%v & [(%Hnotbad & Herr)|(%Hbad & Herr)] & Hhauth)".
         ** simpl.
            iPoseProof (hash_auth_duplicate _ k v with "Hhauth") as "#Hkv";
              [rewrite lookup_insert // |].
            iMod ("IH" $! _ bad with "[] Hhauth [] [Hksnone] Herr") as "(%res&%m'&?&?&?&%Hmm'&?&?)"; auto.
            {
              iApply (big_sepL_mono with "Hksnone").
              iIntros (i k' Hsome) "%Hk'".
              iPureIntro.
              rewrite lookup_insert_ne; auto.
              apply elem_of_list_lookup_2 in Hsome.
              apply NoDup_cons_1_1 in Hndup.
              set_solver.
            }
            iModIntro.
            iExists (bad ∪ res), m'.
            replace (bad ∪ (bad ∪ res)) with (bad ∪ res) by set_solver.
            iFrame.
            iSplit.
            {
              iPureIntro.
              etrans; [ |apply Hmm'].
              by apply insert_subseteq.
            }
            iSplit.
            {
              iPureIntro.
              admit.
            }
            iExists v.
            iSplit; auto.
            iPureIntro.
            set_solver.
         ** simpl.
            iPoseProof (hash_auth_duplicate _ k v with "Hhauth") as "#Hkv";
              [rewrite lookup_insert // |].
            iMod ("IH" $! _ (bad ∪ {[fin_to_nat v]}) with "[] Hhauth [] [Hksnone] [Herr]") as "(%res&%m'&?&?&?&%Hmm'&?&?)"; auto.
            *** iPureIntro.
                intros x Hx.
                apply elem_of_union in Hx as [Hx|Hx]; auto.
                apply elem_of_singleton in Hx as ->.
                apply fin_to_nat_lt.
            *** iApply (big_sepL_mono with "Hksnone").
                iIntros (i k' Hsome) "%Hk'".
                iPureIntro.
                rewrite lookup_insert_ne; auto.
                apply elem_of_list_lookup_2 in Hsome.
                apply NoDup_cons_1_1 in Hndup.
                set_solver.
            *** rewrite size_union; [|set_solver].
                rewrite size_singleton.
                replace (size bad + 1) with (S (size bad)) by lia.
                iFrame.
            *** iModIntro.
                iExists ((bad ∪ {[fin_to_nat v]}) ∪ res), m'.
                replace (bad ∪ (bad ∪ {[fin_to_nat v]} ∪ res)) with ((bad ∪ {[fin_to_nat v]}) ∪ res) by set_solver.
                iFrame.
                iSplit.
                {
                  iPureIntro.
                  etrans; [ |apply Hmm'].
                  by apply insert_subseteq.
                }
                iSplit.
                {
                  iPureIntro.
                  admit.
                }
                iExists (fin_to_nat v).
                iSplit; auto.
                iPureIntro.
                set_solver.
  Admitted.


  Lemma bloom_filter_init_spec N (ks : list nat) :
    (length ks = num_threads) ->
    NoDup ks ->
    ([∗ list] k ∈ ks, ⌜ (k ≤ max_key)%nat ⌝) -∗
    {{{ ↯ (fp_error filter_size num_hash (num_hash * num_threads) 0) }}}
      init_bloom_filter #()
   {{{ (bfl:loc), RET #bfl ;
         ∃ hfuns a hnames s,
             hash_auth_list hnames ks ∗
             bloom_filter_inv N bfl hfuns a hnames ks s
   }}}.
   Proof.
    iIntros (Hthreads Hndup) "#Hks".
    iIntros (Φ).
    iModIntro.
    iIntros "Herr HΦ".
    rewrite /init_bloom_filter.
    wp_pures.
    set (Ψ := (λ l, ⌜ num_hash < length l ⌝ ∨
                (∃ (s : gset nat),
                      ↯(fp_error filter_size num_hash ((num_hash - length l) * num_threads) (size s)) ∗
                      ⌜ ∀ x : nat, x ∈ s → x < S filter_size ⌝ ∗
                      ([∗ list] f ∈ l,
                        (∃ γ,
                            (∃ m, hash_auth4 m γ.1 ∗ [∗ list] k ∈ ks, ⌜ k ∈ dom m ⌝) ∗
                            (∃ lk hm, con_hash_inv4 N f lk hm (λ _, True) γ.1 γ.2 ∗
                            ([∗ list] k ∈ ks, ∃ v, ⌜ v ∈ s ⌝ ∗ hash_frag4 k v γ.1))))))%I).
    wp_apply (wp_list_seq_fun_HO_invariant _ Ψ
                0 num_hash _ (λ _ _, True)%I with "[] [Herr] [HΦ]").
    - iIntros (i l Ξ).
      iModIntro.
      iIntros "HΨ HΞ".
      wp_pures.
      iApply pgl_wp_state_update.
      wp_apply (con_hash_init4 N (λ _, True)%I); auto.
      iIntros (f) "(%lk & %hm & %γ1 & %γ2 & #Hinv & Hhauth)".
      iApply "HΞ".
      iApply (state_update_mono _ _ (Ψ (f :: l))); auto.
      rewrite /Ψ cons_length.
      assert (num_hash ≤ length l \/ num_hash > length l) as [Haux|?] by lia.
      {
        iModIntro.
        iDestruct "HΨ" as "[%|HΨ]"; [iLeft; iPureIntro; lia |].
        iLeft. iPureIntro. lia.
      }
      iDestruct "HΨ" as "[%|HΨ]"; [iModIntro; iLeft; iPureIntro; lia |].
      iDestruct "HΨ" as "(%s & Herr & %Hbound & Hl)".
      rewrite -Hthreads.
      replace ((num_hash - length l) * length ks) with ((num_hash - S (length l)) * length ks + length ks);
        last first.
      {
        rewrite -{2}(Nat.mul_1_l (length ks)).
        rewrite -Nat.mul_add_distr_r.
        f_equal.
        lia.
      }
      iMod (hash_preview_list N _ ks _ _ _ _ _ _ _ s ⊤ with "Hhauth Hinv [][][Herr]") as "Hupd"; auto.
      iModIntro.
      iRight.
      iDestruct "Hupd" as "(%res & %m' & ? & Herr & ? & ? & ? & ?)".
      iExists (s ∪ res).
      iSplitL "Herr"; auto.
      iSplit; auto.
      iApply big_sepL_cons.
      iSplitR "Hl".
      * iExists (γ1, γ2).
        iFrame.
        iExists lk, hm.
        auto.
      * iApply (big_sepL_mono with "Hl").
        iIntros (k v Hkv) "(%γ & Hm & %lk' & %hm' & Hinv & Hlist)".
        iExists γ.
        iFrame.
        iApply (big_sepL_mono with "Hlist").
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
        (*
        iAssert ([∗ list] f ∈ fαs, ∃ (γ : hash_view_gname * hash_lock_gname) (lk hm : val),
                    con_hash_inv4 N f lk hm (λ _ : gmap nat nat, True) γ.1 γ.2 ∗
                    (∃ m : gmap nat nat, hash_auth4 m γ.1 ∗ ([∗ list] k ∈ ks, ⌜k ∈ dom m⌝)) ∗
                      ([∗ list] k ∈ ks, ∃ v : nat, ⌜v ∈ s⌝ ∗ hash_frag4 k v γ.1))%I with "[Hfs]" as "Hfs".
        {
          iApply (big_sepL_mono with "Hfs").
          iIntros (???) "(%&%&%&?)".
          iFrame.
        }
        *)
        iPoseProof (array.big_sepL_exists with "Hfs") as "(%hnames & Hfs)"; eauto.
        iApply "HΦ".
        iExists hfuns, a, hnames, s.
        rewrite /hash_auth_list/=.
        iAssert ( ([∗ list] γ ∈ hnames, (∃ m : gmap nat nat, hash_auth4 m γ.1 ∗ ([∗ list] k ∈ ks, ⌜k ∈ dom m⌝))) ∗
                    [∗ list] v;x ∈ fαs;hnames, ∃ lk hm : val, con_hash_inv4 N v lk hm (λ _ : gmap nat nat, True) x.1 x.2 ∗
                                                                ([∗ list] k ∈ ks, ∃ v0 : nat, ⌜v0 ∈ s⌝ ∗ hash_frag4 k v0 x.1))%I
          with "[Hfs]" as "(Hauths & Hfs)".
        {
          iPoseProof (big_sepL2_alt with "Hfs") as "(%Hlens & Hfs)".
          iPoseProof (big_sepL_sep with "Hfs") as "(Hauths & Hfrags)".
          iSplitL "Hauths".
          - iPoseProof (big_sepL_sep_zip
                          (λ _ _, True)%I
                          (λ _ x, ∃ m : gmap nat nat, hash_auth4 m x.1 ∗ ([∗ list] k ∈ ks, ⌜k ∈ dom m⌝))%I
                          fαs hnames) as "(H1 & H2)"; auto.
            iSpecialize ("H1" with "[Hauths]").
            + iApply (big_sepL_mono with "Hauths"); auto.
            + iDestruct "H1" as "(?&?)".
              iFrame.
          - iApply big_sepL2_alt.
            iSplit; auto.
        }
        iFrame.
        iMod (inv_alloc _ _ (bloom_filter_inv_aux N l hfuns a hnames ks s) with "[Herr Ha Hl Hfs]") as "#Hinv";
          [| iApply "Hinv"].
        rewrite /bloom_filter_inv_aux.
        iModIntro.
        iExists fαs.
        iFrame.
        iPureIntro.
        repeat split; auto.
        ** lia.
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
  Proof using c conerisGS0 conerisGS1 excl_authR filter_size inG0 inG1 max_key max_key0 num_hash num_threads spawnG0 val0 Σ.
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
                    con_hash_inv_list N fs2 hnames2 ks s)%I with "[][][HΦ]"); auto.
    - iIntros (fs1 f fs2 Ψ) "!# (%hnames2 & Hiter) HΨ".
      wp_pures.
      rewrite /con_hash_inv_list.
      iPoseProof (con_hash_inv_list_cons with "Hiter")
        as "(%lk&%hm&%γ&%hnames3&->&#Hinvf&Hfrags&Htail)".
      wp_bind (f _).
      iPoseProof (big_sepL_elem_of _ _ k with "Hfrags") as "(%v&%Hv&Hfrag)"; auto.
      wp_apply (con_hash_spec4 with "[$Hfrag //]").
      iIntros (?) "->".
      wp_pures.
      iInv "Hinv" as "(%&?&?&?&?&?&%arr&Harr&>%HlenA&>%Htrue)" "Hclose".
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
        split.
        - rewrite insert_length //.
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
          hash_auth_list hnames ks ∗
        bloom_filter_inv N bfl hfuns a hnames ks s }}}
           lookup_bloom_filter #bfl #k
      {{{ v, RET v; ⌜ v = #false ⌝ }}}.
 Proof.
   iIntros (Hk Hkleq Hksleq Φ) "!# (Herr & Hauths & #Hinv) HΦ".
   rewrite /lookup_bloom_filter.
   wp_pures.
   wp_bind (!_)%E.
   iInv "Hinv" as "(%hfs&>Hbfl&>%Hhfs&>%Hlenhfs&#Hhinv&?)" "Hclose".
   wp_load.
   iMod ("Hclose" with "[-HΦ Herr]").
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
                     hash_auth_list hnames2 ks ∗
                     con_hash_inv_list N fs2 hnames2 ks s) ∗
                 (res ↦ #false ∨
                 (res ↦ #true ∗
                          ↯ ((size s / (filter_size + 1)) ^ (length fs2))%R)))%I
              with "[][Herr Hres][HΦ]"); auto.
   - iIntros (fs1 f fs2 Ψ) "!# ((%γ2 & Hauths & Hiter) & [Hr | (Hr & Herr)]) HΨ".
     + wp_pures.
       wp_bind (f _).
       iPoseProof (con_hash_inv_list_cons with "Hiter")
         as "(%lk&%hm&%γ&%hnames3&->&#Hinvf&Hfrags&Htail)".
       rewrite /hash_auth_list.
       iPoseProof (big_sepL_cons with "Hauths") as "((%m&Hmauth&Hmdom)&Hauths)"; auto.
       wp_apply (wp_hash_lookup_safe with "[Hmauth]"); auto.
       { admit. }
       iIntros (v) "(?&?)".
       wp_pures.
       wp_bind (!_)%E.
       iInv "Hinv" as "(%&?&?&?&?&?&%arr&Harr&>%HlenA&>%Htrue)" "Hclose".
       wp_apply (wp_load_offset with "Harr").
       { admit. }
       iIntros "Harr".



   Admitted.

 Qed.
