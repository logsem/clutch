From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import gset_bij auth excl frac agree numbers.
From clutch.coneris Require Import coneris par spawn spin_lock hash atomic lock concurrent_hash con_hash_interface1 bloom_filter.
From clutch.coneris.lib Require Import list array.

Set Default Proof Using "Type*".



Section conc_bloom_filter.



  Variables filter_size num_hash num_threads : nat.
  Context `{!conerisGS Σ, !spawnG Σ, c:con_hash1 Σ filter_size, !inG Σ (excl_authR boolO), !inG Σ (prodR fracR val0) }.


  Definition init_bloom_filter : expr :=
    λ: "_" ,
      let: "hfuns" := list_seq_fun #0 #num_hash
                        (λ: "_", let: "h" := init_hash1 #() in
                                 let: "α" := allocate_tape1 #() in
                                 ("h", "α"))%E in
      let: "arr" := array_init #(S filter_size) (λ: "x", #false)%E in
      let: "l" := ref ("hfuns", "arr") in
      "l".

  Definition insert_bloom_filter : expr :=
    λ: "l" "v" ,
      let, ("hfuns", "arr") := !"l" in
      list_iter (λ: "ht",
          let, ("h", "α") := "ht" in
          let: "i" := "h" "v" "α" in
          "arr" +ₗ "i" <- #true) "hfuns".


  Definition lookup_bloom_filter : expr :=
    λ: "l" "v" ,
      let, ("hfuns", "arr") := !"l" in
      let: "res" := ref #true in
      list_iter (λ: "ht",
          let, ("h", "α") := "ht" in
          let: "i" := "h" "v" "α" in
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

  Variable hash_tape_token : val -> nat -> hash_tape_gname -> iProp Σ.
  Lemma hash_token_non_empty α ns k γ1 γ2 :
    hash_tape1 α ns γ1 γ2 -∗ hash_tape_token α (S k) γ2 -∗
   ⌜ exists n ns', ns = n :: ns' ⌝.
  Admitted.

  Lemma hash_token_combine α k k' γ2 :
    hash_tape_token α k γ2 ∗ hash_tape_token α k' γ2 ⊣⊢ hash_tape_token α (k + k') γ2.
  Admitted.

  Lemma hash_frag_valid k v γ γ2 :
    hash_frag1 k v γ γ2 -∗ ⌜ (v ≤ filter_size)%nat ⌝.
  Admitted.


  Definition con_hash_inv_list N hfs hnames :=
      ([∗ list] k↦hf;γ ∈ hfs;hnames,
        ∃ f α lk hm ns,
          ⌜ hf = (f, α)%V ⌝ ∗
          hash_tape1 α ns γ.2.1 γ.2.2.1 ∗
        con_hash_inv1 N f lk hm (λ _, True) γ.1 γ.2.1 γ.2.2.1 γ.2.2.2)%I.


  Lemma con_hash_inv_list_cons N hf hfs2 hnames :
    con_hash_inv_list N ((hf :: hfs2)) hnames -∗
    (∃ f α lk hm γ hnames2 ns,
        ⌜ hf = (f, α)%V⌝ ∗ ⌜ hnames = γ :: hnames2 ⌝ ∗
         hash_tape1 α ns γ.2.1 γ.2.2.1 ∗
         con_hash_inv1 N f lk hm (λ _, True) γ.1 γ.2.1 γ.2.2.1 γ.2.2.2 ∗
         con_hash_inv_list N hfs2 hnames2
    ).
  Admitted.



  Definition bloom_filter_inv N bfl hfuns a
    (hnames : list (hash_view_gname * (hash_set_gname * (hash_tape_gname * hash_lock_gname)))) (s : gset nat) : iPropI Σ :=
      inv (N.@"bf")
        (∃ hfs,
          (bfl ↦ (hfuns, LitV (LitLoc a))%V ∗
          ⌜ is_list_HO hfs hfuns ⌝ ∗
          ⌜ length hfs = num_hash ⌝ ∗
          con_hash_inv_list N hfs hnames ∗
          ⌜ forall i, i ∈ s -> (i < S filter_size)%nat  ⌝ ∗
          (∃ (arr : list val),
            (a ↦∗ arr) ∗
            ⌜ length arr = S filter_size ⌝ ∗
            ⌜ forall i, i < S filter_size -> arr !! i = Some #true -> i ∈ s  ⌝)))%I.


  Lemma bloom_filter_init_spec N :
    {{{ ↯ (fp_error filter_size num_hash (num_hash * num_threads) 0) }}}
      init_bloom_filter #()
    {{{ (bfl:loc), RET #bfl ;
        ∃ hfuns a hnames s,
        bloom_filter_inv N bfl hfuns a hnames s
    }}}.
  Proof.
    iIntros (Φ) "Herr HΦ".
    rewrite /init_bloom_filter.
    wp_pures.
    wp_apply (wp_list_seq_fun_HO _ 0 num_hash _
                (λ _ fα,
                  ∃ f α lk hm γ,
                    ⌜ fα = (f, α)%V ⌝ ∗
                    hash_set1 ∅ γ.2.1  ∗
                    hash_tape1 α [] γ.2.1 γ.2.2.1 ∗
                    con_hash_inv1 N f lk hm (λ _, True) γ.1 γ.2.1 γ.2.2.1 γ.2.2.2)%I).
    - iIntros (i Ψ).
      iModIntro.
      iIntros "_ HΨ".
      wp_pures.
      wp_apply (con_hash_init1 N (λ _, True)%I); auto.
      iIntros (f) "(%lk & %hm & %γ1 & %γ2 & %γ3 & %γ4 & #Hinv & Hs)".
      wp_pures.
      wp_apply (con_hash_alloc_tape1 with "Hinv").
      iIntros (α) "Hht".
      wp_pures.
      iApply ("HΨ" with "[Hs Hht]").
      iExists f,α,lk,hm,(γ1,(γ2,(γ3,γ4))).
      simpl.
      iFrame.
      iSplit; done.
    - iIntros (hfuns fαs) "(%Hhfuns & %Hlen & Hinvs)".
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
        iApply "HΦ".
        iModIntro.
        iPoseProof (array.big_sepL_exists with "Hinvs") as "(%fs & Hinvs)"; auto.
   Admitted.



  Lemma bloom_filter_insert_thread_spec N bfl hfuns a fs αs ls hms hnames (s : gset nat) (x : nat) :
    {{{ ([∗ set] x ∈ s, ∃ γ, (⌜ γ ∈ hnames ⌝∗ (hash_set_frag1 x γ.2.1))) ∗
          bloom_filter_inv N bfl hfuns a fs αs ls hms hnames s
    }}}
      insert_bloom_filter #bfl #x
      {{{ RET #(); True  }}}.
  Proof.
    iIntros (Φ) "(Hs & #Hinv) HΦ".
    rewrite /insert_bloom_filter /is_bloom_filter.
    wp_pures.
    wp_bind (! _)%E.
    iInv "Hinv" as "(Hbfll&#Hfs&Hlen&Hnames&Hbound&?)" "Hclose".
    wp_load.
    iMod ("Hclose" with "[$]").
    iModIntro.
    wp_pures.
    wp_apply (wp_list_iter_invariant_HO
               (λ l1 l2,
                   ∃ hfuns2 fs2 αs2 ls2 hms2 hnames2,
                     ⌜ l2 = (zip_with (λ v1 v2, PairV v1 v2) fs2 αs2) ⌝ ∗
                   ( [∗ list] i ↦ α;γ ∈ αs2; hnames2, hash_tape_token α 1 γ.2.2.1 ) ∗
                   con_hash_inv_list N fs2 αs2 ls2 hms2 hnames2)%I
               with "[][][HΦ]"); auto.
    - iIntros (lpre w lsuf Ψ).
      iModIntro.
      iIntros "(%Hlist & (%&%&%&%&%&%H&Htoks&Hiter)) HΨ".
      destruct fs2 as [|f fs3], αs2 as [|α αs3]; simpl in H; try inversion H.
      iPoseProof (con_hash_inv_list_cons with "Hiter") as
        "(%α' & %αs3' & %lk & %lks3 & %hm & %hms3 & %γ & %hnames3 & (%Hα & -> & -> & -> & (%ns & Hht ) & Hinvcur & ?))".
      inversion Hα; destruct Hα; simplify_eq.
      iDestruct "Htoks" as "(Htok&Htoks)".
      wp_pures.
      iPoseProof (hash_token_non_empty with "Hht Htok") as "(%n & %ns' & ->)".
      wp_bind (f _ _)%E.
      wp_apply (con_hash_spec_test1 with "[$Hinvcur $Hht]").
      iIntros (res) "(Hfrag & [(Hht & ->)| Hht])".
      + wp_pures.
        iInv "Hinv" as "(?&?&?&?&?&(%arr&Harr&>%HlenA&?))" "Hclose".
        iPoseProof (hash_frag_valid with "Hfrag") as "%".
        wp_apply (wp_store_offset with "[$Harr]").
        {
          apply lookup_lt_is_Some_2.
          rewrite HlenA //.
          lia.
        }
        iIntros "Harr".
        iMod ("Hclose" with "[-HΨ]").
        {
          iModIntro.
          iFrame.
          admit.
        }
        iModIntro.
        iApply "HΨ".
        admit.
      + wp_pures.
        iInv "Hinv" as "(?&?&?&?&?&(%arr&Harr&>%HlenA&?))" "Hclose".
        iPoseProof (hash_frag_valid with "Hfrag") as "%".
        wp_apply (wp_store_offset with "[$Harr]").
        {
          apply lookup_lt_is_Some_2.
          rewrite HlenA //.
          lia.
        }
        iIntros "Harr".
        iMod ("Hclose" with "[-HΨ]").
        {
          iModIntro.
          iFrame.
          admit.
        }
        iModIntro.
        iApply "HΨ".
        admit.
   - iSplitL "Hfs".
     { done. }
     iExists _,fs,αs,ls,hms,hnames.
     iFrame.
     admit.
   - iModIntro.
     iIntros "?".
     by iApply "HΦ".
  Admitted.



End conc_bloom_filter.
