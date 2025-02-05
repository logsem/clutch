From stdpp Require Import namespaces finite fin_sets.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth gmap.
From clutch.prelude Require Import stdpp_ext.
From clutch.coneris Require Import coneris coll_free_hash_view_interface con_hash_interface1 con_hash_interface2.

Set Default Proof Using "Type*".

Section con_hash_impl2.
  
  Variable val_size:nat.
  Context `{Hc: conerisGS Σ, 
              h : @hash_view Σ Hc, Hhv: hvG Σ,
                Hs: !ghost_mapG Σ nat (),
               hash1: !con_hash1 val_size
    }.

  (** * Code *)

  Definition init_hash:=init_hash1.
  Definition compute_hash:=compute_hash1.
  Definition allocate_tape:=allocate_tape1.

  
  Definition hash_set_frag v γ_set γ_set' := (hash_set_frag1 v γ_set∗ (v ↪[γ_set'] ()))%I.
  Definition hash_set n γ γ':=
    (∃ s, ⌜size s = n⌝ ∗ hash_set1 s γ ∗ ghost_map_auth γ' 1 (gset_to_gmap () s))%I.
  
  Definition hash_auth m γ1 γ2 γ4 γ5:=
    (hv_auth (L:=Hhv) m γ4 ∗
     hash_auth1 m γ1 γ2 ∗
     ([∗ map] v∈m, hash_set_frag v γ2 γ5) 
    )%I.
  Definition hash_tape α ns γ2 γ_tape :=
    (hash_tape1 α ns γ2 γ_tape (* ∗ [∗ list] n∈ns, hash_set_frag n γ5 *))%I.
  Definition hash_tape_auth m γ2 γ3 :=
    (hash_tape_auth1 m γ2 γ3
    )%I.

  Definition hash_frag k v γ1 γ2 γ4:=
    (hv_frag (L:=Hhv) k v γ4 ∗
     hash_frag1 k v γ1 γ2)%I.

  Definition con_hash_inv N f l hm (P:gmap nat nat -> gmap val (list nat) -> iProp Σ) {HP: ∀ m m', Timeless (P m m')} R {HR:∀ m, Timeless (R m)} γ1 γ2 γ_tape γ4 γ5 γ_lock:=
    con_hash_inv1 N f l hm (λ m m', P m m')%I (λ m, hv_auth (L:=Hhv) m γ4 ∗ ([∗ map] v∈m, (v ↪[γ5] ())) ∗ R m)%I γ1 γ2  γ_tape γ_lock.

  Lemma hash_tape_presample N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR:∀ m, Timeless (R m)} m γ_hv γ_set γ_hv' γ γ_set' γ_lock α ns s (ε εO:nonnegreal) E:
  ↑(N.@"rand")⊆E ->
  (INR s + εO * (val_size + 1 - INR s) <= ε * (val_size + 1))%R ->
  con_hash_inv N f l hm P R γ_hv γ_set γ γ_hv' γ_set' γ_lock -∗
    hash_tape_auth m γ_set γ -∗ hash_tape α ns γ_set γ-∗ ↯ ε -∗
    hash_set s γ_set γ_set'-∗
    state_update E E (∃ (n:fin(S val_size)),
          (  hash_set (s+1)%nat γ_set γ_set' ∗ ↯ εO
          )∗
          hash_tape_auth (<[α:=ns++[fin_to_nat n]]>m) γ_set γ ∗
          hash_tape α (ns++[fin_to_nat n]) γ_set γ ∗ hash_set_frag (fin_to_nat n) γ_set γ_set'
      ).
  Proof.
    rewrite /hash_tape_auth/hash_tape/hash_set/hash_set_frag.
    iIntros (Hsubset Hineq) "#Hinv Htauth Ht Herr (%s' & <- & Hset & Hset')".
    iPoseProof (hash_set_valid with "Hset") as "%Hbound".
    iMod (con_hash_interface1.hash_tape_presample _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' _ 1%NNR with "[//][$][$][$][$]") as "Hcont".
    { done. }
    { intros.
      by apply Nat.lt_succ_r, Hbound.
    }
    { simpl. erewrite Rmult_1_l. done. }
    iDestruct ("Hcont" ) as "(%&[(%&?)|(%&?)]&?&$&$)".
    { by iDestruct (ec_contradict with "[$]") as "%". }
    iMod (ghost_map_insert with "[$]") as "[Hset' Hs']".
    { apply not_elem_of_dom_1. by rewrite dom_gset_to_gmap. }
    rewrite <-gset_to_gmap_union_singleton.
    iModIntro. iFrame.
    repeat iSplit; try done.
    - iPureIntro. rewrite size_union; last set_solver. rewrite size_singleton. lia.
    - by rewrite union_comm_L.
    - iApply (hash_set_duplicate); last done. set_solver.
  Qed.

  Lemma con_hash_presample  N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR:∀ m, Timeless (R m)} γ_hv γ_set γ_tape γ_hv' γ_set' γ_lock Q
    E  :
    ↑(N.@"hash") ⊆ E ->
    con_hash_inv N f l hm P R γ_hv γ_set γ_tape γ_hv' γ_set' γ_lock -∗
    (∀ m m', P m m'  -∗
             hash_tape_auth m' γ_set γ_tape -∗
             state_update (E∖↑(N.@"hash")) (E∖↑(N.@"hash"))
             (∃ m'', P m m'' ∗ hash_tape_auth m'' γ_set γ_tape ∗ Q m m' m'')
    ) -∗
    state_update E E (
        ∃ m m' m'', Q m m' m''
      ) .
  Proof.
    iIntros (Hsubset) "#Hinv Hvs".
    iMod (con_hash_presample1 with "[//][-]"); first done; last done.
    rewrite /hash_tape_auth.
    iIntros (??) "??".
    by iMod ("Hvs" with "[$][$]") as "(%&$&$)".
  Qed.

  Lemma con_hash_init N P {HP: ∀ m m', Timeless (P m m')} R {HR:∀ m, Timeless (R m)}:
    {{{ P ∅ ∅ ∗ R ∅}}}
      init_hash #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ2 γ3 γ4 γ5 γ_lock, con_hash_inv N f l hm P R γ1 γ2 γ3 γ4 γ5 γ_lock ∗
                                                  hash_set 0%nat γ2 γ5
      }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    rewrite /init_hash.
    iApply fupd_pgl_wp.
    iMod (hv_auth_init) as "(%γ1'&H)".
    iMod (ghost_map_alloc_empty) as "(%γ2' &H')".
    iModIntro.
    wp_apply (con_hash_init1 _  with "[HP H]"); last first.
    - iIntros (f)"(%l &%hm&%γ1&%γ2&%γ3&%γ_lock&#H1&H2)".
      iApply "HΦ". rewrite /con_hash_inv/hash_set.
      by iFrame "H1 H2 H'".
    - iDestruct "HP" as "[$$]". by iFrame.
  Qed.

  Lemma con_hash_alloc_tape N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR:∀ m, Timeless (R m)} γ1 γ2 γ3 γ4 γ5 γ_lock Q:
  {{{ con_hash_inv N f l hm P R γ1 γ2 γ3 γ4 γ5 γ_lock ∗
      (∀ m m' α, P m m' -∗ ⌜α∉dom m'⌝ -∗ |={⊤∖↑N.@"hash"}=> P m (<[α:=[]]>m') ∗ Q α)
  }}}
      allocate_tape #()
      {{{ (α: val), RET α; hash_tape α [] γ2 γ3 ∗ Q α }}}.
  Proof.
    iIntros (Φ) "[#Hinv Hvs] HΦ".
    rewrite /allocate_tape.
    wp_apply (con_hash_alloc_tape1 with "[Hvs $Hinv]").
    - iIntros (???) "?%".
      iMod ("Hvs" with "[$][//]") as "[$ H]".
      iFrame.
      iApply "H".
    - rewrite /hash_tape.
      iIntros (?) "[??]".
      iApply "HΦ". iFrame.
  Qed.

  Lemma con_hash_spec  N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} γ1 γ2 γ3 γ4 γ5 γ_lock Q1 Q2 α (v:nat):
  {{{ con_hash_inv N f l hm P R γ1 γ2 γ3 γ4 γ5 γ_lock ∗ 
      ( ∀ m m', R m -∗ P m m' -∗ hash_tape_auth m' γ2 γ3 -∗ hash_auth m γ1 γ2 γ4 γ5-∗ state_update (⊤∖↑N.@"hash") (⊤∖↑N.@"hash")
             match m!!v with
             | Some res => R m ∗ P m m' ∗ hash_tape_auth m' γ2 γ3 ∗ hash_auth m γ1 γ2 γ4 γ5∗ Q1 res
             | None => ∃ n ns, hash_tape α (n::ns) γ2 γ3 ∗ P m (<[α:=n::ns]> m') ∗ hash_tape_auth (<[α:=n::ns]> m') γ2 γ3 ∗
                              (∀ m'', P m m'' -∗ hash_tape α (ns) γ2 γ3 -∗ ⌜m''!!α=Some (n::ns)⌝
                                      ={⊤∖↑N.@"hash"}=∗ R (<[v:=n]> m) ∗ P (<[v:=n]> m) (<[α:=ns]> m'') ∗
                                      hash_auth (<[v:=n]> m) γ1 γ2 γ4 γ5∗ Q2 n ns)
             end                                        
      )
  }}}
      f #v α
      {{{ (res:nat), RET (#res);  (Q1 res ∨
                                 ∃ ns,  Q2 res ns
                                )
      }}}.
  Proof.
    iIntros (Φ) "(#Hinv  & Hvs) HΦ".
    rewrite /hash_tape/hash_set_frag.
    iApply (con_hash_spec1 _ _ _ _ _ _ _ _ _ _ Q1 Q2 with "[$Hinv Hvs]").
    - iIntros (??) "(Hhv & Hfrag & HR) HP Htauth Hauth1".
      rewrite /hash_auth.
      rewrite /hash_set_frag.
      iMod ("Hvs" with "[$][$][$][Hauth1 $Hhv Hfrag]") as "Hcont".
      { rewrite big_sepM_sep. iFrame "Hfrag". iSplit; first done.
        rewrite big_sepM_forall. iIntros.
        iDestruct (con_hash_interface1.hash_auth_duplicate with "[$]") as "#?"; first done.
        by iApply hash_frag_in_hash_set.
      }
      case_match.
      + iDestruct "Hcont" as "($&$&$&($&?&H)&$)".
        iFrame.
        rewrite big_sepM_sep.
        by iDestruct "H" as "[??]".
      + iDestruct "Hcont" as "(%&%&?&?&?&Hcont)".
        iModIntro.
        iFrame. iIntros.
        iMod ("Hcont" with "[$][$][//]") as "(?&?&(?&?&H)&?)".
        iFrame.
        rewrite big_sepM_sep.
        iDestruct "H" as "[??]". by iFrame.
    - iNext. iIntros (?) "[?|(%&?)]"; iApply "HΦ".
      + iLeft. by iFrame.
      + iRight. by iFrame.
  Qed.


  Program Definition con_hash_impl2 : con_hash2 val_size :=
    {| init_hash2:=init_hash;
      allocate_tape2:=allocate_tape;
      compute_hash2:=compute_hash;

      con_hash_inv2 := con_hash_inv;
      hash_tape2:=hash_tape;
      hash_frag2:=hash_frag;
      hash_auth2:=hash_auth;
      hash_tape_auth2 := hash_tape_auth;
      hash_set2:=hash_set;
      hash_set_frag2:=hash_set_frag;
      con_hash_interface2.hash_tape_presample := hash_tape_presample;
      con_hash_presample2 := con_hash_presample;
      con_hash_init2 := con_hash_init;
      con_hash_alloc_tape2 := con_hash_alloc_tape;
      con_hash_spec2:=con_hash_spec
    |}
  .
  Next Obligation.
    iIntros (??????) "[??][??]".
    iApply (hv_auth_exclusive with "[$][$]").
  Qed.
  Next Obligation.
    iIntros (???????)"[??][??]".
    iApply (hv_auth_frag_agree with "[$]").
  Qed.
  Next Obligation.
    iIntros (????????) "[?[??]]".
    iDestruct (hv_auth_duplicate_frag with "[$]") as "[? $]"; first done.
    by iApply (con_hash_interface1.hash_auth_duplicate).
  Qed.
  Next Obligation.
    iIntros (?????) "[??]".
    by iApply hv_auth_coll_free.
  Qed.
  Next Obligation.
    rewrite /hash_frag.
    iIntros (???????) "[??][??]".
    iDestruct (hv_frag_frag_agree with "[$][$]") as "%". iPureIntro. naive_solver.
  Qed.
  Next Obligation.
    iIntros (????????) "[H1 H2][H3[H4 H5]]".
    rewrite /hash_set_frag.
    rewrite big_sepM_sep.
    iDestruct "H5" as "[#H5 H6]".
    rewrite /hash_auth.
    iMod (con_hash_interface1.hash_auth_insert with "[$][$]") as "K"; first done.
    iDestruct (con_hash_interface1.hash_auth_duplicate with "[$]") as "#?"; first apply lookup_insert.
    iAssert (⌜v∉(map_to_list m).*2⌝)%I as "%H0".
    { iIntros (H').
      apply elem_of_list_fmap_2 in H'.
      destruct H' as ([??]&?&H1). simplify_eq.
      rewrite elem_of_map_to_list in H1.
      iDestruct (big_sepM_lookup with "[$]") as "H4"; first done.
      simpl.
      iCombine "H2 H4" gives "%H0".
      cbv in H0. naive_solver.
    }
    iMod (hv_auth_insert with "[$]") as "[$?]"; first done.
    { rewrite Forall_forall.
      intros x Hx.
      intros ->.
      by apply H0. }
    rewrite big_sepM_insert; last done.
    iFrame.
    iDestruct (hash_frag_in_hash_set with "[$]") as "$".
    rewrite /hash_set_frag.
    iModIntro. rewrite big_sepM_sep.
    by iFrame.
  Qed.
  Next Obligation.
    iIntros.
    iApply (con_hash_interface1.hash_tape_auth_frag_agree with "[$][$]").
  Qed.
  Next Obligation.
    iIntros (????) "?".
    by iApply con_hash_interface1.hash_tape_valid.
  Qed.
  Next Obligation.
    iIntros (?????) "??".
    iApply (con_hash_interface1.hash_tape_exclusive with "[$][$]").
  Qed.


End con_hash_impl2.
