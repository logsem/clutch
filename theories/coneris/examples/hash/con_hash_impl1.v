From stdpp Require Import namespaces finite fin_sets.
From iris.proofmode Require Import proofmode.
From iris Require Import ghost_map.
From iris.algebra Require Import excl_auth gmap.
From coneris.prelude Require Import stdpp_ext.
From coneris.coneris Require Import coneris hash_view_interface con_hash_interface0 con_hash_interface1.

Set Default Proof Using "Type*".


Section con_hash_impl1.
  
  Variable val_size:nat.
  Context `{Hc: conerisGS Σ, Hs: !ghost_mapG Σ nat (),
              h : @hash_view Σ Hc, Hhv: hvG Σ,
               hash0: !con_hash0 val_size
    }.

  (** * Code *)

  Definition init_hash:=init_hash0.
  Definition compute_hash:=compute_hash0.
  Definition allocate_tape:=allocate_tape0.

  
  Definition hash_set_frag v (γ:gname) :=(v ↪[γ]□ ())%I.
  Definition hash_set s γ:=(ghost_map_auth γ 1 (gset_to_gmap () s) ∗
                              ⌜ ∀ x, x∈s-> (x < S val_size)%nat⌝ ∗
                                     [∗ set] x∈s, hash_set_frag x γ
                             )%I.
  Definition hash_auth m γ1 γ2:=
    (hv_auth (L:=Hhv) m γ1 ∗
     [∗ map] v∈m, hash_set_frag v γ2)%I.
  Definition hash_tape α ns γ2 γ_tape :=
    (hash_tape0 α ns γ_tape∗ [∗ list] n ∈ ns, hash_set_frag n γ2)%I.

  Definition hash_frag k v γ1 γ2:=
    (hv_frag (L:=Hhv) k v γ1 ∗
     hash_set_frag v γ2)%I.

  Definition con_hash_inv N f l hm  R {HR:∀ m, Timeless (R m)} γ1 γ2 γ_lock:=
    con_hash_inv0 N f l hm (λ m, hash_auth m γ1 γ2 ∗ R m)%I γ_lock.

  
  Lemma hash_set_frag_in_set s n γ:
    hash_set s γ -∗ hash_set_frag n γ -∗ ⌜n ∈ s⌝.
  Proof.
    iIntros "(H1 &_) H2".
    rewrite /hash_set/hash_set_frag.
    iCombine "H1 H2" gives "%H".
    iPureIntro.
    rewrite lookup_gset_to_gmap_Some in H. naive_solver.
  Qed.

  
  Lemma hash_frag_in_hash_set γ1 γ3 s v res:
    hash_frag v res γ1 γ3 -∗ hash_set s γ3 -∗ ⌜res ∈ s⌝.
  Proof.
    iIntros "[_ #H1] H2".
    iApply (hash_set_frag_in_set with "[$][$]").
  Qed.

  Lemma tape_in_hash_set α ns γ γ_tape s:
    hash_tape α ns γ γ_tape -∗ hash_set s γ -∗ ⌜Forall (λ x, x∈s) ns⌝.
  Proof.
    iIntros "[_ #H1] H2".
    rewrite Forall_forall.
    iIntros (x Hx).
    iDestruct (big_sepL_elem_of with "[$]") as "H"; first done.
    iApply (hash_set_frag_in_set with "[$][$]").
  Qed.

  Lemma hash_tape_presample N f l hm R {HR: ∀ m, Timeless (R m )} γ_hv γ_set γ γ_lock α ns s (bad : gset nat)(ε εI εO:nonnegreal) E:
  ↑(N)⊆E ->
  (forall x : nat, x ∈ bad -> (x < S val_size)%nat) ->
  (εI * (size bad) + εO * (val_size + 1 - size bad) <= ε * (val_size + 1))%R ->
  con_hash_inv N f l hm R γ_hv γ_set γ γ_lock -∗
    hash_tape α ns γ_set γ -∗ ↯ ε -∗
    hash_set s γ_set -∗
    state_update E E (∃ (n:fin(S val_size)), 
          ( (⌜fin_to_nat n ∈ bad⌝) ∗ ↯ εI  ∨
            (⌜fin_to_nat n ∉ bad⌝) ∗ ↯ εO
          )∗
          hash_set (s∪{[(fin_to_nat n)]}) γ_set ∗
          hash_tape α (ns++[fin_to_nat n]) γ_set γ
      ).
  Proof.
    iIntros (Hsubset Hbound Hineq) "#Hinv [Ht #?] Herr (Hs&%&#?)".
    pose (ε2 (x:fin (S val_size)):= if bool_decide (fin_to_nat x ∈ bad) then nonneg εI else nonneg εO).
    iMod (con_hash_interface0.hash_tape_presample _ _ _ _ _ _ _ _ _ _ ε2 with "[//][$][$]") as "(%&Herr&Ht)".
    - done.
    - intros. rewrite /ε2. case_bool_decide; apply cond_nonneg.
    - rewrite /ε2.
      (** copied from error rules *)
      rewrite S_INR.
      rewrite SeriesC_scal_l.
      rewrite (SeriesC_ext _ (λ x : fin (S val_size),
                                εI * (if bool_decide (fin_to_nat x ∈ bad) then 1 else 0) +
                                  εO * (if bool_decide (¬(fin_to_nat x ∈ bad)) then 1 else 0))%R); last first.
      {
        intro n.
        case_bool_decide as HE ; case_bool_decide as HF; simpl.
        - done.
        - lra.
        - lra.
        - done.
      }
      rewrite SeriesC_plus; [ | apply ex_seriesC_finite | apply ex_seriesC_finite].
      rewrite 2!SeriesC_scal_l.
      rewrite /Rdiv Rmult_1_l.
      rewrite Rmult_comm.
      rewrite -Rdiv_def.
      pose proof (pos_INR val_size).
      apply Rcomplements.Rle_div_l; [lra |].
      rewrite SeriesC_fin_in_set; auto.
      rewrite SeriesC_fin_not_in_set; auto.
    - iFrame. rewrite /ε2.
      destruct (decide ((fin_to_nat n) ∈ s)).
      + iModIntro.
        replace ((s∪{[(fin_to_nat n)]})) with s by set_solver.
        iFrame.
        repeat iSplit; try done.
        * case_bool_decide; [iLeft| iRight]; by iFrame.
        * by iApply (big_sepS_elem_of with "[$]").
      + iMod (ghost_map_insert_persist (fin_to_nat n) with "[$]") as "[Hs #?]". 
        * by rewrite lookup_gset_to_gmap_None.
        * iModIntro.
          iSplitL "Herr"; [case_bool_decide; [iLeft | iRight]; by iFrame |].
          repeat iSplit; try done.
          -- rewrite <-gset_to_gmap_union_singleton.
             by rewrite union_comm_L.
          -- iPureIntro.
             set_unfold. intros ? [|]; first naive_solver.
             subst.
             apply fin_to_nat_lt.
          -- by iApply big_sepS_insert_2'.
  Qed.

  Lemma con_hash_init N R {HR: ∀ m, Timeless (R m )}:
    {{{ R ∅}}}
      init_hash #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ2 γ3 γ_lock, con_hash_inv N f l hm R γ1 γ2 γ3 γ_lock ∗
                                                  hash_set ∅ γ2
      }}}.
  Proof.
    iIntros (Φ) "HR HΦ".
    rewrite /init_hash.
    iApply fupd_pgl_wp.
    rewrite /hash_auth.
    iMod (hv_auth_init) as "(%&H)".
    iMod (ghost_map_alloc_empty) as "(%γ2 &H')".
    iModIntro.
    wp_apply (con_hash_init0 _ (λ m, hash_auth m _ _ ∗ R m)%I with "[$HR $H]"); first done.
    rewrite /con_hash_inv.
    iIntros (f) "(%&%&%&%&#Hinv)".
    iApply "HΦ".
    rewrite /hash_set.
    rewrite gset_to_gmap_empty.
    iFrame.
    iFrame "Hinv".
    by iSplit.
  Qed.

  Lemma con_hash_alloc_tape N f l hm R {HR: ∀ m, Timeless (R m )} γ1 γ2 γ3 γ_lock:
  {{{ con_hash_inv N f l hm R γ1 γ2 γ3 γ_lock 
  }}}
      allocate_tape #()
      {{{ (α: val), RET α; hash_tape α [] γ2 γ3 }}}.
  Proof.
    iIntros (Φ) "#Hinv HΦ".
    rewrite /allocate_tape.
    wp_apply (con_hash_alloc_tape0 _ _ _ _ _ _ _ _ with "[$Hinv]").
    iIntros (?) "?".
    iApply "HΦ". by iFrame.
  Qed.

  Lemma con_hash_spec N f l hm R {HR: ∀ m, Timeless (R m )} γ1 γ2 γ3 γ_lock Q1 Q2 α (v:nat):
  {{{ con_hash_inv N f l hm R γ1 γ2 γ3 γ_lock ∗ 
      ( ∀ m, R m -∗ hash_auth m γ1 γ2 -∗ state_update (⊤) (⊤)
             match m!!v with
             | Some res => R m ∗ hash_auth m γ1 γ2 ∗ Q1 res
             | None => ∃ n ns, hash_tape α (n::ns) γ2 γ3 ∗ 
                              (hash_tape α (ns) γ2 γ3 
                                      ={⊤}=∗ R (<[v:=n]> m) ∗
                                      hash_auth (<[v:=n]> m) γ1 γ2  ∗ Q2 n ns)
             end                                        
      )
  }}}
      f #v α
      {{{ (res:nat), RET (#res);  (Q1 res ∨
                                 ∃ ns, Q2 res ns
                                )
      }}}.
  Proof.
    iIntros (Φ) "(#Hinv  & Hvs) HΦ".
    iApply (con_hash_spec0 _ _ _ _ _ _ _ Q1 (λ n ns, Q2 n ns ∗ [∗ list] n∈ns, hash_set_frag n _)%I with "[$Hinv Hvs]").
    - iIntros (?) "[Hauth HR]".
      iMod ("Hvs" with "[$][$]") as "Hcont".
      case_match.
      + iDestruct "Hcont" as "(?&?&?)". by iFrame.
      + iDestruct "Hcont" as "(%&%&[? #Hfrag]&Hcont)".
        iFrame. iModIntro.
        iIntros "Ht".
        iMod ("Hcont" with "[$Ht]") as "(?&?&?)".
        { rewrite big_sepL_cons.
          iDestruct "Hfrag" as "[_ $]". }
        iFrame. iModIntro.
        rewrite big_sepL_cons.
        iDestruct "Hfrag" as "[_ $]".
    - iNext. iIntros (res) "[?|(%&?&#?)]"; iApply "HΦ".
      + iLeft. by iFrame.
      + iRight. iFrame. 
  Qed.

  
  Program Definition con_hash_impl1 : con_hash1 val_size :=
    {| init_hash1:=init_hash;
      allocate_tape1:=allocate_tape;
      compute_hash1:=compute_hash;

      hash_view_gname:=_;
      hash_set_gname:=_;
      hash_lock_gname:=_;
      
      con_hash_inv1 := con_hash_inv;
      hash_tape1:=hash_tape;
      hash_frag1:=hash_frag;
      hash_auth1:=hash_auth;
      hash_set1:=hash_set;
      hash_set_frag1:=hash_set_frag;
      con_hash_interface1.hash_tape_presample := hash_tape_presample;
      con_hash_init1 := con_hash_init;
      con_hash_alloc_tape1 := con_hash_alloc_tape;
      con_hash_spec1:=con_hash_spec
    |}
  .
  Next Obligation.
    iIntros (????) "[??][??]".
    iApply (hv_auth_exclusive with "[$][$]").
  Qed.
  Next Obligation.
    iIntros (?????)"[??][??]".
    iApply (hv_auth_frag_agree with "[$]").
  Qed.
  Next Obligation.
    iIntros (??????) "[??]".
    iDestruct (hv_auth_duplicate_frag with "[$]") as "[? $]"; first done.
    by iApply (big_sepM_lookup with "[$]").
  Qed.
  Next Obligation.
    rewrite /hash_frag.
    iIntros (?????) "[??][??]".
    by iDestruct (hv_frag_frag_agree with "[$][$]") as "->".
  Qed.
  Next Obligation.
    iIntros (????) "[?$]".
  Qed.
  Next Obligation.
    iIntros (????) "[? #$]".
  Qed.
  Next Obligation.
    iIntros (????) "[?[_ #?]]".
    by iApply (big_sepS_elem_of with "[$]").
  Qed.
  Next Obligation.
    iIntros (???) "[H1 ?]H2".
    iCombine "H1 H2" gives "%H".
    iPureIntro.
    rewrite lookup_gset_to_gmap_Some in H. naive_solver.
  Qed.
  Next Obligation.
    iIntros (??????) "?[??]".
    rewrite /hash_auth.
    iMod (hv_auth_insert with "[$]") as "[$ ?]"; first done.
    iModIntro.
    rewrite big_sepM_insert; last done. iFrame.
  Qed.
  Next Obligation.
    iIntros (??)"(?&%H&?)". iPureIntro. intros n H'.
    apply H in H'. lia.
  Qed.
  Next Obligation.
    iIntros (????) "[??]".
    by iApply con_hash_interface0.hash_tape_valid.
  Qed.
  Next Obligation.
    iIntros (?????) "[H1 _] [H2 _]".
    iApply (con_hash_interface0.hash_tape_exclusive with "[$][$]").
  Qed.


  
End con_hash_impl1.
