From stdpp Require Import namespaces finite fin_sets.
From iris.proofmode Require Import proofmode.
From iris Require Import ghost_map.
From iris.algebra Require Import excl_auth gmap.
From clutch.prelude Require Import stdpp_ext.
From clutch.coneris Require Import coneris hash_view_interface con_hash_interface0 con_hash_interface1.

Set Default Proof Using "Type*".

(* Section lemmas. *)
(*   Context `{!inG Σ (excl_authR (gmapO nat unitO))}. *)

(*   (* Helpful lemmas *) *)
(*   Lemma ghost_var_alloc b : *)
(*     ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b). *)
(*   Proof. *)
(*     iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]". *)
(*     - by apply excl_auth_valid. *)
(*     - by eauto with iFrame. *)
(*   Qed. *)

(*   Lemma ghost_var_agree γ b c : *)
(*     own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝. *)
(*   Proof. *)
(*     iIntros "Hγ● Hγ◯". *)
(*     by iCombine "Hγ● Hγ◯" gives %->%excl_auth_agree_L. *)
(*   Qed. *)

(*   Lemma ghost_var_update γ b' b c : *)
(*     own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b'). *)
(*   Proof. *)
(*     iIntros "Hγ● Hγ◯". *)
(*     iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]". *)
(*     { by apply excl_auth_update. } *)
(*     done. *)
(*   Qed. *)

(* End lemmas. *)

(* Section lemmas. *)
(*   Context `{!inG Σ (excl_authR (gmapO nat natO))}. *)

(*   (* Helpful lemmas *) *)
(*   Lemma ghost_var_alloc b : *)
(*     ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b). *)
(*   Proof. *)
(*     iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]". *)
(*     - by apply excl_auth_valid. *)
(*     - by eauto with iFrame. *)
(*   Qed. *)

(*   Lemma ghost_var_agree γ b c : *)
(*     own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝. *)
(*   Proof. *)
(*     iIntros "Hγ● Hγ◯". *)
(*     by iCombine "Hγ● Hγ◯" gives %->%excl_auth_agree_L. *)
(*   Qed. *)

(*   Lemma ghost_var_update γ b' b c : *)
(*     own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b'). *)
(*   Proof. *)
(*     iIntros "Hγ● Hγ◯". *)
(*     iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]". *)
(*     { by apply excl_auth_update. } *)
(*     done. *)
(*   Qed. *)

(* End lemmas. *)


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
  Definition hash_tape_auth m γ_set γ :=
    (hash_tape_auth0 m γ ∗
     [∗ map]ns ∈m, [∗ list] x ∈ ns, hash_set_frag x γ_set
    )%I.

  Definition hash_frag k v γ1 γ2:=
    (hv_frag (L:=Hhv) k v γ1 ∗
     hash_set_frag v γ2)%I.

  Definition con_hash_inv N f l hm (P:gmap nat nat -> gmap val (list nat) -> iProp Σ) {HP: ∀ m m', Timeless (P m m')} R {HR:∀ m, Timeless (R m)} γ1 γ2 γ_lock:=
    con_hash_inv0 N f l hm (λ m m',   ([∗ map]ns ∈m', [∗ list] x ∈ ns, hash_set_frag x γ2) ∗ P m m')%I (λ m, hash_auth m γ1 γ2 ∗ R m)%I γ_lock.

  
  Lemma hash_set_frag_in_set s n γ:
    hash_set s γ -∗ hash_set_frag n γ -∗ ⌜n ∈ s⌝.
  Proof.
    iIntros "(H1 &_) H2".
    rewrite /hash_set/hash_set_frag.
    iCombine "H1 H2" gives "%H".
    iPureIntro.
    rewrite lookup_gset_to_gmap_Some in H. naive_solver.
  Qed.
  
  
  (* Definition hash_tape α t γ :=(rand_tapes (L:=Hr) α (val_size, t)∗ [∗ list] n ∈ t, set_frag n γ)%I. *)
  (* Definition con_hash_view k v γ γ' := (hv_frag (L:=Hhv) k v γ ∗ set_frag v γ')%I. *)
  (* Definition abstract_con_hash (f:val) (l:val) (hm:val) γ1 γ2 γ3: iProp Σ := *)
  (*   ∃ m, *)
  (*     ⌜f=compute_con_hash_specialized (l, hm)%V⌝ ∗ *)
  (*     hv_auth (L:=Hhv) m γ1 ∗ *)
  (*     own γ2 (●E m) ∗ *)
  (*     ([∗ map] k↦v∈m, set_frag v γ3)  *)
  (* . *)
  (* Definition abstract_con_hash_inv f l hm γ1 γ2 γ3:= *)
  (*   inv (nroot.@"con_hash_abstract") (abstract_con_hash f l hm γ1 γ2 γ3). *)
  
  (* Definition concrete_con_hash (hm:val) (m:gmap nat nat) γ : iProp Σ:= *)
  (*   ∃ (hm':loc), ⌜hm=#hm'⌝ ∗ *)
  (*   map_list hm' ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗ *)
  (*   own γ (◯E m). *)

  (* Definition concrete_con_hash_inv hm l γ_lock γ:= *)
  (*   is_lock (L:=Hl) γ_lock l (∃ m, concrete_con_hash hm m γ). *)
  
  (* Definition con_hash_inv f l hm γ1 γ3 γ_lock:= *)
  (*   (∃ γ2, abstract_con_hash_inv f l hm γ1 γ2 γ3 ∗ *)
  (*    concrete_con_hash_inv hm l γ_lock γ2)%I. *)

  (* Definition hash_set s γ3 := (ghost_map_auth γ3 1 (gset_to_gmap () s) ∗ *)
  (*                             ⌜ ∀ x, x∈s-> (x < S val_size)%nat⌝ ∗ *)
  (*                                    [∗ set] x∈s, set_frag x γ3 *)
  (*                            )%I *)
  (* . *)

  
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

  Lemma hash_tape_presample N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} m γ_hv γ_set γ γ_lock α ns s (bad : gset nat) (ε εI εO:nonnegreal) E:
  ↑(N.@"rand")⊆E ->
  (forall x : nat, x ∈ bad -> (x < S val_size)%nat) ->
  (εI * (size bad) + εO * (val_size + 1 - size bad) <= ε * (val_size + 1))%R ->
  con_hash_inv N f l hm P R γ_hv γ_set γ γ_lock -∗
    hash_tape_auth m γ_set γ -∗ hash_tape α ns γ_set γ -∗ ↯ ε -∗
    hash_set s γ_set -∗
    state_update E E (∃ (n:fin(S val_size)),
          ( (⌜fin_to_nat n ∈ bad⌝) ∗ ↯ εI  ∨
            (⌜fin_to_nat n ∉ bad⌝) ∗ ↯ εO
          )∗
          hash_set (s∪{[(fin_to_nat n)]}) γ_set ∗
          hash_tape_auth (<[α:=ns++[fin_to_nat n]]>m) γ_set γ ∗
          hash_tape α (ns++[fin_to_nat n]) γ_set γ
      ).
  Proof.
    iIntros (Hsubset Hbound Hineq) "#Hinv [Htauth #?] [Ht #?] Herr (Hs&%&#?)".
    pose (ε2 (x:fin (S val_size)):= if bool_decide (fin_to_nat x ∈ bad) then nonneg εI else nonneg εO).
    iMod (con_hash_interface0.hash_tape_presample _ _ _ _ _ _ _ _ _ _ _ _ ε2 with "[//][$][$][$]") as "(%&Herr&Htauth&Ht)".
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
        * iApply big_sepM_insert_2; last done.
          iSplit; first done.
          iSplit; last done.
          rewrite /hash_set_frag.
          by iApply (big_sepS_elem_of with "[$]").
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
          -- iApply big_sepM_insert_2; last done.
             iSplit; first done.
             by iSplit.
  Qed.

  Lemma con_hash_presample  N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} γ_hv γ_set γ_tape γ_lock Q
    E  :
    ↑(N.@"hash") ⊆ E ->
    con_hash_inv N f l hm P R γ_hv γ_set γ_tape γ_lock -∗
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
    iMod (con_hash_presample0 with "[//][-]"); first done; last done.
    iIntros (m m') "[#?HP] Ht".
    rewrite /hash_tape_auth.
    iMod ("Hvs" with "[$][$Ht]") as "(%&HP&[Ht #?]&HQ)"; first done.
    iFrame. by iModIntro. 
  Qed.

  Lemma con_hash_init N P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )}:
    {{{ P ∅ ∅ ∗ R ∅}}}
      init_hash #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ2 γ3 γ_lock, con_hash_inv N f l hm P R γ1 γ2 γ3 γ_lock ∗
                                                  hash_set ∅ γ2
      }}}.
  Proof.
    iIntros (Φ) "[HP HR] HΦ".
    rewrite /init_hash.
    iApply fupd_pgl_wp.
    rewrite /hash_auth.
    iMod (hv_auth_init) as "(%&H)".
    iMod (ghost_map_alloc_empty) as "(%γ2 &H')".
    iModIntro.
    wp_apply (con_hash_init0 _ (λ (m : gmap nat nat) (m' : gmap val (list nat)), ([∗ map] ns ∈ m', [∗ list] x4 ∈ ns, hash_set_frag x4 γ2) ∗ P m m')%I (λ m, hash_auth m _ _ ∗ R m)%I with "[$HP $HR $H]").
    { by iSplit. }
    rewrite /con_hash_inv.
    iIntros (f) "(%&%&%&%&#Hinv)".
    iApply "HΦ".
    rewrite /hash_set.
    rewrite gset_to_gmap_empty.
    iFrame.
    iFrame "Hinv".
    by iSplit.
  Qed.

  Lemma con_hash_alloc_tape N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} γ1 γ2 γ3 γ_lock Q:
  {{{ con_hash_inv N f l hm P R γ1 γ2 γ3 γ_lock ∗
      (∀ m m' α, P m m' -∗ ⌜α∉dom m'⌝ -∗ |={⊤∖↑N.@"hash"}=> P m (<[α:=[]]>m') ∗ Q α)
  }}}
      allocate_tape #()
      {{{ (α: val), RET α; hash_tape α [] γ2 γ3 ∗ Q α }}}.
  Proof.
    iIntros (Φ) "[#Hinv Hvs] HΦ".
    rewrite /allocate_tape.
    wp_apply (con_hash_alloc_tape0 _ _ _ _ _ _ _ _ Q with "[Hvs $Hinv]").
    - rewrite /hash_auth.
      iIntros (???) "[#? HP] %".
      iMod ("Hvs" with "[$][//]") as "[$$]".
      iFrame. iModIntro. 
      rewrite big_sepM_insert; first repeat by iSplit.
      by apply not_elem_of_dom_1.
    - iIntros (?) "[??]".
      iApply "HΦ". by iFrame.
  Qed.

  Lemma con_hash_spec N f l hm P {HP: ∀ m m', Timeless (P m m')} R {HR: ∀ m, Timeless (R m )} γ1 γ2 γ3 γ_lock Q1 Q2 α (v:nat):
  {{{ con_hash_inv N f l hm P R γ1 γ2 γ3 γ_lock ∗ 
      ( ∀ m m', R m -∗ P m m' -∗ hash_tape_auth m' γ2 γ3 -∗ hash_auth m γ1 γ2 -∗ state_update (⊤∖↑N.@"hash") (⊤∖↑N.@"hash")
             match m!!v with
             | Some res => R m ∗ P m m' ∗ hash_auth m γ1 γ2 ∗ hash_tape_auth m' γ2 γ3 ∗ Q1 res
             | None => ∃ n ns, hash_tape α (n::ns) γ2 γ3 ∗ P m (<[α:=n::ns]> m') ∗ hash_tape_auth (<[α:=n::ns]> m') γ2 γ3 ∗
                              (∀ m'', P m m'' -∗ hash_tape α (ns) γ2 γ3 -∗ ⌜m''!!α=Some (n::ns)⌝
                                      ={⊤∖↑N.@"hash"}=∗ R (<[v:=n]> m) ∗ P (<[v:=n]> m) (<[α:=ns]> m'') ∗
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
    iApply (con_hash_spec0 _ _ _ _ _ _ _ _ Q1 (λ n ns, Q2 n ns ∗ [∗ list] n∈ns, hash_set_frag n _)%I with "[$Hinv Hvs]").
    - iIntros (??) "[Hauth HR](#?&HP)Htauth".
      iMod ("Hvs" with "[$][$][$][$]") as "Hcont".
      case_match.
      + iDestruct "Hcont" as "(?&?&?&[??]&?)". by iFrame.
      + iDestruct "Hcont" as "(%&%&[? #Hfrag]&?&[Htauth #?]&Hcont)".
        iFrame. iModIntro.
        iSplit.
        { iApply big_sepM_insert_2; done. }
        iIntros (?) "[#? HP] Ht %".
        iMod ("Hcont" with "[$][$Ht][//]") as "(?&?&?&?)".
        { rewrite big_sepL_cons.
          iDestruct "Hfrag" as "[_ $]". }
        iFrame. iModIntro. iSplit. 
        * iApply big_sepM_insert_2; last done.
          rewrite big_sepL_cons.
          iDestruct "Hfrag" as "[_ $]".
        * rewrite big_sepL_cons.
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
      con_hash_presample1 := con_hash_presample;
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
  (* Next Obligation. *)
  (*   iIntros (????) "[H1 ?][ H2 ?]". *)
  (*   iApply (con_hash_interface0.hash_tape_auth_exclusive with "[$][$]"). *)
  (* Qed. *)
  Next Obligation.
    iIntros (?????) "[??][??]".
    iApply (con_hash_interface0.hash_tape_auth_frag_agree with "[$][$]").
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
    
  (* Lemma con_hash_presample N f l hm P {HP: ∀ m m', Timeless (P m m')} γ1 γ2 γ_lock Q *)
  (*   E (ε εI εO:nonnegreal) ns α  s: *)
  (*   ↑N ⊆ E -> *)
  (*   (εI * (size s) + εO * (val_size + 1 - size s) <= ε * (val_size + 1))%R -> *)
  (*   con_hash_inv N f l hm P γ1 γ2 γ_lock -∗ *)
  (*   (∀ m m' n, P m m'  -∗ *)
  (*            ⌜m'!!α=Some ns⌝ ∗ *)
  (*            |={E∖↑N}=> *)
  (*              (P m (<[α:=ns++[fin_to_nat n]]> m') ∗ *)
  (*                  Q n *)
  (*              ) *)
  (*   ) -∗ *)
  (*   hash_set s γ2 -∗ *)
  (*   hash_tape α ns γ2 -∗ *)
  (*   ↯ ε -∗ *)
  (*   state_update E E (∃ (n:fin (S val_size)), *)
  (*         ( (⌜fin_to_nat n ∈ s⌝) ∗ hash_set s γ2 ∗ ↯ εI ∨ *)
  (*           (⌜fin_to_nat n ∉ s⌝) ∗ hash_set (s∪{[(fin_to_nat n)]}) γ2 ∗ ↯ εO *)
  (*         ) ∗ *)
  (*         hash_tape α (ns++[fin_to_nat n]) γ2∗ *)
  (*         Q n *)
  (*     ). *)
  (* Proof. *)
  (*   iIntros (Hsubset Hineq) "#Hinv Hvs Hs Htape Herr". *)
  (*   pose (ε2 (x:fin (S val_size)):= if bool_decide (fin_to_nat x ∈s) then nonneg εI else nonneg εO). *)
  (*   iDestruct "Htape" as "[Htape #?]". *)
  (*   iDestruct "Hs" as "(?&%&#?)". *)
  (*   iMod (con_hash_presample0 _ _ _ _ _ _ Q _ _ _ _ ε2 with "[//][Hvs][$][$]") as "(%n&Herr&Htape&HQ)". *)
  (*   - done. *)
  (*   - intros. rewrite /ε2. case_bool_decide; apply cond_nonneg. *)
  (*   - rewrite /ε2. *)
  (*     (** copied from error rules *) *)
  (*     rewrite S_INR. *)
  (*     rewrite SeriesC_scal_l. *)
  (*     rewrite (SeriesC_ext _ (λ x : fin (S val_size), *)
  (*                               εI * (if bool_decide (fin_to_nat x ∈ s) then 1 else 0) + *)
  (*                                 εO * (if bool_decide (¬(fin_to_nat x ∈ s)) then 1 else 0))%R); last first. *)
  (*     { *)
  (*       intro n. *)
  (*       case_bool_decide as HE ; case_bool_decide as HF; simpl. *)
  (*       - done. *)
  (*       - lra. *)
  (*       - lra. *)
  (*       - done. *)
  (*     } *)
  (*     rewrite SeriesC_plus; [ | apply ex_seriesC_finite | apply ex_seriesC_finite]. *)
  (*     rewrite 2!SeriesC_scal_l. *)
  (*     rewrite /Rdiv Rmult_1_l. *)
  (*     rewrite Rmult_comm. *)
  (*     rewrite -Rdiv_def. *)
  (*     pose proof (pos_INR val_size). *)
  (*     apply Rcomplements.Rle_div_l; [lra |]. *)
  (*     rewrite SeriesC_fin_in_set; auto. *)
  (*     rewrite SeriesC_fin_not_in_set; auto. *)
  (*   - iIntros (m m' n) "[Hauth HP]". *)
  (*     iDestruct ("Hvs" with "[$]") as "[% Hvs]". *)
  (*     iSplit; first done. *)
  (*     iMod "Hvs". by iFrame. *)
  (*   - rewrite /ε2. case_bool_decide as Heqn.  *)
  (*     + iFrame. iModIntro. iSplit. *)
  (*       * iLeft. iFrame. by repeat iSplit. *)
  (*       * iSplit; first done. iSplit; last done. *)
  (*         by iApply (big_sepS_elem_of with "[//]"). *)
  (*     + iMod (ghost_map_insert_persist (fin_to_nat n) with "[$]") as "[Hs #?]". *)
  (*       * by rewrite lookup_gset_to_gmap_None. *)
  (*       * iModIntro. iFrame "Htape". *)
  (*         iFrame. iSplit. *)
  (*         -- iRight. iFrame. *)
  (*            iSplit; first done. repeat iSplit. *)
  (*            ++ rewrite <-gset_to_gmap_union_singleton. *)
  (*               by rewrite union_comm_L. *)
  (*            ++ iPureIntro. *)
  (*               set_unfold. intros ? [|]; first naive_solver. *)
  (*               subst. *)
  (*               apply fin_to_nat_lt. *)
  (*            ++ by iApply big_sepS_insert_2'. *)
  (*         -- by repeat iSplit. *)
  (* Qed. *)
          

  (* Lemma con_hash_init N P {HP: ∀ m m', Timeless (P m m')}: *)
  (*   {{{ P ∅ ∅ }}} *)
  (*     init_hash #() *)
  (*     {{{ (f:val), RET f; ∃ l hm γ1 γ2 γ_lock, con_hash_inv N f l hm P γ1 γ2 γ_lock ∗ *)
  (*                                                 hash_set ∅ γ2 *)
  (*     }}}. *)
  (* Proof. *)
  (*   iIntros (Φ) "HP HΦ". *)
  (*   iMod hv_auth_init as "[%γ1 Hv]".   *)
  (*   iMod (ghost_map_alloc_empty) as (γ2) "H2". *)
  (*   rewrite /init_hash. *)
  (*   rewrite /con_hash_inv. *)
  (*   wp_apply (con_hash_init0 _ (λ (m : gmap nat nat) (m' : gmap val (list nat)), hash_auth m γ1 γ2 ∗ P m m')%I with "[$HP $Hv]"); first done. *)
  (*   iIntros (f) "(%&%&%&#Hinv)". *)
  (*   iApply "HΦ". *)
  (*   iFrame "Hinv". iFrame. by repeat iSplit. *)
  (* Qed. *)
  

  (* Lemma con_hash_alloc_tape N f l hm P {HP: ∀ m m', Timeless (P m m')} γ1 γ2 γ_lock Q: *)
  (* {{{ con_hash_inv N f l hm P γ1 γ2 γ_lock ∗ *)
  (*     (∀ m m' α, P m m' -∗ ⌜α∉dom m'⌝ ∗ |={⊤∖↑N}=> P m (<[α:=[]]>m') ∗ Q α) *)
  (* }}} *)
  (*     allocate_tape #() *)
  (*     {{{ (α: val), RET α; hash_tape α [] γ2 ∗ Q α }}}. *)
  (* Proof. *)
  (*   rewrite /hash_tape. *)
  (*   iIntros (Φ) "[#Hinv Hvs] HΦ". *)
  (*   rewrite /allocate_tape. *)
  (*   rewrite /con_hash_inv. *)
  (*   wp_apply (con_hash_alloc_tape0 _ _ _ _ _ _ Q with "[$Hinv Hvs][HΦ]"). *)
  (*   - iIntros (???) "[Hauth HP]". *)
  (*     iDestruct ("Hvs" with "[$]") as "[% Hvs]". *)
  (*     iSplit; first done. *)
  (*     iMod "Hvs". by iFrame. *)
  (*   - iNext. iIntros (?) "[??]". *)
  (*     iApply "HΦ". *)
  (*     by iFrame. *)
  (* Qed. *)

  (* Lemma con_hash_spec N f l hm P {HP: ∀ m m', Timeless (P m m')} γ1 γ2 γ_lock Q1 Q2 α ns (v:nat): *)
  (* {{{ con_hash_inv N f l hm P γ1 γ2 γ_lock ∗ hash_tape α (ns) γ2 ∗ *)
  (*     ( ∀ m m', hash_auth m γ1 γ2 -∗ P m m' -∗ ⌜m'!!α=Some ns⌝ ∗ |={⊤∖↑N}=> *)
  (*            match m!!v with *)
  (*            | Some res => hash_auth m γ1 γ2 ∗ P m m' ∗ Q1 res *)
  (*            | None => ∃ n ns', ⌜n::ns'=ns⌝ ∗ hash_auth (<[v:=n]> m) γ1 γ2 ∗ P (<[v:=n]> m) (<[α:=ns']> m') ∗ Q2 *)
  (*            end                                         *)
  (*     ) *)
  (* }}} *)
  (*     f #v α *)
  (*     {{{ (res:nat), RET (#res);  (hash_tape α (ns) γ2 ∗ Q1 res ∨ *)
  (*                                ∃ n ns', ⌜n::ns'=ns⌝ ∗ hash_tape α ns' γ2 ∗ ⌜res=n⌝ ∗ Q2  *)
  (*                               ) *)
  (*     }}}. *)
  (* Proof. *)
  (*   rewrite /con_hash_inv. *)
  (*   iIntros (Φ) "(#Hinv & Htape & Hvs) HΦ". *)
  (*   iDestruct "Htape" as "[Htape #Hfrag]". *)
  (*   wp_apply (con_hash_spec0 _ _ _ _ _ _ Q1 Q2 with "[$Hinv Hvs $Htape]"). *)
  (*   - iIntros (m m') "[Hauth HP]". *)
  (*     iDestruct ("Hvs" with "[$][$]") as "[% Hvs]". *)
  (*     iSplit; first done. *)
  (*     iMod "Hvs". case_match. *)
  (*     + by iDestruct "Hvs" as "($ &$&$)". *)
  (*     + by iDestruct "Hvs" as "(%&%&<-&$&$&$)". *)
  (*   - iIntros (res) "[[Ht HQ]|(%&%&<-&?&->&H)]"; iApply "HΦ". *)
  (*     + iLeft. by iFrame. *)
  (*     + iRight. iFrame. iExists _. repeat iSplit; try done. *)
  (*       rewrite big_sepL_cons. iDestruct "Hfrag" as "[_ $]". *)
  (* Qed.  *)


  
End con_hash_impl1.

  (* Lemma con_hash_spec f l hm γ1 γ3 γlock α n ns (v:nat): *)
  (*   {{{ con_hash_inv f l hm γ1 γ3 γlock ∗ hash_tape α (n::ns) γ3 }}} *)
  (*     f #v α *)
  (*     {{{ (res:nat), RET (#res);  hash_frag v res γ1 γ3 ∗ *)
  (*                               (hash_tape α ns γ3 ∗ ⌜res=n⌝ ∨ *)
  (*                                hash_tape α (n::ns) γ3 *)
  (*                               ) *)
  (*     }}}. *)
  (* Proof. *)
  (*   rewrite /con_hash_inv/hash_tape. *)
  (*   iIntros (Φ) "[[%γ2 #[Hab Hcon]] [Ht #Hfrag1]] HΦ". *)
  (*   iApply pgl_wp_fupd. *)
  (*   iApply fupd_pgl_wp. *)
  (*   iInv "Hab" as ">(%&->&H1&H2)" "Hclose". *)
  (*   iMod ("Hclose" with "[$H1 $H2]") as "_"; first done. *)
  (*   iModIntro. *)
  (*   rewrite /compute_con_hash_specialized. *)
  (*   wp_pures. *)
  (*   wp_apply (acquire_spec with "Hcon") as "[Hl[% (%&->&Hm&Hfrag)]]". *)
  (*   wp_pures. *)
  (*   rewrite /compute_hash. *)
  (*   wp_pures. *)
  (*   wp_apply (wp_get with "[$]") as (res) "[Hm ->]". *)
  (*   rewrite lookup_fmap. *)
  (*   destruct (_!!_) eqn:Hres; simpl. *)
  (*   - (* hashed before *) *)
  (*     wp_pures. *)
  (*     iApply fupd_pgl_wp. *)
  (*     iInv "Hab" as ">(%&->&H1&H2&#Hfrag2)" "Hclose". *)
  (*     iDestruct (ghost_var_agree with "[$][$]") as "->". *)
  (*     iDestruct (hv_auth_duplicate_frag with "[$]") as "[H1 Hfrag']"; first done. *)
  (*     iMod ("Hclose" with "[$H1 $H2]") as "_"; first by iSplit. *)
  (*     iModIntro. *)
  (*     wp_apply (release_spec with "[$Hl $Hcon $Hfrag $Hm]") as "_"; first done. *)
  (*     wp_pures. *)
  (*     iModIntro. iApply "HΦ". *)
  (*     iFrame. *)
  (*     iSplit. *)
  (*     + by iDestruct (big_sepM_lookup with "[$]") as "?". *)
  (*     + iRight. by iFrame.  *)
  (*   - wp_pures. *)
  (*     rewrite /hash_tape. *)
  (*     wp_apply (rand_tape_spec_some with "[$]") as "Ht". *)
  (*     wp_pures. *)
  (*     wp_apply (wp_set with "[$]") as "Hm". *)
  (*     iApply fupd_pgl_wp. *)
  (*     iInv "Hab" as ">(%&->&H1&H2& #Hfrag2)" "Hclose". *)
  (*     iDestruct (ghost_var_agree with "[$][$]") as "->". *)
  (*     iMod (ghost_var_update _ (<[v:=n]> _) with "[$][$]") as "[H2 Hfrag]". *)
  (*     iMod (hv_auth_insert with "[$]") as "[H1 Hfrag']"; first done. *)
  (*     iMod ("Hclose" with "[$H1 $H2]") as "_". *)
  (*     { iSplit; first done. *)
  (*       iNext. rewrite big_sepM_insert; last done. *)
  (*       iFrame "Hfrag2". *)
  (*       by iDestruct "Hfrag1" as "[??]". *)
  (*     } *)
  (*     iModIntro. *)
  (*     wp_pures. *)
  (*     wp_apply (release_spec with "[$Hl $Hcon $Hfrag Hm]") as "_". *)
  (*     { iExists _. iSplit; first done. by rewrite fmap_insert. } *)
  (*     wp_pures. *)
  (*     iApply "HΦ". *)
  (*     iFrame. iModIntro. *)
  (*     iDestruct "Hfrag1" as "[??]". *)
  (*     iSplit; first done. *)
  (*     iLeft. iFrame. by iSplit. *)
  (* Qed. *)

  (* Lemma con_hash_spec_hashed_before f l hm γ1 γ3 γlock α ns res (v:nat): *)
  (*   {{{ con_hash_inv f l hm γ1 γ3 γlock ∗ hash_tape α ns γ3 ∗ hash_frag v res γ1 γ3 }}} *)
  (*     f #v α *)
  (*     {{{ RET (#res);  hash_frag v res γ1 γ3 ∗ *)
  (*                      (hash_tape α ns γ3 ) *)
  (*     }}}. *)
  (* Proof. *)
  (*   iIntros (Φ) "[[%γ2 [#Hab #Hcon]][Ht #[Hfragv Hfragv']]] HΦ". *)
  (*   rewrite /abstract_con_hash_inv/concrete_con_hash_inv. *)
  (*   iApply fupd_pgl_wp. *)
  (*   iInv "Hab" as ">(%&->&H1&H2)" "Hclose". *)
  (*   iMod ("Hclose" with "[$H1 $H2]") as "_"; first done. *)
  (*   iModIntro. *)
  (*   rewrite /compute_con_hash_specialized. *)
  (*   wp_pures. *)
  (*   wp_apply (acquire_spec with "Hcon") as "[Hl[% (%&->&Hm&Hfrag)]]". *)
  (*   wp_pures. *)
  (*   rewrite /compute_hash. *)
  (*   wp_pures. *)
  (*   wp_apply (wp_get with "[$]") as (res') "[Hm ->]". *)
  (*   rewrite lookup_fmap. *)
  (*   destruct (_!!_) eqn:Hres; simpl. *)
  (*   - (* hashed before *) *)
  (*     wp_pures. *)
  (*     iApply fupd_pgl_wp. *)
  (*     iInv "Hab" as ">(%&->&H1&H2&#Hfrag')" "Hclose". *)
  (*     iDestruct (ghost_var_agree with "[$][$]") as "->". *)
  (*     iDestruct (hv_auth_frag_agree with "[$]") as "%H". *)
  (*     rewrite Hres in H. simplify_eq. *)
  (*     iMod ("Hclose" with "[$H1 $H2]") as "_"; first by iSplit. *)
  (*     iModIntro. *)
  (*     wp_apply (release_spec with "[$Hl $Hcon $Hfrag $Hm]") as "_"; first done. *)
  (*     wp_pures. iModIntro. *)
  (*     iApply "HΦ". *)
  (*     iFrame. rewrite /hash_frag. iFrame "Hfragv Hfragv'".  *)
  (*   - iApply fupd_pgl_wp. *)
  (*     iInv "Hab" as ">(%&->&H1&H2&#?)" "Hclose". *)
  (*     iDestruct (ghost_var_agree with "[$][$]") as "->". *)
  (*     iDestruct (hv_auth_frag_agree with "[$]") as "%H". simplify_eq. *)
  (* Qed. *)
