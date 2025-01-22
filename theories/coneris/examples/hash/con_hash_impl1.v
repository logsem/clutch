From stdpp Require Import namespaces finite fin_sets.
From iris.proofmode Require Import proofmode.
From iris Require Import ghost_map.
From iris.algebra Require Import excl_auth gmap.
From clutch.prelude Require Import stdpp_ext.
From clutch.coneris Require Import coneris hocap_rand lib.map hash_view_interface lock con_hash_interface1.

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

Section lemmas.
  Context `{!inG Σ (excl_authR (gmapO nat natO))}.

  (* Helpful lemmas *)
  Lemma ghost_var_alloc b :
    ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b).
  Proof.
    iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree γ b c :
    own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯" gives %->%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.

End lemmas.


Section con_hash_impl1.
  Context `{Hc: conerisGS Σ, Hs: !ghost_mapG Σ nat (),
              h : @hash_view Σ Hc, Hhv: hvG Σ,
                lo:lock, Hl: lockG Σ,
                  r: @rand_spec Σ Hc, Hr: randG Σ,
                    Hm: inG Σ (excl_authR (gmapO nat natO))}.
  Variable val_size:nat.

  (** * Code *)
  Definition init_hash_state : val := init_map.

  Definition compute_hash : val :=
    λ: "hm" "v" "α",
      match: get "hm" "v" with
      | SOME "b" => "b"
      | NONE =>
          let: "b" := (rand_tape "α" #val_size) in
          set "hm" "v" "b";;
          "b"
      end.
  
  Definition compute_con_hash :val:=
    λ: "lhm" "v" "α",
      let, ("l", "hm") := "lhm" in
      acquire "l";;
      let: "output" := compute_hash "hm" "v" "α" in
      release "l";;
      "output".
  
  (* init_hash returns a hash as a function, basically wrapping the internal state
     in the returned function *)
  Definition init_hash : val :=
    λ: "_",
      let: "hm" := init_hash_state #() in
      let: "l" := newlock #() in
      compute_con_hash ("l", "hm").

  Definition allocate_tape : val :=
    λ: "_",
      rand_allocate_tape #val_size.


  Definition compute_con_hash_specialized (lhm:val):val:=
    λ: "v" "α",
      let, ("l", "hm") := lhm in
      acquire "l";;
      let: "output" := (compute_hash "hm") "v" "α" in
      release "l";;
      "output".

  Definition set_frag v (γ:gname) :=(v ↪[γ]□ ())%I.
  
  Definition hash_tape α t γ :=(rand_tapes (L:=Hr) α (val_size, t)∗ [∗ list] n ∈ t, set_frag n γ)%I.
  Definition con_hash_view k v γ γ' := (hv_frag (L:=Hhv) k v γ ∗ set_frag v γ')%I.
  Definition abstract_con_hash (f:val) (l:val) (hm:val) γ1 γ2 γ3: iProp Σ :=
    ∃ m,
      ⌜f=compute_con_hash_specialized (l, hm)%V⌝ ∗
      hv_auth (L:=Hhv) m γ1 ∗
      own γ2 (●E m) ∗
      ([∗ map] k↦v∈m, set_frag v γ3) 
  .
  Definition abstract_con_hash_inv f l hm γ1 γ2 γ3:=
    inv (nroot.@"con_hash_abstract") (abstract_con_hash f l hm γ1 γ2 γ3).
  
  Definition concrete_con_hash (hm:val) (m:gmap nat nat) γ : iProp Σ:=
    ∃ (hm':loc), ⌜hm=#hm'⌝ ∗
    map_list hm' ((λ b, LitV (LitInt (Z.of_nat b))) <$> m) ∗
    own γ (◯E m).

  Definition concrete_con_hash_inv hm l γ_lock γ:=
    is_lock (L:=Hl) γ_lock l (∃ m, concrete_con_hash hm m γ).
  
  Definition con_hash_inv f l hm γ1 γ3 γ_lock:=
    (∃ γ2, abstract_con_hash_inv f l hm γ1 γ2 γ3 ∗
     concrete_con_hash_inv hm l γ_lock γ2)%I.

  Definition hash_set s γ3 := (ghost_map_auth γ3 1 (gset_to_gmap () s) ∗
                              ⌜ ∀ x, x∈s-> (x < S val_size)%nat⌝ ∗
                                     [∗ set] x∈s, set_frag x γ3
                             )%I
  .

  (** γ1 is hash view 
      γ2 is map 
      γ3 is gmap of numbers sampled
   *)
  
  Lemma con_hash_view_in_hash_set γ1 γ3 s v res:
    con_hash_view v res γ1 γ3 -∗ hash_set s γ3 -∗ ⌜res ∈ s⌝.
  Proof.
    iIntros "H1 H2".
    rewrite /con_hash_view/hash_set/set_frag.
    iDestruct "H1" as "[_ H1]".
    iDestruct "H2" as "[H2 _]".
    iCombine "H1 H2" gives "%H".
    iPureIntro.
    rewrite lookup_gset_to_gmap_Some in H. naive_solver.
  Qed.

  Lemma tape_in_hash_set α ns γ s:
    hash_tape α ns γ -∗ hash_set s γ -∗ ⌜Forall (λ x, x∈s) ns⌝.
  Proof.
    iIntros "[_ #H1] [H2 _]".
    rewrite Forall_forall.
    iIntros (x Hx).
    iDestruct (big_sepL_elem_of with "[$]") as "H"; first done.
    iCombine "H2 H" gives "%".
    iPureIntro.
    rewrite lookup_gset_to_gmap_Some in H. naive_solver.
  Qed.

  Lemma con_hash_presample γ3 E (ε εI εO:nonnegreal) ns α s :
    (εI * (size s) + εO * (val_size + 1 - size s) <= ε * (val_size + 1))%R ->
    hash_tape α ns γ3 -∗
    ↯ ε -∗
    hash_set s γ3 -∗
    state_update E E (∃ (n:fin (S val_size)),
          hash_tape α (ns++[fin_to_nat n]) γ3 ∗
          ( (⌜fin_to_nat n ∈ s⌝) ∗ hash_set s γ3 ∗ ↯ εI ∨
            (⌜fin_to_nat n ∉ s⌝) ∗ hash_set (s∪{[(fin_to_nat n)]}) γ3 ∗ ↯ εO
          )
      ).
  Proof.
    iIntros (Hineq) "Ht Herr Hs".
    pose (ε2 (x:fin (S val_size)):= if bool_decide (fin_to_nat x ∈s) then nonneg εI else nonneg εO).
    rewrite /hash_tape/hash_set.
    iDestruct "Ht" as "[Ht #Hfrag]".
    iDestruct "Hs" as "[Hs [% #Hfrags]]".
    iMod (rand_tapes_presample _ _ _ _ _ ε2 with "[$][$]") as (n) "[Herr Htape]". 
    - intros. rewrite /ε2. case_bool_decide; apply cond_nonneg.
    - rewrite /ε2.
      (** copied from error rules *)
      rewrite S_INR.
      rewrite SeriesC_scal_l.
      rewrite (SeriesC_ext _ (λ x : fin (S val_size),
                                εI * (if bool_decide (fin_to_nat x ∈ s) then 1 else 0) +
                                  εO * (if bool_decide (¬(fin_to_nat x ∈ s)) then 1 else 0))%R); last first.
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
    - rewrite /ε2.
      case_bool_decide as Hin.
      + iModIntro. iFrame "Htape".
        iSplitR.
        * iSplit; first done.
          iSplit; last done.
          by iDestruct (big_sepS_elem_of with "[$Hfrags]") as "$".
        * iLeft. iFrame. iFrame "Hfrags".
          iPureIntro. naive_solver.
      + iMod (ghost_map_insert_persist (fin_to_nat n) with "[$]") as "[Hs #?]".
        * by rewrite lookup_gset_to_gmap_None.
        * iModIntro. iFrame "Htape".
          iSplitR.
          -- iSplit; first done. by iSplit.
          -- iRight. iFrame. repeat iSplit.
             ++ done.
             ++ rewrite -gset_to_gmap_union_singleton.
                by rewrite union_comm_L.
             ++ iPureIntro.
                set_unfold. intros ? [|]; first naive_solver.
                subst.
                apply fin_to_nat_lt.
             ++ by iApply big_sepS_insert_2'.
  Qed.

  Lemma con_hash_init:
    {{{ True }}}
      init_hash #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ3 γ_lock, con_hash_inv f l hm γ1 γ3 γ_lock ∗
                                                  hash_set ∅ γ3
      }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iMod (ghost_map_alloc_empty) as (γ3) "H3".
    rewrite /init_hash.
    wp_pures.
    rewrite /con_hash_inv/abstract_con_hash_inv/abstract_con_hash/concrete_con_hash_inv/concrete_con_hash.
    rewrite /init_hash_state.
    wp_apply (wp_init_map with "[$]") as (l) "Hm".
    wp_pures.
    iMod (ghost_var_alloc ∅) as "[%γ2 [Hauth Hfrag]]".
    wp_apply (newlock_spec with "[Hm Hfrag]") as (loc γ_lock) "#Hl"; last first.
    - wp_pures. 
      iMod hv_auth_init as "[%γ1 Hv]".
      iMod (inv_alloc with "[Hauth Hv]") as "#Hinv"; last first.
      + rewrite /compute_con_hash. wp_pures.  iApply "HΦ". iFrame "Hinv Hl".
        rewrite /hash_set. rewrite gset_to_gmap_empty. iFrame. iModIntro.
        by iSplit. 
      + rewrite /compute_con_hash_specialized. iFrame. iNext. by iSplit. 
    - by iFrame.
  Qed.
  

  Lemma con_hash_alloc_tape f l hm γ1 γ3 γ_lock:
    {{{ con_hash_inv f l hm γ1 γ3 γ_lock }}}
      allocate_tape #()
      {{{ (α: val), RET α; hash_tape α [] γ3 }}}.
  Proof.
    rewrite /hash_tape.
    iIntros (Φ) "_ HΦ".
    rewrite /allocate_tape.
    wp_pures.
    wp_apply (rand_allocate_tape_spec with "[//]") as (v) "?".
    iApply "HΦ".
    by iFrame.
  Qed.

  Lemma con_hash_spec f l hm γ1 γ3 γlock α n ns (v:nat):
    {{{ con_hash_inv f l hm γ1 γ3 γlock ∗ hash_tape α (n::ns) γ3 }}}
      f #v α
      {{{ (res:nat), RET (#res);  con_hash_view v res γ1 γ3 ∗
                                (hash_tape α ns γ3 ∗ ⌜res=n⌝ ∨
                                 hash_tape α (n::ns) γ3
                                )
      }}}.
  Proof.
    rewrite /con_hash_inv/hash_tape.
    iIntros (Φ) "[[%γ2 #[Hab Hcon]] [Ht #Hfrag1]] HΦ".
    iApply pgl_wp_fupd.
    iApply fupd_pgl_wp.
    iInv "Hab" as ">(%&->&H1&H2)" "Hclose".
    iMod ("Hclose" with "[$H1 $H2]") as "_"; first done.
    iModIntro.
    rewrite /compute_con_hash_specialized.
    wp_pures.
    wp_apply (acquire_spec with "Hcon") as "[Hl[% (%&->&Hm&Hfrag)]]".
    wp_pures.
    rewrite /compute_hash.
    wp_pures.
    wp_apply (wp_get with "[$]") as (res) "[Hm ->]".
    rewrite lookup_fmap.
    destruct (_!!_) eqn:Hres; simpl.
    - (* hashed before *)
      wp_pures.
      iApply fupd_pgl_wp.
      iInv "Hab" as ">(%&->&H1&H2&#Hfrag2)" "Hclose".
      iDestruct (ghost_var_agree with "[$][$]") as "->".
      iDestruct (hv_auth_duplicate_frag with "[$]") as "[H1 Hfrag']"; first done.
      iMod ("Hclose" with "[$H1 $H2]") as "_"; first by iSplit.
      iModIntro.
      wp_apply (release_spec with "[$Hl $Hcon $Hfrag $Hm]") as "_"; first done.
      wp_pures.
      iModIntro. iApply "HΦ".
      iFrame.
      iSplit.
      + by iDestruct (big_sepM_lookup with "[$]") as "?".
      + iRight. by iFrame. 
    - wp_pures.
      rewrite /hash_tape.
      wp_apply (rand_tape_spec_some with "[$]") as "Ht".
      wp_pures.
      wp_apply (wp_set with "[$]") as "Hm".
      iApply fupd_pgl_wp.
      iInv "Hab" as ">(%&->&H1&H2& #Hfrag2)" "Hclose".
      iDestruct (ghost_var_agree with "[$][$]") as "->".
      iMod (ghost_var_update _ (<[v:=n]> _) with "[$][$]") as "[H2 Hfrag]".
      iMod (hv_auth_insert with "[$]") as "[H1 Hfrag']"; first done.
      iMod ("Hclose" with "[$H1 $H2]") as "_".
      { iSplit; first done.
        iNext. rewrite big_sepM_insert; last done.
        iFrame "Hfrag2".
        by iDestruct "Hfrag1" as "[??]".
      }
      iModIntro.
      wp_pures.
      wp_apply (release_spec with "[$Hl $Hcon $Hfrag Hm]") as "_".
      { iExists _. iSplit; first done. by rewrite fmap_insert. }
      wp_pures.
      iApply "HΦ".
      iFrame. iModIntro.
      iDestruct "Hfrag1" as "[??]".
      iSplit; first done.
      iLeft. iFrame. by iSplit.
  Qed.

  Lemma con_hash_spec_hashed_before f l hm γ1 γ3 γlock α ns res (v:nat):
    {{{ con_hash_inv f l hm γ1 γ3 γlock ∗ hash_tape α ns γ3 ∗ con_hash_view v res γ1 γ3 }}}
      f #v α
      {{{ RET (#res);  con_hash_view v res γ1 γ3 ∗
                       (hash_tape α ns γ3 )
      }}}.
  Proof.
    iIntros (Φ) "[[%γ2 [#Hab #Hcon]][Ht #[Hfragv Hfragv']]] HΦ".
    rewrite /abstract_con_hash_inv/concrete_con_hash_inv.
    iApply fupd_pgl_wp.
    iInv "Hab" as ">(%&->&H1&H2)" "Hclose".
    iMod ("Hclose" with "[$H1 $H2]") as "_"; first done.
    iModIntro.
    rewrite /compute_con_hash_specialized.
    wp_pures.
    wp_apply (acquire_spec with "Hcon") as "[Hl[% (%&->&Hm&Hfrag)]]".
    wp_pures.
    rewrite /compute_hash.
    wp_pures.
    wp_apply (wp_get with "[$]") as (res') "[Hm ->]".
    rewrite lookup_fmap.
    destruct (_!!_) eqn:Hres; simpl.
    - (* hashed before *)
      wp_pures.
      iApply fupd_pgl_wp.
      iInv "Hab" as ">(%&->&H1&H2&#Hfrag')" "Hclose".
      iDestruct (ghost_var_agree with "[$][$]") as "->".
      iDestruct (hv_auth_frag_agree with "[$]") as "%H".
      rewrite Hres in H. simplify_eq.
      iMod ("Hclose" with "[$H1 $H2]") as "_"; first by iSplit.
      iModIntro.
      wp_apply (release_spec with "[$Hl $Hcon $Hfrag $Hm]") as "_"; first done.
      wp_pures. iModIntro.
      iApply "HΦ".
      iFrame. rewrite /con_hash_view. iFrame "Hfragv Hfragv'". 
    - iApply fupd_pgl_wp.
      iInv "Hab" as ">(%&->&H1&H2&#?)" "Hclose".
      iDestruct (ghost_var_agree with "[$][$]") as "->".
      iDestruct (hv_auth_frag_agree with "[$]") as "%H". simplify_eq.
  Qed.

  Program Definition con_hash_impl1 : con_hash1 val_size :=
    {| init_hash1:=init_hash;
      allocate_tape1:=allocate_tape;
      compute_hash1:=compute_hash;

      hash_view_gname:=_;
      hash_lock_gname:=_;
      con_hash_inv1 := con_hash_inv;
      hash_tape1:=hash_tape;
      con_hash_view1:=con_hash_view;
      con_hash_presample1 := con_hash_presample;
      con_hash_init1 := con_hash_init;
      con_hash_alloc_tape1 := con_hash_alloc_tape;
      con_hash_spec1 := con_hash_spec;
      con_hash_spec_hashed_before1 := con_hash_spec_hashed_before                
    |}
  .
  Next Obligation.
    rewrite /con_hash_view.
    iIntros (?????) "[??][??]".
    by iDestruct (hv_frag_frag_agree with "[$][$]") as "->".
  Qed.
  Next Obligation.
    iIntros.
    by iApply con_hash_view_in_hash_set.
  Qed.
  Next Obligation.
    iIntros (????) "[??]?".
    by iApply (tape_in_hash_set with "[$]").
  Qed.
  Next Obligation.
    iIntros (???) "[??]".
    by iApply rand_tapes_valid.
  Qed.
  
End con_hash_impl1.
