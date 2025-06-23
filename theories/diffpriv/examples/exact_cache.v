From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list map.

Section xcache.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  (* SPEC: If M is ε-dp, then exact_cache M qs is kε-dp where k = |unique(qs)|. *)
  Definition exact_cache : val :=
    λ:"M" "qs" "db",
      let: "cache" := init_map #() in
      list_fold
        (λ: "acc" "q",
          match: get "cache" "q" with
          | SOME "v" => list_cons "v" "acc"
          | NONE =>
              let: "v" := "M" "q" "db" in
              set "cache" "q" "v" ;;
              list_cons "v" "acc"
          end)
        list_nil "qs".

  (* Given a set of queries qs and a ε-dp mechanism M, xcache M QS is kε-dp where k=|qs|.

    To enable caching we need decidable equality on the type of queries, so
    we'll just work with integers (think of this as the Gödel encoding of the
    query program, or as the serialization of the SQL query...).

    Invariant:

    We have ↯ (k - |cache|) ε error credits.

    If q ∈ cache
    then we get the same value in both programs directly,
    else
         we pay ↯ε to make sure that the call to M qi produces the same result
         in the left and right programs, keeping the cache always synchronised.

    NB: No assumption about the sensitivity of qs is made; this is encompassed
    by the premise that for each q ∈ qs, (M q) is ε-dipr. In practice, M may
    well decode q into a sensitive query function and add noise to the result
    of the query to achieve this privacy guarantee.

   *)

  Definition exact_cache_body {DB} {dDB : Distance DB} (M : val) (db : DB) (cache_loc : loc) : expr :=
    ((λ: "acc" "q",
        match: get #cache_loc "q" with
          InjL <> =>
            let: "v" := M "q" (inject db) in
            set #cache_loc "q" "v";; list_cons "v" "acc"
        | InjR "v" => list_cons "v" "acc"
        end)%V).

  Lemma exact_cache_dipr (M : val) DB (dDB : Distance DB) (qs : list nat) (QS : val) (is_qs : is_list qs QS)
    ε δ (εpos : 0 <= ε) (δpos : 0 <= δ)
    (M_dipr : Forall (λ q : nat, ⊢ hoare_diffpriv (M #q) ε δ dDB) qs)
    :
    let k := size ((list_to_set qs) : gset _) in
    ⊢ hoare_diffpriv (exact_cache M QS) (k*ε) (k*δ) dDB.
  Proof with (tp_pures ; wp_pures).
    iIntros (k K c db db' adj φ) "!> [rhs ε] hφ".
    rewrite {2}/exact_cache...
    wp_apply wp_init_map => // ; iIntros (cache_l) "cache_l"...
    rewrite /exact_cache...
    tp_bind (init_map _).
    iMod (spec_init_map with "rhs") as "(%cache_r & rhs & cache_r)" => /=...
    rewrite -!/(exact_cache_body _ _ _).

    revert qs QS is_qs k M_dipr.
    cut
      (∀ (qs : list nat)
         (qs_pre qs' : list nat) (QS' : val)
         (acc : val) cache_map,
          qs = qs_pre ++ qs' →
          dom cache_map = list_to_set qs_pre →
          dom cache_map ∪ list_to_set qs' = list_to_set qs →
          is_list qs' QS' →
          Forall (λ q : nat, ⊢ hoare_diffpriv (M #q) ε δ dDB) qs →
          let k := size (list_to_set qs : gset nat) in
          let k' := size cache_map in
          {{{
                ↯m (c * ((k - k') * ε)) ∗ ↯ (c * ((k - k') * δ))
                ∗ ⤇ fill K (list_fold (exact_cache_body M db' cache_r) acc QS')
                ∗ map_list cache_l cache_map
                ∗ map_slist cache_r cache_map
          }}}
            list_fold (exact_cache_body M db cache_l) acc QS'
            {{{ vl, RET vl ; ∃ (vr : val), ⤇ fill K vr ∗ ⌜vl = vr⌝ }}}
      ).
    {
      intros h. intros. iApply (h qs [] qs QS _ ∅ with "[-hφ]") => //.
      1: set_solver.
      2: iNext ; iIntros (?) "(% & ? & ->)" ; iApply "hφ" => //.
      iFrame. rewrite map_size_empty. rewrite Rminus_0_r. subst k. simpl. iFrame.
    }
    clear φ.
    iLöb as "IH".
    iIntros (qs qs_pre qs' QS' acc cache qs_pre_qs' dom_cache_pre dom_cache_qs'_qs is_qs'
               M_dipr φ) "(ε & δ & rhs & cache_l & cache_r) hφ".
    set (k := size (list_to_set qs : gset nat)).
    set (k' := size cache).
    rewrite {4}/exact_cache_body/list_fold... rewrite -!/(exact_cache_body _ _ _) -/list_fold.
    destruct qs' as [|q' qs''] eqn:qs'_qs''.
    1:{ rewrite is_qs'. rewrite {3}/exact_cache_body/list_fold... iApply "hφ". iExists _. iFrame => //. }
    rewrite {3}/exact_cache_body/list_fold... rewrite -!/(exact_cache_body _ _ _) -/list_fold.
    destruct is_qs' as (QS'' & -> & is_qs'')...
    wp_apply (wp_get with "cache_l"). iIntros (?) "[cache_l ->]".
    tp_bind (get _ _). iMod (spec_get with "cache_r rhs") as "[rhs cache_r]" => /=.
    rewrite -!/(exact_cache_body _ _ _) -/list_fold.
    rewrite qs_pre_qs' in M_dipr.
    destruct ((proj1 (List.Forall_app _ _ _)) M_dipr) as [M_dipr_qs_pre M_dipr_qs'].
    destruct (Forall_cons_1 _ _ _ M_dipr_qs') as [M_dipr_q' M_dipr_qs''].
    assert (0 <= dDB db db') by apply distance_pos.
    destruct (cache !! q') eqn:cache_q' => /=.
    - opose proof (elem_of_dom_2 _ _ _ cache_q') as h...
      rewrite /list_cons. do 7 wp_pure.
      do 7 tp_pure.
      rewrite -!/(exact_cache_body _ _ _) -/list_fold.
      iSpecialize ("IH" $! qs (qs_pre ++ [q']) qs'' QS'' (InjRV (v, acc)) cache).
      unshelve iApply ("IH" $! _ _ _ _ _ _ with "[$ε $δ $rhs $cache_l $cache_r]") => //.
      1: subst ; by rewrite cons_middle assoc.
      all: subst ; assumption || set_solver.
    - opose proof (not_elem_of_dom_2 _ _ cache_q') as h...
      tp_bind (M _ _).
      wp_bind (M _ _).
      assert ((c * ((k - k') * ε)) = (c * (k - (k'+1)) * ε + c * ε)) as -> by lra.
      assert ((c * ((k - k') * δ)) = (c * (k - (k'+1)) * δ + c * δ)) as -> by lra.
      assert (0 <= k - (k' + 1)).
      {
        subst. subst k k'. apply Rle_0_le_minus.
        rewrite -dom_cache_qs'_qs.
        replace (size cache) with (size (dom cache)) by apply size_dom.
        rewrite dom_cache_pre.
        replace 1 with (INR 1) by auto.
        replace 1%nat with (size (list_to_set [q'] : gset nat)).
        2:{ cbn. rewrite union_empty_r_L. apply size_singleton. }
        rewrite -plus_INR.
        rewrite -size_union.
        2: set_solver.
        rewrite (list_to_set_cons _ qs''). simpl.
        apply le_INR.
        apply subseteq_size. set_solver.
      }
      iDestruct (ecm_split with "ε") as "[kε ε]".
      2: real_solver. 1: repeat real_solver_partial => //.
      iDestruct (ec_split with "δ") as "[kδ δ]".
      2: real_solver. 1: repeat real_solver_partial => //.
      iApply (M_dipr_q' with "[] [rhs ε δ]") => // ; iFrame.
      iNext. iIntros (vq') "rhs" => /=...
      tp_bind (set _ _ _).
      iMod (spec_set with "cache_r rhs") as "[rhs cache_r]".
      wp_apply (wp_set with "cache_l") ; iIntros "cache_l"...
      rewrite /list_cons. wp_pure. wp_pure. wp_pure. wp_pure. wp_pure. wp_pure. wp_pure.
      simpl. do 7 tp_pure.
      tp_pure. tp_pure.
      iSpecialize ("IH" $! qs (qs_pre ++ [q']) qs'' QS'' (InjRV (vq', acc)) _).
      iSpecialize ("IH" $! _ _ _ _ _ _ with "[kε kδ $rhs $cache_l $cache_r]") => //.
      2: iApply "IH" => //.
      iSplitL "kε".
      + iApply ecm_eq. 2: iFrame. real_solver_partial.
        subst k. simpl. subst k'.
        replace (INR $ size (<[q' := vq']> cache)) with (size cache + 1).
        1: done.
        rewrite map_size_insert_None => //. qify_r ; zify_q. lia.
      + iApply ec_eq. 2: iFrame. real_solver_partial.
        subst k. simpl. subst k'.
        replace (INR $ size (<[q' := vq']> cache)) with (size cache + 1).
        1: done.
        rewrite map_size_insert_None => //. qify_r ; zify_q. lia.
        Unshelve.
        1: subst ; by rewrite cons_middle assoc.
        all: subst ; assumption || set_solver.
  Qed.

  (* TODO instantiate exact_cache with a mechanism *)


  Definition online_xcache : val :=
    λ:"M" "db",
      let: "cache" := init_map #() in
      (λ: "q",
         match: get "cache" "q" with
         | SOME "v" => "v"
         | NONE =>
             let: "v" := "M" "q" "db" in
             set "cache" "q" "v" ;;
             "v"
          end).

  (* pay as you go, cache map exposed, M only needs to be private on the queries it gets executed on *)
  Lemma oxc_spec0 (M : val) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K :
    ⤇ fill K (online_xcache M (Val (inject db')))
    ⊢ WP online_xcache M (Val (inject db))
        {{ f, ∃ f', ⤇ fill K (Val f') ∗
              ∃ (F : gmap nat val → iProp Σ),
              F ∅ ∗
              (∀ (q : nat) A K,
                  ⌜q ∈ dom A⌝ -∗
                  F(A) -∗
                  ⤇ fill K (Val f' #q) -∗
                  WP (Val f) #q {{ v, F(A) ∗ ⤇ fill K (Val v) ∗  ⌜A !! q = Some v⌝ }}) ∗
              (∀ (q : nat) A ε δ K,
                  ⌜q ∉ dom A⌝ -∗
                  wp_diffpriv (M #q) ε δ dDB -∗
                  ↯m ε -∗
                  ↯ δ -∗
                  F(A) -∗
                  ⤇ fill K (Val f' #q) -∗
                  WP (Val f) #q {{ v, F( <[q := v]> A) ∗ ⤇ fill K (Val v) ∗ ⌜<[q := v]> A !! q = Some v⌝ }})
        }}.
  Proof.
    iIntros "rhs".
    rewrite /online_xcache. wp_pures.
    tp_pures. tp_bind (init_map _). iMod (spec_init_map with "rhs") as "[%cache_r [rhs cache_r]]".
    simpl. tp_pures.
    wp_apply wp_init_map => //. iIntros (cache_l) "?". wp_pures.

    iModIntro. iExists _. simpl. iFrame "rhs".

    iExists (λ A, map_list cache_l A ∗ map_slist cache_r A)%I.
    iFrame.
    iSplitR.
    - iIntros (??? cached) "[cache_l cache_r] rhs". tp_pures. wp_pures.
      tp_bind (get _ _).
      iMod (spec_get with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_get with "cache_l") ; iIntros (vq) "[cache_l %hvq]".
      simpl. subst.
      apply elem_of_dom in cached. rewrite /opt_to_val.
      destruct cached as [vq hvq]. rewrite hvq.
      tp_pures. wp_pures. iFrame. done.
    - iIntros (????? cached) "M_dipr ε δ [cache_l cache_r] rhs". tp_pures. wp_pures.
      tp_bind (get _ _).
      iMod (spec_get with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_get with "cache_l") ; iIntros (vq) "[cache_l %hvq]".
      simpl. subst.
      apply not_elem_of_dom_1 in cached. rewrite /opt_to_val.
      rewrite !cached. tp_pures ; wp_pures.
      tp_bind (M _ _). wp_bind (M _ _).
      rewrite /wp_diffpriv. iSpecialize ("M_dipr" $! _ 1 db db' adj).
      rewrite !Rmult_1_l.
      iSpecialize ("M_dipr" with "[$rhs $ε $δ]").
      iPoseProof (wp_frame_l with "[cache_r $M_dipr]") as "M_dipr". 1: iAssumption.
      iPoseProof (wp_frame_l with "[cache_l $M_dipr]") as "M_dipr". 1: iAssumption.
      iApply (wp_mono with "M_dipr").
      iIntros (vq) "[cache_l [cache_r rhs]]" => /=.
      tp_pures. wp_pures. tp_bind (set _ _ _). iMod (spec_set with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_set with "cache_l") ; iIntros "cache_l".
      simpl. tp_pures. wp_pures. iFrame. iPureIntro. by rewrite lookup_insert.
  Qed.

  (* F can store error credits ; could also ask for N*ε error credits upfront and hand out F(∅, N) instead of F(∅, 0). *)
  Lemma oxc_spec1 (M : val) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K ε δ (εpos : 0 <= ε) (δpos : 0 <= δ) :
    (∀ q : nat, hoare_diffpriv (M #q) ε δ dDB) ∗
    ⤇ fill K (online_xcache M (Val (inject db')))
    ⊢ WP online_xcache M (Val (inject db))
        {{ f, ∃ f', ⤇ fill K (Val f') ∗
              ∃ (F : gmap nat val * nat → iProp Σ),
              F (∅, 0%nat) ∗
              (∀ A k, ↯m ε ∗ ↯ δ ∗ F(A, k) -∗ F(A, S k)) ∗
              (∀ (q : nat) A K (N : nat),
                  ⌜q ∈ dom A⌝ -∗
                  F(A, N) -∗
                  ⤇ fill K (Val f' #q) -∗
                  WP (Val f) #q {{ v, F(A, N) ∗ ⤇ fill K (Val v) ∗  ⌜A !! q = Some v⌝ }}) ∗
              (∀ (q : nat) A K (N : nat),
                  ⌜q ∉ dom A⌝ -∗
                  F(A, S N) -∗
                  ⤇ fill K (Val f' #q) -∗
                  WP (Val f) #q {{ v, F( <[q := v]> A, N) ∗ ⤇ fill K (Val v) ∗ ⌜<[q := v]> A !! q = Some v⌝ }})
        }}.
  Proof.
    iIntros "(#M_dipr & rhs)".
    unshelve iPoseProof (oxc_spec0 with "[rhs]") as "spec0" => //.
    iMod ecm_zero as "ε0".
    iMod ec_zero as "δ0".
    iPoseProof (wp_frame_l with "[ε0 δ0 $spec0]") as "spec0". 1: iApply (combine_sep_as with "[ε0 δ0]").
    2: iSplitR "δ0". 2: iApply "ε0". 2: iApply "δ0". 1: done.
    iPoseProof (wp_frame_l with "[M_dipr $spec0]") as "spec0". 1: iApply "M_dipr".
    iApply (wp_mono with "spec0").
    iIntros "%f (#M_dipr & (ε0 & δ0) & %f' & rhs & (%F & F0 & f_cached & f_fresh))".
    iExists f'. iFrame "rhs".
    iExists (λ Ak : gmap nat val * nat, let (A, k) := Ak in F A ∗ ↯m (k * ε) ∗ ↯ (k * δ))%I.
    rewrite !Rmult_0_l. iFrame "F0 ε0 δ0".
    iSplitR ; [|iSplitL "f_cached"].
    - iIntros (??) "(ε&δ&?&kε&kδ)". iFrame. iPoseProof (ecm_combine with "[ε kε]") as "ε" ; iFrame.
      iPoseProof (ec_combine with "[δ kδ]") as "δ" ; iFrame. iSplitL "ε".
      + iApply ecm_eq. 2: iFrame. replace (S k) with (k+1)%nat by lia. replace (INR (k+1)) with (k+1)%R.
        2: real_solver. lra.
      + iApply ec_eq. 2: iFrame. replace (S k) with (k+1)%nat by lia. replace (INR (k+1)) with (k+1)%R.
        2: real_solver. lra.
    - simpl. iIntros (?????) "[FA [ε δ]] rhs".
      iSpecialize ("f_cached" with "[] [$FA] [$rhs]") => //.
      iPoseProof (wp_frame_l with "[$f_cached ε δ]") as "f_cached".
      1: iApply (combine_sep_as with "[ε δ]").
      2: iSplitR "δ". 2: iApply "ε". 2: iApply "δ". 1: done.
      iApply (wp_mono with "f_cached"). iIntros (?) "((ε & δ) & FA & rhs & %)". iFrame => //.
    - iIntros (?????) "[FA [ε δ]] rhs".
      replace ((S N)) with (N + 1)%nat by lia. replace (INR (N+1)) with (N+1) by real_solver.
      rewrite !Rmult_plus_distr_r. rewrite !Rmult_1_l.
      iDestruct (ecm_split with "ε") as "[Nε ε]". 1,2: real_solver.
      iDestruct (ec_split with "δ") as "[Nδ δ]". 1,2: real_solver.
      iSpecialize ("f_fresh" with "[] [] [$ε] [$δ] [$FA] [$rhs]") => //.
      { iIntros (?????) "[??]". iApply ("M_dipr" with "[] [-]") => //. 2: iNext ; iIntros => //.
        iFrame. }
      iPoseProof (wp_frame_l with "[$f_fresh Nε Nδ]") as "f_fresh".
      1: iApply (combine_sep_as with "[Nε Nδ]").
      2: iSplitR "Nδ". 2: iApply "Nε". 2: iApply "Nδ". 1: done.
      iApply (wp_mono with "f_fresh"). iIntros (?) "((ε & δ) & FA & rhs & %)". iFrame => //.
  Qed.


  (* TODO define the original exact_cache as a client of the online spec (keeping the direct def.) *)
  (* TODO prove exact_cache_dipr from the online spec *)


  (* Does it make sense to store f' (the result of the rhs) in F? Probably not. *)
  Lemma oxc_spec2 (M : val) `(dDB : Distance DB) (db db' : DB) (adj : dDB db db' <= 1) K ε δ :
    (∀ q : nat, hoare_diffpriv (M #q) ε δ dDB) ∗
    ⤇ fill K (online_xcache M (Val (inject db')))
    ⊢ WP online_xcache M (Val (inject db))
        {{ f,
              ∃ f' (F : gmap nat val * nat * bool → iProp Σ),
              F (∅, 0%nat, true) ∗
              (∀ A k b, ↯m ε ∗ ↯ δ ∗ F(A, k, b) -∗ F(A, S k, b)) ∗
              (∀ A k, F(A, k, true) -∗ F(A, k, false) ∗ ∃ K, ⤇ fill K (Val f')) ∗
              (∀ A k K, F(A, k, false) ∗ ⤇ fill K (Val f') -∗ F(A, k, true)) ∗
              (∀ (q : nat) A (N : nat),
                  ⌜q ∈ dom A⌝ -∗
                  F(A, N, true) -∗
                  WP (Val f) #q {{ v, F(A, N, true) ∗  ⌜A !! q = Some v⌝ }}) ∗
              (∀ (q : nat) A ε δ (N : nat),
                  ⌜q ∉ dom A⌝ -∗
                  ↯m ε -∗
                  ↯ δ -∗
                  F(A, S N, true) -∗
                  WP (Val f) #q {{ v, F( <[q := v]> A, N, true) ∗ ⌜<[q := v]> A !! q = Some v⌝ }})
        }}.
  Proof.
  Admitted.

  (* some ideas for online specs:

     { ↯ (c*ε) ∗ bigSep c-times (∀ q, (M q) is ε-dipr) }
       online_xcache M c
     { f . ∃ (F : gmap(Query,val) * nat → iProp),
           F(∅, c) ∗
           ∀ q A k, q ∈ A → { F(A, k) } f q { v ∗ F(A, k) } ∗
           ∀ q A k, q ∉ A → { F(A, S k) } f q { v ∗ F(A ∪ {q}, k) }
     }

     or alternatively:

     { □ ∀ q, (M q) is ε-dipr }
       online_xcache M c
     { f .
         F(∅, c) ∗
         ∀ q A k, q ∈ A → { F(A, k) } f q { v ∗ F(A, k) } ∗
         ∀ q A k, q ∉ A → { ↯ ε ∗ F(A, S k) } f q { v ∗ F(A ∪ {q}, k) }
     }

     or even:

     {  }
       online_xcache M c
     { f .
         F(∅, c) ∗
         ( ∀ A k, ↯ ε ∗ F(A, k) -∗ F(A, S k) )
         ∀ q A k, q ∈ A → { F(A, k) } f q { v ∗ F(A, k) } ∗
         ∀ q A k, q ∉ A → { (M q) is ε-dipr ∗ F(A, S k) } f q { v ∗ F(A ∪ {q}, k) }
     }

     or even:

     {  }
       online_xcache M
     { f .
         F(∅) ∗
         ∀ q A k, q ∈ A → { F(A) } f q { v ∗ F(A) } ∗
         ∀ q A k, q ∉ A → { (M q) is ε-dipr ∗ ↯ ε ∗ F(A) } f q { v ∗ F(A ∪ {q}) }
     }

   *)

End xcache.
