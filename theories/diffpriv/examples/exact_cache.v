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
    ε (εpos : 0 <= ε)
    (M_dipr : Forall (λ q : nat, wp_diffpriv (M #q) ε dDB) qs)
    :
    let k := size ((list_to_set qs) : gset _) in
    wp_diffpriv (exact_cache M QS) (k*ε) dDB.
  Proof with (tp_pures ; wp_pures).
    iIntros (k K c db db' adj φ) "[rhs ε] hφ".
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
          Forall (λ q : nat, wp_diffpriv (M #q) ε dDB) qs →
          let k := size (list_to_set qs : gset nat) in
          let k' := size cache_map in
          {{{
                ↯ (c * ((k - k') * ε))
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
               M_dipr φ) "(ε & rhs & cache_l & cache_r) hφ".
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
      unshelve iApply ("IH" $! _ _ _ _ _ _ with "[ε $rhs $cache_l $cache_r]") => //.
      1: subst ; by rewrite cons_middle assoc.
      all: subst ; assumption || set_solver.
    - opose proof (not_elem_of_dom_2 _ _ cache_q') as h...
      tp_bind (M _ _).
      wp_bind (M _ _).
      assert ((c * ((k - k') * ε)) = (c * (k - (k'+1)) * ε + c * ε)) as -> by lra.
      iDestruct (ec_split with "ε") as "[kε ε]".
      2: real_solver. 1: repeat real_solver_partial => //.
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
      iApply (M_dipr_q' with "[rhs ε]") => // ; iFrame.
      iNext. iIntros (vq') "rhs" => /=...
      tp_bind (set _ _ _).
      iMod (spec_set with "cache_r rhs") as "[rhs cache_r]".
      wp_apply (wp_set with "cache_l") ; iIntros "cache_l"...
      rewrite /list_cons. wp_pure. wp_pure. wp_pure. wp_pure. wp_pure. wp_pure. wp_pure.
      simpl. do 7 tp_pure.
      tp_pure. tp_pure.
      iSpecialize ("IH" $! qs (qs_pre ++ [q']) qs'' QS'' (InjRV (vq', acc)) _).
      iSpecialize ("IH" $! _ _ _ _ _ _ with "[kε $rhs $cache_l $cache_r]") => //.
      2: iApply "IH" => //.
      iApply ec_eq. 2: iFrame. real_solver_partial.
      subst k. simpl. subst k'.
      replace (INR $ size (<[q' := vq']> cache)) with (size cache + 1).
      1: done.
      rewrite map_size_insert_None => //. qify_r ; zify_q. lia.
      Unshelve.
      1: subst ; by rewrite cons_middle assoc.
      all: subst ; assumption || set_solver.
  Qed.


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

  (* online spec:

     { ↯ (c*ε) ∗ bigSep c-times (∀ q, (M q) is ε-dipr) }
       mk_cache M c
     { f .
         F(∅, c) ∗
         ∀ q A k, q ∈ A → { F(A, k) } f q { v ∗ F(A, k) } ∗
         ∀ q A k, q ∉ A → { F(A, S k) } f q { v ∗ F(A ∪ {q}, k) }
     }

     or alternatively:

     { □ ∀ q, (M q) is ε-dipr }
       mk_cache M c
     { f .
         F(∅, c) ∗
         ∀ q A k, q ∈ A → { F(A, k) } f q { v ∗ F(A, k) } ∗
         ∀ q A k, q ∉ A → { ↯ ε ∗ F(A, S k) } f q { v ∗ F(A ∪ {q}, k) }
     }

     or even:

     {  }
       mk_cache M c
     { f .
         F(∅, c) ∗
         ∀ q A k, q ∈ A → { F(A, k) } f q { v ∗ F(A, k) } ∗
         ∀ q A k, q ∉ A → { (M q) is ε-dipr ∗ ↯ ε ∗ F(A, S k) } f q { v ∗ F(A ∪ {q}, k) }
     }

   *)

End xcache.
