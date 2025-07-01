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


  (* we can define the original exact_cache as a client of the online spec (keeping the direct def.) *)
  Definition exact_cache_offline : val :=
    λ:"M" "qs" "db",
      let: "oXC" := online_xcache "M" "db" in
      list_fold (λ: "acc" "q", list_cons ("oXC" "q") "acc") list_nil "qs".

  (* same but with list_map *)
  Definition exact_cache_offline_map : val :=
    λ:"M" "qs" "db",
      let: "oXC" := online_xcache "M" "db" in
      list_map "oXC" "qs".

  Definition oxc_spec0_cached (f f' : val) (F : gmap nat val → iProp Σ) : iProp Σ :=
    (∀ (q : nat) A K,
          ⌜q ∈ dom A⌝ -∗
          F(A) -∗
          ⤇ fill K (Val f' #q) -∗
          WP (Val f) #q {{ v, F(A) ∗ ⤇ fill K (Val v) ∗  ⌜A !! q = Some v⌝ }}).

  Definition oxc_spec0_fresh (M : val) c `(dDB : Distance DB) (f f' : val) (F : gmap nat val → iProp Σ) : iProp Σ :=
    (∀ (q : nat) A ε δ K,
          ⌜q ∉ dom A⌝ -∗
          wp_diffpriv (M #q) ε δ dDB -∗
          ↯m (c * ε) -∗
          ↯ (c * δ) -∗
          F(A) -∗
          ⤇ fill K (Val f' #q) -∗
          WP (Val f) #q {{ v, F( <[q := v]> A) ∗ ⤇ fill K (Val v) ∗ ⌜<[q := v]> A !! q = Some v⌝ }}).

  (* pay as you go, cache map exposed, M only needs to be private on the queries it gets executed on *)
  Lemma oxc_spec0 (M : val) `(dDB : Distance DB) (db db' : DB) c (adj : dDB db db' <= c) K :
    ⤇ fill K (online_xcache M (Val (inject db')))
    ⊢ WP online_xcache M (Val (inject db))
        {{ f, ∃ f', ⤇ fill K (Val f') ∗
              ∃ (F : gmap nat val → iProp Σ),
              F ∅ ∗
              □ oxc_spec0_cached f f' F ∗
              □ oxc_spec0_fresh M c dDB f f' F
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
    - iIntros "!>" (??? cached) "[cache_l cache_r] rhs". tp_pures. wp_pures.
      tp_bind (get _ _).
      iMod (spec_get with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_get with "cache_l") ; iIntros (vq) "[cache_l %hvq]".
      simpl. subst.
      apply elem_of_dom in cached. rewrite /opt_to_val.
      destruct cached as [vq hvq]. rewrite hvq.
      tp_pures. wp_pures. iFrame. done.
    - iIntros "!>" (????? cached) "M_dipr ε δ [cache_l cache_r] rhs". tp_pures. wp_pures.
      tp_bind (get _ _).
      iMod (spec_get with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_get with "cache_l") ; iIntros (vq) "[cache_l %hvq]".
      simpl. subst.
      apply not_elem_of_dom_1 in cached. rewrite /opt_to_val.
      rewrite !cached. tp_pures ; wp_pures.
      tp_bind (M _ _). wp_bind (M _ _).
      rewrite /wp_diffpriv. iSpecialize ("M_dipr" $! _ c db db' adj).
      iSpecialize ("M_dipr" with "[$rhs $ε $δ]").
      iPoseProof (wp_frame_l with "[cache_r $M_dipr]") as "M_dipr". 1: iAssumption.
      iPoseProof (wp_frame_l with "[cache_l $M_dipr]") as "M_dipr". 1: iAssumption.
      iApply (wp_mono with "M_dipr").
      iIntros (vq) "[cache_l [cache_r rhs]]" => /=.
      tp_pures. wp_pures. tp_bind (set _ _ _). iMod (spec_set with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_set with "cache_l") ; iIntros "cache_l".
      simpl. tp_pures. wp_pures. iFrame. iPureIntro. by rewrite lookup_insert.
  Qed.

  Definition oxc_spec0_pw_cached (f f' : val) (G : gmap nat val → gmap nat val → iProp Σ) : iProp Σ :=
    (∀ (q : nat) B B' K,
          ⌜q ∈ dom B⌝ -∗
          ⌜q ∈ dom B'⌝ -∗
          G B B' -∗
          ⤇ fill K (Val f' #q) -∗
          WP (Val f) #q {{ v, ∃ v' : val, G B B' ∗ ⤇ fill K (Val v') ∗
                                          ⌜B !! q = Some v⌝ ∗ ⌜B' !! q = Some v'⌝ ∗
                                          ⌜B = B' → v = v'⌝ }}).

  Definition oxc_spec0_pw_fresh (M : val) c `(dDB : Distance DB) (f f' : val) (F : gmap nat val → iProp Σ)
    (G : gmap nat val → gmap nat val → iProp Σ)
    : iProp Σ :=
    (∀ (q : nat) B B' ε δ K,
        ⌜q ∉ dom B⌝ -∗
        ⌜q ∉ dom B'⌝ -∗
        wp_diffpriv_pw (M #q) ε δ dDB -∗
        ↯m (c * ε) -∗
        ↯ (c * δ) -∗
        G B B' -∗
        ⤇ fill K (Val f' #q) -∗
        ∀ RES,
          (* WP (Val f) #q {{ v, ∃ (v' : val) A', F A' ∗ ⤇ fill K (Val v') ∗ ⌜v = RES → (v' = RES ∧ A' = <[q := v]> A)⌝ }}). *)
          WP (Val f) #q {{ v, ∃ (v' : val),
                  G ((<[q := v]> B)) (<[q := v']> B') ∗
                  ⤇ fill K (Val v') ∗
                  (⌜v = RES ∧ B = B'⌝ -∗ G ((<[q := v]> B)) (<[q := v']> B') -∗ F (<[q := v]> B) ∗ ⌜(v' = RES)⌝) }}).
          (* WP (Val f) #q {{ v, ⌜v = RES⌝ -∗ F( <[q := v]> A) ∗ ⤇ fill K (Val v) ∗ ⌜<[q := v]> A !! q = Some v⌝ }}). *)

  (* pointwise equality variant *)
  Lemma oxc_spec0_pw (M : val) `(dDB : Distance DB) (db db' : DB) `(adj : dDB db db' <= c) K :
    ⤇ fill K (online_xcache M (Val (inject db')))
    ⊢ WP online_xcache M (Val (inject db))
        {{ f, ∃ f', ⤇ fill K (Val f') ∗
              ∃ (F : gmap nat val → iProp Σ) (G : gmap nat val → gmap nat val → iProp Σ),
              F ∅ ∗ □ (∀ A, F A ∗-∗ G A A) ∗
              □ oxc_spec0_pw_cached f f' G ∗
              □ oxc_spec0_pw_fresh M c dDB f f' F G
        }}.
  Proof.
    iIntros "rhs".
    rewrite /online_xcache. wp_pures.
    tp_pures. tp_bind (init_map _). iMod (spec_init_map with "rhs") as "[%cache_r [rhs cache_r]]".
    simpl. tp_pures.
    wp_apply wp_init_map => //. iIntros (cache_l) "?". wp_pures.

    iModIntro. iExists _. simpl. iFrame "rhs".

    iExists (λ A, map_list cache_l A ∗ map_slist cache_r A)%I.
    iExists (λ B B', map_list cache_l B ∗ map_slist cache_r B')%I.
    iFrame.
    repeat iSplitR.
    - iModIntro. iIntros. iSplit ; by iIntros.
    - iIntros "!>" (???? cached cached') "[cache_l cache_r] rhs". tp_pures. wp_pures.
      tp_bind (get _ _).
      iMod (spec_get with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_get with "cache_l") ; iIntros (vq) "[cache_l %hvq]".
      simpl. subst.
      apply elem_of_dom in cached, cached'. rewrite /opt_to_val.
      destruct cached as [vq hvq]. rewrite hvq.
      destruct cached' as [vq' hvq']. rewrite hvq'.
      tp_pures. wp_pures. iFrame. iModIntro ; iPureIntro ; intuition auto. simplify_eq. done.
    - iIntros "!>" (?????? cached cached') "M_dipr ε δ [cache_l cache_r] rhs %RES". tp_pures. wp_pures.
      tp_bind (get _ _).
      iMod (spec_get with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_get with "cache_l") ; iIntros (vq) "[cache_l %hvq]".
      simpl. subst.
      apply not_elem_of_dom_1 in cached, cached'. rewrite /opt_to_val.
      rewrite cached cached'. tp_pures ; wp_pures.
      tp_bind (M _ _). wp_bind (M _ _).
      rewrite /wp_diffpriv_pw. iSpecialize ("M_dipr" $! _ c db db' adj).
      (* rewrite !Rmult_1_l. *)
      iSpecialize ("M_dipr" with "[$rhs $ε $δ]").
      iSpecialize ("M_dipr" $! RES).
      iPoseProof (wp_frame_l with "[cache_r $M_dipr]") as "M_dipr". 1: iAssumption.
      iPoseProof (wp_frame_l with "[cache_l $M_dipr]") as "M_dipr". 1: iAssumption.
      iApply (wp_mono with "M_dipr").
      iIntros (vq) "[cache_l [cache_r rhs]]" => /=.
      iDestruct "rhs" as "(%v' & rhs & %pweq)".
      tp_pures. wp_pures. tp_bind (set _ _ _). iMod (spec_set with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_set with "cache_l") ; iIntros "cache_l".
      simpl. tp_pures. wp_pures. (* iExists v',(<[q:=vq]> A). *)
      iModIntro. iFrame. iIntros "[->->]". rewrite pweq //.
      iIntros "[F_l F_r]". iFrame. done.
      (* iFrame. iPureIntro. by rewrite lookup_insert. *)
  Qed.

  (* BEGIN TEMP COMMENT *)
  (* (* F can store error credits ; could also ask for N*ε error credits upfront and hand out F(∅, N) instead of F(∅, 0). *)
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
         iSpecialize ("f_fresh" with "[] [] [ε] [δ] [$FA] [$rhs]") => //.
         { iIntros (?????) "[??]". iApply ("M_dipr" with "[] [-]") => //. 2: iNext ; iIntros => //.
           iFrame. }
         1,2: rewrite Rmult_1_l => //.
         iPoseProof (wp_frame_l with "[$f_fresh Nε Nδ]") as "f_fresh".
         1: iApply (combine_sep_as with "[Nε Nδ]").
         2: iSplitR "Nδ". 2: iApply "Nε". 2: iApply "Nδ". 1: done.
         iApply (wp_mono with "f_fresh"). iIntros (?) "((ε & δ) & FA & rhs & %)". iFrame => //.
     Qed.

     (* we can prove exact_cache_dipr from the online spec *)
     Lemma exact_cache_dipr_offline (M : val) DB (dDB : Distance DB) (qs : list nat) (QS : val) (is_qs : is_list qs QS)
       ε δ (εpos : 0 <= ε) (δpos : 0 <= δ)
       (M_dipr : Forall (λ q : nat, ⊢ wp_diffpriv (M #q) ε δ dDB) qs)
       :
       let k := size ((list_to_set qs) : gset _) in
       ⊢ wp_diffpriv (exact_cache_offline M QS) (k*ε) (k*δ) dDB.
     Proof with (tp_pures ; wp_pures).
       iIntros (k K c db db' adj) "[rhs [ε δ]]".
       rewrite {2}/exact_cache_offline...
       rewrite /exact_cache_offline...
       tp_bind (online_xcache _ _). wp_bind (online_xcache _ _).
       iPoseProof (oxc_spec0 M _ _ _ _) as "oXC" => //.
       iSpecialize ("oXC" with "rhs").
       iApply (wp_strong_mono'' with "oXC").
       iIntros "%f (%f' & rhs & %F & F & #cached & #fresh) /="...
       set (exact_cache_offline_body (f : val) := (λ: "acc" "q", list_cons (f "q") "acc")%V).
       rewrite -!/(exact_cache_offline_body _).
       revert qs QS is_qs k M_dipr.
       cut
         (∀ (qs : list nat)
            (qs_pre qs' : list nat) (QS' : val)
            (acc : val) cache_map,
             qs = qs_pre ++ qs' →
             dom cache_map = list_to_set qs_pre →
             dom cache_map ∪ list_to_set qs' = list_to_set qs →
             is_list qs' QS' →
             Forall (λ q : nat, ⊢ wp_diffpriv (M #q) ε δ dDB) qs →
             let k := size (list_to_set qs : gset nat) in
             let k' := size cache_map in
             {{{
                   ↯m (c * ((k - k') * ε)) ∗ ↯ (c * ((k - k') * δ)) ∗
                   □ oxc_spec0_cached f f' F ∗
                   □ oxc_spec0_fresh M c dDB f f' F ∗
                   ⤇ fill K (list_fold (exact_cache_offline_body f') acc QS') ∗
                   F cache_map
             }}}
               list_fold (exact_cache_offline_body f) acc QS'
               {{{ vl, RET vl ; ∃ (vr : val), ⤇ fill K vr ∗ ⌜vl = vr⌝ }}}
         ).
       {
         intros h. intros. iApply (h qs [] qs QS _ ∅ with "[-]") => //.
         1: set_solver.
         2: iNext ; iIntros (?) "(% & ? & ->)" ; done.
         iFrame. rewrite map_size_empty. rewrite Rminus_0_r. subst k. simpl. iFrame.
         iSplit ; done.
       }
       iLöb as "IH".
       iIntros (qs qs_pre qs' QS' acc cache qs_pre_qs' dom_cache_pre dom_cache_qs'_qs is_qs'
                  M_dipr φ) "(ε & δ & #cached & #fresh & rhs & F) hφ".
       set (k := size (list_to_set qs : gset nat)).
       set (k' := size cache).
       rewrite {4}/exact_cache_offline_body/list_fold... rewrite -!/(exact_cache_offline_body _) -/list_fold.
       destruct qs' as [|q' qs''] eqn:qs'_qs''.
       1:{ rewrite is_qs'. rewrite {3}/exact_cache_offline_body/list_fold... iApply "hφ". iExists _. iFrame => //. }
       destruct is_qs' as (QS'' & -> & is_qs'')...
       rewrite -!/(exact_cache_offline_body _) -/list_fold.
       rewrite qs_pre_qs' in M_dipr.
       destruct ((proj1 (List.Forall_app _ _ _)) M_dipr) as [M_dipr_qs_pre M_dipr_qs'].
       destruct (Forall_cons_1 _ _ _ M_dipr_qs') as [M_dipr_q' M_dipr_qs''].
       assert (0 <= dDB db db') by apply distance_pos.
       destruct (cache !! q') eqn:cache_q' => /=.
       - opose proof (elem_of_dom_2 _ _ _ cache_q') as h...
         rewrite /exact_cache_offline_body...
         tp_bind (f' _) ; wp_bind (f _).
         iCombine "cached" as "h".
         iSpecialize ("h" $! q' cache _ h with "F rhs").
         iApply (wp_strong_mono'' with "h").
         iIntros "/= %v' (F & rhs & %cache_q'')".
         assert (v = v') as <-. { rewrite cache_q' in cache_q''. inversion cache_q''. done. }
         rewrite /list_cons...
         rewrite -!/(exact_cache_offline_body _) -/list_fold.
         iSpecialize ("IH" $! qs (qs_pre ++ [q']) qs'' QS'' (InjRV (v, acc)) cache).
         unshelve iApply ("IH" $! _ _ _ _ _ _ with "[ε δ rhs F]") => //.
         1: subst ; by rewrite cons_middle assoc.
         all: subst ; try assumption.
         1,2: set_solver. iFrame. iSplit ; done.
       - opose proof (not_elem_of_dom_2 _ _ cache_q') as h...
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
         rewrite /exact_cache_offline_body...
         tp_bind (f' _) ; wp_bind (f _).
         iCombine "fresh" as "h".
         iSpecialize ("h" $! q' cache ε δ _ h M_dipr_q' with "ε δ F rhs").
         iApply (wp_strong_mono'' with "h").
         iIntros "/= %vq' (F & rhs & %cache_q'') /=".
         rewrite /list_cons... rewrite -/list_cons.
         iSpecialize ("IH" $! qs (qs_pre ++ [q']) qs'' QS'' (InjRV (vq', acc)) _).
         iSpecialize ("IH" $! _ _ _ _ _ _) => //.
         iSpecialize ("IH" with "[kε kδ rhs $F]") => //.
         2: iApply "IH" => //. iFrame.
         iSplitL "kε" ; [|iSplitL "kδ"]. 3: iSplit ; done.
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


     (* we can prove exact_cache_dipr from the online spec *)
     Lemma exact_cache_dipr_offline_map (M : val) DB (dDB : Distance DB) (qs : list nat) (QS : val) (is_qs : is_list qs QS)
       ε δ (εpos : 0 <= ε) (δpos : 0 <= δ)
       (M_dipr : Forall (λ q : nat, ⊢ wp_diffpriv (M #q) ε δ dDB) qs)
       :
       let k := size ((list_to_set qs) : gset _) in
       ⊢ wp_diffpriv (exact_cache_offline_map M QS) (k*ε) (k*δ) dDB.
     Proof with (tp_pures ; wp_pures).
       iIntros (k K c db db' adj) "[rhs [ε δ]]".
       rewrite {2}/exact_cache_offline_map...
       rewrite /exact_cache_offline_map...
       tp_bind (online_xcache _ _). wp_bind (online_xcache _ _).
       iPoseProof (oxc_spec0 M _ _ _ _) as "oXC" => //.
       iSpecialize ("oXC" with "rhs").
       iApply (wp_strong_mono'' with "oXC").
       iIntros "%f (%f' & rhs & %F & F & #cached & #fresh) /="...
       (* strengthen the postcondition with the resources for the cache & size information for the credits *)
       cut
         ( ∀ K, {{{
                   ↯m (c * (k * ε)) ∗ ↯ (c * (k * δ)) ∗
                   □ oxc_spec0_cached f f' F ∗
                   □ oxc_spec0_fresh M c dDB f f' F ∗
                   ⤇ fill K (list_map f' QS) ∗
                   F ∅
             }}}
                  list_map f QS
                  {{{ vl, RET vl ;
                      ∃ (vr : val) (lvl lvr : list val) cache_qs,
                        ⌜is_list lvl vl⌝ ∗ ⌜is_list lvr vr⌝ ∗ ⌜dom cache_qs = list_to_set qs⌝ ∗
                        ⤇ fill K vr ∗
                        F cache_qs ∗
                        ⌜vl = vr⌝ }}} ).
       { intros h. intros. iApply (h ∅ with "[-]") => //.
         2: iNext ; iIntros (?) "(% & % & % & % & % & % & % & rhs & F & %)" ; subst ; done.
         iFrame. by repeat iSplit. }
       iInduction qs as [|q' qs'] "IH" forall (QS is_qs).
       - iIntros (K' φ). iIntros "(ε & δ & #? & #? & rhs & F) hφ".
         simpl in is_qs. subst. rewrite /list_map... simplify_eq. iApply "hφ". iFrame. iExists [],[].
         iPureIntro. intuition auto ; try done.
       - iIntros (K' φ).
         iIntros "(ε & δ & #cached & #fresh & rhs & F) hφ".
         set (qs := q' :: qs').
         rewrite {4}/list_map... rewrite -/list_map.
         rewrite {3}/list_map... rewrite -/list_map.

         destruct is_qs as (QS' & -> & is_qs')...
         destruct (Forall_cons_1 _ _ _ M_dipr) as [M_dipr_q' M_dipr_qs'].
         assert (0 <= dDB db db') by apply distance_pos.
         tp_bind (list_map f' _) ; wp_bind (list_map f _).
         iSpecialize ("IH" $! M_dipr_qs' QS' is_qs' _).
         destruct_decide (make_decision (q' ∈ qs')) as cache_q'.
         + subst k.
           assert (list_to_set qs = list_to_set qs') as ->.
           { subst qs. simpl. set_solver. }
           iSpecialize ("IH" with "[-hφ]").
           { iFrame. iSplit ; done. }
           iApply ("IH"). iIntros "!> %vl (%vr & %lvl & %lvr & %cache_qs' & %is_vl & %is_vr & %dom_cache_qs' & rhs & F & %eqv)".
           iSimpl in "rhs"... tp_bind (f' _) ; wp_bind (f _).
           unshelve iSpecialize ("cached" $! q' cache_qs' _ _ with "F rhs").
           { rewrite dom_cache_qs'. set_solver. }
           iApply (wp_strong_mono'' with "cached").
           iIntros "/= %v' (F & rhs & %cache_q'')".
           rewrite /list_cons...
           iApply "hφ". iFrame. iModIntro. iPureIntro. simpl.
           eexists (v' :: lvl), (v' :: lvr). intuition auto.
           * simpl. eexists _. intuition auto.
           * simpl. eexists _. intuition auto.
           * set_solver.
           * subst. done.
         + set (k' := size (list_to_set qs' : gset _)).
           assert ((k = 1 + k')%nat) as ->.
           { subst k. simpl list_to_set. rewrite size_union. 1: rewrite size_singleton ; lia. set_solver. }
           replace (c * ((1 + k')%nat * δ)) with (c * δ + c * (k' * δ)).
           2:{ real_solver_partial. rewrite plus_INR INR_1. field. }
           replace (c * ((1 + k')%nat * ε)) with (c * ε + c * (k' * ε)).
           2:{ real_solver_partial. rewrite plus_INR INR_1. field. }
           iDestruct (ecm_split with "ε") as "[ε k'ε]".
           2: real_solver. 1: repeat real_solver_partial => //.
           iDestruct (ec_split with "δ") as "[δ k'δ]".
           2: real_solver. 1: repeat real_solver_partial => //.
           iSpecialize ("IH" with "[-hφ ε δ]").
           { iFrame. iSplit ; done. }
           iApply "IH".
           iIntros "!> %vl (%vr & %lvl & %lvr & %cache_qs' & %is_vl & %is_vr & %dom_cache_qs' & rhs & F & %eqv)".
           iSimpl in "rhs"... tp_bind (f' _) ; wp_bind (f _).
           unshelve iSpecialize ("fresh" $! q' cache_qs' ε δ _ _ M_dipr_q' with "ε δ F rhs").
           { rewrite dom_cache_qs'. set_solver. }
           iApply (wp_strong_mono'' with "fresh").
           iIntros "/= %v' (F & rhs & %cache_q'')".
           rewrite /list_cons...
           iApply "hφ". iFrame. iModIntro. iPureIntro. simpl.
           eexists (v' :: lvl), (v' :: lvr). intuition auto.
           * simpl. eexists _. intuition auto.
           * simpl. eexists _. intuition auto.
           * set_solver.
           * subst. done.
     Qed.

     Section concrete_example.

       Lemma wp_list_map_safe (f : val) (f_safe : ∀ (x : val), ⊢ WP f x {{_, ⌜True⌝ }})
         (l : list val) (lv : val) (hl : is_list l lv) :
         ⊢ WP (list_map f lv) {{_, ⌜True⌝}}.
       Proof.
         iInduction l as [ | x xs'] "IH" forall (lv hl) ; simpl in hl ; subst.
         - rewrite /list_map ; wp_pures. done.
         - rewrite {2}/list_map.
           destruct hl as (lv' & -> & hl').
           do 3 wp_pure. fold list_map. wp_pures.
           wp_bind (list_map _ _).
           iSpecialize ("IH" $! lv' hl').
           iApply (wp_strong_mono'' with "IH").
           iIntros. rewrite /list_cons ; wp_pures.
           wp_bind (f _). iApply (wp_strong_mono'' $! (f_safe _)). iIntros. wp_pures. done.
       Qed.

       Lemma spec_list_map_safe (f' : val) (f'_safe : ∀ K (x : val), ⤇ fill K (f' x) ⊢ spec_update ⊤ (∃ v' : val, ⤇ fill K v'))
         (l : list val) (lv : val) (hl : is_list l lv) K :
             (⤇ fill K (list_map f' lv)) ⊢ spec_update ⊤ (∃ v' : val, ⤇ fill K v').
       Proof.
         iIntros "rhs".
         iInduction l as [ | x xs'] "IH" forall (lv hl K) ; simpl in hl ; subst.
         - rewrite /list_map ; tp_pures. iFrame. done.
         - rewrite {2}/list_map.
           destruct hl as (lv' & -> & hl').
           do 3 tp_pure. fold list_map. tp_pures.
           tp_bind (list_map _ _).
           iSpecialize ("IH" $! lv' hl').
           iMod ("IH" with "rhs") as "(% & rhs) /=".
           rewrite /list_cons ; tp_pures.
           tp_bind (f' _). iMod (f'_safe with "rhs") as "(% & rhs) /=". tp_pures. iFrame. done.
       Qed.

       (* An exercise on point-wise equality of lists. *)
       Variable (f f' : val).
       (* f and f' are pointwise equal and safe to execute. *)
       Variable (ff_pweq : ∀ K (x r : val), ⤇ fill K (f' x) ⊢ WP f x {{v , ∃ v' : val, ⤇ fill K v' ∗ ⌜v = r → v' = r⌝ }} ).
       Variable (f_safe : ∀ x : val, ⊢ WP f x {{ v , ⌜True⌝ }}).
       Variable (f'_safe : ∀ K (x : val), ⤇ fill K (f' x) ⊢ spec_update ⊤ (∃ v' : val, ⤇ fill K v')).

       (* (map f [0]) and (map f' [0]) are point-wise equal. *)
       Goal (∀ R, ⊢ ⤇ fill [] (list_map f' (list_cons #0 list_nil)) -∗ WP (list_map f (list_cons #0 list_nil))
            {{ v , ∃ v' : val , ⤇ fill [] (Val v') ∗ ⌜v = R → v' = R⌝ }}).
         iIntros "%RES rhs". rewrite /list_map/list_cons. tp_pures. wp_pures.
         tp_bind (f' _). wp_bind (f _).
         destruct_decide (make_decision (∃ r0 : val, RES = InjRV (r0, InjLV #()))) as HRES.
         - destruct HRES as [r0 ->].
           iPoseProof (ff_pweq _ #0 r0) as "h0".
           iSpecialize ("h0" with "rhs").
           iApply (wp_strong_mono'' with "h0").
           iIntros "%v (%v' & rhs & %hvv') /=". tp_pures. wp_pures.
           iFrame. iModIntro. iPureIntro. intros h.
           inversion h. rewrite hvv'. 1: reflexivity. assumption.
         - iApply (wp_strong_mono'' $! (f_safe _)). iIntros.
           iMod (f'_safe with "rhs") as "(%v' & rhs)". simpl. tp_pures. wp_pures.
           iModIntro. iFrame. iPureIntro. intros.
           exfalso. apply HRES. eauto.
       Qed.

       (* (map f [1; 0]) and (map f' [1; 0]) are point-wise equal. *)
       Goal (∀ R, ⊢ ⤇ fill [] (list_map f' (list_cons #1 (list_cons #0 list_nil))) -∗ WP (list_map f (list_cons #1 (list_cons #0 list_nil)))
            {{ v , ∃ v' : val , ⤇ fill [] (Val v') ∗ ⌜v = R → v' = R⌝ }}).

         iIntros "%RES rhs". rewrite /list_map/list_cons. tp_pures. wp_pures.
         destruct_decide (make_decision (∃ r1 r0 : val, RES = InjRV (r1, InjRV (r0, InjLV #())))) as HRES.
         - tp_bind (f' _). wp_bind (f _).
           destruct HRES as (r1 & r0 & ->).
           iPoseProof (ff_pweq _ #0 r0) as "h0".
           iSpecialize ("h0" with "rhs").
           iApply (wp_strong_mono'' with "h0").
           iIntros "%v0 (%v0' & rhs & %hvv0') /=". tp_pures. wp_pures.

           tp_bind (f' _). wp_bind (f _).
           iPoseProof (ff_pweq _ #1 r1) as "h1".
           iSpecialize ("h1" with "rhs").
           iApply (wp_strong_mono'' with "h1").
           iIntros "%v1 (%v1' & rhs & %hvv1') /=". tp_pures. wp_pures.

           iFrame. iModIntro. iPureIntro. intros h.
           simplify_eq.
           specialize (hvv0' eq_refl). specialize (hvv1' eq_refl).
           simplify_eq. reflexivity.
         - tp_bind (f' _). wp_bind (f _).
           iApply (wp_strong_mono'' $! (f_safe _)). iIntros.
           iMod (f'_safe with "rhs") as "(% & rhs)". simpl. tp_pures. wp_pures.
           tp_bind (f' _). wp_bind (f _).
           iApply (wp_strong_mono'' $! (f_safe _)). iIntros.
           iMod (f'_safe with "rhs") as "(% & rhs)". simpl. tp_pures. wp_pures.
           iModIntro. iFrame. iPureIntro. intros.
           exfalso. apply HRES. eauto.
       Qed.



       (* (map f qs) and (map f' qs) are point-wise equal for any list qs. *)
       (* This proof reconstructs the entire list of results, which turns out to be overly complicated. *)
       Goal (∀ K RES (qs : val) QS (hqs : is_list QS qs), ⊢ ⤇ fill K (list_map f' qs) -∗
                  WP (list_map f qs)
                    {{ v , ∃ v' : val , ⤇ fill K (Val v') ∗ ⌜v = RES → v' = RES⌝ }}).

         intros. iIntros "rhs".
         (* we have to conjure up the intermediate results that got collected into RES *)
         destruct_decide (make_decision (∃ LRES : list val, is_list LRES RES ∧ length LRES = length QS)) as HRES.
         - destruct HRES as (LRES & hres & res_qs).
           iInduction QS as [ | Q QS'] "IH" forall (RES LRES res_qs hres qs hqs K) ; simpl in hqs.
           + subst. rewrite /list_map. tp_pures ; wp_pures. iFrame. done.
           + destruct hqs as (qs' & hqs & hqs').
             rewrite {4}/list_map. wp_pures.
             rewrite hqs.
             do 4 wp_pure _. fold list_map.
             destruct LRES as [|RQ LRES']. 1: done.
             simpl in hres. destruct hres as [RES' [RES_RQ_RES' hres']].
             inversion res_qs as [res_qs'].
             iSpecialize ("IH" $! RES' LRES' eq_refl hres' qs' hqs').
             rewrite {3}/list_map. do 7 tp_pure ; fold list_map.
             tp_bind (list_map f' _).
             iSpecialize ("IH" with "rhs").
             wp_bind (list_map f _).
             iApply (wp_strong_mono'' with "IH").
             iIntros "%vRES (%vRES' & rhs & %hRES)".
             rewrite /list_cons /= ; tp_pures ; wp_pures ; rewrite -/list_cons.
             tp_bind (f' _) ; wp_bind (f _).
             iPoseProof (ff_pweq _ Q RQ) as "hQ".
             iSpecialize ("hQ" with "rhs").
             iApply (wp_strong_mono'' with "hQ").
             iIntros "%vQ (%vQ' & rhs & %hQQ') /=".
             rewrite /list_cons /= ; tp_pures ; wp_pures ; rewrite -/list_cons.
             iFrame. iPureIntro. intros. simplify_eq.
             specialize (hQQ' eq_refl). specialize (hRES eq_refl). subst. done.
         -
           (* if RES is not a list of the same length as the inputs qs, we should get a contradiction out of safety. *)
           iRevert "rhs".
           iAssert
             (⤇ fill K (list_map f' qs) -∗
              WP list_map f qs {{ v, ∃ v' : val,
                      ⤇ fill K v'
                      ∗ ⌜v = RES → ∃ Lv : list val, is_list Lv RES ∧ length Lv = length QS⌝ }})%I as "HH".
           2: { iIntros "rhs". iSpecialize ("HH" with "rhs"). iApply (wp_strong_mono'' with "HH").
                iIntros "%v (%v' & rhs & %Lv)".
                iFrame. iIntros "%h". exfalso.
                apply HRES in Lv. all: assumption.
           }
           iIntros "rhs". clear HRES.
           iInduction QS as [ | Q QS'] "IH" forall (qs hqs K RES) ; simpl in hqs.
           + subst. rewrite /list_map. tp_pures ; wp_pures. iFrame. iIntros "!> %". subst. iExists []. done.
           + destruct hqs as (qs' & hqs & hqs').
             rewrite {4}/list_map. wp_pures.
             rewrite hqs.
             do 4 wp_pure _. fold list_map.
             rewrite {3}/list_map. do 7 tp_pure ; fold list_map.
             (* To use the IH we need to conjure up the result corresponding to the recursive call. *)
             destruct_decide (make_decision (∃ RQ RQS' : val, RES = InjRV (RQ, RQS'))) as HRES.
             * destruct HRES as (RQ & RQS' & HRES).
               iSpecialize ("IH" $! qs' hqs' _ RQS'). tp_bind (list_map f' _). iSpecialize ("IH" with "rhs").
               wp_bind (list_map f _).
               iApply (wp_strong_mono'' with "IH").
               iIntros "%vRES (%vRES' & rhs & %hRES)".
               rewrite /list_cons /= ; tp_pures ; wp_pures ; rewrite -/list_cons.
               tp_bind (f' _) ; wp_bind (f _).
               iApply (wp_strong_mono'' $! (f_safe _)). iIntros.
               iMod (f'_safe with "rhs") as "(% & rhs)". simpl. tp_pures. wp_pures.
               rewrite /list_cons /= ; tp_pures ; wp_pures ; rewrite -/list_cons.
               iFrame. iPureIntro. intros. simplify_eq.
               specialize (hRES eq_refl). destruct hRES as (Lv' & Lv_RQS' & Lv_QS').
               eexists (RQ :: Lv'). simpl. intuition eauto.
             *
               (* by safety of list_map and f we should be able to get a contradiction now even w/o the IH. *)
               iClear "IH".
               iRevert "rhs".
               iAssert
                 (⤇ fill K (list_cons (f' (Fst (Q, qs')%V)) (list_map f' qs')) -∗
                  WP list_cons (f (Fst (Q, qs')%V)) (list_map f qs')
                    {{ v, ∃ v' : val, ⤇ fill K v' ∗ ⌜v = RES → ∃ RQ RQS' : val, RES = InjRV (RQ, RQS')⌝ }})%I as "HH".
               2: { iIntros "rhs". iSpecialize ("HH" with "rhs"). iApply (wp_strong_mono'' with "HH").
                    iIntros "%v (%v' & rhs & %Lv)". iFrame. iPureIntro. intros ->.
                    specialize (Lv eq_refl). done.
               }
               iIntros "rhs". clear HRES.
               pose proof wp_list_map_safe as hh.
               pose proof (spec_list_map_safe f' f'_safe) as hh'.
               tp_bind (list_map _ _). iMod ((hh' _ _) with "rhs") as "(%v' & rhs) /=". 1: done. tp_pures. tp_bind (f' _).
               iMod (f'_safe _ _ with "rhs") as "(% & rhs) /=". rewrite {1}/list_cons. tp_pures.
               wp_bind (list_map _ _).
               pose proof (hh f f_safe) as h.
               iApply (wp_strong_mono'' $! (h _ _ _)). iIntros. wp_pures. wp_bind (f _).
               iApply (wp_strong_mono'' $! (f_safe _)). iIntros. rewrite /list_cons. wp_pures.
               iFrame. iPureIntro. intros <-. eauto.
               Unshelve. 2: eauto.
       Qed.

       (* (map f qs) and (map f' qs) are point-wise equal for any list qs. *)
       (* different proof strategy: start the induction before casing and only get two cases instead of the full list of results *)
       Goal (∀ K RES (qs : val) QS (hqs : is_list QS qs), ⊢ ⤇ fill K (list_map f' qs) -∗
                  WP (list_map f qs)
                    {{ v , ∃ v' : val , ⤇ fill K (Val v') ∗ ⌜v = RES → v' = RES⌝ }}).

         intros. iIntros "rhs".
         iInduction QS as [ | Q QS'] "IH" forall (RES qs hqs K) ; simpl in hqs.
         (* we have to conjure up the intermediate results that got collected into RES *)
         - subst. rewrite /list_map. tp_pures. wp_pures. iFrame. done.
         -
           destruct hqs as (qs' & hqs & hqs').
           rewrite {4}/list_map. wp_pures.
           rewrite hqs.
           do 4 wp_pure _. fold list_map.
           rewrite {3}/list_map. do 7 tp_pure ; fold list_map.
           (* To use the IH we need to conjure up the result corresponding to the recursive call. *)
           destruct_decide (make_decision (∃ RQ RQS' : val, RES = InjRV (RQ, RQS'))) as HRES.
           + destruct HRES as (RQ & RQS' & HRES).
             iSpecialize ("IH" $! RQS' qs' hqs' _). tp_bind (list_map f' _). iSpecialize ("IH" with "rhs").
             wp_bind (list_map f _).
             iApply (wp_strong_mono'' with "IH").
             iIntros "%vRES (%vRES' & rhs & %hRES)".
             rewrite /list_cons /= ; tp_pures ; wp_pures ; rewrite -/list_cons.
             tp_bind (f' _) ; wp_bind (f _).
             iPoseProof (ff_pweq _ Q RQ) as "hQ".
             iSpecialize ("hQ" with "rhs").
             iApply (wp_strong_mono'' with "hQ").
             iIntros "%vQ (%vQ' & rhs & %hQQ') /=".
             rewrite /list_cons /= ; tp_pures ; wp_pures ; rewrite -/list_cons.
             iFrame. iPureIntro. intros. simplify_eq.
             specialize (hQQ' eq_refl). specialize (hRES eq_refl). subst. done.
           +
             (* by safety of list_map and f we should be able to get a contradiction now even w/o the IH. *)
             iClear "IH".
             iRevert "rhs".
             iAssert
               (⤇ fill K (list_cons (f' (Fst (Q, qs')%V)) (list_map f' qs')) -∗
                WP list_cons (f (Fst (Q, qs')%V)) (list_map f qs')
                  {{ v, ∃ v' : val, ⤇ fill K v' ∗ ⌜v = RES → ∃ RQ RQS' : val, RES = InjRV (RQ, RQS')⌝ }})%I as "HH".
             2: { iIntros "rhs". iSpecialize ("HH" with "rhs"). iApply (wp_strong_mono'' with "HH").
                  iIntros "%v (%v' & rhs & %Lv)". iFrame. iPureIntro. intros ->.
                  specialize (Lv eq_refl). done.
             }
             iIntros "rhs". clear HRES.
             pose proof wp_list_map_safe as hh.
             pose proof (spec_list_map_safe f' f'_safe) as hh'.
             tp_bind (list_map _ _). iMod ((hh' _ _) with "rhs") as "(%v' & rhs) /=". 1: done. tp_pures. tp_bind (f' _).
             iMod (f'_safe _ _ with "rhs") as "(% & rhs) /=". rewrite {1}/list_cons. tp_pures.
             wp_bind (list_map _ _).
             pose proof (hh f f_safe) as h.
             iApply (wp_strong_mono'' $! (h _ _ _)). iIntros. wp_pures. wp_bind (f _).
             iApply (wp_strong_mono'' $! (f_safe _)). iIntros. rewrite /list_cons. wp_pures.
             iFrame. iPureIntro. intros <-. eauto.
             Unshelve. 2: eauto.
       Qed.

     End concrete_example.
   *)
  (* END TEMP COMMENT *)

  (* TODO fix condition on M to be safety *)
  Definition oxc_spec0_pw_fresh_safe (M : val) `(dDB : Distance DB) (f f' : val)
    (* (F : gmap nat val → iProp Σ) *)
    (G : gmap nat val → gmap nat val → iProp Σ)
    : iProp Σ :=
    (∀ (q : nat) B B' ε δ K,
        ⌜q ∉ dom B⌝ -∗
        ⌜q ∉ dom B'⌝ -∗
        wp_diffpriv_pw (M #q) ε δ dDB -∗
        (* ↯m (c * ε) -∗
           ↯ (c * δ) -∗ *)
        G B B' -∗
        ⤇ fill K (Val f' #q) -∗
        (* ∀ RES, *)
          (* WP (Val f) #q {{ v, ∃ (v' : val) A', F A' ∗ ⤇ fill K (Val v') ∗ ⌜v = RES → (v' = RES ∧ A' = <[q := v]> A)⌝ }}). *)
          WP (Val f) #q {{ v, ∃ (v' : val),
                  G ((<[q := v]> B)) (<[q := v']> B') ∗
                  ⤇ fill K (Val v')
                  (* ∗ (⌜v = RES ∧ B = B'⌝ -∗ G ((<[q := v]> B)) (<[q := v']> B') -∗ F (<[q := v]> B) ∗ ⌜(v' = RES)⌝) *)
    }}).
          (* WP (Val f) #q {{ v, ⌜v = RES⌝ -∗ F( <[q := v]> A) ∗ ⤇ fill K (Val v) ∗ ⌜<[q := v]> A !! q = Some v⌝ }}). *)

  (* list_map offline XC from online, but pointwise *)
  Lemma exact_cache_dipr_offline_map_pw (M : val) DB (dDB : Distance DB) (qs : list nat) (QS : val) (is_qs : is_list qs QS)
    ε δ (εpos : 0 <= ε) (δpos : 0 <= δ)
    (M_dipr : Forall (λ q : nat, ⊢ wp_diffpriv_pw (M #q) ε δ dDB) qs)
    :
    let k := size ((list_to_set qs) : gset _) in
    ⊢ wp_diffpriv_pw (exact_cache_offline_map M QS) (k*ε) (k*δ) dDB.
  Proof with (tp_pures ; wp_pures).
    iIntros (k K c db db' adj) "[rhs [ε δ]] %RES".
    rewrite {2}/exact_cache_offline_map...
    rewrite /exact_cache_offline_map...
    tp_bind (online_xcache _ _). wp_bind (online_xcache _ _).
    iPoseProof (oxc_spec0_pw M _ _ _ _) as "oXC" => //.
    iSpecialize ("oXC" with "rhs").
    iApply (wp_strong_mono'' with "oXC").
    iIntros "%f (%f' & rhs & %F & %G & F & FG & #cached & #fresh) /="...
    (* strengthen the postcondition with the resources for the cache & size information for the credits *)
    cut
      ( ∀ K,
                ↯m (c * (k * ε)) ∗ ↯ (c * (k * δ)) ∗
                □ oxc_spec0_pw_cached f f' G ∗
                □ oxc_spec0_pw_fresh M c dDB f f' F G ∗
                ⤇ fill K (list_map f' QS) ∗
                F ∅ ∗
                □ (∀ A : gmap nat val, F A ∗-∗ G A A)
                -∗
               WP list_map f QS
                 {{ vl,
                   ∃ (vr : val) (lvl lvr : list val) cache_qs_l cache_qs_r,
                     ⌜is_list lvl vl⌝ ∗ ⌜is_list lvr vr⌝ ∗
                     ⌜dom cache_qs_l = list_to_set qs⌝ ∗
                     ⌜dom cache_qs_r = list_to_set qs⌝ ∗
                     ⤇ fill K vr ∗
                     G cache_qs_l cache_qs_r ∗
                     (⌜vl = RES⌝ -∗
                     (⌜cache_qs_l = cache_qs_r⌝ ∗ ⌜vr = RES⌝)) }} ).
    { intros h. intros. iPoseProof (h with "[-]") as "h" => //.
      1: iFrame ; repeat iSplit ; try done.
      iApply (wp_strong_mono'' with "h").
      iIntros (?) "(% & % & % & % & % & % & % & % & % & rhs & G & F_heq)" ; subst ; iFrame.
      iIntros "%eqres". iDestruct ("F_heq" $! eqres) as "[-> ->]". done.
    }
    Unshelve. 2: eauto.
    iInduction qs as [|q' qs'] "IH" forall (RES QS is_qs).
    - iIntros (K'). iIntros "(ε & δ & #? & #? & rhs & F & FG)".
      simpl in is_qs. subst. rewrite /list_map... simplify_eq.
      iDestruct ("FG" with "F") as "G".
      iFrame. iExists [],[].
      iModIntro.
      repeat iSplit ; try done.
    - iIntros (K').
      iIntros "(ε & δ & #cached & #fresh & rhs & F & #FG)".
      set (qs := q' :: qs').
      rewrite {4}/list_map... rewrite -/list_map.
      rewrite {3}/list_map... rewrite -/list_map.

      destruct is_qs as (QS' & -> & is_qs')...
      destruct (Forall_cons_1 _ _ _ M_dipr) as [M_dipr_q' M_dipr_qs'].
      assert (0 <= dDB db db') by apply distance_pos.
      destruct_decide (make_decision (∃ RQ RQS' : val, RES = InjRV (RQ, RQS'))) as HRES.
{
      tp_bind (list_map f' _) ; wp_bind (list_map f _).
      destruct HRES as (RQ & RQS' & HRES).
      iSpecialize ("IH" $! M_dipr_qs' RQS' QS' is_qs' _).
      destruct_decide (make_decision (q' ∈ qs')) as cache_q'.
      + subst k.
        assert (list_to_set qs = list_to_set qs') as ->.
        { subst qs. simpl. set_solver. }
        iSpecialize ("IH" with "[$]").
        iApply (wp_strong_mono'' with "IH").
        iIntros "%vl (%vr & %lvl & %lvr & %cache_qs'_l & %cache_qs'_r & %is_vl & %is_vr & %dom_cache_qs'_l & %dom_cache_qs'_r & rhs & G & %eqv)".
        iSimpl in "rhs"... tp_bind (f' _) ; wp_bind (f _).
        unshelve iSpecialize ("cached" $! q' cache_qs'_l cache_qs'_r _ _ _ with "G rhs").
        { rewrite dom_cache_qs'_l. set_solver. }
        { rewrite dom_cache_qs'_r. set_solver. }
        iApply (wp_strong_mono'' with "cached").
        iIntros "/= %vq'_l (%vq'_r & G & rhs & %cache_q'')".
        rewrite /list_cons...
        iFrame. iModIntro. iPureIntro. simpl.
        eexists (vq'_l :: lvl), (vq'_r :: lvr). intuition auto.
        * simpl. eexists _. intuition auto.
        * simpl. eexists _. intuition auto.
        * set_solver.
        * set_solver.
        * subst. simplify_eq. destruct (eqv eq_refl) as [-> ->]. reflexivity.
        * subst. simplify_eq. destruct (eqv eq_refl) as [-> ->]. simplify_eq. reflexivity.
      + set (k' := size (list_to_set qs' : gset _)).
        assert ((k = 1 + k')%nat) as ->.
        { subst k. simpl list_to_set. rewrite size_union. 1: rewrite size_singleton ; lia. set_solver. }
        replace (c * ((1 + k')%nat * δ)) with (c * δ + c * (k' * δ)).
        2:{ real_solver_partial. rewrite plus_INR INR_1. field. }
        replace (c * ((1 + k')%nat * ε)) with (c * ε + c * (k' * ε)).
        2:{ real_solver_partial. rewrite plus_INR INR_1. field. }
        iDestruct (ecm_split with "ε") as "[ε k'ε]".
        2: real_solver. 1: repeat real_solver_partial => //.
        iDestruct (ec_split with "δ") as "[δ k'δ]".
        2: real_solver. 1: repeat real_solver_partial => //.
        iSpecialize ("IH" with "[-ε δ]") ; [iFrame ; repeat iSplit ; done|].
        iApply (wp_strong_mono'' with "IH").
        iIntros "%vqs'_l (%vqs'_r & %lvqs'_l & %lvqs'_r & %cache_qs'_l & %cache_qs'_r & %is_vqs'_l & %is_vqs'_r & %dom_cache_qs'_l & %dom_cache_qs'_r & rhs & G & %pweq_vqs')".
        iSimpl in "rhs"... tp_bind (f' _) ; wp_bind (f _).
        unshelve iSpecialize ("fresh" $! q' cache_qs'_l cache_qs'_r ε δ _ _ _ M_dipr_q' with "ε δ G rhs").
        1: rewrite dom_cache_qs'_l ; set_solver.
        1: rewrite dom_cache_qs'_r ; set_solver.
        iSpecialize ("fresh" $! RQ).
        iApply (wp_strong_mono'' with "fresh").
        iIntros "/= %vq'_l (%vq'_r & G & rhs & pweq_fresh)".
        rewrite /list_cons...
        iFrame "rhs". iModIntro. simpl.
        iExists (vq'_l :: lvqs'_l), (vq'_r :: lvqs'_r).
        iExists (<[q':=vq'_l]> cache_qs'_l), (<[q':=vq'_r]> cache_qs'_r).
        repeat iSplit.
        * iPureIntro. simpl. eexists _. intuition auto.
        * iPureIntro. simpl. eexists _. intuition auto.
        * iPureIntro. set_solver.
        * iPureIntro. set_solver.
        * iFrame.
        * iIntros "%". iSplit.
          -- simplify_eq. destruct pweq_vqs' => //. simplify_eq.
             iDestruct ("pweq_fresh" with "[] G") as "[F %eq_vq'_r]".
             1: done. simplify_eq. done.
          -- simplify_eq. destruct pweq_vqs' => //. simplify_eq.
             iDestruct ("pweq_fresh" with "[] G") as "[F %eq_vq'_r]".
             1: done. simplify_eq. done.
}
{
  iClear "IH ε δ".
  iRevert "rhs".
  iAssert (
              (* ↯m (c * (k * ε)) ∗ ↯ (c * (k * δ)) ∗ *)
              (* □ oxc_spec0_pw_cached f f' G ∗
                 □ oxc_spec0_pw_fresh M c dDB f f' F G ∗ *)
              ⤇ fill K' (list_cons (f' (Fst (#q', QS')%V)) (list_map f' QS')) -∗
              F ∅
              (* □ (∀ A : gmap nat val, F A ∗-∗ G A A) *)
              -∗
              WP list_cons (f (Fst (#q', QS')%V)) (list_map f QS')
                {{ vl,
                     ∃ (vr : val) (lvl lvr : list val) cache_qs_l cache_qs_r,
                       ⌜is_list lvl vl⌝ ∗ ⌜is_list lvr vr⌝ ∗
                       ⌜dom cache_qs_l = list_to_set qs⌝ ∗
                       ⌜dom cache_qs_r = list_to_set qs⌝ ∗
                       ⤇ fill K' vr ∗
                       G cache_qs_l cache_qs_r ∗
                       (⌜vl = RES → ∃ RQ RQS' : val, RES = InjRV (RQ, RQS')⌝
                        (* (⌜cache_qs_l = cache_qs_r⌝ ∗ ⌜vr = RES⌝) *)) }} )%I as "HH".
  2: { iIntros "rhs". iSpecialize ("HH" with "rhs F"). iApply (wp_strong_mono'' with "HH").
       iIntros "%v (%v' &% &% &% &% &% &% &% &% & rhs & G & %Lv)". iFrame. iPureIntro. simpl.
       eexists _,_.
       repeat split ; try done.
       - exfalso. eauto.
       - exfalso. eauto.
  }
  iIntros "rhs F".
  (* TODO don't do another induction here, instead factor out another lemma about list_map safety. *)
  iInduction qs' as [|q'' qs''] "IH" forall (RES HRES QS' is_qs').
  - simpl in * ; subst. rewrite /list_map...
    tp_bind (f' _) ; wp_bind (f _).
    (* destruct_decide (make_decision (q' ∈ qs')) as cache_q'. *)
    iAssert (□ oxc_spec0_pw_fresh_safe M dDB f f' G)%I as "#safe". 1: admit.
    iDestruct ("FG" with "F") as "G".
    iSpecialize ("safe" with "[] [] [] G [rhs]") => //.
    iApply (wp_strong_mono'' with "safe").
    iIntros "%vq (%vq' & G & rhs) /=".
    rewrite /list_cons... iFrame. iModIntro. iExists [vq],[vq'].
    iPureIntro. intuition eauto. 3,4: set_solver.
    all: cbn ; intuition eauto.
  - simpl in *.
    tp_bind (list_map _ _) ; wp_bind (list_map _ _).
    destruct is_qs' as (QS'' & -> & is_qs'').
    iSpecialize ("IH" $! _ _ _ _ QS'' is_qs'' with "[rhs]").

Qed.

  (* offline XC from online, but pointwise *)
  Lemma exact_cache_dipr_offline_pw (M : val) DB (dDB : Distance DB) (qs : list nat) (QS : val) (is_qs : is_list qs QS)
    ε δ (εpos : 0 <= ε) (δpos : 0 <= δ)
    (M_dipr : Forall (λ q : nat, ⊢ wp_diffpriv_pw (M #q) ε δ dDB) qs)
    :
    let k := size ((list_to_set qs) : gset _) in
    ⊢ wp_diffpriv_pw (exact_cache_offline M QS) (k*ε) (k*δ) dDB.
  Proof with (tp_pures ; wp_pures).
    iIntros (k K c db db' adj) "[rhs [ε δ]] %RES".
    rewrite {2}/exact_cache_offline...
    rewrite /exact_cache_offline...
    tp_bind (online_xcache _ _). wp_bind (online_xcache _ _).
    iPoseProof (oxc_spec0_pw M _ _ _ adj with "rhs") as "oXC" => //.
    iApply (wp_strong_mono'' with "oXC").
    iIntros "%f (%f' & rhs & %F & F & cached & fresh) /="...
    set (exact_cache_offline_body (f : val) := (λ: "acc" "q", list_cons (f "q") "acc")%V).
    rewrite -!/(exact_cache_offline_body _).
    revert RES qs QS is_qs k M_dipr.
    cut
      (∀ (RES : val) (qs : list nat)
         (qs_pre qs' : list nat) (QS' : val)
         (acc : val) cache_map,
          qs = qs_pre ++ qs' →
          dom cache_map = list_to_set qs_pre →
          dom cache_map ∪ list_to_set qs' = list_to_set qs →
          is_list qs' QS' →
          Forall (λ q : nat, ⊢ wp_diffpriv_pw (M #q) ε δ dDB) qs →
          let k := size (list_to_set qs : gset nat) in
          let k' := size cache_map in
          {{{
                ↯m (c * ((k - k') * ε)) ∗ ↯ (c * ((k - k') * δ)) ∗
                □ oxc_spec0_cached f f' F ∗
                □ oxc_spec0_pw_fresh M c dDB f f' F ∗
                ⤇ fill K (list_fold (exact_cache_offline_body f') acc QS') ∗
                F cache_map
          }}}
            list_fold (exact_cache_offline_body f) acc QS'
            {{{ vl, RET vl ; ∃ (vr : val), ⤇ fill K vr ∗ (⌜vl = RES → vr = RES⌝) }}}
      ).
    {
      intros h. intros. iApply (h RES qs [] qs QS _ ∅ with "[-]") => //.
      1: set_solver.
      2:{ iNext. iIntros "%vl h". iApply "h". }
      iFrame. rewrite map_size_empty. rewrite Rminus_0_r. subst k. simpl. iFrame.
    }
    iLöb as "IH".
    iIntros (RES qs qs_pre qs' QS' acc cache qs_pre_qs' dom_cache_pre dom_cache_qs'_qs is_qs'
               M_dipr φ) "(ε & δ & #cached & #fresh & rhs & F) hφ".
    set (k := size (list_to_set qs : gset nat)).
    set (k' := size cache).
    rewrite {4}/exact_cache_offline_body/list_fold... rewrite -!/(exact_cache_offline_body _) -/list_fold.
    destruct qs' as [|q' qs''] eqn:qs'_qs''.
    1:{ rewrite is_qs'. rewrite {3}/exact_cache_offline_body/list_fold... iApply "hφ". iExists _. iFrame => //. }
    destruct is_qs' as (QS'' & -> & is_qs'')...
    rewrite -!/(exact_cache_offline_body _) -/list_fold.
    rewrite qs_pre_qs' in M_dipr.
    destruct ((proj1 (List.Forall_app _ _ _)) M_dipr) as [M_dipr_qs_pre M_dipr_qs'].
    destruct (Forall_cons_1 _ _ _ M_dipr_qs') as [M_dipr_q' M_dipr_qs''].
    assert (0 <= dDB db db') by apply distance_pos.
    destruct (cache !! q') eqn:cache_q' => /=.
    - opose proof (elem_of_dom_2 _ _ _ cache_q') as h...
      rewrite /exact_cache_offline_body...
      tp_bind (f' _) ; wp_bind (f _).
      iCombine "cached" as "h".
      iSpecialize ("h" $! q' cache _ h with "F rhs").
      iApply (wp_strong_mono'' with "h").
      iIntros "/= %v' (F & rhs & %cache_q'')".
      assert (v = v') as <-. { rewrite cache_q' in cache_q''. inversion cache_q''. done. }
      rewrite /list_cons...
      rewrite -!/(exact_cache_offline_body _) -/list_fold.
      iSpecialize ("IH" $! RES qs (qs_pre ++ [q']) qs'' QS'' (InjRV (v, acc)) cache).
      unshelve iApply ("IH" $! _ _ _ _ _ _ with "[ε δ rhs F]") => //.
      1: subst ; by rewrite cons_middle assoc.
      all: subst ; try assumption.
      1,2: set_solver. iFrame. iSplit ; done.
    - opose proof (not_elem_of_dom_2 _ _ cache_q') as h...
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
      rewrite /exact_cache_offline_body...
      tp_bind (f' _) ; wp_bind (f _).
      iCombine "fresh" as "h".
      iSpecialize ("h" $! q' cache ε δ _ h M_dipr_q' with "ε δ F rhs").
      (* need to guess the result of (f #q') here... *)
      destruct_decide (make_decision (∃ RQ' RQS' : val, RES = InjRV (RQ', RQS'))) as HRES.
      {
        destruct HRES as (RQ' & RQS' & RES_QQS').
        iSpecialize ("h" $! RQ').
      iApply (wp_strong_mono'' with "h").
      iIntros "%vq' Hres".
      (* postponing these two lines until we need them *)
      (* iSpecialize ("Hres" $! _).
         iDestruct "Hres" as "(F & rhs & %cache_q'') /=". *)
      rewrite /list_cons... rewrite -/list_cons.
      iSpecialize ("IH" $! RES qs (qs_pre ++ [q']) qs'' QS'' (InjRV (vq', acc)) (<[q':=vq']> cache)).
      unshelve iSpecialize ("IH" $! _ _ _ _ _) => //.
      1: subst ; by rewrite cons_middle assoc.
      1: { simplify_eq. rewrite list_to_set_app_L. rewrite -dom_cache_pre.
           simpl. pose proof (dom_insert_L cache q' (vq' : val)) as ->. set_solver. }
      1: set_solver. 1: done. 1: { rewrite qs_pre_qs'. done. }
      iSpecialize ("IH" with "[kε kδ rhs $F]") => //.
      2: iApply "IH" => //. iFrame.
      iSplitL "kε" ; [|iSplitL "kδ"]. 3: iSplit ; done.
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
simpl in *. simplify_eq.

        1: {  }
        all: try (subst ; done).
        3,4: set_solver.
        1: subst ; by rewrite cons_middle assoc.
        all: subst ; assumption || set_solver.

  Qed.

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
