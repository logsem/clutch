From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list map.


Lemma map_equiv_lookup_None `{Countable A} `{Equiv B} (m m' : gmap A B) (a : A) :
  m ≡ m' → m !! a = None → m' !! a = None.
Proof.
  intros Heq.
  pose proof lookup_proper a m m' Heq as Hl.
  destruct (m !! a), (m' !! a); try done.
  by apply Some_equiv_eq in Hl as (? & ? & ?).
Qed.

Section xcache.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

  (* TODO instantiate exact_cache with a mechanism *)

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

  (* Given a set of queries qs and a ε-dp mechanism M, exact_cache M qs is kε-dp where k=|qs|. *)

(*     To enable caching we need decidable equality on the type of queries, so *)
(*     we'll just work with integers (think of this as the Gödel encoding of the *)
(*     query program, or as the serialization of the SQL query...). *)

(*     Invariant: *)

(*     We have ↯ (k - |cache|) ε error credits. *)

(*     If q ∈ cache *)
(*     then we get the same value in both programs directly, *)
(*     else *)
(*          we pay ↯ε to make sure that the call to M qi produces the same result *)
(*          in the left and right programs, keeping the cache always synchronised. *)

(*     NB: No assumption about the sensitivity of qs is made; this is encompassed *)
(*     by the premise that for each q ∈ qs, (M q) is ε-dipr. In practice, M may *)
(*     well decode q into a sensitive query function and add noise to the result *)
(*     of the query to achieve this privacy guarantee. *)

(*    *)


  #[local] Definition exact_cache_body `{Inject DB val} (M : val) (db : DB) (cache_loc : loc) : expr :=
    ((λ: "acc" "q",
        match: get #cache_loc "q" with
          InjL <> =>
            let: "v" := M "q" (inject db) in
            set #cache_loc "q" "v";; list_cons "v" "acc"
        | InjR "v" => list_cons "v" "acc"
        end)%V).

  Definition online_xcache : val :=
    λ:"M" "db",
      let: "cache" := init_map #() in
      (λ: "q",
         match: get "cache" "q" with
         | SOME "v" => "v"
         | NONE => let: "v" := "M" "q" "db" in
                   set "cache" "q" "v" ;;
                   "v"
         end).

  (* We can define the original exact_cache as a client of the online spec (keeping the direct def.) *)
  Definition exact_cache_offline_map : val :=
    λ:"M" "qs" "db",
      let: "oXC" := online_xcache "M" "db" in
      list_map "oXC" "qs".

  (* Same but with list_fold (used in one proof) *)
  Definition exact_cache_offline : val :=
    λ:"M" "qs" "db",
      let: "oXC" := online_xcache "M" "db" in
      list_fold (λ: "acc" "q", list_cons ("oXC" "q") "acc") list_nil "qs".

  Definition oxc_spec0_cached A `{Inject A val} (f f' : val) (F : gmap nat A → iProp Σ) : iProp Σ :=
    (∀ (q : nat) (m : gmap nat A) K,
        ⌜q ∈ dom m⌝ -∗
        F m -∗
        ⤇ fill K (Val f' #q) -∗
        WP (Val f) #q {{ v, ∃ (a : A), ⌜v = inject a⌝ ∗ F m ∗ ⤇ fill K (inject a) ∗  ⌜m !! q = Some a⌝ }}).

  Definition oxc_spec0_fresh (M : val) c `(dDB : Distance DB) A `{Inject A val}
    (f f' : val) (F : gmap nat A → iProp Σ) : iProp Σ :=
    (∀ (q : nat) m ε δ K,
        ⌜q ∉ dom m⌝ -∗
        wp_diffpriv (M #q) ε δ dDB A -∗
        ↯m (c * ε) -∗
        ↯ (c * δ) -∗
        F m -∗
        ⤇ fill K (Val f' #q) -∗
        WP (Val f) #q {{ v, ∃ (a : A), ⌜v = inject a⌝ ∗ F (<[q := a]> m) ∗ ⤇ fill K (inject a) }}).

  (* pay as you go, cache map exposed, M only needs to be private on the queries it gets executed on *)
  Lemma oxc_spec0 (M : val) `(dDB : Distance DB) A `{Inject A val}
    (db db' : DB) c (adj : dDB db db' <= c) K :
    ⤇ fill K (online_xcache M (Val (inject db')))
    ⊢ WP online_xcache M (Val (inject db))
        {{ f, ∃ f', ⤇ fill K (Val f') ∗
                    ∃ (F : gmap nat A → iProp Σ),
                      F ∅ ∗
                      □ oxc_spec0_cached A f f' F ∗
                      □ oxc_spec0_fresh M c dDB A f f' F
        }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "rhs". rewrite /online_xcache...
    tp_bind (init_map _). iMod (spec_init_map with "rhs") as "[%cache_r [rhs cache_r]]".
    simpl... wp_apply wp_init_map => //. iIntros (cache_l) "?"...
    iModIntro. iExists _. iFrame "rhs".
    iExists (λ m, map_list cache_l (inject <$> m) ∗ map_slist cache_r (inject <$> m))%I.
    iFrame. iSplit.
    - iIntros "!>" (??? cached ) "[cache_l cache_r] rhs"...
      tp_bind (get _ _). iMod (spec_get with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_get with "cache_l") ; iIntros (vq) "[cache_l %hvq]".
      simpl. subst. apply elem_of_dom in cached. rewrite /opt_to_val.
      rewrite !lookup_fmap.
      destruct cached as [vq Hvq] => /=. rewrite Hvq.
      tp_pures. wp_pures. iFrame. eauto.
    - iIntros "!>" (????? cached) "M_dipr ε δ [cache_l cache_r] rhs"...
      tp_bind (get _ _). iMod (spec_get with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_get with "cache_l") ; iIntros (vq) "[cache_l %hvq]".
      simpl. subst. apply not_elem_of_dom_1 in cached. rewrite /opt_to_val.
      rewrite !lookup_fmap.
      rewrite !cached... tp_bind (M _ _). wp_bind (M _ _).
      rewrite /wp_diffpriv. iSpecialize ("M_dipr" $! _ c db db' adj).
      iSpecialize ("M_dipr" with "[$rhs $ε $δ]").
      iApply (wp_strong_mono'' with "M_dipr"). iIntros (vq) "(%a & -> & rhs)" => /=...
      tp_bind (set _ _ _). iMod (spec_set with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_set with "cache_l") ; iIntros "cache_l".
      simpl. tp_pures. wp_pures. iExists a. rewrite -!fmap_insert. iFrame "∗ %". done.
  Qed.

  (* we can derive spec1 from spec0 *)
  (* F can store error credits ; could also ask for N*ε error credits upfront and hand out F(∅, N) instead of F(∅, 0). *)
  Lemma oxc_spec1 (M : val) `(dDB : Distance DB) A `{Inject A val} (db db' : DB)
    (adj : dDB db db' <= 1) K ε δ (εpos : 0 <= ε) (δpos : 0 <= δ) :
    (∀ q : nat, hoare_diffpriv (M #q) ε δ dDB A) ∗
    ⤇ fill K (online_xcache M (Val (inject db')))
    ⊢ WP online_xcache M (Val (inject db))
        {{ f, ∃ f', ⤇ fill K (Val f') ∗
                    ∃ (F : gmap nat A * nat → iProp Σ),
                      F (∅, 0%nat) ∗
                      □ (∀ m k, ↯m ε ∗ ↯ δ ∗ F(m, k) -∗ F(m, S k)) ∗
                      □ (∀ (q : nat) m K (N : nat),
                            ⌜q ∈ dom m⌝ -∗
                            F (m, N) -∗
                            ⤇ fill K (Val f' #q) -∗
                            WP (Val f) #q {{ v, ∃ (a : A), ⌜v = inject a⌝ ∗ F(m, N) ∗ ⤇ fill K (inject a) ∗  ⌜m !! q = Some a⌝ }}) ∗
                      □ (∀ (q : nat) m K (N : nat),
                            ⌜q ∉ dom m⌝ -∗
                            F(m, S N) -∗
                            ⤇ fill K (Val f' #q) -∗
                            WP (Val f) #q {{ v, ∃ (a : A), ⌜v = inject a⌝ ∗ F (<[q := a]> m, N) ∗ ⤇ fill K (inject a) }})
        }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "(#M_dipr & rhs)". iPoseProof (oxc_spec0 with "rhs") as "spec0" => //.
    iMod ecm_zero as "ε0" ; iMod ec_zero as "δ0".
    iApply (wp_strong_mono'' with "spec0"). iIntros "%f (%f' & rhs & (%F & F0 & #f_cached & #f_fresh))".
    iExists f'. iFrame "rhs".
    iExists (λ mk : gmap nat A * nat, let '(m, k) := mk in F m ∗ ↯m (k * ε) ∗ ↯ (k * δ))%I.
    rewrite !Rmult_0_l. iFrame "F0 ε0 δ0".
    iSplitR ; [|iSplitL "f_cached"].
    - iIntros "!>" (??) "(ε&δ&?&kε&kδ)". iFrame. iPoseProof (ecm_combine with "[ε kε]") as "ε" ; iFrame.
      iPoseProof (ec_combine with "[δ kδ]") as "δ" ; iFrame. iSplitL "ε".
      + iApply ecm_eq. 2: iFrame. replace (S k) with (k+1)%nat by lia. replace (INR (k+1)) with (k+1)%R.
        2: real_solver. lra.
      + iApply ec_eq. 2: iFrame. replace (S k) with (k+1)%nat by lia. replace (INR (k+1)) with (k+1)%R.
        2: real_solver. lra.
    - simpl. iIntros "!>" (?????) "[FA [ε δ]] rhs". iSpecialize ("f_cached" with "[//] [$FA] [$rhs]").
      iApply (wp_strong_mono'' with "f_cached"). iIntros (?) "(%a & -> & FA & rhs & ?)". iFrame => //.
    - iIntros "!>" (?????) "[FA [ε δ]] rhs".
      replace ((S N)) with (N + 1)%nat by lia. replace (INR (N+1)) with (N+1) by real_solver.
      rewrite !Rmult_plus_distr_r. rewrite !Rmult_1_l.
      iDestruct (ecm_split with "ε") as "[Nε ε]". 1,2: real_solver.
      iDestruct (ec_split with "δ") as "[Nδ δ]". 1,2: real_solver.
      iSpecialize ("f_fresh" with "[//] [] [ε] [δ] [$FA] [$rhs]").
      { iIntros (?????) "[??]". iApply ("M_dipr" with "[//] [$]").
        iIntros "!>" (?) "$ //". }
      1,2: rewrite Rmult_1_l => //.
      iApply (wp_strong_mono'' with "f_fresh").
      iIntros (?) "(%a  & -> & FA & rhs)". iFrame => //.
  Qed.

  (* We can prove exact_cache_dipr from the online spec. The proof is essentially the same as the direct proof. *)
  Lemma exact_cache_dipr_offline (M : val) DB (dDB : Distance DB) A `{Inject A val}
    (qs : list nat) (QS : val) (is_qs : is_list qs QS)
    ε δ (εpos : 0 <= ε) (δpos : 0 <= δ)
    (M_dipr : Forall (λ q : nat, ⊢ wp_diffpriv (M #q) ε δ dDB A) qs)
    :
    let k := size ((list_to_set qs) : gset _) in
    ⊢ wp_diffpriv (exact_cache_offline M QS) (k*ε) (k*δ) dDB (list A).
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
         (acc : list A) cache_map,
          qs = qs_pre ++ qs' →
          dom cache_map = list_to_set qs_pre →
          dom cache_map ∪ list_to_set qs' = list_to_set qs →
          is_list qs' QS' →
          Forall (λ q : nat, ⊢ wp_diffpriv (M #q) ε δ dDB A) qs →
          let k := size (list_to_set qs : gset nat) in
          let k' := size cache_map in
          {{{
                ↯m (c * ((k - k') * ε)) ∗ ↯ (c * ((k - k') * δ)) ∗
                □ oxc_spec0_cached A f f' F ∗
                □ oxc_spec0_fresh M c dDB A f f' F ∗
                ⤇ fill K (list_fold (exact_cache_offline_body f') (inject acc) QS') ∗
                F cache_map
          }}}
            list_fold (exact_cache_offline_body f) (inject acc)%V QS'
          {{{ (l : list A), RET (inject l); ⤇ fill K (inject l) }}}
      ).
    {
      intros h. intros. iApply (h qs [] qs QS [] ∅ with "[-]") => //.
      { set_solver. }
      { iFrame. rewrite map_size_empty. rewrite Rminus_0_r. subst k. simpl. iFrame "∗ #". }
      by iIntros "!>" (?) "$".
    }
    iLöb as "IH".
    iIntros (qs qs_pre qs' QS' acc cache qs_pre_qs' dom_cache_pre dom_cache_qs'_qs is_qs'
                M_dipr φ) "(ε & δ & #cached & #fresh & rhs & F) hφ".
    set (k := size (list_to_set qs : gset nat)).
    set (k' := size cache).
    rewrite /exact_cache_offline_body /=.
    tp_rec. tp_pures.
    wp_rec. wp_pures.
    destruct qs' as [|q' qs''] eqn:qs'_qs''.
    { rewrite is_qs'. tp_pures. wp_pures. iApply "hφ". iModIntro. iFrame "∗ %". }
    destruct is_qs' as (QS'' & -> & is_qs'').
    tp_pures. wp_pures.
    rewrite qs_pre_qs' in M_dipr.
    destruct ((proj1 (List.Forall_app _ _ _)) M_dipr) as [M_dipr_qs_pre M_dipr_qs'].
    destruct (Forall_cons_1 _ _ _ M_dipr_qs') as [M_dipr_q' M_dipr_qs''].
    assert (0 <= dDB db db') by apply distance_pos.
    destruct (cache !! q') eqn:cache_q' => /=.
    - opose proof (elem_of_dom_2 _ _ _ cache_q') as h...
      tp_bind (f' _) ; wp_bind (f _).
      iCombine "cached" as "h".
      iSpecialize ("h" $! q' cache _ h with "F rhs").
      iApply (wp_strong_mono'' with "h").
      iIntros "/= %v' (%b & -> & F & rhs & %cache_q'')".
      assert (a = b) as <-. { rewrite cache_q' in cache_q''. inversion cache_q''. done. }
      tp_rec. wp_rec. tp_pures. wp_pures.
      iSpecialize ("IH" $! qs (qs_pre ++ [q']) qs'' QS'' (_ :: _) cache ).
      iApply ("IH" with "[%] [%] [%] [%] [%] [ε δ rhs F]") => //.
      { subst. rewrite cons_middle assoc //. }
      { set_solver. }
      { set_solver. }
      { subst. done. }
      iFrame "∗ #".
    - opose proof (not_elem_of_dom_2 _ _ cache_q') as h...
      assert ((c * ((k - k') * ε)) = (c * (k - (k'+1)) * ε + c * ε)) as -> by lra.
      assert ((c * ((k - k') * δ)) = (c * (k - (k'+1)) * δ + c * δ)) as -> by lra.
      assert (0 <= k - (k' + 1)).
      {
        subst. subst k k'. apply Rle_0_le_minus.
        rewrite -dom_cache_qs'_qs.
        replace (size cache) with (size (dom cache)) by apply size_dom.
        rewrite dom_cache_pre. replace 1 with (INR 1) by auto.
        replace 1%nat with (size (list_to_set [q'] : gset nat)).
        2:{ cbn. rewrite union_empty_r_L. apply size_singleton. }
        rewrite -plus_INR. rewrite -size_union. 2: set_solver.
        rewrite (list_to_set_cons _ qs''). simpl.
        apply le_INR. apply subseteq_size. set_solver.
      }
      iDestruct (ecm_split with "ε") as "[kε ε]". 1,2: real_solver.
      iDestruct (ec_split with "δ") as "[kδ δ]". 1,2: real_solver.
      rewrite /exact_cache_offline_body... tp_bind (f' _) ; wp_bind (f _).
      iCombine "fresh" as "h".
      iSpecialize ("h" $! q' cache ε δ _ h M_dipr_q' with "ε δ F rhs").
      iApply (wp_strong_mono'' with "h").
      iIntros "/= %vq' (%a & -> & F & rhs) /=".
      tp_rec. wp_rec. tp_pures. wp_pures.
      iSpecialize ("IH" $! qs (qs_pre ++ [q']) qs'' QS'' (_ :: _)).
      iApply ("IH" with "[%] [%] [%] [%] [%] [kε kδ $rhs $F]") => //.
      { subst. rewrite cons_middle assoc //. }
      { set_solver. }
      { set_solver. }
      { subst. done. }
      iSplitL "kε" ; [|iSplitL "kδ"]. 3: iSplit ; done.
      + iApply ecm_eq. 2: iFrame. real_solver_partial. subst k. simpl. subst k'.
        replace (INR $ size (<[q' := _]> cache)) with (size cache + 1) => //.
        rewrite map_size_insert_None => //. qify_r ; zify_q. lia.
      + iApply ec_eq. 2: iFrame. real_solver_partial. subst k. simpl. subst k'.
        replace (INR $ size (<[q' := _]> cache)) with (size cache + 1) => //.
        rewrite map_size_insert_None => //. qify_r ; zify_q. lia.
  Qed.

  (* We can also prove the map variant of the offline exact_cache_dipr from the online spec *)
  (* This proof uses induction on the list of queries, which is a bit simpler than direct Löb induction. *)
  Lemma exact_cache_dipr_offline_map (M : val) DB (dDB : Distance DB) A `{Inject A val}
    (qs : list nat) (QS : val) (is_qs : is_list qs QS)
    ε δ (εpos : 0 <= ε) (δpos : 0 <= δ)
    (M_dipr : Forall (λ q : nat, ⊢ wp_diffpriv (M #q) ε δ dDB A) qs)
    :
    let k := size ((list_to_set qs) : gset _) in
    ⊢ wp_diffpriv (exact_cache_offline_map M QS) (k*ε) (k*δ) dDB (list A).
  Proof with (tp_pures ; wp_pures).
    iIntros (k K c db db' adj) "[rhs [ε δ]]".
    rewrite /exact_cache_offline_map...
    tp_bind (online_xcache _ _) ; wp_bind (online_xcache _ _).
    iPoseProof (oxc_spec0 M _ _ _ _ with "rhs") as "oXC" => //.
    iApply (wp_strong_mono'' with "oXC").
    iIntros "%f (%f' & rhs & %F & F & #cached & #fresh) /="...
    (* strengthen the postcondition with the resources for the cache & size information for the credits *)
    cut
      ( ∀ K, {{{ ↯m (c * (k * ε)) ∗ ↯ (c * (k * δ)) ∗
                 □ oxc_spec0_cached A f f' F ∗
                 □ oxc_spec0_fresh M c dDB A f f' F ∗
                 ⤇ fill K (list_map f' QS) ∗ F ∅ }}}
               list_map f QS
               {{{ (l : list A), RET (inject l);
                   ∃ cache_qs,
                     ⌜dom cache_qs = list_to_set qs⌝ ∗
                     ⤇ fill K (inject l) ∗ F cache_qs }}} ).
    { intros h. intros. iApply (h with "[$]") => //.
      iNext ; iIntros (?) "(% & % & $ & F) //".
    }
    revert QS is_qs. iInduction qs as [|q' qs'] "IH" ; iIntros (QS is_qs).
    - iIntros (K' φ). iIntros "(ε & δ & #? & #? & rhs & F) hφ".
      simpl in is_qs. subst. wp_rec; tp_rec... iApply ("hφ" $! []). iFrame. iModIntro. iPureIntro. done.
    - iIntros (K' φ). iIntros "(ε & δ & #cached & #fresh & rhs & F) hφ". set (qs := q' :: qs').
      tp_rec; wp_rec...
      destruct is_qs as (QS' & -> & is_qs')...
      destruct (Forall_cons_1 _ _ _ M_dipr) as [M_dipr_q' M_dipr_qs'].
      assert (0 <= dDB db db') by apply distance_pos.
      tp_bind (list_map f' _) ; wp_bind (list_map f _).
      iSpecialize ("IH" $! M_dipr_qs' QS' is_qs' _).
      destruct (decide (q' ∈ qs')) as [cache_q'|cache_q'].
      + subst k. assert (list_to_set qs = list_to_set qs') as ->. { subst qs. simpl. set_solver. }
        iSpecialize ("IH" with "[-hφ]"). { iFrame. iSplit ; done. }
        iApply ("IH").
        iIntros "!>" (l) "(%cache_qs & %dom_cache_qs & rhs & F)".
        iSimpl in "rhs"... tp_bind (f' _) ; wp_bind (f _).
        iSpecialize ("cached" with "[%] F rhs").
        { rewrite dom_cache_qs. set_solver. }
        iApply (wp_strong_mono'' with "cached"). iIntros "/= %v' (%a & -> & F & rhs & %cache_q'')".
        rewrite /list_cons... iApply ("hφ" $! (_ :: _)). iFrame. iModIntro. iPureIntro.
        set_solver.
      + set (k' := size (list_to_set qs' : gset _)).
        assert ((k = 1 + k')%nat) as ->.
        { subst k. simpl list_to_set. rewrite size_union. 1: rewrite size_singleton ; lia. set_solver. }
        assert (∀ α, c * ((1 + k')%nat * α) = c * α + c * (k' * α)) as eq_err ; [|rewrite !eq_err].
        1:{ real_solver_partial. rewrite plus_INR INR_1. field. }
        iDestruct (ecm_split with "ε") as "[ε k'ε]" ; [real_solver|real_solver|].
        iDestruct (ec_split with "δ") as "[δ k'δ]" ; [real_solver|real_solver|].
        iSpecialize ("IH" with "[-hφ ε δ]"). { iFrame. iSplit ; done. }
        iApply "IH".
        iIntros "!>" (l) "(%cache_qs' & %dom_cache_qs & rhs & F)".
        iSimpl in "rhs"... tp_bind (f' _) ; wp_bind (f _).
        iSpecialize ("fresh" $! q' cache_qs' with "[%] [//] ε δ F rhs").
        { rewrite dom_cache_qs. set_solver. }
        iApply (wp_strong_mono'' with "fresh"). iIntros "/= %v' (%a & -> & F & rhs)".
        wp_rec; tp_rec... iApply ("hφ" $! (_ :: _)). iFrame. iModIntro. iPureIntro.
        set_solver.
  Qed.

  (* Direct proof via Löb induction for the definition with fold. *)
  Lemma exact_cache_dipr (M : val) `(dDB : Distance DB) A `(Inject A val)
    (qs : list nat) (QS : val) (is_qs : is_list qs QS) ε δ (εpos : 0 <= ε) (δpos : 0 <= δ)
    (M_dipr : Forall (λ q : nat, ⊢ hoare_diffpriv (M #q) ε δ dDB A) qs)
    :
    let k := size ((list_to_set qs) : gset _) in
    ⊢ hoare_diffpriv (exact_cache M QS) (k*ε) (k*δ) dDB (list A).
  Proof with (tp_pures ; wp_pures).
    iIntros (k K c db db' adj φ) "!> [rhs ε] hφ". rewrite {2}/exact_cache...
    wp_apply wp_init_map => // ; iIntros (cache) "cache"...
    rewrite /exact_cache... tp_bind (init_map _).
    iMod (spec_init_map with "rhs") as "(%cache_r & rhs & cache_r)" => /=...
    rewrite -!/(exact_cache_body _ _ _).
    revert qs QS is_qs k M_dipr.
    cut
      (∀ (qs : list nat)
         (qs_pre qs' : list nat) (QS' : val)
         (acc : list A)
         (cache_map : gmap nat A),
          qs = qs_pre ++ qs' →
          dom cache_map = list_to_set qs_pre →
          dom cache_map ∪ list_to_set qs' = list_to_set qs →
          is_list qs' QS' →
          Forall (λ q : nat, ⊢ hoare_diffpriv (M #q) ε δ dDB A) qs →
          let k := size (list_to_set qs : gset nat) in
          let k' := size cache_map in
          {{{
                ↯m (c * ((k - k') * ε)) ∗ ↯ (c * ((k - k') * δ))
                ∗ ⤇ fill K (list_fold (exact_cache_body M db' cache_r) (inject acc) QS')
                ∗ map_list cache (inject <$> cache_map)
                ∗ map_slist cache_r (inject <$> cache_map)
          }}}
            list_fold (exact_cache_body M db cache) (inject acc) QS'
            {{{ (l : list A), RET (inject l); ⤇ fill K (inject l) }}}
      ).
    {
      intros h. intros. iApply (h qs [] qs QS []  ∅ with "[-hφ]") => //.
      { set_solver. }
      iFrame. rewrite map_size_empty. rewrite Rminus_0_r. subst k. simpl. iFrame.
    }
    clear φ.
    iLöb as "IH".
    iIntros (qs qs_pre qs' QS' acc cache' qs_pre_qs' dom_cache_pre dom_cache_qs'_qs is_qs'
               M_dipr φ) "(ε & δ & rhs & cache & cache_r) hφ /=".
    set (k := size (list_to_set qs : gset nat)).
    set (k' := size cache').
    tp_rec; tp_pures. rewrite -!/(exact_cache_body _ _ _).
    wp_rec; wp_pures. rewrite -!/(exact_cache_body _ _ _).
    destruct qs' as [|q' qs''] eqn:qs'_qs''.
    { rewrite is_qs'. tp_pures. wp_pures. iApply "hφ". iFrame. iModIntro. done. }
    destruct is_qs' as (QS'' & -> & is_qs'').
    tp_pures. rewrite -!/(exact_cache_body _ _ _).
    wp_pures. rewrite -!/(exact_cache_body _ _ _).
    wp_apply (wp_get with "cache"). iIntros (?) "[cache ->]".
    tp_bind (get _ _). iMod (spec_get with "cache_r rhs") as "[rhs cache_r]" => /=.
    rewrite qs_pre_qs' in M_dipr.
    destruct ((proj1 (List.Forall_app _ _ _)) M_dipr) as [M_dipr_qs_pre M_dipr_qs'].
    destruct (Forall_cons_1 _ _ _ M_dipr_qs') as [M_dipr_q' M_dipr_qs''].
    assert (0 <= dDB db db') by apply distance_pos.
    destruct (cache' !! q') eqn:cache_q' => /=.
    - opose proof (elem_of_dom_2 _ _ _ cache_q') as h...
      rewrite !lookup_fmap cache_q' /=.
      rewrite /list_cons.
      wp_pures. tp_pures. rewrite -!/(exact_cache_body _ _ _).
      iSpecialize ("IH" $! qs (qs_pre ++ [q']) qs'' QS'' (a :: acc) cache').
      iApply ("IH" with "[%] [%] [%] [%] [%] [$ε $δ $rhs $cache $cache_r]") => //; subst.
      { rewrite cons_middle assoc //. }
      { set_solver. }
      { set_solver. }
      done.
    - opose proof (not_elem_of_dom_2 _ _ cache_q') as h.
      rewrite !lookup_fmap cache_q'.
      tp_pures. wp_pures.
      tp_bind (M _ _). wp_bind (M _ _).
      assert ((c * ((k - k') * ε)) = (c * (k - (k'+1)) * ε + c * ε)) as -> by lra.
      assert ((c * ((k - k') * δ)) = (c * (k - (k'+1)) * δ + c * δ)) as -> by lra.
      assert (0 <= k - (k' + 1)).
      {
        subst. subst k k'. apply Rle_0_le_minus.
        rewrite -dom_cache_qs'_qs.
        replace (size cache') with (size (dom cache')) by apply size_dom.
        rewrite dom_cache_pre. replace 1 with (INR 1) by auto.
        replace 1%nat with (size (list_to_set [q'] : gset nat)).
        2:{ cbn. rewrite union_empty_r_L. apply size_singleton. }
        rewrite -plus_INR. rewrite -size_union.
        { rewrite (list_to_set_cons _ qs''). simpl.
          apply le_INR. apply subseteq_size. set_solver. }
        rewrite list_to_set_singleton.
        set_solver.
      }
      iDestruct (ecm_split with "ε") as "[kε ε]". 2: real_solver. 1: repeat real_solver_partial => //.
      iDestruct (ec_split with "δ") as "[kδ δ]". 2: real_solver. 1: repeat real_solver_partial => //.
      iApply (M_dipr_q' with "[] [rhs ε δ]") => // ; iFrame. iNext. iIntros (a) "rhs" => /=...
      tp_bind (set _ _ _). iMod (spec_set with "cache_r rhs") as "[rhs cache_r]".
      wp_apply (wp_set with "cache") ; iIntros "cache"...
      rewrite /list_cons. do 7 wp_pure. simpl. do 9 tp_pure. rewrite -!/(exact_cache_body _ _ _).
      rewrite -!fmap_insert.
      iSpecialize ("IH" $! qs (qs_pre ++ [q']) qs'' QS'' (a :: _)).
      iApply ("IH" with "[%] [%] [%] [%] [%] [kε kδ $rhs $cache $cache_r]") => //; subst.
      { rewrite cons_middle assoc //. }
      { set_solver. }
      { set_solver. }
      { done. }
      iSplitL "kε".
      + iApply ecm_eq. 2: iFrame. real_solver_partial. subst k. simpl. subst k'.
        replace (INR $ size (<[q' := _]> cache')) with (size cache' + 1) => //.
        rewrite map_size_insert_None => //. qify_r ; zify_q. lia.
      + iApply ec_eq. 2: iFrame. real_solver_partial. subst k. simpl. subst k'.
        replace (INR $ size (<[q' := _]> cache')) with (size cache' + 1) => //.
        rewrite map_size_insert_None => //. qify_r ; zify_q. lia.
  Qed.

End xcache.
