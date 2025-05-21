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
   *)

  Lemma exact_cache_dipr (M : val) DB (dDB : Distance DB) (qs : list nat) (QS : val) (is_qs : is_list qs QS)
    ε (εpos : 0 <= ε)
    (M_dipr : Forall (λ q : nat, wp_diffpriv (M #q) ε dDB) qs)
    (qs_sens : Forall (λ q : nat, wp_sensitive #q 1 dDB dZ) qs)
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

    revert qs QS is_qs qs_sens k M_dipr.

    cut
      (∀ (qs : list nat) QS, is_list qs QS →
                             Forall (λ q : nat, wp_diffpriv (M #q) ε dDB) qs →
                             Forall (λ q : nat, wp_sensitive #q 1 dDB dZ) qs →
                let k := size (list_to_set qs : gset nat) in
                ∀ (acc : val) cache_map,

                {{{
                      (* every element in qs is either in the cache or we have ε credit for it *)
                      (* ([∗ set] q ∈ (list_to_set qs),( ⌜ q ∈ dom cache_map ⌝ ∨ ↯ (c * ε))) *)
                      (* couldn't get this to work. *)

                      ↯ (c * (k * ε))
                      ∗ ⤇ fill K (list_fold
                       (λ: "acc" "q",
                          match: get #cache_r "q" with
                            InjL <> =>
                              let: "v" := M "q" (inject db') in
                              set #cache_r "q" "v";; list_cons "v" "acc"
                          | InjR "v" => list_cons "v" "acc"
                          end)%V acc QS)
                    ∗ map_list cache_l cache_map
                    ∗ map_slist cache_r cache_map
                }}}
                  list_fold
             (λ: "acc" "q",
                match: get #cache_l "q" with
                  InjL <> =>
                    let: "v" := M "q" (inject db) in
                    set #cache_l "q" "v";; list_cons "v" "acc"
                | InjR "v" => list_cons "v" "acc"
                end)%V acc QS
             {{{ vl, RET vl ; ∃ (vr : val), ⤇ fill K vr ∗ ⌜vl = vr⌝ }}}
      ).
    {
      intros h. intros. iApply (h with "[-hφ]") => //.
      2: iNext ; iIntros (?) "(% & ? & ->)" ; iApply "hφ" => //.
      iFrame.
    }
    clear φ.
    iLöb as "IH".
    iIntros (qs QS is_qs M_dipr qs_sens acc cache φ) "(ε & rhs & cache_l & cache_r) hφ".
    rewrite {4}/list_fold...
    destruct qs as [|q' qs'].
    1:{ rewrite is_qs. rewrite {3}/list_fold... iApply "hφ". iExists _. iFrame => //. }
    rewrite {3}/list_fold...
    destruct is_qs as (QS' & -> & is_qs')...
    wp_apply (wp_get with "cache_l"). iIntros (?) "[cache_l ->]".
    tp_bind (get _ _). iMod (spec_get with "cache_r rhs") as "[rhs cache_r]" => /=.
    assert (0 <= size (list_to_set qs' : gset nat) <= size ({[q']} ∪ (list_to_set qs' : gset nat)))%R.
    {
      split. 1: real_solver.
      apply le_INR.
      (* rewrite size_union_alt.
         rewrite size_difference_alt.
         destruct (decide ({[q']} ## (list_to_set qs' : gset nat))).
         + rewrite size_union => //. lia.
         + assert (q' ∈ list_to_set qs') *)
      admit.
    }
    destruct (cache !! q') => /=.
    - idtac...
      rewrite /list_cons. wp_pure. wp_pure. wp_pure. wp_pure. wp_pure. wp_pure. wp_pure.
      do 7 tp_pure.
      iApply ("IH" with "[] [] [] [ε cache_l cache_r rhs]") => //.
      1,2: admit.
      iFrame.
      iApply (ec_weaken with "ε").
      assert (0 <= dDB db db') by apply distance_pos.
      real_solver.

    - idtac...
      tp_bind (M _ _).
      wp_bind (M _ _).
      destruct (Forall_cons_1 _ _ _ M_dipr) as [Mq'_dipr Mqs'_dipr].
      assert ((size ({[q']} ∪ list_to_set qs' : gset nat) * ε) = ε + size (list_to_set qs' : gset nat) * ε) as ->.
      1: admit.
      rewrite Rmult_plus_distr_l.
      iDestruct (ec_split with "ε") as "[ε kε]".
      1,2: admit.
      iApply (Mq'_dipr with "[rhs ε]") => // ; iFrame.
      iNext. iIntros (vq') "rhs" => /=...
      tp_bind (set _ _ _).
      iMod (spec_set with "cache_r rhs") as "[rhs cache_r]".
      wp_apply (wp_set with "cache_l") ; iIntros "cache_l"...
      rewrite /list_cons. wp_pure. wp_pure. wp_pure. wp_pure. wp_pure. wp_pure. wp_pure.
      simpl. do 7 tp_pure.
      tp_pure. tp_pure.
      iApply ("IH" with "[] [] [] [kε cache_l cache_r rhs]") => //.
      1: admit. iClear "IH".
      iFrame.
  Admitted.



End xcache.
