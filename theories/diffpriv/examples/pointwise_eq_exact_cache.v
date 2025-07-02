From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list map exact_cache.

Section xcache_pw.
  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.
  (* If we want to use OXC with a mechanism M that only satisfies pw-DP, we need weaker/more general specs. *)
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

  (* TODO fix condition on M to be safety instead of wp_diffpriv_pw *)
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

  (* We can prove the point-wise online spec. *)
  Lemma oxc_spec0_pw (M : val) `(dDB : Distance DB) (db db' : DB) `(adj : dDB db db' <= c) K :
    ⤇ fill K (online_xcache M (Val (inject db')))
    ⊢ WP online_xcache M (Val (inject db))
        {{ f, ∃ f', ⤇ fill K (Val f') ∗
              ∃ (F : gmap nat val → iProp Σ) (G : gmap nat val → gmap nat val → iProp Σ),
              F ∅ ∗ □ (∀ A, F A ∗-∗ G A A) ∗
              □ oxc_spec0_pw_cached f f' G ∗
              □ oxc_spec0_pw_fresh M c dDB f f' F G
        }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "rhs". rewrite /online_xcache...
    tp_bind (init_map _). iMod (spec_init_map with "rhs") as "[%cache_r [rhs cache_r]]" => /=...
    wp_apply wp_init_map => //. iIntros (cache_l) "?"...
    iModIntro. iExists _. simpl. iFrame "rhs".
    iExists (λ A, map_list cache_l A ∗ map_slist cache_r A)%I.
    iExists (λ B B', map_list cache_l B ∗ map_slist cache_r B')%I.
    iFrame. repeat iSplit.
    - iModIntro. iIntros. iSplit ; by iIntros.
    - iIntros "!>" (???? cached cached') "[cache_l cache_r] rhs"...
      tp_bind (get _ _). iMod (spec_get with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_get with "cache_l") ; iIntros (vq) "[cache_l %hvq]".
      simpl. subst. apply elem_of_dom in cached, cached'. rewrite /opt_to_val.
      destruct cached as [vq hvq]. rewrite hvq. destruct cached' as [vq' hvq']. rewrite hvq'...
      iFrame. iModIntro ; iPureIntro ; intuition auto. simplify_eq. done.
    - iIntros "!>" (?????? cached cached') "M_dipr ε δ [cache_l cache_r] rhs %RES"...
      tp_bind (get _ _). iMod (spec_get with "[$cache_r] [$rhs]") as "[rhs cache_r]".
      wp_apply (wp_get with "cache_l") ; iIntros (vq) "[cache_l %hvq]".
      simpl. subst. apply not_elem_of_dom_1 in cached, cached'. rewrite /opt_to_val.
      rewrite cached cached'... tp_bind (M _ _) ; wp_bind (M _ _).
      rewrite /wp_diffpriv_pw. iSpecialize ("M_dipr" $! _ c db db' adj).
      iSpecialize ("M_dipr" with "[$rhs $ε $δ]"). iSpecialize ("M_dipr" $! RES).
      iApply (wp_strong_mono'' with "M_dipr"). iIntros (vq) "(%v' & rhs & %pweq)" => /=...
      tp_bind (set _ _ _). iMod (spec_set with "[$cache_r] [$rhs]") as "[rhs cache_r]" => /=.
      wp_apply (wp_set with "cache_l") ; iIntros "cache_l"...
      iModIntro. iFrame. iIntros "[->->]". rewrite pweq //.
      iIntros "[F_l F_r]". iFrame. done.
  Qed.

  (* list_map offline exact_cache from online, but pointwise *)
  (* This proof is complete modulo the safety part that proves that if list_map f xs returns a
     value v, then v is a list. The real lemma is more subtle because it also has to preserve some
     resources. It should be possible to complete the proof. *)
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
    revert RES QS is_qs ; iInduction qs as [|q' qs'] "IH" ; iIntros (RES QS is_qs).
    - iIntros (K'). iIntros "(ε & δ & #? & #? & rhs & F & FG)".
      simpl in is_qs. subst. rewrite /list_map...
      iDestruct ("FG" with "F") as "G". iFrame.
      iExists [],[]. iModIntro. repeat iSplit ; done.
    - iIntros (K'). iIntros "(ε & δ & #cached & #fresh & rhs & F & #FG)". set (qs := q' :: qs').
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
      + subst k. assert (list_to_set qs = list_to_set qs') as ->. { subst qs. simpl. set_solver. }
        iSpecialize ("IH" with "[$]").
        iApply (wp_strong_mono'' with "IH").
        iIntros "%vl (%vr & %lvl & %lvr & %cache_qs'_l & %cache_qs'_r & %is_vl & %is_vr & %dom_cache_qs'_l & %dom_cache_qs'_r & rhs & G & %eqv)".
        iSimpl in "rhs"... tp_bind (f' _) ; wp_bind (f _).
        unshelve iSpecialize ("cached" $! q' cache_qs'_l cache_qs'_r _ _ _ with "G rhs").
        1,2: rewrite ?dom_cache_qs'_l ?dom_cache_qs'_r ; set_solver.
        iApply (wp_strong_mono'' with "cached"). iIntros "/= %vq'_l (%vq'_r & G & rhs & %cache_q'')".
        rewrite /list_cons... iFrame. iModIntro. iPureIntro. simpl.
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

Abort.

End xcache_pw.
