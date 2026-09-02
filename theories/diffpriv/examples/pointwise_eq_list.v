(* Some examples of how mapping pointwise equal functions (f,f') onto a list xs yields pointwise equal results.

The difficulty lies in reconstructing the intermediate results required to call (f,f') from the result of map f xs.

The proofs are completed, but only apply to functions that are unconditionally safe (see f_safe, f'_safe).

This can serve as a blueprint for proving that (list_map f) is pointwise DP if f is pw-PD.
 *)
From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics.
From clutch.prob Require Import differential_privacy.
From clutch.diffpriv Require Import adequacy diffpriv proofmode.
From clutch.diffpriv.examples Require Import list map.

Section pweq_list.

  Context `{!diffprivGS Σ}.

  #[local] Open Scope R.

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

  Lemma spec_list_map_safe (f' : val)
    (f'_safe : ∀ K (x : val), ⤇ fill K (f' x) ⊢ spec_update ⊤ (∃ v' : val, ⤇ fill K v'))
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
  Variable (ff_pweq : ∀ K (x r : val),
               ⤇ fill K (f' x) ⊢ WP f x {{v , ∃ v' : val, ⤇ fill K v' ∗ ⌜v = r → v' = r⌝ }} ).
  Variable (f_safe : ∀ x : val, ⊢ WP f x {{ v , ⌜True⌝ }}).
  Variable (f'_safe : ∀ K (x : val), ⤇ fill K (f' x) ⊢ spec_update ⊤ (∃ v' : val, ⤇ fill K v')).

  (* (map f [0]) and (map f' [0]) are point-wise equal. *)
  Lemma pweq_singleton :
    (∀ R, ⊢ ⤇ fill [] (list_map f' (list_cons #0 list_nil))
             -∗ WP (list_map f (list_cons #0 list_nil))
                {{ v , ∃ v' : val , ⤇ fill [] (Val v') ∗ ⌜v = R → v' = R⌝ }}).
  Proof using ff_pweq f_safe f'_safe.
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
  Lemma pweq_pair :
    (∀ R, ⊢ ⤇ fill [] (list_map f' (list_cons #1 (list_cons #0 list_nil)))
            -∗ WP (list_map f (list_cons #1 (list_cons #0 list_nil)))
                 {{ v , ∃ v' : val , ⤇ fill [] (Val v') ∗ ⌜v = R → v' = R⌝ }}).
  Proof using ff_pweq f_safe f'_safe.
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
  Lemma pweq_list_map_strong :
    (∀ K RES (qs : val) QS (hqs : is_list QS qs),
           ⊢ ⤇ fill K (list_map f' qs)
           -∗ WP (list_map f qs)
              {{ v , ∃ v' : val , ⤇ fill K (Val v') ∗ ⌜v = RES → v' = RES⌝ }}).
  Proof using ff_pweq f_safe f'_safe.
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
        (⤇ fill K (list_map f' qs)
         -∗
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
            (⤇ fill K (list_cons (f' (Fst (Q, qs')%V)) (list_map f' qs'))
             -∗
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
  Lemma pweq_list_map :
    (∀ K RES (qs : val) QS (hqs : is_list QS qs),
        ⊢ ⤇ fill K (list_map f' qs)
          -∗
        WP (list_map f qs)
          {{ v , ∃ v' : val , ⤇ fill K (Val v') ∗ ⌜v = RES → v' = RES⌝ }}).
  Proof using ff_pweq f_safe f'_safe.
    intros. iIntros "rhs".
    iInduction QS as [ | Q QS'] "IH" forall (RES qs hqs K) ; simpl in hqs.
    (* we have to conjure up the intermediate results that got collected into RES *)
    - subst. rewrite /list_map. tp_pures. wp_pures. iFrame. done.
    - destruct hqs as (qs' & hqs & hqs').
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
          (⤇ fill K (list_cons (f' (Fst (Q, qs')%V)) (list_map f' qs'))
           -∗
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

End pweq_list.
