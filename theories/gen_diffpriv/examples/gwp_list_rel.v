(** * Relational parametricity for the [gwp.list] list combinators

    [report_noisy_max_generic.v] (and the idiomatic report-noisy-max) builds its
    lists with the combinators of [gen_prob_lang.gwp.list] (imported there as
    [gwp.list]), which differ from the combinators of
    [gen_diffpriv.examples.list] — notably [list_init], which here counts DOWN
    from [len] to [1] prepending (so [list_init len f = [f 1; …; f len]]) with no
    final [list_rev].

    The list combinators are bare recursive lambdas, not type-abstracted, so we
    cannot get their congruence "for free" from the fundamental theorem.  Instead
    we (re)define the semantic list relation [lrel_list] directly (via
    [lrel_rec], copied verbatim from [examples/list.v] — the value encoding
    [NONE = InjLV #()], [SOME x = InjRV x], [a::l = SOME(a,l)] is identical) and
    prove the relational congruences ([refines_list_map], [refines_list_init],
    [refines_list_max_index]) semantically, meta-quantified over the element
    relations. *)
From clutch.gen_prob_lang Require Import lang notation.
From clutch.gen_prob_lang Require Import gwp.list.
From clutch.gen_diffpriv Require Import model interp app_rel_rules rel_tactics.
From iris.prelude Require Import options.

Section gwp_list_rel.
  Context {Sg : Sig} `{!diffprivRGS Sg Σ}.
  Canonical Structure gen_ectxi_lang_lr := gen_ectxi_lang Sg.
  Canonical Structure gen_ectx_lang_lr := gen_ectx_lang Sg.
  Canonical Structure gen_lang_lr := gen_lang Sg.
  Canonical Structure gen_markov_lr := lang_markov (gen_lang Sg).
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).

  (** The least relation [R] such that:
       - [R nilv nilv'] when both are [InjLV #()]  (the [NONEV] nil encoding);
       - [R consv consv'] when both are [InjRV (a, rest)] / [InjRV (a', rest')]
         with [A a a'] and [R rest rest'] (the [SOMEV (a, rest)] cons encoding). *)
  Program Definition lrel_list_gen (A : lrel Σ) : lrelC Σ -n> lrelC Σ :=
    λne X, lrel_sum lrel_unit (lrel_prod A X).
  Next Obligation. solve_proper. Qed.

  Definition lrel_list (A : lrel Σ) : lrel Σ := lrel_rec (lrel_list_gen A).

  Lemma lrel_list_unfold (A : lrel Σ) (v1 v2 : val) :
    lrel_list A v1 v2 ⊣⊢
      ▷ ((⌜v1 = InjLV #()⌝ ∧ ⌜v2 = InjLV #()⌝)
         ∨ (∃ a1 a2 r1 r2,
              ⌜v1 = InjRV (a1, r1)%V⌝ ∧ ⌜v2 = InjRV (a2, r2)%V⌝
              ∗ A a1 a2 ∗ lrel_list A r1 r2)).
  Proof.
    rewrite {1}/lrel_list.
    etrans; [iApply (lrel_rec_unfold (lrel_list_gen A) v1 v2)|].
    rewrite /lrel_list_gen /lrel_rec1 /lrel_sum /lrel_prod /lrel_unit /lrel_car /=.
    iSplit.
    - iIntros "H !>".
      iDestruct "H" as (w1 w2) "[(-> & -> & [-> ->])|(-> & -> & H)]".
      + iLeft. done.
      + iRight. iDestruct "H" as (b1 b2 b1' b2') "(-> & -> & HA & HX)".
        iExists b1, b2, b1', b2'. by iFrame.
    - iIntros "H".
      iApply (bi.later_mono with "H").
      iIntros "[(-> & ->)|H]".
      + iExists #(), #(). iLeft. by auto.
      + iDestruct "H" as (a1 a2 r1 r2) "(-> & -> & HA & HX)".
        iExists (a1, r1)%V, (a2, r2)%V. iRight.
        iSplit; [done|]. iSplit; [done|].
        iExists a1, a2, r1, r2. by iFrame.
  Qed.

  (** The relational congruence for [list_map] at the value level. *)
  Lemma refines_list_map_vals (A B : lrel Σ) (fv fv' : val) :
    (A → B)%lrel fv fv' -∗
    □ (∀ lv lv', lrel_list A lv lv' -∗
         REL list_map fv lv << list_map fv' lv' : lrel_list B).
  Proof.
    iIntros "#Hff !>".
    iLöb as "IH". iIntros (lv lv') "Hll".
    rewrite lrel_list_unfold.
    rel_rec_l. rel_rec_r.
    iDestruct "Hll" as "[(-> & ->)|Hcons]".
    - rel_pures_l. rel_pures_r. rel_values.
      rewrite (lrel_list_unfold B (InjLV _) (InjLV _)).
      iModIntro. iNext. iLeft. by auto.
    - iDestruct "Hcons" as (a1 a2 r1 r2) "(-> & -> & #HA & Hrest)".
      rel_pures_l. rel_pures_r.
      rel_bind_l (list_map _ _). rel_bind_r (list_map _ _).
      iApply (refines_bind with "[Hrest]").
      { iApply ("IH" with "Hrest"). }
      iIntros (tv tv') "#Htail /=".
      rel_bind_l (fv _). rel_bind_r (fv' _).
      iApply (refines_bind with "[]").
      { rel_pures_l. rel_pures_r. iApply ("Hff" with "HA"). }
      iIntros (hv hv') "#Hhead /=".
      rel_pures_l. rel_pures_r. rewrite /list_cons. rel_pures_l. rel_pures_r.
      rel_values.
      rewrite (lrel_list_unfold B (InjRV _) (InjRV _)).
      iModIntro. iNext. iRight.
      iExists hv, hv', tv, tv'. by iFrame "Hhead Htail".
  Qed.

  (** The relational congruence for [list_map] over arbitrary related
      expressions. *)
  Lemma refines_list_map (A B : lrel Σ) (f f' l l' : expr) :
    (REL f << f' : (A → B)%lrel) -∗
    (REL l << l' : lrel_list A) -∗
    REL list_map f l << list_map f' l' : lrel_list B.
  Proof.
    iIntros "Hf Hl".
    rel_bind_l l. rel_bind_r l'.
    iApply (refines_bind with "Hl").
    iIntros (lv lv') "Hll /=".
    rel_bind_l f. rel_bind_r f'.
    iApply (refines_bind with "Hf").
    iIntros (fv fv') "Hff /=".
    iDestruct (refines_list_map_vals with "Hff") as "#Hmap".
    by iApply "Hmap".
  Qed.

  (** Relational congruence for [list_init].  Here [list_init len f] runs the
      inner loop [aux acc i] with [i] counting DOWN from [len] to [0],
      prepending [f i] each step; the accumulator stays related at
      [lrel_list A]. *)
  Lemma refines_list_init (A : lrel Σ) (n n' f f' : expr) :
    (REL n << n' : lrel_nat) -∗
    (REL f << f' : (lrel_nat → A)%lrel) -∗
    REL list_init n f << list_init n' f' : lrel_list A.
  Proof.
    iIntros "Hn Hf".
    (* Evaluation is right-to-left: the inner argument [f] reduces first. *)
    rel_bind_l f. rel_bind_r f'.
    iApply (refines_bind with "Hf").
    iIntros (fv fv') "#Hff /=".
    rel_bind_l n. rel_bind_r n'.
    iApply (refines_bind with "Hn").
    iIntros (nv nv') "Hn /=".
    iDestruct "Hn" as (k) "[-> ->]".
    rewrite /list_init.
    (* Reduce the three outer betas, exposing the loop body [aux [] #k].  We
       unfold [list_cons] so the loop body matches the (unfolded-cons) [Hloop]
       statement below; the loop's recursive occurrence reproduces this same
       unfolded shape, so the lockstep [rel_pure] counts stay stable. *)
    do 3 (rel_pure_l _). do 3 (rel_pure_r _).
    rewrite /list_cons.
    (* Generalise over the (Coq nat) counter and the related accumulators, and
       run the down-count loop in lockstep. *)
    iAssert (□ ∀ (j : nat) (av av' : val),
                lrel_list A av av' -∗
                REL (rec: "aux" "acc" "i" :=
                       if: "i" = #0 then "acc"
                       else "aux"
                              ((λ: "elem" "list", SOME ("elem", "list"))%V
                                 (Val fv "i") "acc") ("i" - #1))%V av #j
                 << (rec: "aux" "acc" "i" :=
                       if: "i" = #0 then "acc"
                       else "aux"
                              ((λ: "elem" "list", SOME ("elem", "list"))%V
                                 (Val fv' "i") "acc") ("i" - #1))%V av' #j
                 : lrel_list A)%I as "#Hloop".
    { iModIntro. iIntros (j). iInduction j as [|j] "IH"; iIntros (av av') "Hacc".
      - (* counter 0: both runs return the accumulator. *)
        rel_rec_l. rel_rec_r.
        rel_pures_l. rel_pures_r. rel_values.
      - (* counter [S j]: cons [f #(S j)] onto the accumulator, recurse at [j]. *)
        rel_rec_l. rel_rec_r.
        rel_pures_l. rel_pures_r.
        rel_bind_l (fv _)%E. rel_bind_r (fv' _)%E.
        iApply (refines_bind with "[]").
        { iApply ("Hff" $! #(S j) #(S j)). iExists (S j). by auto. }
        iIntros (hv hv') "#Hhead /=".
        (* Reduce the head cons and the [- #1], stopping before the recursive
           [aux] fires, so the goal matches the induction hypothesis. *)
        do 5 (rel_pure_l _). do 5 (rel_pure_r _).
        replace (Z.of_nat (S j) - 1)%Z with (Z.of_nat j) by lia.
        iApply ("IH" $! (InjRV (hv, av)) (InjRV (hv', av'))
                 with "[Hhead Hacc]").
        rewrite (lrel_list_unfold A (InjRV _) (InjRV _)).
        iNext. iRight.
        iExists hv, hv', av, av'. by iFrame "Hhead Hacc". }
    (* Run the loop from the empty accumulator [[]] and counter [#k].  First
       reduce the [InjL #()] accumulator to a value and fold the (bare) loop
       [Rec] to its value form [(rec …)%V], so the goal matches [Hloop]. *)
    do 2 (rel_pure_l _). do 2 (rel_pure_r _).
    iApply ("Hloop" $! k).
    rewrite (lrel_list_unfold A (InjLV _) (InjLV _)).
    iNext. iLeft. by auto.
  Qed.

  (** Relational congruence for [list_max_index]: two lists related at
      [lrel_list lrel_int] are pointwise equal integers, hence the argmax indices
      agree.  The result is a [nat] index, so the conclusion is at [lrel_nat]. *)
  Lemma refines_list_max_index (l l' : expr) :
    (REL l << l' : lrel_list lrel_int) -∗
    REL list_max_index l << list_max_index l' : lrel_nat.
  Proof.
    iIntros "Hl".
    rel_bind_l l. rel_bind_r l'.
    iApply (refines_bind with "Hl").
    iIntros (lv lv') "Hll /=".
    rewrite /list_max_index.
    rewrite lrel_list_unfold.
    rel_pures_l. rel_pures_r.
    iDestruct "Hll" as "[(-> & ->)|Hcons]".
    - rel_pures_l. rel_pures_r. rel_values. iExists 0%nat. by auto.
    - iDestruct "Hcons" as (a1 a2 r1 r2) "(-> & -> & #Hhd & Hrest)".
      iDestruct "Hhd" as (y) "[-> ->]".
      rel_pures_l. rel_pures_r.
      rewrite /list_max_index_aux.
      rel_pures_l. rel_pures_r.
      set (handler := (λ: "(y, iy, ix)" "x",
                         let: "y" := "(y, iy, ix)" in
                         let: "iy" := Snd (Fst "y") in
                         let: "ix" := Snd "y" in
                         let: "y" := Fst (Fst "y") in
                         if: "y" < "x" then ("x", "ix", "ix" + #1)
                         else ("y", "iy", "ix" + #1))%V).
      set (R := (lrel_prod (lrel_prod lrel_int lrel_nat) lrel_nat) : lrel Σ).
      iAssert (□ ∀ (av av' : val) (rs rs' : val),
                  R av av' -∗ lrel_list lrel_int rs rs' -∗
                  REL list_fold handler av rs << list_fold handler av' rs' : R)%I
        as "#Hfold".
      { iModIntro. iLöb as "IH". iIntros (av av' rs rs') "#Hacc Hrs".
        rewrite (lrel_list_unfold lrel_int rs rs').
        rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r.
        iDestruct "Hrs" as "[(-> & ->)|Hcons]".
        - rel_pures_l. rel_pures_r. rel_values.
        - iDestruct "Hcons" as (b1 b2 t1 t2) "(-> & -> & #Hb & Htail)".
          rel_pures_l. rel_pures_r.
          iDestruct "Hb" as (xb) "[-> ->]".
          iDestruct "Hacc" as (p1 p2 q1 q2) "(-> & -> & #Hp & #Hq)".
          iDestruct "Hp" as (pp1 pp2 pq1 pq2) "(-> & -> & #Hpp & #Hpq)".
          iDestruct "Hpp" as (yv) "[-> ->]".
          iDestruct "Hpq" as (iv) "[-> ->]".
          iDestruct "Hq" as (xv) "[-> ->]".
          rel_bind_l (handler _ _). rel_bind_r (handler _ _).
          rewrite /handler.
          rel_pures_l. rel_pures_r.
          case_bool_decide as Hlt; rel_pures_l; rel_pures_r.
          + replace (Z.of_nat xv + 1)%Z with (Z.of_nat (xv + 1)) by lia.
            iApply ("IH" with "[] Htail").
            iExists (#xb, #xv)%V, (#xb, #xv)%V, #(xv + 1)%nat, #(xv + 1)%nat.
            iSplit; [done|]. iSplit; [done|]. iSplit.
            * iExists #xb, #xb, #xv, #xv.
              iSplit; [done|]. iSplit; [done|].
              iSplit; [iExists xb; by auto|iExists xv; by auto].
            * iExists (xv + 1)%nat; by auto.
          + replace (Z.of_nat xv + 1)%Z with (Z.of_nat (xv + 1)) by lia.
            iApply ("IH" with "[] Htail").
            iExists (#yv, #iv)%V, (#yv, #iv)%V, #(xv + 1)%nat, #(xv + 1)%nat.
            iSplit; [done|]. iSplit; [done|]. iSplit.
            * iExists #yv, #yv, #iv, #iv.
              iSplit; [done|]. iSplit; [done|].
              iSplit; [iExists yv; by auto|iExists iv; by auto].
            * iExists (xv + 1)%nat; by auto. }
      rel_bind_l (list_fold handler _ r1). rel_bind_r (list_fold handler _ r2).
      iApply (refines_bind with "[Hrest]").
      { iApply ("Hfold" with "[] Hrest").
        iExists (#y, #0)%V, (#y, #0)%V, #1, #1.
        iSplit; [done|]. iSplit; [done|]. iSplit.
        - iExists #y, #y, #0, #0.
          iSplit; [done|]. iSplit; [done|].
          iSplit; [iExists y; by auto|iExists 0%nat; by auto].
        - iExists 1%nat; by auto. }
      iIntros (fr fr') "#Hfr /=".
      iDestruct "Hfr" as (p1 p2 q1 q2) "(-> & -> & #Hp & #Hq)".
      iDestruct "Hp" as (pp1 pp2 pq1 pq2) "(-> & -> & #Hyy & #Hii)".
      iDestruct "Hii" as (iyv) "[-> ->]".
      rel_pures_l. rel_pures_r.
      rel_values.
  Qed.

End gwp_list_rel.
