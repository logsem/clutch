(** * Relational parametricity for the [gwp.list] list combinators

    [report_noisy_max_generic.v] (and the idiomatic report-noisy-max) builds its
    lists with the combinators of [gen_prob_lang.gwp.list] (imported there as
    [gwp.list]): [list_init] (OCaml-faithful — forward, 0-indexed:
    [list_init len f = [f 0; …; f (len-1)]]), [list_map], and [list_max_index].

    These combinators have polymorphic, syntactically-typeable counterparts
    ([list_map_poly] / [list_init_poly] / the typed [list_max_index], all typed in
    [typing/list_typed.v]), so their relational congruences ([refines_list_map],
    [refines_list_init], [refines_list_max_index]) come *for free* from the
    fundamental theorem: each is [fundamental_val] on the typed value, with its
    [lrel_forall]/[lrel_arr] structure eliminated and its list argument / result
    bridged through [interp_TList] below ([interp (TList τ) ≡ lrel_list]).  We
    still define the semantic list relation [lrel_list] explicitly (via
    [lrel_rec] — value encoding [NONE = InjLV #()], [SOME x = InjRV x],
    [a::l = SOME(a,l)]), since it is the element/output relation those free
    theorems are read against, at *arbitrary* element relations. *)
From clutch.gen_prob_lang Require Import lang notation.
From clutch.gen_prob_lang Require Import gwp.list.
From clutch.gen_prob_lang.typing Require Import types list_typed.
From clutch.gen_diffpriv Require Import model interp app_rel_rules rel_tactics fundamental.
From clutch.prelude Require Import properness.
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

  (** Bridge between the syntactic list type [TList] and the semantic list
      relation [lrel_list]: the relational interpretation of [TList τ] is
      exactly [lrel_list] over the interpretation of [τ].  This is what lets
      the fundamental theorem's free theorems (stated over [interp (TList _)])
      be read as congruences over [lrel_list] at *arbitrary* element relations.
      The [τ.[ren (+1)]] shift in [TList] cancels the [μ]-bound variable via
      [interp_ren_up]. *)
  Lemma interp_TList (τ : type) (Δ : list (lrel Σ)) :
    interp (TList τ) Δ ≡ lrel_list (interp τ Δ).
  Proof.
    rewrite /lrel_list /TList /=.
    apply fixpoint_proper => X w1 w2 /=.
    rewrite /lrel_list_gen /lrel_rec1 /lrel_car /=.
    unfold lrel_car; simpl.
    properness; auto.
    symmetry. apply (interp_ren_up [] Δ τ X).
  Qed.

  (** The relational congruence for [list_map] over arbitrary related
      expressions, derived "for free" from the fundamental theorem applied to
      the syntactically typed polymorphic combinator [list_map_poly]. *)
  Lemma refines_list_map (A B : lrel Σ) (f f' l l' : expr) :
    (REL f << f' : (A → B)%lrel) -∗
    (REL l << l' : lrel_list A) -∗
    REL list_map_poly #() #() f l << list_map_poly #() #() f' l' : lrel_list B.
  Proof.
    iIntros "Hf Hl".
    iPoseProof (fundamental_val [] list_map_poly _ (list_map_poly_typed _)) as "#Hpoly".
    iSpecialize ("Hpoly" $! A).
    (* The arguments [l] and [f] are the deepest redexes; bind them to values
       first, then the two head type-applications. *)
    rel_bind_l l. rel_bind_r l'.
    iApply (refines_bind with "Hl").
    iIntros (lv lv') "#Hlv /=".
    rel_bind_l f. rel_bind_r f'.
    iApply (refines_bind with "Hf").
    iIntros (fv fv') "#Hfv /=".
    (* First type-application [list_map_poly #()]. *)
    rel_bind_l (App list_map_poly #())%E. rel_bind_r (App list_map_poly #())%E.
    iApply (refines_bind with "[Hpoly]").
    { iApply ("Hpoly" $! #() #()); by []. }
    iIntros (g1 g1') "#Hg1 /=".
    iSpecialize ("Hg1" $! B).
    rel_bind_l (App g1 #())%E. rel_bind_r (App g1' #())%E.
    iApply (refines_bind with "[Hg1]").
    { iApply ("Hg1" $! #() #()); by []. }
    iIntros (g g') "#Hg /=".
    (* [Hg : (A → B) → lrel_list A → lrel_list B], since [TVar1 ↦ A], [TVar0 ↦ B]. *)
    iSpecialize ("Hg" with "Hfv").
    rel_bind_l (g fv)%E. rel_bind_r (g' fv')%E.
    iApply (refines_bind with "Hg").
    iIntros (h h') "#Hh".
    rewrite -(interp_TList (TVar 0) (B :: A :: [])).
    iApply "Hh".
    rewrite (interp_TList (TVar 1) (B :: A :: []) lv lv').
    iApply "Hlv".
  Qed.

  (** Relational congruence for [list_init], derived "for free" from the
      fundamental theorem applied to the typed [list_init_poly].  The index
      relation is [lrel_int], matching the [TInt] index of the OCaml-faithful
      forward [list_init]. *)
  Lemma refines_list_init (A : lrel Σ) (n n' f f' : expr) :
    (REL n << n' : lrel_int) -∗
    (REL f << f' : (lrel_int → A)%lrel) -∗
    REL list_init_poly #() n f << list_init_poly #() n' f' : lrel_list A.
  Proof.
    iIntros "Hn Hf".
    iPoseProof (fundamental_val [] list_init_poly _ (list_init_poly_typed _)) as "#Hpoly".
    iSpecialize ("Hpoly" $! A).
    (* The arguments [n] and [f] are the deepest redexes (rightmost-innermost),
       so bind them to values first; then bind the head type-application. *)
    rel_bind_l f. rel_bind_r f'.
    iApply (refines_bind with "Hf").
    iIntros (fv fv') "#Hfv /=".
    rel_bind_l n. rel_bind_r n'.
    iApply (refines_bind with "Hn").
    iIntros (nv nv') "#Hnv /=".
    (* Now bind the type-application [list_init_poly #()] on both sides. *)
    rel_bind_l (App list_init_poly #())%E. rel_bind_r (App list_init_poly #())%E.
    iApply (refines_bind with "[Hpoly]").
    { iApply ("Hpoly" $! #() #()); by []. }
    iIntros (g g') "#Hg /=".
    (* [Hg : interp (TInt → (TInt → 0) → TList 0) (A::[]) g g'], i.e. the curried
       arrow [lrel_int → (lrel_int → A) → interp (TList 0) (A::[])].  Apply it to
       [nv] then [fv]. *)
    iSpecialize ("Hg" with "Hnv").
    rel_bind_l (g nv)%E. rel_bind_r (g' nv')%E.
    iApply (refines_bind with "Hg").
    iIntros (h h') "#Hh /=".
    iSpecialize ("Hh" with "Hfv").
    (* Goal: [REL h fv << h' fv' : lrel_list A]; [Hh] proves it at
       [interp (TList 0) (A::[])].  Convert the goal's result relation via
       [interp_TList]. *)
    rewrite -(interp_TList (TVar 0) (A :: [])).
    iApply "Hh".
  Qed.

  (** Relational congruence for [list_max_index], derived "for free" from the
      fundamental theorem applied to the syntactically typed [list_max_index]
      (see [list_max_index_typed]).  [list_max_index] is a *monomorphic* value
      typed at [TList TInt → TInt], so its interpretation is directly the arrow
      [interp (TList TInt) [] → interp TInt []]; we only bridge the domain
      [interp (TList TInt) [] ≡ lrel_list (interp TInt [])] via [interp_TList].

      The output relation is [interp TInt [] = lrel_int] (not [lrel_nat]): the
      argmax index is built with integer [+], so the syntactic type is
      [TList TInt → TInt].  This is sound — the index is in fact always a
      [nat] — and nothing downstream depends on its [nat]-ness (the consumers
      only need [∃ k, v = #k ∧ v' = #k], which [lrel_int] provides). *)
  Lemma refines_list_max_index (l l' : expr) :
    (REL l << l' : lrel_list (interp TInt [])) -∗
    REL list_max_index l << list_max_index l' : interp TInt [].
  Proof.
    iIntros "Hl".
    iPoseProof (fundamental_val [] list_max_index _ (list_max_index_typed _)) as "#Hmi".
    (* [Hmi : interp (TList TInt → TInt) [] list_max_index list_max_index], i.e.
       [∀ v1 v2, interp (TList TInt) [] v1 v2 -∗ REL … : interp TInt []].  Bind
       the (expression) arguments [l]/[l'] to values, then feed them to [Hmi],
       bridging the domain [interp (TList TInt) [] ≡ lrel_list (interp TInt [])]
       via [interp_TList]. *)
    rel_bind_l l. rel_bind_r l'.
    iApply (refines_bind with "Hl").
    iIntros (lv lv') "#Hlv /=".
    iApply ("Hmi" with "[Hlv]").
    rewrite (interp_TList TInt [] lv lv').
    iApply "Hlv".
  Qed.

End gwp_list_rel.
