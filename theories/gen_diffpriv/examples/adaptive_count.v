(** Adaptive-composition / privacy-FILTER (RRUV odometer) DP case study, ported
    from [clutch.diffpriv.examples.adaptive_count] to the GENERIC language.
    This is the close sibling of [gen_diffpriv.examples.privacy_filter]: the same
    RRUV privacy-filter odometer ([create_filter] returning a [run_dp]/[try_run]
    runner), but with INTEGER budgets [(budget : Z)] paired with a runtime
    denominator [(den : Z)] (where [privacy_filter] used rational [(num, den)]
    pairs throughout).

    "Enable" the Laplace distribution (one signature + one [SampleIn] instance),
    pin the spec-context [fill], and the proofs go through with the standard
    proof-mode tactics and the library Laplace coupling rules.  As in
    [privacy_filter] / [sum_queries], by the time control reaches a [Laplace]
    draw the [(num,den,mean)] parameter [Pair]s have been reduced (by
    [wp_pures]/[tp_pures]) to a [PairV] VALUE, so the matching coupling rule is
    the reduced VALUE-FORM [wp_couple_laplace (S:=Sg) … 0 1] applied after
    [tp_bind (Sample _ _ _)] / [wp_bind (Sample _ _ _)] (the surface [Laplace …]
    notation no longer matches, since it is folded over the un-reduced [Pair]).

    GEN SPEC-STEPPING NOTE.  On the SPEC side a [tp_load]/[tp_store]/[tp_alloc]
    (and a returning sub-lemma / coupling) leaves the spec term
    [⤇ fill (ctxs ++ K) v] with the next redex buried in the (concrete) inner
    context [ctxs]; the spec [tp_pures] (and a [tp_bind] of a deeper redex) then
    cannot see it.  We re-fold with [tp_normalise] (re-exposing the head redex),
    after which [tp_pures] advances the spec.  Hence the extra [tp_normalise…]
    interleaved through the odometer body (cf. [privacy_filter], same for its
    [rat_lt] / [rat_sub] steps).

    USE OF THE COMPOSITION LAWS.  The per-query work is [Laplace ∘ count] with
    [count = list_length ∘ list_filter].  We make the COUNT-sensitivity structure
    explicit and reusable:

      - [count_sens]: the COUNT [list_length ∘ list_filter] is 1-sensitive, proven
        by sequencing the two 1-sensitive pieces [filter_sens] / [length_sens]
        (the sensitivity-composition argument of [sensitive_comp], specialised to
        the curried [list_filter pred], an [expr] — done by hand in two
        [wp_apply]s).  It is genuinely USED in every spec below for the count step,
        replacing the original's two hand-chained [filter_sens]/[length_sens] WP
        couplings with a single application.

      - [count_query_diffpriv]: a single query [Laplace ∘ count] is [(num/den)]-DP
        (metric form [hoare_diffpriv_metric]), obtained by
        [diffpriv_metric_sensitive_comp count_sens (hoare_laplace_diffpriv …)]
        — the sensitivity·DP composition law.  Exposed as a reusable building block
        (mirrors [privacy_filter.count_query_diffpriv] / [sum_queries]).

    WHAT STAYS BY HAND, AND WHY.  The example's CORE is the dynamic-budget odometer
    ([create_filter] / [run_dp]), which is MORE general than the fixed 2-step
    sequential law — we port it faithfully.  At the [run_dp] closure CALL sites the
    program feeds an ALREADY-COMPUTED count INTEGER (shared between the coarse and
    the precise noise draws) into a data-free closure [f #()] — there is no dataset
    argument in scope, so the [hoare_diffpriv_metric]/[count_query_diffpriv] shape
    (which needs [g (inject x)] for adjacent [x x']) does NOT match there.  Hence those
    noise draws keep the by-hand value-form coupling [wp_couple_laplace … 0 1]
    (with the [|count−count'|≤1] distance established once, up front, by
    [count_sens]). *)
From iris.base_logic Require Export na_invariants.
From clutch.prelude Require Import tactics.
From clutch.common Require Import inject.
From clutch.prob Require Import differential_privacy.
From clutch.gen_diffpriv Require Import adequacy all.
From clutch.gen_diffpriv.lib Require Import laplace.
From clutch.gen_prob_lang Require Import inject families.
From clutch.gen_prob_lang.spec Require Import spec_ra spec_rules.
From clutch.gen_diffpriv.examples Require Import sparse_vector_technique.
From clutch.gen_prob_lang.gwp Require Import gen_weakestpre arith list.
From iris.prelude Require Import options.

(** Keep the family index [sample_idx] folded so the [Laplace] surface notation
    matches the library coupling rules syntactically (cf. [sum_queries]). *)
#[global] Opaque sample_idx.

Definition list_count : val :=
  λ: "p" "l", list_length (list_filter "p" "l").

Definition data : list Z := [25; 30; 31; 22; 40; 35; 29; 29; 31; 30]%Z.

Definition predicates : list (Z → bool) :=
  [λ x, bool_decide (x < 30) ; λ x, bool_decide (30 <= x) ; λ x, bool_decide (x `rem` 2 = 0)]%Z.
Definition vpredicates : val :=
  SOMEV ((λ:"x", "x" < #30)
         , SOMEV ((λ:"x", #30 <= "x")
                  , SOMEV ((λ:"x", "x" `rem` #2 = #0), NONEV))).

Definition create_filter : val :=
  λ:"budget",
  let: "budget_remaining" := ref "budget" in
  let: "try_run" :=
    λ:"ε" "f", if: !"budget_remaining" < "ε" then
             NONE
           else
             ("budget_remaining" <- !"budget_remaining" - "ε" ;;
              SOME ("f" #())) in
  "try_run".

(** Spec-side [GenWp] instance, built from the generic spec step rules — the
    [gwp]-based list operators are also run on the SPEC program.  Identical to
    [privacy_filter.gwp_spec] / [sum_queries.gwp_spec]. *)
Section spec_gwp.
  Context {Sg : Sig} `{!specG_prob_lang Σ, invGS_gen hl Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  Local Notation spec_update :=
    (@spec_update (lang_markov (gen_lang Sg)) Σ _ _ _).

  Notation spec_wp :=
    (λ E e Ψ, ∀ K,
        ⤇ fill K e -∗ spec_update E (∃ (v : val), ⤇ fill K v ∗ Ψ v))%I.

  Lemma gwp_mixin_spec :
    GenWpMixin (S := Sg) false spec_wp (λ l dq v, l ↦ₛ{dq} v)%I.
  Proof.
    constructor; intros.
    - apply _.
    - by iIntros "H" (?) "$".
    - iIntros "H" (?) "Hs". by iMod ("H" with "[$Hs //]") as (?) "[$ >$]".
    - iIntros "H" (?) "Hs". rewrite fill_comp.
      iMod ("H" with "[$Hs //]") as (?) "[Hs Hcnt]". rewrite -fill_comp.
      by iMod ("Hcnt" with "[$Hs //]").
    - iIntros "H" (?) "Hs".
      iMod (step_pure with "Hs") as "Hs"; [done|].
      by iMod ("H" with "[$Hs //]").
    - iIntros "H" (?) "Hs".
      iMod (step_alloc with "Hs") as (l) "($ & Hl)".
      by iApply "H".
    - iIntros "Hl H" (?) "Hs".
      iMod (step_load with "[$Hl $Hs]") as "($ & Hl)".
      by iApply "H".
    - iIntros "Hl H" (?) "Hs".
      iMod (step_store with "[$Hl $Hs]") as "($ & Hl)".
      by iApply "H".
  Qed.

  Canonical Structure gwp_spec := Build_GenWp gwp_mixin_spec.
End spec_gwp.

#[local] Open Scope Z.

Section adaptive.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  Local Notation lidx := (@sample_idx laplace_family Sg _).

  (** A fully-unrolled concrete adaptive program (two coarse/precise rounds with
      a hard-wired budget odometer in a single [ref]).  [Laplace] lives in the
      generic language, so this is an in-section program (cf. [privacy_filter]). *)
  Definition adaptive : val :=
    λ:"data",
    let: "εₛ" := #2 in
    let: "εₗ" := #10 in
    let: "b" := ref #20 in
    let: "counts" := ref [] in

    let: "count_exact_1" := list_count (λ:"x", "x" < #30) "data" in
    let: "count_coarse_1" := Laplace "εₛ" #10 "count_exact_1" #() in
    "b" <- ! "b" -  "εₛ" ;;
    "counts" <- ("count_coarse_1" :: !"counts") ;;
    (if: #5 < "count_coarse_1" then
      let: "count_precise_1" := Laplace "εₗ" #10 "count_exact_1" #() in
      let: "_" := "b" <- ! "b" -  "εₗ" in
      "counts" <- "count_precise_1" :: !"counts"
     else #()) ;;

    let: "count_exact_2" := list_count (λ:"x", "x" < #32) "data" in
    let: "count_coarse_2" := Laplace "εₛ" #10 "count_exact_2" #() in
    let: "_" := "b" <- ! "b" -  "εₛ" in
    "counts" <- ("count_coarse_2" :: !"counts") ;;
    (if: #5 < "count_coarse_2" then
       if: "εₗ" <= !"b" then
         let: "count_precise_2" := Laplace "εₗ" #10 "count_exact_2" #() in
         let: "_" := "b" <- ! "b" -  "εₗ" in
         "counts" <- "count_precise_2" :: !"counts"
       else #()
     else #()) ;;

    !"counts"
  .

  Definition laplace : val :=
    λ:"eps" "mean", Laplace (Fst "eps") (Snd "eps") "mean" #().

  Definition iter_adaptive_acc : val :=
    λ:"ε_coarse" "ε_precise" "den"
      "threshold" "budget" "predicates" "data",
      let: "counts" := ref [] in
      let: "index" := ref #0 in
      let: "try_run" := create_filter "budget" in
      list_iter
        (λ:"pred",
          let: "count_exact" := list_count "pred" "data" in
          "try_run" "ε_coarse"
            (λ:<>,
               let: "count_coarse" := Laplace "ε_coarse" "den" "count_exact" #() in
               let: "idx_coarse" := !"index" in
               "counts" <- ("idx_coarse", "count_coarse") :: !"counts" ;;

               if: "threshold" < "count_coarse" then
                 "try_run" "ε_precise"
                   (λ:<>,
                      let: "count_precise" := Laplace "ε_precise" "den" "count_exact" #() in
                      let: "idx_precise" := !"index" in
                      "counts" <- ("idx_precise", "count_precise") :: !"counts")
               else #()) ;;
          "index" <- !"index" + #1)
        "predicates" ;;
      list_rev ! "counts".

  Lemma create_filter_private K budget den (_ : 0 <= budget) (_ : 0 < den) :
    {{{ ↯m (IZR budget / IZR den) ∗ ⤇ fill K ((of_val create_filter) #budget) }}}
      create_filter #budget
      {{{ try_run, RET try_run;
           ∃ (try_run' : val) l l' budget_remaining,
             ⌜ 0 <= budget_remaining ⌝ ∗
               ↯m (IZR budget_remaining / IZR den) ∗
             l ↦ #budget_remaining ∗
             l' ↦ₛ #budget_remaining ∗
             ⤇ fill K try_run' ∗
             (∀ (ε : Z) K (f f' : val) (budget_remaining : Z) I_f,
                 ⌜ 0 <= ε ⌝ →
                 {{{
                       (∀ K (budget_remaining' : Z),
                           {{{ ↯m (IZR ε / IZR den) ∗
                               ⤇ fill K ((of_val f') #()) ∗
                               I_f ∗
                               ↯m (IZR budget_remaining' / IZR den) ∗
                               l ↦ #budget_remaining' ∗
                               l' ↦ₛ #budget_remaining'
                           }}}
                             (of_val f) #()
                             {{{ v, RET v; ⤇ fill K (of_val v) ∗ I_f
                                           ∗ ∃ (budget_remaining'' : Z),
                                               ↯m (IZR budget_remaining'' / IZR den) ∗
                                               l ↦ #budget_remaining'' ∗
                                               l' ↦ₛ #budget_remaining''
                       }}})
                       ∗
                         ↯m (IZR budget_remaining / IZR den) ∗
                       l ↦ #budget_remaining ∗
                       l' ↦ₛ #budget_remaining ∗
                       I_f ∗
                       ⤇ fill K (try_run' #ε f')
                 }}}
                   ((of_val try_run) #ε f : expr)
                   {{{ v, RET v;
                       ⤇ fill K (of_val v) ∗
                       I_f ∗
                       ∃ budget_remaining,
                         ↯m (IZR budget_remaining / IZR den) ∗
                         l ↦ #budget_remaining ∗
                         l' ↦ₛ #budget_remaining
             }}})
      }}}.
  Proof with (tp_pures ; wp_pures).
    iIntros "% (ε & rhs) Hpost". rewrite /create_filter...
    tp_alloc as budget_r "budget_r" ; wp_alloc budget_l as "budget_l"...
    iModIntro. iApply "Hpost". iExists _,_,_,_ ; iFrame. iSplit => //.
    iIntros "* % !> * (f_dp & ε & budget_l & budget_r & I_f & rhs) Hpost"... tp_load ; wp_load...
    tp_normalise...
    case_bool_decide as h ; tp_normalise... 1: iApply "Hpost" ; iFrame ; done.
    assert (ε <= budget_remaining) as h' by lia.
    iDestruct (ecm_split (IZR ε / IZR den)%R (IZR (budget_remaining - ε) / IZR den)%R with "[ε]") as "[ε εrem]".
    1,2: repeat real_solver_partial ; qify_r ; zify_q ; lia.
    1: iApply ecm_eq ; [|iFrame].
    1: { rewrite minus_IZR ; field. intro F. assert (den ≠ 0) as hh by lia. apply hh.
         by apply eq_IZR. }

    tp_load ; wp_load... tp_normalise... tp_store ; wp_store... tp_normalise...
    tp_bind (f' _) ; wp_bind (f _).
    iApply ("f_dp" with "[$rhs $ε $I_f $budget_l $budget_r $εrem]").
    simpl. iNext. iIntros "* [??]"... iApply "Hpost".
    iFrame. done.
  Qed.

  (* We can make the resources that try_run depends on abstract. *)
  Lemma create_filter_private' K budget den (_ : 0 <= budget) (_ : 0 < den) :
    {{{ ↯m (IZR budget / IZR den) ∗ ⤇ fill K ((of_val create_filter) #budget) }}}
      create_filter #budget
      {{{ try_run, RET try_run;
           ∃ (try_run' : val) (TRY_RUN : iProp Σ),
             ⤇ fill K try_run' ∗
             TRY_RUN ∗
             (∀ (ε : Z) K (f f' : val) I_f,
                 ⌜ 0 <= ε ⌝ →
                 {{{
                       (∀ K,
                           {{{ ↯m (IZR ε / IZR den) ∗ ⤇ fill K ((of_val f') #()) ∗ I_f ∗ TRY_RUN }}}
                             (of_val f) #()
                             {{{ v, RET v; ⤇ fill K (of_val v) ∗ I_f ∗ TRY_RUN
                       }}})
                       ∗
                         ⤇ fill K (try_run' #ε f') ∗
                       I_f ∗
                       TRY_RUN
                 }}}
                   ((of_val try_run) #ε f : expr)
                   {{{ v, RET v;
                       ⤇ fill K (of_val v) ∗
                       I_f ∗
                       TRY_RUN
             }}})
      }}}.
  Proof with (tp_pures ; wp_pures).
    iIntros "% (ε & rhs) Hpost".
    iApply (create_filter_private with "[$]") => //.
    iNext. iIntros "% (% & % & % & % & % & ε & l & l' & rhs & #h)".
    iApply "Hpost".
    set (inv := (∃ budget_remaining,
                  ↯m (IZR budget_remaining / IZR den) ∗
                  l ↦ #budget_remaining ∗
                  l' ↦ₛ #budget_remaining)%I).
    iExists _,inv. iFrame.
    iIntros "* % !> * (#f_dp & rhs & I_f & TRY_RUN) Hpost"...
    iDestruct "TRY_RUN" as "(% & ε & l & l')".
    iApply ("h" $! ε _ f f' budget_remaining0 I_f with "[] [-Hpost] [Hpost]") => // ; iFrame.
    iIntros "* % !> (ε & rhs & if & εrem & l & l') Hpost".
    iApply ("f_dp" with "[-Hpost]") ; iFrame.
  Qed.

  Definition is_predicate {A} `[Inject A val] (pred : A -> bool) (vpred : val) : iProp Σ :=
    ∀ x, {{{ True }}} vpred (inject x) {{{ w, RET w; ⌜w = (inject (pred x))⌝ }}}.

  Definition is_spec_predicate {A} `[Inject A val] (pred : A -> bool) (vpred : val) : iProp Σ :=
    ∀ x, G{{{ True }}} vpred (inject x) @ gwp_spec (Sg:=Sg) ; ⊤ {{{ w, RET w; ⌜w = (inject (pred x))⌝ }}}.

  Fixpoint is_predicate_list {A} `[Inject A val] (l : list (A -> bool)) (v : val) : iProp Σ :=
    match l with
    | [] => ⌜v = NONEV⌝
    | pred::l' => ∃ vpred vl',
    ⌜v = SOMEV (vpred, vl')⌝
     ∗ is_predicate pred vpred ∗ is_spec_predicate pred vpred ∗ is_predicate_list l' vl' end.

  Lemma filter_sens (P : Z → bool) (f : val) :
    (∀ (x : Z),
        {{{ True }}}
          f (inject x)
          {{{ w, RET w; ⌜w = inject (P x)⌝ }}})
    -∗
    (∀ (x : Z),
        G{{{ True }}}
          f (inject x) @ gwp_spec (Sg:=Sg) ; ⊤
          {{{ w, RET w; ⌜w = inject (P x)⌝ }}})
    -∗
    hoare_sensitive Sg (list_filter f) 1 (dlist Z) (dlist Z).
  Proof.
    iIntros "* #Hf #Hf'".
    iIntros (?) "* !> * rhs HΦ".
    simpl.
    iPoseProof (gwp_list_filter (g:=gwp_spec (Sg:=Sg)) _ x' f (inject x') _
                  (λ v, ⌜is_list (filter P x') v⌝)%I with "[] []") as "hh'" => // ; [iSplit|..].
    1: { iIntros (??) "!> * _ h". by iApply "Hf'". }
    1: iPureIntro ; apply is_list_inject.
    1: done.
    { simpl. iIntros. done. }
    simpl. iMod ("hh'" with "rhs") as "(% & rhs & %)".
    iApply (gwp_list_filter (g:=gwp_wpre) _ x f (inject x) _ _ %I with "[Hf] [HΦ rhs]") => //.
    1: iSplit.
    1: { iIntros (??) "!> * _ h". by iApply "Hf". }
    1: iPureIntro ; apply is_list_inject.
    1: done.
    simpl. iNext. iIntros. iApply "HΦ".
    iExists (filter P x), (filter P x').
    repeat iSplit ; iFrame ; try iPureIntro.
    - apply is_list_inject => //.
    - assert (v = (inject (filter P x'))) as -> => //.
      apply is_list_inject => //.
    - rewrite Rmult_1_l. apply IZR_le.
      apply list_filter_bound.
  Qed.

  Lemma length_sens :
    ⊢ hoare_sensitive Sg list_length 1 (dlist Z) dZ.
  Proof.
    iIntros (?) "* !> * rhs HΦ".
    simpl.

    iMod (gwp_list_length (g:=gwp_spec (Sg:=Sg)) _ x' (inject x')
                  (λ v, ⌜v = #(List.length x')⌝)%I with "[] [] [rhs]") as "(% & rhs & %)" => //.
    1: iPureIntro ; by apply is_list_inject.
    { simpl. iIntros. subst. done. }
    iApply (gwp_list_length (g:=gwp_wpre) _ x (inject x) with "[] [HΦ rhs]") => //.
    1: iPureIntro ; by apply is_list_inject.
    simpl. iNext. iIntros. iApply "HΦ". iExists (length x),(length x'). simplify_eq.
    repeat iSplit ; iFrame ; iPureIntro => //. rewrite Rmult_1_l.
    rewrite Rabs_Zabs.
    qify_r ; zify_q. ring_simplify.
    apply list_length_bound.
  Qed.

  (** COMPOSITION LAW (sensitivity).  The count [list_count pred = λ x,
      list_length (list_filter pred x)] is 1-sensitive, established by sequencing
      the two 1-sensitive pieces [filter_sens] / [length_sens] (sensitivities
      multiply, [1·1 = 1]) — the [sensitive_comp] argument, specialised to the
      curried [list_filter pred] (an [expr]).  USED below for the count step. *)
  Lemma count_sens (P : Z → bool) (f : val) :
    (∀ (x : Z),
        {{{ True }}}
          f (inject x)
          {{{ w, RET w; ⌜w = inject (P x)⌝ }}})
    -∗
    (∀ (x : Z),
        G{{{ True }}}
          f (inject x) @ gwp_spec (Sg:=Sg) ; ⊤
          {{{ w, RET w; ⌜w = inject (P x)⌝ }}})
    -∗
    hoare_sensitive Sg (list_count f) 1 (dlist Z) dZ.
  Proof.
    iIntros "* #Hf #Hf'".
    iIntros (c_pos) "* !> * rhs HΦ".
    rewrite /list_count. wp_pures. tp_pures.
    tp_bind (list_filter _ _) ; wp_bind (list_filter _ _).
    wp_apply (wp_wand with "[rhs]").
    { iApply (filter_sens P f with "Hf Hf' [] rhs"); [iPureIntro; lra|]. iIntros "!> % h"; iExact "h". }
    simpl. iIntros "% (%ds_f1&%ds_f2&->&rhs&%d_out)".
    tp_bind (list_length _) ; wp_bind (list_length _).
    wp_apply (wp_wand with "[rhs]").
    { iApply (length_sens $! _ _ _ _ with "rhs"). iNext. iIntros "* H". iApply "H". }
    simpl. iIntros "% (%len_l&%len_r&->&rhs&%d_out')".
    iApply "HΦ". iExists len_l, len_r. iFrame. iPureIntro.
    split; [done|]. etrans; [apply d_out'|]. rewrite Rmult_1_l.
    etrans; [apply d_out|]. rewrite Rmult_1_l. done.
    Unshelve. all: try exact Sg; try (lra).
  Qed.

  (** COMPOSITION LAW (sensitivity · DP).  A single query [Laplace ∘ count] is
      [(num/den)]-DP in the metric [hoare_diffpriv_metric] form: the 1-sensitive
      [count_sens] composed with the [(num/den)]-DP Laplace mechanism
      [hoare_laplace_diffpriv] via [diffpriv_metric_sensitive_comp] gives budget
      [1·(num/den) = (num/den)] (and additive [0·grp eps 1 = 0]).  Exposed
      as a reusable building block (mirrors [privacy_filter.count_query_diffpriv]).
      The odometer program SHARES the count between draws, so this exact lemma is
      not the direct fit at the [run_dp] sites (see header); the by-hand surface
      coupling is used there instead. *)
  Lemma count_query_diffpriv (P : Z → bool) (f : val) (num den : Z) :
    (0 < IZR num / IZR den)%R →
    (∀ (x : Z),
        {{{ True }}}
          f (inject x)
          {{{ w, RET w; ⌜w = inject (P x)⌝ }}})
    -∗
    (∀ (x : Z),
        G{{{ True }}}
          f (inject x) @ gwp_spec (Sg:=Sg) ; ⊤
          {{{ w, RET w; ⌜w = inject (P x)⌝ }}})
    -∗
    hoare_diffpriv_metric Sg
      (λ:"x", (λ:"loc", Laplace #num #den "loc" #())%V ((λ:"x", list_count f "x")%V "x"))
      (IZR num / IZR den) 0 (dlist Z) Z.
  Proof.
    iIntros (Hpos) "#Hf #Hf'".
    rewrite -{1}(Rmult_1_l (IZR num / IZR den)) -{1}(Rmult_0_l (grp (IZR num / IZR den) 1)).
    iApply (diffpriv_metric_sensitive_comp Sg
              (λ:"x", list_count f "x")%V
              (λ: "loc", Laplace #num #den "loc" #())%V
              (IZR num / IZR den) 0 1 (dlist Z) dZ (C := Z)); [done|lra| |].
    - iIntros (c_pos) "* !> * rhs HΦ". wp_pures. tp_pures.
      iApply (count_sens P f with "Hf Hf' [] rhs"); [iPureIntro; lra|].
      iApply "HΦ".
    - by iApply hoare_laplace_diffpriv.
  Qed.

  Lemma wp_adaptive (ds1 ds2 : list Z) dsv1 dsv2 K :
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ↯m (IZR 20 / IZR 10) -∗
    ⤇ fill K (adaptive dsv2) -∗
    WP adaptive dsv1 {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "* % %". iIntros "%adj". iIntros "ε rhs". rewrite /adaptive...
    tp_alloc as b_r "b_r". wp_alloc b_l as "b_l"...
    tp_alloc as counts_r "counts_r". wp_alloc counts_l as "counts_l"...
    replace dsv1 with (inject ds1). 2: symmetry ; by apply is_list_inject.
    replace dsv2 with (inject ds2). 2: symmetry ; by apply is_list_inject.
    (* COUNT STEP via the count-sensitivity lemma [count_sens]. *)
    tp_bind (list_count _ _) ; wp_bind (list_count _ _).
    wp_apply (wp_wand with "[rhs]").
    { iApply (count_sens (λ x : Z, bool_decide (x < 30)) _ with "[] [] [] rhs"); [..|iPureIntro; lra| iIntros "!> % h"; iExact "h"].
      - iIntros "* !> * _ HΦ"... case_bool_decide as h ; by iApply "HΦ".
      - iIntros "* !> * ? HΦ". gwp_pures. case_bool_decide as h ; by iApply "HΦ". }
    simpl. iIntros "% (%len_f_l&%len_f_r&->&rhs&%d_out)"... tp_normalise...

    tp_bind (Sample _ _ _) ; wp_bind (Sample _ _ _).
    iDestruct (ecm_split (IZR 2 / IZR 10)%R (IZR 18 / IZR 10)%R with "[ε]") as "[εₛ ε]".
    1,2: real_solver. 1: iApply ecm_eq ; [|iFrame] ; real_solver.

    assert (Z.abs (len_f_l - len_f_r) <= 1).
    {
      assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
      2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
      etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
      etrans. 1: eassumption. rewrite Rmult_1_l.
      done.
    }
    couple_laplace_apply 0%Z 1%Z with "[$rhs εₛ]".
    { lra. }
    { rewrite Rmult_1_l ; iFrame "εₛ". }
    iNext. iIntros (count_coarse_1) "rhs" ; simpl... rewrite Z.add_0_r.
    tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store... tp_normalise...
    rewrite /list_cons.
    tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store...
    tp_normalise... case_bool_decide as cc1 ; tp_normalise...

    - tp_bind (Sample _ _ _) ; wp_bind (Sample _ _ _).
      iDestruct (ecm_split (IZR 10 / IZR 10)%R (IZR 8 / IZR 10)%R with "[ε]") as "[εₗ ε]".
      1,2: real_solver. 1: iApply ecm_eq ; [|iFrame] ; real_solver.
      couple_laplace_apply 0%Z 1%Z with "[$rhs εₗ]".
      { lra. }
      { rewrite Rmult_1_l ; iFrame "εₗ". }
      iNext. iIntros (count_precise_1) "rhs" ; simpl... rewrite Z.add_0_r.
      tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store... tp_normalise...
      tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store... tp_normalise...

      tp_bind (list_count _ _) ; wp_bind (list_count _ _).
      wp_apply (wp_wand with "[rhs]").
      { iApply (count_sens (λ x : Z, bool_decide (x < 32)) _ with "[] [] [] rhs"); [..|iPureIntro; lra| iIntros "!> % h"; iExact "h"].
        - iIntros "* !> * _ HΦ"... case_bool_decide as h ; by iApply "HΦ".
        - iIntros "* !> * ? HΦ". gwp_pures. case_bool_decide as h ; by iApply "HΦ". }
      simpl. iIntros "% (%len_f2_l&%len_f2_r&->&rhs&%d_out2)"...

      assert (Z.abs (len_f2_l - len_f2_r) <= 1).
      {
        assert (Rabs (IZR (len_f2_l - len_f2_r)) <= 1)%R as h.
        2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
        etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
        etrans. 1: eassumption. rewrite Rmult_1_l.
        done.
      }

      tp_bind (Sample _ _ _) ; wp_bind (Sample _ _ _).
      iDestruct (ecm_split (IZR 2 / IZR 10)%R (IZR 6 / IZR 10)%R with "[ε]") as "[εₛ ε]".
      1,2: real_solver. 1: iApply ecm_eq ; [|iFrame] ; real_solver.
      couple_laplace_apply 0%Z 1%Z with "[$rhs εₛ]".
      { lra. }
      { rewrite Rmult_1_l ; iFrame "εₛ". }
      iNext. iIntros (count_coarse_2) "rhs" ; simpl... rewrite Z.add_0_r.
      tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store... tp_normalise...
      tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store...
      tp_normalise... case_bool_decide as cc2 ; tp_normalise...
      2: tp_load ; wp_load ; done.

      tp_load ; wp_load... tp_normalise... tp_load ; wp_load ; done.

    - tp_bind (list_count _ _) ; wp_bind (list_count _ _).
      wp_apply (wp_wand with "[rhs]").
      { iApply (count_sens (λ x : Z, bool_decide (x < 32)) _ with "[] [] [] rhs"); [..|iPureIntro; lra| iIntros "!> % h"; iExact "h"].
        - iIntros "* !> * _ HΦ"... case_bool_decide as h ; by iApply "HΦ".
        - iIntros "* !> * ? HΦ". gwp_pures. case_bool_decide as h ; by iApply "HΦ". }
      simpl. iIntros "% (%len_f2_l&%len_f2_r&->&rhs&%d_out2)"...

      assert (Z.abs (len_f2_l - len_f2_r) <= 1).
      {
        assert (Rabs (IZR (len_f2_l - len_f2_r)) <= 1)%R as h.
        2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
        etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
        etrans. 1: eassumption. rewrite Rmult_1_l.
        done.
      }

      tp_bind (Sample _ _ _) ; wp_bind (Sample _ _ _).
      iDestruct (ecm_split (IZR 2 / IZR 10)%R (IZR 16 / IZR 10)%R with "[ε]") as "[εₛ ε]".
      1,2: real_solver. 1: iApply ecm_eq ; [|iFrame] ; real_solver.
      couple_laplace_apply 0%Z 1%Z with "[$rhs εₛ]".
      { lra. }
      { rewrite Rmult_1_l ; iFrame "εₛ". }
      iNext. iIntros (count_coarse_2) "rhs" ; simpl... rewrite Z.add_0_r.
      tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store... tp_normalise...
      tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store...
      tp_normalise... case_bool_decide as cc2 ; tp_normalise...
      2: tp_load ; wp_load ; done.

      tp_load ; wp_load... tp_normalise...

      tp_bind (Sample _ _ _) ; wp_bind (Sample _ _ _).
      iDestruct (ecm_split (IZR 10 / IZR 10)%R (IZR 6 / IZR 10)%R with "[ε]") as "[εₗ ε]".
      1,2: real_solver. 1: iApply ecm_eq ; [|iFrame] ; real_solver.
      couple_laplace_apply 0%Z 1%Z with "[$rhs εₗ]".
      { lra. }
      { rewrite Rmult_1_l ; iFrame "εₗ". }
      iNext. iIntros (count_precise_2) "rhs" ; simpl... rewrite Z.add_0_r.
      tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store... tp_normalise...
      tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store... tp_normalise...

      tp_load ; wp_load ; done.
      Unshelve. all: try exact Sg.
  Qed.

  Definition iter_adaptive_acc_simple_unrolled : val :=
    λ:"ε_coarse" "den" "budget" "pred" "data",
      let: "counts" := ref [] in
      let: "try_run" := create_filter "budget" in

      let: "count" := list_count "pred" "data" in
      "try_run" "ε_coarse"
        (λ:<>,
           let: "count_coarse" := Laplace "ε_coarse" "den" "count" #() in
           "counts" <- "count_coarse" :: !"counts") ;;

      ! "counts".

  (* No conditional nested call, just iterate through predicates until the budget is gone. *)
  Definition iter_adaptive_acc_simple : val :=
    λ:"ε_coarse" "den" "budget" "predicates" "data",
      let: "counts" := ref [] in
      let: "try_run" := create_filter "budget" in
      list_iter
        (λ:"pred",
          let: "count" := list_count "pred" "data" in
          "try_run" "ε_coarse"
            (λ:<>,
               let: "count_coarse" := Laplace "ε_coarse" "den" "count" #() in
               "counts" <- "count_coarse" :: !"counts"))
        "predicates" ;;
      ! "counts".

  Lemma vpreds_is_predicate_list : ⊢ is_predicate_list predicates vpredicates.
  Proof.
    simpl. repeat (iExists _,_ ; repeat iSplitR => //).
    - iIntros (??) "!> _ HΦ". wp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
    - iIntros (??) "!> _ HΦ". gwp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
    - iIntros (??) "!> _ HΦ". wp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
    - iIntros (??) "!> _ HΦ". gwp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
    - iIntros (??) "!> _ HΦ". wp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
      do 2 case_bool_decide; simplify_eq=>//.
      exfalso; apply H. f_equal. rewrite H0. done.
    - iIntros (??) "!> _ HΦ". gwp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
      do 2 case_bool_decide; simplify_eq=>//.
      exfalso; apply H. f_equal. rewrite H0. done.
  Qed.

  Lemma wp_iter_adaptive_acc_simple_unrolled (ε_coarse den budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K (pred : (Z -> bool)) (vpred : val)
    (_ : 0 < ε_coarse) (_ : 0 < den) (_ : 0 <= budget)
    :
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    is_predicate pred vpred -∗
    is_spec_predicate pred vpred -∗
    ↯m (IZR budget / IZR den) -∗
    ⤇ fill K (iter_adaptive_acc_simple_unrolled #ε_coarse #den #budget vpred dsv2) -∗
    WP iter_adaptive_acc_simple_unrolled #ε_coarse #den #budget vpred dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "* % %". iIntros "%adj". iIntros "#is_pred #is_spec_pred ε rhs". rewrite /iter_adaptive_acc_simple_unrolled...
    tp_alloc as counts_r "counts_r" ; wp_alloc counts_l as "counts_l"...
    tp_bind (create_filter _). wp_bind (create_filter _).
    iApply (create_filter_private _ _ den with "[$ε $rhs]") => //.
    iIntros "!> * (%&%&%&%&%&budget&l&l'&rhs&run_dp)"... tp_normalise...

       replace dsv1 with (inject ds1).
       2: symmetry ; by apply is_list_inject.
       replace dsv2 with (inject ds2).
       2: symmetry ; by apply is_list_inject.
       (* COUNT STEP via [count_sens]. *)
       tp_bind (list_count _ _) ; wp_bind (list_count _ _).
       wp_apply (wp_wand with "[rhs]").
       { iApply (count_sens pred vpred with "is_pred is_spec_pred [] rhs"); [iPureIntro; lra|]. iIntros "!> % h"; iExact "h". }
       simpl.
       iIntros "% (%len_f_l&%len_f_r&->&rhs&%d_out')"...
       tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
       set (I := (∃ counts, counts_r ↦ₛ counts ∗ counts_l ↦ counts)%I).
       iApply ("run_dp" $! _ _ _ _ _ I with "[] [-]") => // ; iFrame. 1: iPureIntro ; lia.
       - iIntros "* % !> (eps & rhs & I & l & l') Hpost"...
         assert (Z.abs (len_f_l - len_f_r) <= 1).
         {
           assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
           2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
           etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
           etrans. 1: eassumption. rewrite Rmult_1_l.
           done.
         }
         couple_laplace 0 1 with "[$rhs eps]".
         { epose proof (IZR_lt 0 ε_coarse _) => //.
           epose proof (IZR_lt 0 den _) => //.
           apply Rcomplements.Rdiv_lt_0_compat => //. }
         1: rewrite Rmult_1_l ; iFrame "eps".
         iNext. iIntros (count_precise_2) "rhs" ; simpl... rewrite Z.add_0_r.
         iDestruct "I" as "(% & ? & ?)". rewrite /list_cons.
         tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store. iApply "Hpost". iFrame. done.

       - iNext. iIntros "* (?&(%&?&?)&(%&?&?&?))" => /=... tp_load ; wp_load. done.
         Unshelve. all: try exact Sg ; auto ; lra.
     Qed.

  Fixpoint is_list_HO (l : list val) (v : val) :=
    match l with
    | [] => v = NONEV
    | w::l' => ∃ lv, v = SOMEV (w, lv) ∧ is_list_HO l' lv
  end.

  Lemma wp_list_iter_invariant_HO' (Ψ: list val -> list val -> iProp Σ) E l (fv lv : val) lrest :
    (∀ lpre (w : val) lsuf,
        {{{ Ψ lpre (w :: lsuf) }}}
          fv w @ E
        {{{v, RET v; Ψ (lpre ++ [w]) lsuf }}}) -∗
    {{{ ⌜ is_list_HO l lv ⌝ ∗ Ψ lrest l }}}
      list_iter fv lv @ E
    {{{ RET #(); Ψ (lrest++l) [] }}}.
  Proof.
    rewrite /list_iter.
    iInduction l as [|a l'] "IH" forall (lv lrest).
    - iIntros "#Helem";
      iIntros (Φ') "!# (Hlist & HΨ) HΦ'";
      iDestruct "Hlist" as "%Hlist"; simpl in Hlist; subst; wp_pures.
      iApply "HΦ'".
      rewrite app_nil_r //.
    - iIntros "#Helem";
      iIntros (Φ') "!# (Hlist & HΨ) HΦ'".
      iDestruct "Hlist" as "%Hlist"; simpl in Hlist; subst; wp_pures.
      destruct Hlist as [lv' [Hlv Hlcoh]]; subst.
      wp_pures.
      wp_apply ("Helem" with "[$HΨ]").
      iIntros (v) "HΨ".
      do 2 wp_pure.
      iApply ("IH" $! lv' (lrest ++ [a]) with "[$Helem] [$HΨ //]").
      iModIntro.
      by rewrite -app_assoc.
  Qed.

  Lemma wp_list_iter_invariant_HO (Ψ: list val -> list val -> iProp Σ) E l (fv lv : val) :
    (∀ lpre (w : val) lsuf,
        {{{ Ψ lpre (w :: lsuf) }}}
          fv w @ E
        {{{v, RET v; Ψ (lpre ++ [w]) lsuf }}}) -∗
    {{{ ⌜ is_list_HO l lv ⌝ ∗ Ψ [] l }}}
      list_iter fv lv @ E
    {{{ RET #(); Ψ l [] }}}.
  Proof.
    replace l with ([]++l); last by apply app_nil_l.
    iApply wp_list_iter_invariant_HO'.
  Qed.

  Lemma wp_iter_adaptive_acc_simple (ε_coarse den budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K
    (predicates : list (Z -> bool))
    (lvpredicates : list val)
    (vpredicates : val)
    (_ : 0 < ε_coarse) (_ : 0 < den) (_ : 0 <= budget)
    :
    length predicates = length lvpredicates →
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ⌜is_list_HO lvpredicates vpredicates⌝ -∗
    ([∗ list] pred;vpred ∈ predicates;lvpredicates, is_predicate pred vpred ∗ is_spec_predicate pred vpred) -∗
    ↯m (IZR budget / IZR den) -∗
    ⤇ fill K (iter_adaptive_acc_simple #ε_coarse #den #budget vpredicates dsv2) -∗
    WP iter_adaptive_acc_simple #ε_coarse #den #budget vpredicates dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "%hlen * % %". iIntros "%adj".
    iIntros "%ho_pred #is_pred ε rhs".
    rewrite /iter_adaptive_acc_simple...
    tp_alloc as counts_r "counts_r" ; wp_alloc counts_l as "counts_l"...
    tp_bind (create_filter _). wp_bind (create_filter _).
    iApply (create_filter_private _ _ den with "[$ε $rhs]") => //.
    iIntros "!> * (%&%&%&%&%&budget&l&l'&rhs&#run_dp)"... simpl...
    tp_bind (list_iter _ _). wp_bind (list_iter _ _).
    iAssert (∃ counts budget_remaining,
                counts_l ↦ counts ∗ counts_r ↦ₛ counts ∗
                ↯m (IZR budget_remaining / IZR den) ∗
                    l ↦ #budget_remaining ∗ l' ↦ₛ #budget_remaining
            )%I with "[counts_l counts_r budget l l']" as "hh". 1: iFrame.
    iRevert (predicates vpredicates ho_pred hlen) "is_pred rhs".
    iInduction lvpredicates as [|vpred lvpredicates'] "IH" ;
      iIntros (predicates vpredicates ho_pred hlen) "#is_pred rhs".
    - rewrite ho_pred.
      rewrite /list_iter...
      iDestruct "hh" as "(%&%&?&?&?&?&?)".
      tp_normalise... tp_load... wp_load. done.
    - simpl in ho_pred. destruct ho_pred as (vpredicates' & hpred & ho_pred). rewrite hpred.
      rewrite /list_iter...
      replace dsv1 with (inject ds1).
      2: symmetry ; by apply is_list_inject.
      replace dsv2 with (inject ds2).
      2: symmetry ; by apply is_list_inject.
      destruct predicates as [|pred predicates'] => //.
      iDestruct (big_sepL2_cons_inv_l with "is_pred") as "(%vpred'&%&%&[#Hp #Hp']&is_pred')" ; simplify_eq.
      (* COUNT STEP via [count_sens]. *)
      fold list_iter.
      tp_bind (list_count _ _) ; wp_bind (list_count _ _).
      wp_apply (wp_wand with "[rhs]").
      { iApply (count_sens pred vpred' with "Hp Hp' [] rhs"); [iPureIntro; lra|]. iIntros "!> % h"; iExact "h". }
      simpl.
      iIntros "% (%len_f_l&%len_f_r&->&rhs&%d_out')"...
      tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
      set (I := (∃ counts, counts_r ↦ₛ counts ∗ counts_l ↦ counts)%I).
      iDestruct "hh" as "(%&%&?&?&?&?&?)".
      iApply ("run_dp" $! _ _ _ _ _ I with "[] [-]") => // ; iFrame. 1: iPureIntro ; lia.
      + iIntros "* % !> (eps & rhs & I & l & l') Hpost"...
        assert (Z.abs (len_f_l - len_f_r) <= 1).
        {
          assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
          2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
          etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
          etrans. 1: eassumption. rewrite Rmult_1_l.
          done.
        }
        couple_laplace 0 1 with "[$rhs eps]".
        {
          epose proof (IZR_lt 0 ε_coarse _) => //.
          epose proof (IZR_lt 0 den _) => //.
          apply Rcomplements.Rdiv_lt_0_compat => //. }
        1: rewrite Rmult_1_l ; iFrame "eps".
        iNext. iIntros (count_precise_2) "rhs" ; simpl... rewrite Z.add_0_r.
        iDestruct "I" as "(% & ? & ?)". rewrite /list_cons.
        tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store. iApply "Hpost". iFrame. done.

         + iNext. iIntros "* (rhs&(%&counts_r&counts_l)&(%&budget&l&l'))" => /=...
           iApply ("IH" with "[$l $l' $counts_r $counts_l $budget] [] [] [] [$rhs]") => //.
           Unshelve. all: try exact Sg ; auto ; lra.
     Qed.

  Definition lvpredicates : list val :=
    [(λ:"x", "x" < #30) ; (λ:"x", #30 <= "x") ; (λ:"x", "x" `rem` #2 = #0)]%V.

  Lemma lvpredicates_is_list_HO : is_list_HO lvpredicates vpredicates.
  Proof.
    repeat (eexists ; split ; eauto).
  Qed.

  Lemma predicates_lvpredicates_is_predicate :
    ⊢ ([∗ list] pred;vpred ∈ predicates;lvpredicates, is_predicate pred vpred ∗ is_spec_predicate pred vpred).
  Proof.
    repeat iSplit. 7: done.
    - iIntros (??) "!> _ HΦ". wp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
    - iIntros (??) "!> _ HΦ". gwp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
    - iIntros (??) "!> _ HΦ". wp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
    - iIntros (??) "!> _ HΦ". gwp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.

    - iIntros (??) "!> _ HΦ". wp_pures.
      case_decide.
      { rewrite !bool_decide_eq_true_2 //; [|by do 2 f_equal]. by iApply "HΦ". }
      rewrite !bool_decide_eq_false_2 //; [|by intros [=]]. by iApply "HΦ".
    - iIntros (??) "!> _ HΦ". gwp_pures.
      iApply "HΦ". iPureIntro. simpl. repeat f_equal.
      case_decide; simplify_eq /=.
      { rewrite !bool_decide_eq_true_2 //. }
      rewrite !bool_decide_eq_false_2 //.
      intros ?. apply H. do 2 f_equal. done.
  Qed.

  Lemma wp_iter_adaptive_acc_simple_app (ε_coarse den budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K
    (_ : 0 < ε_coarse) (_ : 0 < den) (_ : 0 <= budget)
    :
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ↯m (IZR budget / IZR den) -∗
    ⤇ fill K (iter_adaptive_acc_simple #ε_coarse #den #budget vpredicates dsv2) -∗
    WP iter_adaptive_acc_simple #ε_coarse #den #budget vpredicates dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "%hlen * % % ε rhs".
    iApply (wp_iter_adaptive_acc_simple with "[] [] ε rhs") ; last first.
    1: iApply predicates_lvpredicates_is_predicate. 1: iPureIntro ; apply lvpredicates_is_list_HO. all: eauto.
  Qed.

  (* This is the spec one would want for iter_adaptive_acc.  After the [iter_adaptive_acc]
     odometer body was de-nested (the index load lifted into a [let] so the spec [tp_load]
     can step it), the proof goes through with the same odometer argument used by the
     abstracted [wp_iter_adaptive_acc'] below (the [create_filter_private'] filter spec). *)
  Lemma wp_iter_adaptive_acc (ε_coarse ε_precise den threshold budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K
    (predicates : list (Z -> bool))
    (lvpredicates : list val)
    (vpredicates : val)
    (_ : 0 < ε_coarse) (_ : 0 < ε_precise) (_ : 0 < den) (_ : 0 <= budget)
    :
    length predicates = length lvpredicates →
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ⌜is_list_HO lvpredicates vpredicates⌝ -∗
    ([∗ list] pred;vpred ∈ predicates;lvpredicates, is_predicate pred vpred ∗ is_spec_predicate pred vpred) -∗
    ↯m (IZR budget / IZR den) -∗
    ⤇ fill K (iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv2) -∗
    WP iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "%hlen * % %". iIntros "%adj".
    iIntros "%ho_pred #is_pred ε rhs".
    rewrite /iter_adaptive_acc...
    tp_alloc as counts_r "counts_r" ; wp_alloc counts_l as "counts_l"...
    tp_alloc as index_r "index_r" ; wp_alloc index_l as "index_l"...
    tp_bind (create_filter _). wp_bind (create_filter _).
    iApply (create_filter_private' _ _ den with "[$ε $rhs]") => //.
    iIntros "!> * (%&%&rhs&TRY_RUN&#run_dp)"... simpl...
    tp_bind (list_iter _ _). wp_bind (list_iter _ _).
    set (Inv := (∃ lcounts counts (index : Z), ⌜is_list lcounts counts⌝ ∗ counts_l ↦ counts ∗ counts_r ↦ₛ counts
                                               ∗ index_l ↦ #index ∗ index_r ↦ₛ #index)%I).
    iAssert Inv with "[counts_l counts_r index_l index_r]" as "hh". 1: iFrame ; iExists [] ; done.
    iRevert (predicates vpredicates ho_pred hlen) "is_pred rhs TRY_RUN".
    iInduction lvpredicates as [|vpred lvpredicates'] "IH" ;
      iIntros (predicates vpredicates ho_pred hlen) "#is_pred rhs TRY_RUN".
    - rewrite ho_pred.
      rewrite /list_iter...
      iDestruct "hh" as "(%&%&%&%&?&?&?&?)".
      tp_normalise... tp_load... wp_load.
      iMod (gwp_list_rev (g:=gwp_spec (Sg:=Sg)) _ counts lcounts
              (λ v, ⌜is_list (reverse lcounts) v⌝%I)
             with "[] [] [rhs]") as "(%rev_counts & rhs & %)" => //=.
      1: by iIntros.
      iApply (gwp_list_rev (g:=gwp_wpre) _ counts lcounts with "[] [rhs]") => //.
      iIntros "!> % %". erewrite (is_list_eq _ rev_counts) ; [iFrame "rhs"| eauto..].
    - simpl in ho_pred. destruct ho_pred as (vpredicates' & hpred & ho_pred). rewrite hpred.
      rewrite /list_iter...
      replace dsv1 with (inject ds1).
      2: symmetry ; by apply is_list_inject.
      replace dsv2 with (inject ds2).
      2: symmetry ; by apply is_list_inject.
      destruct predicates as [|pred predicates'] => //.
      iDestruct (big_sepL2_cons_inv_l with "is_pred") as "(%vpred'&%&%&[#Hp #Hp']&is_pred')" ; simplify_eq.
      (* COUNT STEP via [count_sens]. *)
      fold list_iter.
      tp_bind (list_count _ _) ; wp_bind (list_count _ _).
      wp_apply (wp_wand with "[rhs]").
      { iApply (count_sens pred vpred' with "Hp Hp' [] rhs"); [iPureIntro; lra|]. iIntros "!> % h"; iExact "h". }
      simpl.
      iIntros "% (%len_f_l&%len_f_r&->&rhs&%d_out')"...
      (* COARSE [try_run] call; same structure as the abstracted [wp_iter_adaptive_acc']
         below.  The de-nested index load (now the head of a [let]) lets [tp_load] step
         the spec index load cleanly. *)
      tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
      assert (Z.abs (len_f_l - len_f_r) <= 1).
      {
        assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
        2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
        etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
        etrans. 1: eassumption. rewrite Rmult_1_l. done.
      }
      iApply ("run_dp" $! _ _ _ _ Inv with "[] [-]") ; iFrame.
      1: iPureIntro ; lia.
      + iIntros "* % !> (eps & rhs & hh & TRY_RUN) Hpost"...
        couple_laplace 0 1 with "[$rhs eps]".
        {
          epose proof (IZR_lt 0 ε_coarse _) => //.
          epose proof (IZR_lt 0 den _) => //.
          apply Rcomplements.Rdiv_lt_0_compat => //. }
        1: rewrite Rmult_1_l ; iFrame "eps".
        iNext. iIntros (count_coarse) "rhs" ; simpl... rewrite Z.add_0_r.
        iDestruct "hh" as "(%lcounts0 & %counts0 & %index0 & %His0 & counts_l & counts_r & index_l & index_r)".
        (* de-nested index load: [let: "idx" := !"index" in ("idx", count) :: !"counts"] *)
        tp_load ; wp_load... tp_normalise...
        rewrite /list_cons.
        tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store...
        iAssert Inv with "[counts_l counts_r index_l index_r]" as "hh".
        { iFrame. iPureIntro. eexists (_ :: lcounts0). eexists. split; [reflexivity|exact His0]. }
        tp_normalise... tp_normalise...
        case_bool_decide as Hthr.
        * tp_normalise... tp_normalise...
          tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
          iApply ("run_dp" $! _ _ _ _ Inv with "[] [$rhs $hh $TRY_RUN]").
          1: iPureIntro ; lia.
          -- iIntros "* % !> (eps & rhs & hh & TRY_RUN) Hpost"...
             couple_laplace 0 1 with "[$rhs eps]".
             {
               epose proof (IZR_lt 0 ε_precise _) => //.
               epose proof (IZR_lt 0 den _) => //.
               apply Rcomplements.Rdiv_lt_0_compat => //. }
             1: rewrite Rmult_1_l ; iFrame "eps".
             iNext. iIntros (count_precise) "rhs" ; simpl... rewrite Z.add_0_r.
             iDestruct "hh" as "(%lcounts1 & %counts1 & %index1 & %His1 & counts_l & counts_r & index_l & index_r)".
             tp_load ; wp_load... tp_normalise...
             rewrite /list_cons.
             tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store.
             iApply "Hpost". iFrame. iPureIntro. eexists (_ :: lcounts1). eexists. split; [reflexivity|exact His1].
          -- iNext. iIntros (v) "(rhs & hh & TRY_RUN)". simpl.
             iApply "Hpost". iFrame.
        * tp_normalise...
          iApply "Hpost". iFrame "rhs hh TRY_RUN". all: try done. Unshelve. all: try done.
      + iNext. iIntros "* (rhs & hh & TRY_RUN)" => /=...
        iDestruct "hh" as "(%lcountsf & %countsf & %indexf & %Hisf & counts_l & counts_r & index_l & index_r)".
        tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store...
        tp_normalise ; tp_pures.
        iApply ("IH" with "[counts_l counts_r index_l index_r] [] [] [] [$rhs] [$TRY_RUN]") => //.
        1: { iExists lcountsf. iFrame. iPureIntro. exact Hisf. }
        Unshelve. all: try exact Sg ; auto ; lra.
  Qed.

  (* This is the spec one would want for iter_adaptive_acc, proven from the abstracted spec for the privacy filter. *)
  Lemma wp_iter_adaptive_acc' (ε_coarse ε_precise den threshold budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K
    (predicates : list (Z -> bool))
    (lvpredicates : list val)
    (vpredicates : val)
    (_ : 0 < ε_coarse) (_ : 0 < ε_precise) (_ : 0 < den) (_ : 0 <= budget)
    :
    length predicates = length lvpredicates →
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ⌜is_list_HO lvpredicates vpredicates⌝ -∗
    ([∗ list] pred;vpred ∈ predicates;lvpredicates, is_predicate pred vpred ∗ is_spec_predicate pred vpred) -∗
    ↯m (IZR budget / IZR den) -∗
    ⤇ fill K (iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv2) -∗
    WP iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "%hlen * % %". iIntros "%adj".
    iIntros "%ho_pred #is_pred ε rhs".
    rewrite /iter_adaptive_acc...
    tp_alloc as counts_r "counts_r" ; wp_alloc counts_l as "counts_l"...
    tp_alloc as index_r "index_r" ; wp_alloc index_l as "index_l"...
    tp_bind (create_filter _). wp_bind (create_filter _).
    iApply (create_filter_private' _ _ den with "[$ε $rhs]") => //.
    iIntros "!> * (%&%&rhs&TRY_RUN&#run_dp)"... simpl...
    tp_bind (list_iter _ _). wp_bind (list_iter _ _).
    set (Inv := (∃ lcounts counts (index : Z), ⌜is_list lcounts counts⌝ ∗ counts_l ↦ counts ∗ counts_r ↦ₛ counts
                                               ∗ index_l ↦ #index ∗ index_r ↦ₛ #index)%I).
    iAssert Inv with "[counts_l counts_r index_l index_r]" as "hh". 1: iFrame ; iExists [] ; done.
    iRevert (predicates vpredicates ho_pred hlen) "is_pred rhs TRY_RUN".
    iInduction lvpredicates as [|vpred lvpredicates'] "IH" ;
      iIntros (predicates vpredicates ho_pred hlen) "#is_pred rhs TRY_RUN".
    - rewrite ho_pred.
      rewrite /list_iter...
      iDestruct "hh" as "(%&%&%&%&?&?&?&?)".
      tp_normalise... tp_load... wp_load.
      iMod (gwp_list_rev (g:=gwp_spec (Sg:=Sg)) _ counts lcounts
              (λ v, ⌜is_list (reverse lcounts) v⌝%I)
             with "[] [] [rhs]") as "(%rev_counts & rhs & %)" => //=.
      1: by iIntros.
      iApply (gwp_list_rev (g:=gwp_wpre) _ counts lcounts with "[] [rhs]") => //.
      iIntros "!> % %". erewrite (is_list_eq _ rev_counts) ; [iFrame "rhs"| eauto..].
    - simpl in ho_pred. destruct ho_pred as (vpredicates' & hpred & ho_pred). rewrite hpred.
      rewrite /list_iter...
      replace dsv1 with (inject ds1).
      2: symmetry ; by apply is_list_inject.
      replace dsv2 with (inject ds2).
      2: symmetry ; by apply is_list_inject.
      destruct predicates as [|pred predicates'] => //.
      iDestruct (big_sepL2_cons_inv_l with "is_pred") as "(%vpred'&%&%&[#Hp #Hp']&is_pred')" ; simplify_eq.
      (* COUNT STEP via [count_sens]. *)
      fold list_iter.
      tp_bind (list_count _ _) ; wp_bind (list_count _ _).
      wp_apply (wp_wand with "[rhs]").
      { iApply (count_sens pred vpred' with "Hp Hp' [] rhs"); [iPureIntro; lra|]. iIntros "!> % h"; iExact "h". }
      simpl.
      iIntros "% (%len_f_l&%len_f_r&->&rhs&%d_out')"...
      (* COARSE [try_run] call.  [I_f] carries the [Inv] resources (counts/index
         pointers), since the f-body reads/writes them; the de-nested index load is
         now the head of a [let] so [tp_load] steps it cleanly (cf. the GREEN sibling
         [wp_iter_adaptive_acc_simple]). *)
      tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
      assert (Z.abs (len_f_l - len_f_r) <= 1).
      {
        assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
        2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
        etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
        etrans. 1: eassumption. rewrite Rmult_1_l. done.
      }
      iApply ("run_dp" $! _ _ _ _ Inv with "[] [-]") ; iFrame.
      1: iPureIntro ; lia.
      + iIntros "* % !> (eps & rhs & hh & TRY_RUN) Hpost"...
        couple_laplace 0 1 with "[$rhs eps]".
        {
          epose proof (IZR_lt 0 ε_coarse _) => //.
          epose proof (IZR_lt 0 den _) => //.
          apply Rcomplements.Rdiv_lt_0_compat => //. }
        1: rewrite Rmult_1_l ; iFrame "eps".
        iNext. iIntros (count_coarse) "rhs" ; simpl... rewrite Z.add_0_r.
        iDestruct "hh" as "(%lcounts0 & %counts0 & %index0 & %His0 & counts_l & counts_r & index_l & index_r)".
        (* de-nested index load: [let: "idx" := !"index" in ("idx", count) :: !"counts"] *)
        tp_load ; wp_load... tp_normalise...
        rewrite /list_cons.
        tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store...
        (* re-establish [Inv] for the new counts list [(index0, count_coarse) :: lcounts0] *)
        iAssert Inv with "[counts_l counts_r index_l index_r]" as "hh".
        { iFrame. iPureIntro. eexists (_ :: lcounts0). eexists. split; [reflexivity|exact His0]. }
        (* the conditional precise branch.  The guard is the abstract
           [bool_decide (threshold < count_coarse)]; re-expose the buried spec
           comparison ([tp_normalise]) so the spec [if:] reduces alongside the impl. *)
        tp_normalise... tp_normalise...
        case_bool_decide as Hthr.
        * (* threshold < count_coarse: nested precise [try_run] *)
          tp_normalise... tp_normalise...
          tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
          iApply ("run_dp" $! _ _ _ _ Inv with "[] [$rhs $hh $TRY_RUN]").
          1: iPureIntro ; lia.
          -- iIntros "* % !> (eps & rhs & hh & TRY_RUN) Hpost"...
             couple_laplace 0 1 with "[$rhs eps]".
             {
               epose proof (IZR_lt 0 ε_precise _) => //.
               epose proof (IZR_lt 0 den _) => //.
               apply Rcomplements.Rdiv_lt_0_compat => //. }
             1: rewrite Rmult_1_l ; iFrame "eps".
             iNext. iIntros (count_precise) "rhs" ; simpl... rewrite Z.add_0_r.
             iDestruct "hh" as "(%lcounts1 & %counts1 & %index1 & %His1 & counts_l & counts_r & index_l & index_r)".
             tp_load ; wp_load... tp_normalise...
             rewrite /list_cons.
             tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store.
             iApply "Hpost". iFrame. iPureIntro. eexists (_ :: lcounts1). eexists. split; [reflexivity|exact His1].
          -- iNext. iIntros (v) "(rhs & hh & TRY_RUN)". simpl.
             iApply "Hpost". iFrame.
        * (* threshold not exceeded: no precise draw *)
          tp_normalise...
          iApply "Hpost". iFrame "rhs hh TRY_RUN". all: try done. Unshelve. all: try done.
      + iNext. iIntros "* (rhs & hh & TRY_RUN)" => /=...
        (* index increment [ "index" <- !"index" + #1 ], part of the outer iter body *)
        iDestruct "hh" as "(%lcountsf & %countsf & %indexf & %Hisf & counts_l & counts_r & index_l & index_r)".
        tp_load ; wp_load ; tp_pures ; tp_normalise ; tp_pures ; tp_store ; wp_store...
        tp_normalise ; tp_pures.
        iApply ("IH" with "[counts_l counts_r index_l index_r] [] [] [] [$rhs] [$TRY_RUN]") => //.
        1: { iExists lcountsf. iFrame. iPureIntro. exact Hisf. }
        Unshelve. all: try exact Sg ; auto ; lra.
  Qed.

  (* apply the general iter spec for some concrete predicates *)
  Lemma wp_iter_adaptive_acc_app (ε_coarse ε_precise den threshold budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K
    (_ : 0 < ε_coarse) (_ : 0 < ε_precise) (_ : 0 < den) (_ : 0 <= budget)
    :
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ↯m (IZR budget / IZR den) -∗
    ⤇ fill K (iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv2) -∗
    WP iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "%hlen * % % ε rhs".
    iApply (wp_iter_adaptive_acc' with "[] [] ε rhs") ; last first.
    1: iApply predicates_lvpredicates_is_predicate. 1: iPureIntro ; apply lvpredicates_is_list_HO. all: eauto.
  Qed.

End adaptive.

(* We can apply adequacy to derive differential privacy at the pure mathematical level. *)

Lemma adaptive_count_diffpriv_cpl (Sg : Sig) `{!SampleIn laplace_family Sg}
    (ε_coarse ε_precise den threshold budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2
    (_ : 0 < ε_coarse) (_ : 0 < ε_precise) (_ : 0 < den) (_ : 0 <= budget)
    :
    is_list ds1 dsv1 ->
    is_list ds2 dsv2 ->
    list_dist ds1 ds2 <= 1 ->
    ∀ σ,
      DPcoupl
        (lim_exec (δ := lang_markov (gen_lang Sg)) ((iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv1), σ))
        (lim_exec (δ := lang_markov (gen_lang Sg)) ((iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates dsv2), σ))
        (λ v v', v = v')
        (IZR budget / IZR den) 0.
Proof.
  intros. replace 0%R with (SeriesC (λ _ : val, 0%R)). 2: by by apply SeriesC_0.
  eapply (wp_adequacy Sg diffprivΣ) => //.
  2: by rewrite SeriesC_0.
  { apply Rcomplements.Rdiv_le_0_compat.
    1: apply IZR_le => //.
    apply IZR_lt => //.
  }
  iIntros (?) "rhs ε _".
  iPoseProof (wp_iter_adaptive_acc_app ε_coarse ε_precise den threshold budget ds1 ds2 _ _ []) as "h" => //.
  iSpecialize ("h" with "ε [rhs]"). 1: simpl ; iFrame.
  simpl.
  iApply (wp_wand with "h").
  iIntros. iFrame. done.
Qed.

Lemma adaptive_count_diffpriv (Sg : Sig) `{!SampleIn laplace_family Sg}
    (ε_coarse ε_precise den threshold budget : Z)
    (_ : 0 < ε_coarse) (_ : 0 < ε_precise) (_ : 0 < den) (_ : 0 <= budget)
    :
    ∀ σ,
      diffpriv_pure
        (λ x y : list Z, IZR (list_dist x y))
        (λ db, lim_exec (δ := lang_markov (gen_lang Sg)) ((iter_adaptive_acc #ε_coarse #ε_precise #den #threshold #budget vpredicates (inject db)), σ))
        (IZR budget / IZR den).
Proof.
  intros. apply diffpriv_approx_pure. apply DPcoupl_diffpriv.
  intros. eapply (adaptive_count_diffpriv_cpl Sg ε_coarse ε_precise den threshold budget) => //. 3: apply le_IZR.
  3: done.
  1,2: by apply is_list_inject.
Qed.
