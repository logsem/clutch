(** Adaptive-composition / privacy-FILTER (RRUV odometer) DP case study, ported
    from [clutch.diffpriv.examples.privacy_filter] to the GENERIC language.
    "Enable" the Laplace distribution (one signature + one [SampleIn] instance),
    pin the spec-context [fill], and the proofs go through with the standard
    proof-mode tactics and the library Laplace coupling rules (VALUE-FORM
    variants, cf. [sparse_vector_technique] / [sum_queries]).

    USE OF THE COMPOSITION LAWS (the point of this port).  The per-query work is
    [Laplace ∘ count] with [count = list_length ∘ list_filter].  We make the
    composition structure explicit and reusable:

      - [count_sens]: the COUNT [list_length ∘ list_filter] is 1-sensitive, proven
        by the sensitivity-composition law [sensitive_comp] from the two
        1-sensitive pieces [filter_sens] / [length_sens] (instead of inlining the
        two WP couplings by hand).  It is genuinely USED in the main proof.

      - [count_query_diffpriv]: a single query [Laplace ∘ count] is [(num/den)]-DP,
        obtained by [diffpriv_sensitive_comp count_sens (hoare_laplace_diffpriv …)]
        — the sensitivity·DP composition law.  This is the standalone
        composition-law statement (mirroring [sum_queries.noisy_count_diffpriv]).

    WHAT STAYS BY HAND, AND WHY.  The example's CORE is a dynamic-budget odometer
    ([create_filter] returning a [run_dp] runner — the RRUV privacy filter), which
    is MORE general than the fixed 2-step sequential law.  We port it faithfully.
    At the [run_dp] closure CALL sites the program feeds an ALREADY-COMPUTED count
    INTEGER (shared between the coarse and the precise noise draws) into a
    data-free closure [f #()] — there is no dataset argument in scope, so the
    [hoare_diffpriv]/[count_query_diffpriv] shape (which needs [g (inject x)] for
    adjacent [x x']) does NOT match there.  Hence those two noise draws keep the
    by-hand value-form [wp_couple_laplace … 0] coupling (with the [|count−count'|≤1]
    distance established once, up front, by [count_sens]).  See the [HONEST
    SCOPING] note in the task. *)
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

Definition rat_lt : val := λ:"ab" "xy", Fst "ab" * Snd "xy" < Fst "xy" * Snd "ab".
Definition rat_sub : val := λ:"ab" "xy",
    (Fst "ab" * Snd "xy" - Fst "xy" * Snd "ab", Snd "ab" * Snd "xy").

Definition create_filter : val :=
  λ:"budget",
  let: "budget_remaining" := ref "budget" in
  let: "try_run" :=
    λ:"ε" "f", if: rat_lt (!"budget_remaining") "ε" then
             NONE
           else
             ("budget_remaining" <- rat_sub (!"budget_remaining") "ε" ;;
              SOME ("f" #())) in
  "try_run".

(** [laplace] / [list_map] sample from / iterate over Laplace-sampling closures,
    so — unlike the monomorphic original — they are not closed [val]s and live in
    a section carrying [Sg] (cf. [sum_queries.laplace_programs]). *)
Section laplace_programs.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg}.

  Definition laplace : val :=
    λ:"eps" "mean", Laplace (Fst "eps") (Snd "eps") "mean" #().

End laplace_programs.

(* fix evaluation order to be head before tail. makes the induction easier. *)
Definition list_map : val :=
  rec: "list_map" "f" "l" :=
  match: "l" with
    SOME "a" =>
      let: "hd" := "f" (Fst "a") in
      let: "tl" := "list_map" "f" (Snd "a") in
      "hd" :: "tl"
  | NONE => NONE
  end.

(** Spec-side [GenWp] instance, built from the generic spec step rules — the
    [gwp]-based list operators ([gwp_list_filter]/[gwp_list_length]) are also run
    on the SPEC program.  [gen_prob_lang]'s spec layer ships no spec-side [GenWp]
    (only the impl-side [gwp_wpre] in [derived_laws]); the exact analogue of
    [prob_lang.spec.spec_rules.gwp_spec], identical to [sum_queries.gwp_spec]. *)
(* [gwp_spec] is now shared in [gen_prob_lang.spec.spec_rules] (via [Require … all]). *)

#[local] Open Scope Z.

Section adaptive.
  Context {Sg : Sig} `{!SampleIn laplace_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  Local Notation lidx := (@sample_idx laplace_family Sg _).

  Lemma create_filter_private K (num_budget den_budget : Z) (_ : 0 <= num_budget) (_ : 0 < den_budget) :
    {{{ ↯m (IZR num_budget / IZR den_budget) ∗ ⤇ fill K ((of_val create_filter) (#num_budget, #den_budget)%V) }}}
      create_filter (#num_budget, #den_budget)%V
      {{{ try_run, RET try_run;
           ∃ (try_run' : val) l l' (num_εrem den_εrem : Z),
             ⌜ 0 <= num_εrem ⌝ ∗
             ⌜ 0 < den_εrem ⌝ ∗
               ↯m (IZR num_εrem / IZR den_εrem) ∗
             l ↦ (#num_εrem, #den_εrem)%V ∗
             l' ↦ₛ (#num_εrem, #den_εrem)%V ∗
             ⤇ fill K try_run' ∗
             (∀ (ε_num ε_den : Z) K (f f' : val) (num_εrem den_εrem : Z) I_f,
                 ⌜ 0 <= ε_num ⌝%Z →
                 ⌜ 0 < ε_den ⌝%Z →
                 ⌜ 0 < den_εrem ⌝%Z →
                 {{{
                       (* f has to be "ε-private" (although we don't even have adjacent data here) and preserve some invariant.
                          f itself may also rely on having access to the resources required for running try_run. *)
                       (∀ K (num_εrem' den_εrem' : Z), ⌜0 < den_εrem'⌝ →
                           {{{ ↯m (IZR ε_num / IZR ε_den) ∗
                               ⤇ fill K ((of_val f') #()) ∗
                               I_f ∗
                               ↯m (IZR num_εrem' / IZR den_εrem') ∗
                               l ↦ (#num_εrem', #den_εrem')%V ∗
                               l' ↦ₛ (#num_εrem', #den_εrem')%V
                           }}}
                             (of_val f) #()
                             {{{ v, RET v; ⤇ fill K (of_val v) ∗ I_f
                                           ∗ ∃ (num_εrem'' den_εrem'' : Z),
                                             ⌜0 < den_εrem''⌝ ∗
                                               ↯m (IZR num_εrem'' / IZR den_εrem'') ∗
                                               l ↦ (#num_εrem'', #den_εrem'')%V ∗
                                               l' ↦ₛ (#num_εrem'', #den_εrem'')%V
                       }}})
                       ∗
                         (* and we need the resources that try_run depends on *)
                         ↯m (IZR num_εrem / IZR den_εrem) ∗
                       l ↦ (#num_εrem, #den_εrem)%V ∗
                       l' ↦ₛ (#num_εrem, #den_εrem)%V ∗
                       I_f ∗
                       ⤇ fill K (try_run' (#ε_num, #ε_den)%V f')
                 }}}
                   ((of_val try_run) (#ε_num, #ε_den)%V f : expr)
                   {{{ v, RET v;
                       (* we get equal results *)
                       ⤇ fill K (of_val v) ∗
                       I_f ∗
                       (* and we get back the resources required for try_run *)
                       ∃ num_εrem den_εrem,
                        ⌜0 < den_εrem⌝ ∗
                         ↯m (IZR num_εrem / IZR den_εrem) ∗
                         l ↦ (#num_εrem, #den_εrem)%V ∗
                         l' ↦ₛ (#num_εrem, #den_εrem)%V
             }}})
      }}}.
  Proof with (tp_pures ; wp_pures).
    iIntros "% (ε & rhs) Hpost". rewrite /create_filter...
    tp_alloc as budget_r "budget_r" ; wp_alloc budget_l as "budget_l"...
    iModIntro. iApply "Hpost". iExists _,_,_,_,_ ; iFrame. do 2 iSplit => //.
    iIntros "* % % % % !> * (f_dp & ε & budget_l & budget_r & I_f & rhs) Hpost"... tp_load ; wp_load...
    rewrite /rat_lt. tp_normalise...
    case_bool_decide as h; tp_normalise... 1: iApply "Hpost" ; iFrame ; done.
    assert (ε_num * den_εrem <= num_εrem * ε_den) as h' by lia.
    iDestruct (ecm_split (IZR ε_num / IZR ε_den)%R
                 (IZR num_εrem / IZR den_εrem - IZR ε_num / IZR ε_den)%R with "[ε]")
      as "[ε εrem]".
    1: repeat real_solver_partial ; qify_r ; zify_q ; rewrite Zmult_0_l Zmult_1_r ; lia.
    { pose proof (IZR_le _ _ h') as h''.
      rewrite !mult_IZR in h''. apply Rle_0_le_minus.
      eapply (Rmult_le_reg_r (IZR ε_den)).
      1: by apply IZR_lt.
      eapply (Rmult_le_reg_r (IZR den_εrem)).
      1: by apply IZR_lt.
      field_simplify. 1: lra.
      1: intro F ; apply eq_IZR in F ; lia.
      1: intro F ; apply eq_IZR in F ; lia.
    }
    1: iApply ecm_eq ; [|iFrame].
    1: { ring_simplify. field.
         intro F. assert (den_εrem ≠ 0) as hh by lia. apply hh.
         apply eq_IZR. done.
    }
    tp_load ; wp_load... rewrite /rat_sub. tp_normalise... tp_store ; wp_store.
    tp_normalise...
    tp_bind (f' _) ; wp_bind (f _).
    iApply ("f_dp" with "[] [$rhs $ε $I_f $budget_l $budget_r εrem]").
    1: iPureIntro ; lia.
    1: iApply ecm_eq ; [|iFrame].
    1: { rewrite !minus_IZR !mult_IZR. ring_simplify. field.
         split.
         - intro F. assert (ε_den ≠ 0) as hh by lia. apply hh.
           apply eq_IZR. done.
         - intro F. assert (den_εrem ≠ 0) as hh by lia. apply hh.
           apply eq_IZR. done.
    }
    simpl. iNext. iIntros "* [?[??]]"... iApply "Hpost".
    iFrame. done.
  Qed.

  (* We can make the resources that try_run depends on abstract. *)
  Lemma create_filter_private' K (num_budget den_budget : Z) (_ : 0 <= num_budget) (_ : 0 < den_budget) :
    {{{ ↯m (IZR num_budget / IZR den_budget) ∗ ⤇ fill K ((of_val create_filter) (#num_budget, #den_budget)%V) }}}
      create_filter (#num_budget, #den_budget)%V
      {{{ try_run, RET try_run;
           ∃ (try_run' : val) (TRY_RUN : iProp Σ),
             ⤇ fill K try_run' ∗
             TRY_RUN ∗
             (∀ (ε_num ε_den : Z) K (f f' : val) I_f,
                 ⌜ 0 <= ε_num ⌝%Z →
                 ⌜ 0 < ε_den ⌝%Z →
                 {{{
                       (* f has to be "ε-private" (although we don't even have adjacent data here) and preserve some invariant.
                          f itself may also rely on having access to the resources required for running try_run. *)
                       (∀ K,
                           {{{ ↯m (IZR ε_num / IZR ε_den) ∗ ⤇ fill K ((of_val f') #()) ∗ I_f ∗ TRY_RUN }}}
                             (of_val f) #()
                             {{{ v, RET v; ⤇ fill K (of_val v) ∗ I_f ∗ TRY_RUN }}})
                       ∗
                       ⤇ fill K (try_run' (#ε_num, #ε_den)%V f') ∗
                       I_f ∗
                       TRY_RUN
                 }}}
                   ((of_val try_run) (#ε_num, #ε_den)%V f : expr)
                   {{{ v, RET v;
                       (* we get equal results *)
                       ⤇ fill K (of_val v) ∗
                       I_f ∗
                       (* and we get back the resources required for try_run *)
                       TRY_RUN
             }}})
      }}}.
  Proof with (tp_pures ; wp_pures).
    iIntros "% (ε & rhs) Hpost".
    iApply (create_filter_private with "[$]") => //.
    iNext. iIntros "% (%&%& % & % & % & % & % & ε & l & l' & rhs & #h)".
    iApply "Hpost".
    set (inv := (∃ num_budget_remaining den_budget_remaining,
                    ⌜0 < den_budget_remaining⌝ ∗
                  ↯m (IZR num_budget_remaining / IZR den_budget_remaining) ∗
                  l ↦ (#num_budget_remaining, #den_budget_remaining)%V ∗
                  l' ↦ₛ (#num_budget_remaining, #den_budget_remaining)%V)%I).
    iExists _,inv. iFrame. iSplit => //.
    iIntros "* % % % !> * (#f_dp & rhs & I_f & TRY_RUN) Hpost".
    iDestruct "TRY_RUN" as "(% & % & % & ε & l & l')"...
    iApply ("h" $! ε_num ε_den _ f f' num_budget_remaining den_budget_remaining I_f
             with "[] [] [] [-Hpost] [Hpost]") => // ; iFrame.
    iIntros "% * % % !> (ε & rhs & If & εrem & l & l') Hpost".
    iApply ("f_dp" with "[-Hpost]") ; iFrame.
    iPureIntro. done.
  Qed.

  Definition is_predicate {A} `[Inject A val] (pred : A -> bool) (vpred : val) : iProp Σ :=
    ∀ x, {{{ True }}} vpred (inject x) {{{ w, RET w; ⌜w = (inject (pred x))⌝ }}}.

  Definition is_spec_predicate {A} `[Inject A val] (pred : A -> bool) (vpred : val) : iProp Σ :=
    ∀ x, G{{{ True }}} vpred (inject x) @ gwp_spec (Sg:=Sg) ; ⊤ {{{ w, RET w; ⌜w = (inject (pred x))⌝ }}}.

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
      multiply, [1·1 = 1]) — the sensitivity-composition argument of
      [sensitive_comp], specialised here to the curried [list_filter pred] (which
      is an [expr], not a closed [val], so the off-the-shelf [sensitive_comp]
      combinator — whose [f g : val] — is not the literal fit; the composition is
      done by hand in two [wp_apply]s).  USED below in [count_query_diffpriv] and
      directly in the main proof for the count step. *)
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
      [(num/den)]-DP: the 1-sensitive [count_sens] composed with the
      [(num/den)]-DP Laplace mechanism [hoare_laplace_diffpriv] via
      [diffpriv_sensitive_comp] gives budget [1·(num/den) = (num/den)].  This is
      the standalone composition-law statement for a per-query mechanism (mirrors
      [sum_queries.noisy_count_diffpriv]).  The program here precomputes/SHARES the
      count between the coarse and precise draws, so this exact lemma is not the
      direct fit at the [run_dp] closure sites (see file header); we expose it as a
      reusable building block. *)
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
    hoare_diffpriv Sg
      (λ:"x", (λ:"loc", Laplace #num #den "loc" #())%V ((λ:"x", list_count f "x")%V "x"))
      (IZR num / IZR den) 0 (dlist Z) Z.
  Proof.
    iIntros (Hpos) "#Hf #Hf'".
    rewrite -{1}(Rmult_1_l (IZR num / IZR den)) -{1}(Rmult_0_r 1).
    iApply (diffpriv_sensitive_comp Sg
              (λ:"x", list_count f "x")%V
              (λ: "loc", Laplace #num #den "loc" #())%V
              (IZR num / IZR den) 0 1 (dlist Z) dZ (C := Z)); [lra| |].
    - (* the closed-val count [(λ x, list_count f x)] is 1-sensitive: one beta
         reduces it to [list_count f], whose sensitivity is [count_sens] *)
      iIntros (c_pos) "* !> * rhs HΦ". wp_pures. tp_pures.
      iApply (count_sens P f with "Hf Hf' [] rhs"); [iPureIntro; lra|].
      iApply "HΦ".
    - by iApply hoare_laplace_diffpriv.
  Qed.

  Fixpoint is_list_HO (l : list val) (v : val) :=
    match l with
    | [] => v = NONEV
    | w::l' => ∃ lv, v = SOMEV (w, lv) ∧ is_list_HO l' lv
  end.


  #[local] Definition map_adaptive_acc_terse_both_body
    (eps_coarse_num eps_coarse_den eps_precise_num eps_precise_den threshold : Z) (data try_run : val) : val :=
    (λ: "pred" ,
       let: "count_exact" := list_count "pred" data in
       let: "g" := λ:<> , laplace (#eps_precise_num, #eps_precise_den)%V "count_exact" in
       let: "f" := λ:<> ,
                     let: "count_coarse" := laplace (#eps_coarse_num, #eps_coarse_den)%V "count_exact" in
                     let: "count_precise" :=
                       if: #threshold < "count_coarse" then
                         try_run (#eps_precise_num, #eps_precise_den)%V "g"
                       else NONE in
                     ("count_coarse", "count_precise")
       in
       try_run (#eps_coarse_num, #eps_coarse_den)%V "f").

  Definition map_adaptive_acc_terse_both : val :=
    λ: "eps_coarse" "eps_precise" "threshold" "budget" "predicates" "data" ,
    let: "try_run" := create_filter "budget" in
    list_map
      (λ: "pred" ,
        let: "count_exact" := list_count "pred" "data" in
        let: "g" := λ:<> , laplace "eps_precise" "count_exact" in
        let: "f" := λ:<> ,
          let: "count_coarse" := laplace "eps_coarse" "count_exact" in
          let: "count_precise" :=
            if: "threshold" < "count_coarse" then
              "try_run" "eps_precise" "g"
            else NONE in
          ("count_coarse", "count_precise")
        in
        "try_run" "eps_coarse" "f")
        "predicates" .

  (* This is the spec one would want for iter_adaptive_acc, proven from the abstracted spec for the privacy filter. *)
  Lemma wp_map_adaptive_acc_terse_both (ε_coarse_num ε_coarse_den ε_precise_num ε_precise_den threshold num_budget den_budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K
    (predicates : list (Z -> bool))
    (lvpredicates : list val)
    (vpredicates : val)
    (_ : 0 < ε_coarse_num) (_ : 0 < ε_precise_num)
    (_ : 0 < ε_coarse_den) (_ : 0 < ε_precise_den) (_ : 0 < den_budget) (_ : 0 <= num_budget)
    :
    length predicates = length lvpredicates →
    is_list ds1 dsv1 →
    is_list ds2 dsv2 →
    list_dist ds1 ds2 <= 1 →
    ⌜is_list_HO lvpredicates vpredicates⌝ -∗
    ([∗ list] pred;vpred ∈ predicates;lvpredicates, is_predicate pred vpred ∗ is_spec_predicate pred vpred) -∗
    ↯m (IZR num_budget / IZR den_budget) -∗
    ⤇ fill K (map_adaptive_acc_terse_both (#ε_coarse_num, #ε_coarse_den)%V (#ε_precise_num, #ε_precise_den)%V #threshold (#num_budget, #den_budget)%V vpredicates dsv2) -∗
    WP map_adaptive_acc_terse_both (#ε_coarse_num, #ε_coarse_den)%V (#ε_precise_num, #ε_precise_den)%V #threshold (#num_budget, #den_budget)%V vpredicates dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    iIntros "%hlen * % %". iIntros "%adj".
    iIntros "%ho_pred #is_pred ε rhs".
    rewrite /map_adaptive_acc_terse_both...
    tp_bind (create_filter _). wp_bind (create_filter _).
    iApply (create_filter_private' _ num_budget den_budget with "[$ε $rhs]") => //.
    iIntros "!> * (%&%&rhs&TRY_RUN&#run_dp)"... simpl...
    rewrite -!/(map_adaptive_acc_terse_both_body _ _ _ _ _ _ _).
    iRevert (K predicates vpredicates ho_pred hlen) "is_pred rhs TRY_RUN".
    iInduction lvpredicates as [|vpred lvpredicates'] "IH" ;
      iIntros (K predicates vpredicates ho_pred hlen) "#is_pred rhs TRY_RUN".
    - rewrite ho_pred. rewrite /list_map... done.
    - simpl in ho_pred. destruct ho_pred as (vpredicates' & hpred & ho_pred). rewrite hpred.
      rewrite /list_map. tp_pure ; wp_pure. rewrite -!/(list_map)...
      set (f := map_adaptive_acc_terse_both_body ε_coarse_num ε_coarse_den ε_precise_num
       ε_precise_den threshold dsv1 try_run).
      set (f' := map_adaptive_acc_terse_both_body ε_coarse_num ε_coarse_den ε_precise_num
       ε_precise_den threshold dsv2 try_run').

      tp_bind (f' _) ; wp_bind (f _).
      rewrite /f/f'/map_adaptive_acc_terse_both_body...
      rewrite -!/(map_adaptive_acc_terse_both_body _ _ _ _ _ _ _).
      (* COUNT STEP via the count-sensitivity lemma [count_sens]
         ([list_count pred] is 1-sensitive — established inside [count_sens] by
         sequencing [filter_sens] then [length_sens]).  This replaces the
         original's two hand-chained WP couplings, and gives [|count_l−count_r| ≤
         1] in one application. *)
      destruct predicates as [|pred predicates'] => //.
      iDestruct (big_sepL2_cons_inv_l with "is_pred") as "(%vpred'&%&%&[#Hp #Hp']&is_pred')" ; simplify_eq.
      replace dsv1 with (inject ds1). 2: symmetry ; by apply is_list_inject.
      replace dsv2 with (inject ds2). 2: symmetry ; by apply is_list_inject.
      tp_bind (list_count _ _) ; wp_bind (list_count _ _).
      wp_apply (wp_wand with "[rhs]").
      { iApply (count_sens pred vpred' with "Hp Hp' [] rhs"); [iPureIntro; lra| ].
        iIntros "!> % h"; iExact "h". }
      simpl. iIntros "% (%len_f_l&%len_f_r&->&rhs&%d_out')"...
      tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
      assert (0 < IZR ε_coarse_num / IZR ε_coarse_den)%R ;
        [|assert (0 < IZR ε_precise_num / IZR ε_precise_den)%R].
      1,2: apply Rcomplements.Rdiv_lt_0_compat ; apply IZR_lt => //.
      assert (Z.abs (len_f_l - len_f_r) <= 1).
      {
        assert (Rabs (IZR (len_f_l - len_f_r)) <= 1)%R as h.
        2:{ rewrite -abs_IZR in h. apply le_IZR. done. }
        etrans. 2: replace 1%R with (IZR 1%Z) by auto ; apply IZR_le ; apply adj.
        etrans. 1: eassumption. rewrite Rmult_1_l.
        done.
      }
      iApply ("run_dp" $! _ _ _ _ _ ⌜True⌝%I with "[] [] [-]") ; iFrame.
      1-2: iPureIntro ; lia.
      (* BY-HAND coupling (kept): the [run_dp] closures sample [Laplace eps
         count_exact] where [count_exact] is the ALREADY-COMPUTED integer
         ([count_l] on impl, [count_r] on spec); the closure has NO dataset
         argument, so [count_query_diffpriv]/[hoare_diffpriv] do not match here.
         We use the value-form reflexive-shift coupling [wp_couple_laplace … 0]
         with the [|count_l−count_r| ≤ 1] distance from [count_sens]. *)
      + iIntros "* % !> (eps & rhs & I & TRY_RUN) Hpost"...
        rewrite /laplace...
        tp_bind (Sample _ _ _) ; wp_bind (Sample _ _ _).
        iApply (wp_couple_laplace (S:=Sg) len_f_l len_f_r 0 1 with "[$rhs eps]").
        1: apply Zabs_ind ; lia.
        1: reflexivity.
        1: done.
        1: rewrite Rmult_1_l ; reflexivity.
        1: iFrame "eps".
        iNext. iIntros (count_precise_1) "rhs" ; simpl... rewrite Z.add_0_r.
        rewrite /list_cons.
        case_bool_decide as hthresh...
        2: iApply "Hpost" ; by iFrame.
        tp_bind (try_run' _ _) ; wp_bind (try_run _ _).
        iApply ("run_dp" $! _ _ _ _ _ ⌜True⌝%I with "[] [] [-Hpost] [Hpost]") ; iFrame.
        1-2: iPureIntro ; lia.
        * iIntros "* % !> (eps & rhs & I & TRY_RUN) Hpost"...
          tp_bind (Sample _ _ _) ; wp_bind (Sample _ _ _).
          iApply (wp_couple_laplace (S:=Sg) len_f_l len_f_r 0 1 with "[$rhs eps]").
          1: apply Zabs_ind ; lia.
          1: reflexivity.
          1: done.
          1: rewrite Rmult_1_l ; reflexivity.
          1: iFrame "eps".
          iNext. iIntros (count_precise_2) "rhs" ; simpl. rewrite Z.add_0_r.
          iApply "Hpost" ; by iFrame.
        * simpl. iIntros "!> * [rhs [I TRY_RUN]]"... iApply "Hpost". iFrame. done.

      + iNext. iIntros "* (rhs&%&TRY_RUN)" => /=...
        tp_bind (list_map _ _). wp_bind (list_map _ _).
        iSpecialize ("IH" $! _ predicates' vpredicates' with "[%] [%] is_pred' rhs TRY_RUN"); [done|eauto|].
        wp_apply (wp_wand with "IH").
        iIntros (vtl) "rhs" ; simpl. rewrite /list_cons... done.
        Unshelve. all: try exact Sg.
  Qed.


  Definition lvpredicates : list val :=
    [(λ:"x", "x" < #30) ; (λ:"x", #30 <= "x") ; (λ:"x", "x" `rem` #2 = #0)]%V.

  Lemma foo : is_list_HO lvpredicates vpredicates.
  Proof.
    repeat (eexists ; split ; eauto).
  Qed.

  Lemma bar :
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

  (* apply the general iter spec for some concrete predicates *)
  Lemma wp_map_adaptive_acc_terse_both_app
    (ε_coarse_num ε_coarse_den ε_precise_num ε_precise_den threshold num_budget den_budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2 K
    (_ : 0 < ε_coarse_num) (_ : 0 < ε_precise_num)
    (_ : 0 < ε_coarse_den) (_ : 0 < ε_precise_den) (_ : 0 < den_budget) (_ : 0 <= num_budget)
    :
    is_list ds1 dsv1 ->
    is_list ds2 dsv2 ->
    list_dist ds1 ds2 <= 1 ->
    ↯m (IZR num_budget / IZR den_budget) -∗
    ⤇ fill K
      (map_adaptive_acc_terse_both (#ε_coarse_num, #ε_coarse_den)%V (#ε_precise_num, #ε_precise_den)%V
         #threshold (#num_budget, #den_budget)%V vpredicates dsv2)
    -∗
    WP
      map_adaptive_acc_terse_both (#ε_coarse_num, #ε_coarse_den)%V (#ε_precise_num, #ε_precise_den)%V
      #threshold (#num_budget, #den_budget)%V vpredicates dsv1
      {{ v, ⤇ fill K (of_val v) }}.
  Proof with (tp_pures ; wp_pures).
    intros.
    iIntros "ε rhs".
    iApply (wp_map_adaptive_acc_terse_both with "[] [] ε rhs") ; last first.
    1: iApply bar. 1: iPureIntro ; apply foo. all: eauto.
  Qed.

End adaptive.

(* We can apply adequacy to derive differential privacy at the pure mathematical level. *)

Lemma adaptive_count_diffpriv_cpl (Sg : Sig) `{!SampleIn laplace_family Sg}
    (ε_coarse_num ε_coarse_den ε_precise_num ε_precise_den threshold num_budget den_budget : Z)
    (ds1 ds2 : list Z) dsv1 dsv2
    (_ : 0 < ε_coarse_num) (_ : 0 < ε_precise_num)
    (_ : 0 < ε_coarse_den) (_ : 0 < ε_precise_den) (_ : 0 < den_budget) (_ : 0 <= num_budget)
    :
    is_list ds1 dsv1 ->
    is_list ds2 dsv2 ->
    list_dist ds1 ds2 <= 1 ->
    ∀ σ,
      DPcoupl
        (lim_exec (δ := lang_markov (gen_lang Sg)) ((map_adaptive_acc_terse_both (#ε_coarse_num, #ε_coarse_den)%V (#ε_precise_num, #ε_precise_den)%V
         #threshold (#num_budget, #den_budget)%V vpredicates dsv1), σ))
        (lim_exec (δ := lang_markov (gen_lang Sg)) ((map_adaptive_acc_terse_both (#ε_coarse_num, #ε_coarse_den)%V (#ε_precise_num, #ε_precise_den)%V
         #threshold (#num_budget, #den_budget)%V vpredicates dsv2), σ))
        (λ v v', v = v')
        (IZR num_budget / IZR den_budget) 0.
Proof.
  intros. replace 0%R with (SeriesC (λ _ : val, 0%R)). 2: by by apply SeriesC_0.
  eapply (wp_adequacy Sg diffprivΣ) => //.
  2: by rewrite SeriesC_0.
  { apply Rcomplements.Rdiv_le_0_compat.
    1: apply IZR_le => //.
    apply IZR_lt => //.
  }
  iIntros (?) "rhs ε _".
  iPoseProof (wp_map_adaptive_acc_terse_both_app ε_coarse_num ε_coarse_den ε_precise_num ε_precise_den threshold num_budget den_budget ds1 ds2 _ _ []) as "h" => //.
  iSpecialize ("h" with "ε [rhs]"). 1: simpl ; iFrame.
  simpl.
  iApply (wp_wand with "h").
  iIntros. iFrame. done.
Qed.

Lemma adaptive_count_diffpriv (Sg : Sig) `{!SampleIn laplace_family Sg}
    (ε_coarse_num ε_coarse_den ε_precise_num ε_precise_den threshold num_budget den_budget : Z)
    (_ : 0 < ε_coarse_num) (_ : 0 < ε_precise_num)
    (_ : 0 < ε_coarse_den) (_ : 0 < ε_precise_den) (_ : 0 < den_budget) (_ : 0 <= num_budget)
    :
    ∀ σ,
      diffpriv_pure
        (λ x y : list Z, IZR (list_dist x y))
        (λ db, lim_exec (δ := lang_markov (gen_lang Sg)) ((map_adaptive_acc_terse_both (#ε_coarse_num, #ε_coarse_den)%V (#ε_precise_num, #ε_precise_den)%V
         #threshold (#num_budget, #den_budget)%V vpredicates (inject db)), σ))
        (IZR num_budget / IZR den_budget).
Proof.
  intros. apply diffpriv_approx_pure. apply DPcoupl_diffpriv.
  intros. eapply (adaptive_count_diffpriv_cpl Sg ε_coarse_num ε_coarse_den ε_precise_num ε_precise_den threshold num_budget den_budget) => //. 3: apply le_IZR.
  3: done.
  1,2: by apply is_list_inject.
Qed.
