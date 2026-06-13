(** Report-noisy-max (presampling) DP case study with ONE-SIDED EXPONENTIAL
    noise (the exponential mechanism), ported from
    [clutch.diffpriv.examples.report_noisy_max] to the GENERIC language.
    "Enable" the Exp distribution (one signature + one [SampleIn] instance),
    pin the spec-context [fill], and use the generic Exp tape API
    ([AllocTapeExp]/[↪E]/[↪Eₛ]/[wp_exp_tape]) and the list presampling
    coupling [hoare_couple_exp_list] (from [report_noisy_max_lemmas]).

    See [report_noisy_max_pointwise] for the pointwise (coupling) variant and the
    rationale for [#[global] Opaque sample_idx]. *)
From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics iris_ext.
From clutch.prob Require Import differential_privacy.
From clutch.gen_diffpriv Require Import adequacy all.
From clutch.gen_diffpriv.lib Require Import exponential exponential_tapes.
From clutch.gen_prob_lang Require Import gwp.list inject families.
From clutch.gen_prob_lang.spec Require Import spec_ra spec_rules.
(* [report_noisy_max_lemmas] for the noise-independent pure argmax lemmas
   ([list_max_index_eq], …); [report_noisy_max_exp_lemmas] for the exp-specific
   [hoare_couple_exp_list] etc. *)
From clutch.gen_diffpriv.examples Require Import report_noisy_max_lemmas report_noisy_max_exp_lemmas.
From iris.prelude Require Import options.

(** Enable the Exp distribution for this development. *)
(** PARAMETRIC over any signature [Sg] containing [exp_family] (composes with
    other mechanisms; concrete [Sg] supplied at the closing adequacy corollary).
    Abstract [SampleIn] ⇒ [sample_idx] is a frozen atom, so the concrete-instance
    [Opaque SampleIn_rnme] OOM workaround is unnecessary. *)
#[global] Opaque sample_idx.

(** [inject x : expr] resolves to the *unreduced* [@inject A expr _ x] rather
    than the [Val]-headed form; the spec reshape tactics need a [Val] head.  See
    [report_noisy_max_pointwise] for the full explanation. *)
Lemma inject_expr_Val_e {A} `{!Inject A val} (x : A) :
  (inject x : expr) = Val (inject x).
Proof. reflexivity. Qed.

(** Spec-side [GenWp] instance: the [gwp]-based list ADT ([gwp_list_mapi],
    [gwp_list_cons], [gwp_list_max_index]) is also run on the SPEC program (via
    [(g:=gwp_spec_e)]).  [gen_prob_lang]'s spec layer does not ship a spec-side
    [GenWp] (only the impl-side [gwp_wpre] in [derived_laws]), so we build it here
    from the generic spec step rules ([step_pure]/[step_alloc]/[step_load]/
    [step_store]) — the exact analogue of [prob_lang.spec.spec_rules.gwp_spec_e].
    INFRA GAP: ideally this would live in [gen_prob_lang.spec.spec_rules]. *)
Section spec_gwp_e.
  Context {Sg : Sig} `{!specG_prob_lang Σ, invGS_gen hl Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  Local Notation spec_update :=
    (@spec_update (lang_markov (gen_lang Sg)) Σ _ _ _).

  Notation spec_wp :=
    (λ E e Ψ, ∀ K,
        ⤇ fill K e -∗ spec_update E (∃ (v : val), ⤇ fill K v ∗ Ψ v))%I.

  Lemma gwp_mixin_spec_e :
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

  Canonical Structure gwp_spec_e := Build_GenWp gwp_mixin_spec_e.
End spec_gwp_e.

Section rnme.
  Context {Sg : Sig} `{!SampleIn exp_family Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  Local Notation lidx := (@sample_idx exp_family Sg _).
  (* the generic tape value standing in for [prob_lang]'s [Tape_Exp] record *)
  Local Notation ExpT num den mean zs :=
    (sample_idx (D := exp_family), sf_param_to_val exp_family (num, den, mean)%Z,
      ((λ z : Z, LitV (LitInt z)) <$> zs)).

  #[local] Open Scope R.

  Definition list_map'_e (v:val) :=
    (list_mapi (λ: <>, v))%E.

  Definition report_noisy_max_exp_presampling (num den : Z) : val :=
    (* ↯ (num/den) ∗ evalQ is 1-sensitive ∗ N ∈ ℕ \ {0} ∗ 0 < num/2den ∗ dDB db db' <= 1 *)
    λ:"evalQ" "N" "d",
      let: "xs" := list_init "N" (λ:"i", "evalQ" "i" "d") in
      let: "xs_tapes" := list_map (λ:"x", ("x", AllocTapeExp #num #(2*den) "x")) "xs" in
      let: "noisy_xs" := list_map'_e (λ: "x_ι", Exp #num #(2*den) (Fst "x_ι") (Snd "x_ι")) "xs_tapes" in
      list_max_index "noisy_xs".

  Lemma rnme_init (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) 1 dDB dZ) →
    ∀ db db', dDB db db' <= 1 →
              {{{ ⤇ fill K ((of_val list_init) #N (λ:"i", (of_val evalQ) "i" (of_val (inject db'))))%V }}}
                (list_init #N (λ:"i", evalQ "i" (of_val (inject db))))%V
                {{{ vxs, RET vxs ; ∃ (vxs' : val) (xs xs' : list Z),
                        ⤇ fill K vxs' ∗
                        ⌜ is_list xs vxs ∧ is_list xs' vxs' ∧ length xs = N ∧ length xs' = N ∧
                        Forall2 (λ x x', dZ x x' <= 1) xs xs'⌝
                }}}.
  Proof with (tp_pures ; wp_pures).
    iIntros (ev_sens ?? adj post) "rhs Hpost".
    wp_lam. wp_pure. wp_lam.
    tp_lam. tp_pure. tp_lam.
    tp_pure. wp_pure.
    set (vxs := InjLV #()).
    unfold vxs at 1.
    set (vxs' := InjLV #()).
    set (k := N).
    wp_pure. tp_pure.
    assert
      (∃ (xs xs' : list Z),
                 is_list xs vxs
                  ∧ is_list xs' vxs'
                    ∧ (length xs + k = N)%nat
                      ∧ (length xs' + k = N)%nat
                        ∧ Forall2 (λ x x' : Z, dZ x x' <= 1) xs xs') as hpre.
    1: exists [], [] ; cbn ; intuition eauto.
    revert hpre.
    unfold k at 4 5.
    generalize k vxs vxs'.
    clear vxs vxs' k. intros.
    iInduction k as [|k'] forall (vxs vxs' hpre).
    - idtac... iApply "Hpost".
      destruct hpre as (?&?&?&?&?&?&?).
      iModIntro. iExists _,_,_. iFrame ; iPureIntro. intuition eauto ; cbn.
      + simplify_eq. lia.
      + simplify_eq. lia.

    - idtac...
      tp_bind (evalQ _ _) ; wp_bind (evalQ _ _).
      wp_apply (ev_sens with "[] [rhs]"). 1: iPureIntro ; lra. 1: iFrame.
      iIntros "% (%&%&->&rhs&%h)".
      idtac... wp_rec. wp_pure. wp_pure. wp_pure. wp_pure.
      simpl. tp_rec. tp_pure. tp_pure. tp_pure. tp_pure.
      replace (S k' - 1)%Z with (Z.of_nat k') by lia.
      destruct hpre as (xs & xs' &?&?&?&?&?).
      iSpecialize ("IHk'" $! (InjRV (#b, vxs)) ((InjRV (#b', vxs'))) with "[] [rhs]").
      2: iFrame.
      + iPureIntro. exists (b::xs). exists (b' :: xs'). intuition eauto.
        * simpl. eauto.
        * simpl. eauto.
        * simpl. lia.
        * simpl. lia.
        * constructor. 2: done.
          simpl in h. etrans. 2: exact adj. rewrite Rmult_1_l in h. done.
      + iSpecialize ("IHk'" with "Hpost").
        iApply "IHk'".
  Qed.

Local Program Instance : Inject loc val := {| inject := LitV ∘ LitLbl |}.
Next Obligation. by intros ?? [=]. Qed.

(* γ := (dZ x x' <= 1) *)
Lemma rwp_list_map_e {A} `{!Inject A val} `{!Inject B val}
  (l l' : list A) (lv lv' fv fv' : val)
  (γ : A -> A -> iProp Σ) (ψ : B -> B -> iProp Σ)
  (P P' : list B -> iProp Σ) E K :
  {{{
        □ (∀ (x x' : A) K' (prev prev' : list B),
            {{{ γ x x' ∗ ⤇ fill K' (fv' (inject x')) ∗ P prev ∗ P' prev' }}}
              fv (inject x) @ E
              {{{ frv, RET frv;
                  ∃ frv' fr fr',
                    ⌜frv = (inject fr)⌝ ∗ ⌜frv' = (inject fr')⌝
                    ∗ ⤇ fill K' frv'
                    ∗ ψ fr fr' ∗ P (fr :: prev) ∗ P' (fr' :: prev')
          }}}) ∗
      ⌜is_list l lv⌝ ∗
      ⌜is_list l' lv'⌝ ∗
      ⌜length l = length l'⌝ ∗
      ([∗ list] i ↦ a;a' ∈ l;l', γ a a') ∗
      P [] ∗ P' [] ∗
      ⤇ fill K (list_map fv' lv')
  }}}
    list_map fv lv @ E
    {{{ rv, RET rv;
        ∃ rv' xs xs',
          ⌜is_list xs rv⌝ ∗
          ⌜is_list xs' rv'⌝ ∗
          ⌜length xs = length l⌝ ∗
          ⌜length xs' = length l'⌝ ∗
          ⤇ fill K rv' ∗
          ([∗ list] i ↦ a;a' ∈ xs;xs', ψ a a')
          ∗ P xs ∗ P' xs'
    }}}.
Proof.
  iRevert (l' lv lv' fv fv' K).
  iInduction l as [|l_hd l_tl] "IH".
  - iIntros (l' lv lv' fv fv' K Φ).
    iIntros "[#H (%H1&%H2&%&H3)] HΦ".
    destruct l'; last (simpl in *; lia).
    simpl.
    rewrite /list_map.
    wp_pures.
    inversion H1. inversion H2.
    iDestruct "H3" as "(_&?&?&H3)".
    tp_pures.
    wp_pures.
    iApply "HΦ".
    iFrame. by simpl.
  - iIntros (l' lv lv' fv fv' K Φ).
    iIntros "[#H (%H1&%H2&%&H3)] HΦ".
    simpl in *.
    destruct l' as [|]; first (simpl in *; lia).
    simpl in H2. destruct!/=.
    rewrite /list_map.
    iDestruct "H3" as "([Hγ ?]&?&?&?)".
    wp_pure.
    tp_pure.
    rewrite -/list_map.
    tp_pures.
    wp_pures.
    tp_bind (list_map _ _).
    wp_bind (list_map _ _).
    iApply ("IH" with "[-HΦ Hγ]"); first (iFrame; by repeat iSplit).
    iNext.
    iIntros (?) "(%&%&%&%&%&%&%&?&HΨ&?&?)".
    simpl.
    tp_pures.
    wp_pures.
    wp_bind (fv _).
    tp_bind (fv' _).
    iApply ("H" with "[-HΦ HΨ]"); first iFrame.
    iNext.
    iIntros (?) "(%&%&%&->&->&Hspec&?&?&?)".
    simpl.
    iDestruct (gwp_list_cons (g:=gwp_spec_e) with "[][][$]") as ">(%&?&K)"; first done.
    { iNext. iIntros (?) "K". iApply "K". }
    iDestruct "K" as "%".
    iApply gwp_list_cons; [done |].
    iNext.
    iIntros (?) "%".
    iApply "HΦ".
    iFrame.
    iPureIntro; repeat split; try done; simpl; lia.
Qed.

Lemma wp_alloc_tapes_exp :
  (forall (num den : Z) K xs xs' vxs vxs',
      is_list xs vxs → is_list xs' vxs' → length xs = length xs' →
      Forall2 (λ x x' : Z, dZ x x' <= 1) xs xs' →
      {{{ ⤇ fill K ((list_map (λ: "x", ("x", AllocTapeExp #num #(2 * den) "x")))%V vxs') }}}
        (list_map (λ: "x", ("x", AllocTapeExp #num #(2 * den) "x")))%V vxs
        {{{ vxιs, RET vxιs ; ∃ vxιs' xιs xιs',
                ⌜is_list xιs vxιs⌝ ∗ ⌜length xιs = length xs⌝ ∗
                ⌜is_list xιs' vxιs'⌝ ∗ ⌜length xιs' = length xs'⌝ ∗
                ⌜ NoDup xιs.*2 ⌝ ∗ ⌜ NoDup xιs'.*2 ⌝ ∗
                ⤇ fill K vxιs' ∗
                [∗ list] '(x, ι) ; '(x', ι') ∈ xιs ; xιs',
              ι ↪E (num, 2*den, x; []) ∗ ι' ↪Eₛ (num, 2*den, x'; []) ∗
              ⌜dZ x x' <= 1⌝
  }}}).
Proof.
  iIntros (??????? hxs hxs' hlen adj post) "rhs post".
  iApply (rwp_list_map_e xs xs' vxs vxs'
            (λ: "x", ("x", AllocTapeExp #num #(2 * den) "x"))%V
            (λ: "x", ("x", AllocTapeExp #num #(2 * den) "x"))%V
            (λ x x', ⌜dZ x x' <= 1⌝)%I
            (λ '(x, ι) '(x', ι'), ⌜dZ x x' <= 1⌝ )%I
            (λ xιs, ([∗ list] xι ∈ xιs, let '(x, ι) := xι in ι ↪E (num, 2*den, x; [])) ∗ ⌜NoDup xιs.*2⌝)%I
            (λ xιs', ([∗ list] xι' ∈ xιs', let '(x', ι') := xι' in ι' ↪Eₛ (num, 2*den, x'; [])) ∗ ⌜NoDup xιs'.*2⌝)%I
           with "[-post]").
  2: iNext ; iIntros (?) "h". 2: iApply "post".
  2: {
    iDestruct "h" as "(%&%&%&%&%&%&%&rhs&h&[hh %]&[hh' %])".

    iExists _,_,_. iFrame.
    repeat iSplit => //.
    iAssert (
        ([∗ list] xι ; xι' ∈ xs0 ; xs'0,
           let '(x, ι) := xι in
           let '(x', ι') := xι' in
           (ι ↪E (num,2 * den,x; []) ∗ ι' ↪Eₛ (num,2 * den,x'; [])))
)%I
 with "[hh hh']" as "hh".
    {
      iApply big_sepL2_mono ; last first.
      - iApply (big_sepL2_sep_2 with "[hh]") ; iFrame.
        + iApply big_sepL2_const_sepL_l.
          iSplit => //. iPureIntro. lia.
        + iApply big_sepL2_const_sepL_r.
          iSplit => //. iPureIntro. lia.
      - iIntros. destruct y1, y2. done.
    }
    iDestruct (big_sepL2_sep_2 _ _ xs0 xs'0 with "[h] [hh]") as "hhh".
    1,2: done.


    rewrite !big_sepL2_alt. iSplit ; [iPureIntro ; lia|].
    iApply big_sepL_mono ; last first.
    - iDestruct "hhh" as "[% h]".
      done.
    - iIntros "* % h". simpl. destruct y. destruct p, p0. simpl.
      iDestruct "h" as "(%&h&h')". iFrame. done.
  }
  iFrame. repeat iSplit => //.
  2:{ iInduction adj as [|] forall (vxs vxs' hxs hxs' hlen) => //.
      iSplit => //. simpl.
      inversion hlen. destruct hxs, hxs'.
      iApply "IHadj" => // ; intuition eauto.
  }
  2,3: iPureIntro ; constructor.
  iModIntro. iIntros. iIntros "%post' !> (% & rhs & (hh & %) & (hh' & %)) post'".
  tp_pures. wp_pures.
  (* allocate the spec-side tape, then the impl-side tape (generic gen API).
     After [wp_pures] the [AllocTapeExp] [Pair] argument is already reduced to
     a value, so we fire the generic [wp_alloc_sample_tape]/[tp_alloc_sample_tape]
     on the reduced [AllocSampleTape idx (Val pv)] form directly; the resulting
     [α ↪ (sample_idx, PairV …, [])] is definitionally the [↪E]/[↪Eₛ] view. *)
  tp_alloc_sample_tape as ι' "ι'".
  wp_apply (wp_alloc_sample_tape lidx
              (PairV (LitV (LitInt num)) (PairV (LitV (LitInt (2 * den))) (LitV (LitInt x))))
              with "[//]"); iIntros (ι) "ι".
  tp_pures. wp_pures. iApply "post'".
  iModIntro. iExists _,(x, ι),(x', ι'). simpl. iFrame "rhs".
  repeat iSplit => //=. iSplitL "ι hh".
  - simpl.
    iAssert (⌜ι ∈ list_fmap (Z * loc)%type loc snd prev⌝ -∗ False)%I as "%".
    {
      iIntros "%not_fresh".
      destruct (list_elem_of_fmap_1 snd prev ι not_fresh) as [? []].
      destruct x0. simpl in H2. symmetry in H2.
      simplify_eq.
      iDestruct (big_sepL_elem_of with "hh") as "ι2".
      1: done.
      (* two full-fraction tape points-to on the same [ι]: contradiction *)
      iCombine "ι ι2" gives %[Hbad _].
      by cbv in Hbad.
    }
    iFrame. iPureIntro.
    econstructor. 1,2: assumption.
  - simpl.
    iAssert (⌜ι' ∈ list_fmap (Z * loc)%type loc snd prev'⌝ -∗ False)%I as "%".
    {
      iIntros "%not_fresh'".
      destruct (list_elem_of_fmap_1 snd prev' ι' not_fresh') as [? []].
      destruct x0. simpl in H2. symmetry in H2.
      simplify_eq.
      iDestruct (big_sepL_elem_of with "hh'") as "ι2'".
      1: done.
      iCombine "ι' ι2'" gives %[Hbad _].
      by cbv in Hbad.
    }
    iFrame. iPureIntro.
    econstructor. 1,2: assumption.
Qed.

  Lemma rnm_exp_pres_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (0 < IZR num / IZR (2 * den)) →
    (∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) 1 dDB dZ) →
    ∀ db db', dDB db db' <= 1 →
                {{{ ↯m (IZR num / IZR den) ∗
                    ⤇ fill K (report_noisy_max_exp_presampling num den evalQ #N (of_val (inject db'))) }}}
                  report_noisy_max_exp_presampling num den evalQ #N (of_val (inject db))
                  {{{ v, RET v ; ∃ (v' : val), ⤇ fill K v' ∗ ⌜ v = v' ⌝  }}}.
  Proof with (tp_pures ; wp_pures).
    intros εpos qi_sens db db' db_adj post. iIntros "[ε rhs] Hpost".
    wp_lam. tp_lam...
    destruct N as [|N'].
    {
      rewrite /list_init/list_map/list_map'_e/list_mapi/list_mapi_loop/list_max_index...
      iApply "Hpost". iFrame. done.
    }
    set (N := S N'). assert (0 < N)%nat by (unfold N ; lia).
    tp_bind (list_init _ _). wp_bind (list_init _ _).
    iApply (rnme_init with "rhs") => //.
    iIntros "!> % (% & % & % & rhs & % & % & % & % & %)". simpl...
    tp_bind (list_map _ _). wp_bind (list_map _ _).
    wp_apply (wp_alloc_tapes_exp with "rhs") => //.
    1: lia.
    iIntros "% (% & % & % & % & % & % & % & % & % & rhs & Htapes) /="...
    wp_apply (hoare_couple_exp_list with "[$ε] [$Htapes] [rhs Hpost]") => //.
    1,2: lia.
    iIntros "(% & % & Htapes & %Hmax)".
    (* split the tapes assumption into three list-foralls (two unary ones and one that's pure about the dZ). *)
    iAssert (([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs',
               ι ↪E (num, 2 * den,x; [zs !!! k]))
             ∗
               ([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs',
                  ι' ↪Eₛ (num, 2 * den,x'; [zs' !!! k]) ∗ ⌜dZ x x' <= 1⌝)
            )%I with "[Htapes]" as "[Htapes Htapes']".
    {
      opose proof big_sepL2_sep as h.
      symmetry in h.
      iApply (h with "[Htapes]").
      iApply (big_sepL2_mono with "Htapes").
      iIntros (?[][]) "%% [?[??]]". iFrame.
    }
    iAssert (([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs',
                  ι' ↪Eₛ (num, 2 * den,x'; [zs' !!! k]))
             ∗
               ([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs', ⌜dZ x x' <= 1⌝)
            )%I with "[Htapes']" as "[Htapes' htapes]".
    {
      opose proof big_sepL2_sep as h.
      symmetry in h.
      iApply (h with "[Htapes']").
      iApply (big_sepL2_mono with "Htapes'").
      iIntros (?[][]) "%% [??]". iFrame.
    }
    iAssert ((
                ∃ (xs xs' : list Z) (ιs ιs' : list loc),
                  ([∗ list] k↦'xι ∈ xιs,
                     let '(x, ι) := xι in
                     ⌜xs !!! k = x⌝ ∗ ⌜ιs !!! k = ι⌝ ∗
                     ι ↪E (num, 2 * den,x; [zs !!! k]))
                ∗
                  ([∗ list] k↦xι' ∈ xιs',
                     let '(x', ι') := xι' in
                     ⌜xs' !!! k = x'⌝ ∗ ⌜ιs' !!! k = ι'⌝ ∗
                     ι' ↪Eₛ (num, 2 * den,x'; [zs' !!! k]))
                ∗ ⌜Forall2 (λ x x', dZ x x' <= 1) xs xs'⌝
             )%I
              ) with "[Htapes Htapes' htapes]" as
      "(%&%&%&%& Htapes & Htapes' & %htapes)".
    {
      assert (forall (xys : list (Z * loc)) k x y, xys !! k = Some (x,y) → (xys .*1) !! k = Some x) as lookup_fmap_fst.
      {
        clear. intro xys. induction xys. 1: done.
        intros. destruct k.
        - simpl. simpl in H. inversion H. subst. simpl. done.
        - destruct a.
          rewrite fmap_cons.
          simpl. simpl in H. eapply IHxys. done.
      }
      assert (forall (xys : list (Z * loc)) k x y, xys !! k = Some (x,y) → (xys .*2) !! k = Some y) as lookup_fmap_snd.
      {
        clear. intro xys. induction xys. 1: done.
        intros. destruct k.
        - simpl. simpl in H. inversion H. subst. simpl. done.
        - destruct a.
          rewrite fmap_cons.
          simpl. simpl in H. eapply IHxys. done.
      }
      iExists (xιs.*1). iExists (xιs'.*1).
      iExists (xιs.*2). iExists (xιs'.*2).
      iSplitL "Htapes" ; [|iSplitL "Htapes'"].
      - opose proof (big_sepL2_const_sepL_l (λ k '(x, ι), ι ↪E (num, 2 * den,x; [zs !!! k]))%I xιs xιs') as h.
        symmetry in h.
        iDestruct (h with "[Htapes]") as "[% Htapes]" ; clear h.
        { iApply (big_sepL2_mono with "Htapes").
          iIntros (? [] []). iIntros. done. }
        iApply (big_sepL_mono with "Htapes").
        iIntros (? []). iIntros. iFrame.
        iPureIntro. split.
        + apply list_lookup_total_correct. eapply lookup_fmap_fst. done.
        + apply list_lookup_total_correct. eapply lookup_fmap_snd. done.
      - opose proof (big_sepL2_const_sepL_r (λ k '(x, ι), ι ↪Eₛ (num, 2 * den,x; [zs' !!! k]))%I xιs xιs') as h.
        symmetry in h.
        iDestruct (h with "[Htapes']") as "[% Htapes']" ; clear h.
        { iApply (big_sepL2_mono with "Htapes'").
          iIntros (? [] []). iIntros. done. }
        iApply (big_sepL_mono with "Htapes'").
        iIntros (? []). iIntros. iFrame.
        iPureIntro. split.
        + apply list_lookup_total_correct. eapply lookup_fmap_fst. done.
        + apply list_lookup_total_correct. eapply lookup_fmap_snd. done.
      -
        iApply big_sepL2_Forall2.
        iApply big_sepL2_fmap_l.
        iApply big_sepL2_fmap_r.
        iApply (big_sepL2_mono with "htapes").
        { iIntros (? [] []). iIntros. simpl. done. }
    }

    wp_bind (list_mapi _ _).

    iApply (gwp_list_mapi (A:=Z*loc) (B:=Z)
              (Inject0 := (@Inject_prod Z _ loc _))
              (λ k '(x, ι), zs !!! k)
              xιs
              _
              _
              (λ k xι, let '(x, ι) := xι in ι ↪E (num, 2*den, x; [zs !!! k]))%I
              (λ k z', ⌜zs !!! k = z'⌝)%I
             with "[Htapes]").
    { repeat iSplit.
      - iModIntro.
        iIntros (k [x ι] Φ) "!> ι HΦ". simpl.
        wp_pures.
        (* The coupling left a concrete singleton tape [zs !!! k]; pin [z]/[zs] of
           [wp_exp_tape_val] explicitly so its [↪E] precondition (an fmap over
           [z :: zs]) matches the goal's [↪E (…; [zs !!! k])] syntactically — the
           generic tape stores [list val], so unification can't invert the fmap. *)
        wp_apply (wp_exp_tape_val num (2 * den)%Z x (zs !!! k) [] ι with "[$ι]") ; iIntros "ι".
        iApply "HΦ". done.
      - done.
      - iApply (big_sepL_mono with "Htapes").
        iIntros (?[]) "% [?[??]]". iFrame.
    }
    iIntros "!> % h_list_mapi". idtac...

    tp_pures.
    tp_bind (list_mapi _ _).

    iMod (gwp_list_mapi (g:=gwp_spec_e)
                  (λ k '(x, ι), zs' !!! k) xιs'
                  _
                  vxιs'
                  (λ k '(x, ι), ι ↪Eₛ (num, 2*den, x; [zs' !!! k]))%I
                  (λ k z', ⌜zs' !!! k = z'⌝)%I
               with "[Htapes'] [] [$rhs]") as (?) "[rhs h_list_mapi']".
    {
      repeat iSplit.
      - iModIntro.
        iIntros (k [x ι] Φ) "!> ι HΦ %K' rhs". simpl.
        tp_pures.
        tp_sample_tape.
        iModIntro. iFrame. iApply "HΦ". done.
      - done.
      - iApply (big_sepL_mono with "Htapes'").
        iIntros (?[]) "% [?[??]]". iFrame.
    }
    1: { iIntros "% hh". iExact "hh". }
    iSimpl in "rhs". tp_pures.
    iDestruct "h_list_mapi" as "(%mapi1&%mapi2)".
    iDestruct "h_list_mapi'" as "(%mapi1'&%mapi2')".

    iMod (gwp_list_max_index (g:=gwp_spec_e) _ _ _
            (fun (i : val) => ⌜i = LitV (LitInt (List_max_index (mapi (λ (k : nat) '(_, _), zs' !!! k) xιs')))⌝)%I
          with "[] [] rhs")
      as (?) "[rhs %max_rhs]".
    1: done.
    { iIntros (?) "%hh". rewrite hh. done. }
    iApply gwp_list_max_index.
    1: done.
    iIntros "!> **".
    iApply "Hpost".
    iFrame.
    simplify_eq.
    iPureIntro. f_equal. f_equal. f_equal.
    destruct Hmax as (?&?&?).
    rewrite !list_max_index_eq.
    assert (zs' = (mapi (λ (k : nat) '(_, _), zs' !!! k) xιs')) as <- ; first last.
    1: assert (zs = (mapi (λ (k : nat) '(_, _), zs !!! k) xιs)) as <- ; first last.
    1: assumption.
    - eapply lookup_eq_pointwise.
      { rewrite mapi_length. lia. }
      intros. apply mapi2.
      apply list_lookup_lookup_total_lt.
      done.
    - eapply lookup_eq_pointwise.
      { rewrite mapi_length. lia. }
      intros. apply mapi2'.
      apply list_lookup_lookup_total_lt.
      done.
  Qed.

End rnme.

Lemma rnm_exp_diffpriv_presampling (Sg : Sig) `{!SampleIn exp_family Sg} num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR num / IZR den)%R →
  (∀ `{!diffprivGS Sg Σ}, ∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) 1 dDB dZ) → ∀ σ,
      diffpriv_pure
        dDB
        (λ db, lim_exec (δ := lang_markov (gen_lang Sg)) ((report_noisy_max_exp_presampling num den evalQ #N (inject db)), σ))
        (IZR num / IZR den).
Proof.
  intros. apply diffpriv_approx_pure. apply DPcoupl_diffpriv.
  intros.
  eapply (wp_adequacy Sg diffprivΣ) => //.
  iIntros (?)"H1 H2".
  iDestruct (rnm_exp_pres_diffpriv with "[$H2 H1]") as "K"; try done.
  - by erewrite fill_empty.
  - iIntros.
    iApply "K".
    iNext. iIntros (?) "(%&?&%)".
    by iFrame.
Qed.
