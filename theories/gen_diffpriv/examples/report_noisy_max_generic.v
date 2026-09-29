(** Report-noisy-max (presampling) DP case study, NOISE-GENERIC IMPLEMENTATION.

    This file factors the ~480-line implementation body shared between the
    Laplace ([report_noisy_max]) and one-sided exponential
    ([report_noisy_max_exp]) report-noisy-max developments into ONE
    library parametric over the noise distribution [sample : Z → Z → Z → distr Z].

    The two reference files were identical modulo renaming EXCEPT the per-noise
    list-presampling coupling ([hoare_couple_laplace_list]/[hoare_couple_exp_list]).
    That single spot becomes the section hypothesis [Hcouple]; everything else is
    a verbatim copy with [laplace_family]/[↪L]/[Laplace]/[AllocTapeLaplace]
    replaced by their generic [mkZNoise sample mass]-level analogues.

    The noise distribution is presented to the language as [mkZNoise sample mass],
    whose projections reduce DEFINITIONALLY ([sf_out = Z], [sf_inj = LitV ∘ LitInt],
    the standard [(num,den,mean) ↔ PairV] encoding).  That is what lets the tape
    notations / generic tape rules go through with NO [sf_out = Z] transport.

    See [report_noisy_max_pointwise] for the pointwise (coupling) variant and the
    rationale for [#[global] Opaque sample_idx]. *)
From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics iris_ext.
From clutch.prob Require Import differential_privacy distribution.
From clutch.gen_diffpriv Require Import adequacy all.
From clutch.gen_prob_lang Require Import gwp.list inject families znoise.
From clutch.gen_prob_lang.spec Require Import spec_ra spec_rules.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_lemmas.
From iris.prelude Require Import options.

(** This development genuinely depends on the section hypotheses
    [sample]/[mass]/[Hcouple], so we let every proof generalise over all in-scope
    section variables (matching [report_noisy_max_generic_lemmas]). *)
Set Default Proof Using "All".

(** PARAMETRIC over any signature [Sg] containing the (abstract) noise family
    [mkZNoise sample mass] (recovered via the ambient [SampleIn (mkZNoise …) Sg])
    — so RNM composes with any other mechanism whose program samples from a
    richer signature; the concrete [Sg] is supplied only at the closing adequacy
    corollary (in the per-noise instantiation file).  With an abstract
    [SampleIn], [sample_idx] is already a frozen atom, so the concrete-instance
    [Opaque SampleIn_rnm] OOM workaround is no longer needed. *)
#[global] Opaque sample_idx.

(** [inject x : expr] resolves to the *unreduced* [@inject A expr _ x] rather
    than the [Val]-headed form; the spec reshape tactics need a [Val] head.  See
    [report_noisy_max_pointwise] for the full explanation. *)
Lemma inject_expr_Val_gen {A} `{!Inject A val} (x : A) :
  (inject x : expr) = Val (inject x).
Proof. reflexivity. Qed.

(** Spec-side [GenWp] instance [gwp_spec] is now SHARED in
    [gen_prob_lang.spec.spec_rules] (available here via [Require Import … all]),
    de-duplicating the copy that used to live in this file. *)

Section generic.
  Context (sample : Z → Z → Z → distr Z)
          (mass : ∀ num den mean, (SeriesC (sample num den mean) = 1)%R).
  Local Notation D := (mkZNoise sample mass).
  Context {Sg : Sig} `{!SampleIn D Sg} `{!diffprivGS Sg Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Sg)).
  Local Notation lidx := (@sample_idx D Sg _).

  (** Generic noise tape views, the [mkZNoise]-level analogue of [laplace_tapes]'
      [↪L]/[↪Lₛ] (hardcoded to [laplace_family]).  Here [D = mkZNoise sample mass]
      is section-local, so these are [Local Notation]s off the ambient
      [SampleIn D Sg] instance; [sf_param_to_val D (num,den,mean)] reduces
      definitionally to the explicit [PairV …] form below. *)
  Local Notation "α ↪N ( num , den , mean ; zs )" :=
    ((α ↪ (sample_idx (D := D),
             PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))),
             ((λ z : Z, LitV (LitInt z)) <$> zs)))%I)
    (at level 20, format "α  ↪N  ( num ,  den ,  mean ;  zs )") : bi_scope.

  Local Notation "α ↪Nₛ ( num , den , mean ; zs )" :=
    ((α ↪ₛ (sample_idx (D := D),
              PairV (LitV (LitInt num)) (PairV (LitV (LitInt den)) (LitV (LitInt mean))),
              ((λ z : Z, LitV (LitInt z)) <$> zs)))%I)
    (at level 20, format "α  ↪Nₛ  ( num ,  den ,  mean ;  zs )") : bi_scope.

  (** The ONLY noise-specific input: the list-presampling coupling for this noise,
      discharged per noise by [hoare_couple_noise_list sample mass Hiso Hshift]
      from the thin per-noise lemmas files.  Its type is copied verbatim from
      [report_noisy_max_generic_lemmas]'s [hoare_couple_noise_list], with the
      generic [↪N]/[↪Nₛ] notations above. *)
  Context (Hcouple : ∀ (Δ : Z) (num den : Z) (xιs xιs' : list (Z * loc)) (N : nat) (e : expr)
                       (Φ : val → iProp Σ),
              (1 <= Δ)%Z →
              (0 < IZR num / IZR (2 * den))%R →
              length xιs = N →
              length xιs = length xιs' →
              (length xιs > 0)%nat →
              NoDup xιs.*2 → NoDup xιs'.*2 →
              ↯m (IZR Δ * (IZR num / IZR den)) -∗
              ([∗ list] '(x, ι);'(x', ι') ∈ xιs;xιs',
                 ι ↪N (num, 2 * den, x; []) ∗ ι' ↪Nₛ (num, 2 * den, x'; []) ∗
                 ⌜(dZ x x' <= IZR Δ)%R⌝) -∗
              ((∃ zs zs', ([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs',
                              ι ↪N (num, 2 * den, x; [zs !!! k]) ∗
                              ι' ↪Nₛ (num, 2 * den, x'; [zs' !!! k]) ∗
                              ⌜(dZ x x' <= IZR Δ)%R⌝) ∗
                           ⌜length zs = N⌝ ∗
                           ⌜length zs' = N⌝ ∗
                           ⌜list_Z_max zs = list_Z_max zs'⌝)
               -∗ WP e {{ v, Φ v }}) -∗
              WP e {{ v, Φ v }}).

  #[local] Open Scope R.

  Definition report_noisy_max_presampling (num den : Z) : val :=
    (* ↯ (num/den) ∗ evalQ is 1-sensitive ∗ N ∈ ℕ \ {0} ∗ 0 < num/2den ∗ dDB db db' <= 1 *)
    λ:"evalQ" "N" "d",
      let: "xs" := list_init_poly #() "N" (λ:"i", "evalQ" "i" "d") in
      let: "xs_tapes" := list_map_poly #() #() (λ:"x", ("x", AllocSampleTape (sample_idx (D := D)) (Pair #num (Pair #(2*den) "x")))) "xs" in
      let: "noisy_xs" := list_map_poly #() #() (λ: "x_ι", Sample (sample_idx (D := D)) (Pair #num (Pair #(2*den) (Fst "x_ι"))) (Snd "x_ι")) "xs_tapes" in
      list_max_index "noisy_xs".

  Lemma rnm_init (Δ : Z) (C : Z) (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (1 <= Δ)%Z →
    (0 <= C)%Z →
    (∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) →
    ∀ db db', dDB db db' <= IZR C →
              {{{ ⤇ fill K ((of_val list_init_poly) #() #N (λ:"i", (of_val evalQ) "i" (of_val (inject db'))))%V }}}
                (list_init_poly #() #N (λ:"i", evalQ "i" (of_val (inject db))))%V
                {{{ vxs, RET vxs ; ∃ (vxs' : val) (xs xs' : list Z),
                        ⤇ fill K vxs' ∗
                        ⌜ is_list xs vxs ∧ is_list xs' vxs' ∧ length xs = N ∧ length xs' = N ∧
                        Forall2 (λ x x', dZ x x' <= IZR Δ * IZR C) xs xs'⌝
                }}}.
  Proof.
    iIntros (HΔ HC ev_sens db db' adj post) "rhs Hpost".
    (* enter the type-app [#()] and the two lambdas on both master ([wp_]) and
       spec ([tp_]) sides, reaching [aux #0] applied on each. *)
    rewrite /list_init_poly.
    (* enter the wrapper lambdas, then STOP at the head [(rec…) #0] (the loop-spec
       head): the wrapper is [(λ:<>, λ:"len" "f", (rec…)#0) #() #N f], 3 betas
       (each preceded by a [Rec→RecV] closure-formation step) — do NOT [wp_pures]
       all the way, which would additionally rec-unfold [(rec…) #0]. *)
    do 6 wp_pure. do 6 tp_pure.
    (* Forward loop spec: for the run starting at index [#i] with [m] elements
       remaining ([i + m = N]), [aux #i] on master and spec produce related lists
       of length [m].  Thread the spec [⤇] through [tp_]. *)
    iAssert (□ ∀ (m i : nat) (K2 : ectx (gen_ectx_lang Sg)), ⌜(i + m = N)%nat⌝ -∗
              ⤇ fill K2 ((rec: "aux" "i" :=
                           if: "i" = #N then InjL #()
                           else let: "h" := (λ:"i", (of_val evalQ) "i" (of_val (inject db')))%V "i" in
                                let: "t" := "aux" ("i" + #1) in
                                "h" :: "t")%V #i) -∗
              WP ((rec: "aux" "i" :=
                     if: "i" = #N then InjL #()
                     else let: "h" := (λ:"i", evalQ "i" (of_val (inject db)))%V "i" in
                          let: "t" := "aux" ("i" + #1) in
                          "h" :: "t")%V #i)
                {{ vxs, ∃ (vxs' : val) (xs xs' : list Z), ⤇ fill K2 vxs' ∗
                    ⌜is_list xs vxs ∧ is_list xs' vxs' ∧ length xs = m ∧ length xs' = m ∧
                     Forall2 (λ x x', dZ x x' <= IZR Δ * IZR C) xs xs'⌝ }})%I as "#Hloop".
    { iModIntro. iIntros (m). iInduction m as [|m] "IH"; iIntros (i K2 Hi) "rhs".
      - (* i = N: both runs take the [if #N = #N then []] branch; return [] with xs = []. *)
        assert (i = N) as -> by lia.
        tp_rec. tp_pures. rewrite bool_decide_eq_true_2 //. tp_pures.
        wp_rec. wp_pures. rewrite bool_decide_eq_true_2 //. wp_pures.
        iModIntro. iExists (InjLV #()), [], []. iSplitL "rhs"; [iExact "rhs"|].
        iPureIntro; cbn; intuition eauto.
      - (* i < N: [if #i = #N] is FALSE; take the else branch. *)
        wp_rec. wp_pures. tp_rec. tp_pures.
        rewrite bool_decide_eq_false_2; [|injection 1 as ?%Nat2Z.inj; lia].
        wp_pures. tp_pures.
        (* [let h := evalQ #i db] -- bound first (forward), use sensitivity. *)
        tp_bind (evalQ _ _) ; wp_bind (evalQ _ _).
        wp_apply (ev_sens with "[] [rhs]").
        1: iPureIntro; apply Rle_trans with (r2 := 1%R); [lra| apply IZR_le; lia].
        1: iFrame.
        iIntros "% (%b&%b'&->&rhs&%h)".
        (* The [ev_sens] return left the spec value [inject b'] sitting inside an
           [AppRCtx (λ:"h", …)]; [tp_normalise] reassembles it into a head
           [let]-redex so the spec [tp_] reshape can see it. *)
        tp_normalise.
        (* Beta the [let: "h" := …] on both sides.  Each side needs TWO pure steps:
           the first FORMS the [Rec → RecV] closure of the let-lambda, the second
           BETA-reduces it.  Stop here (do NOT [wp_pures]/[tp_pures] on): the
           recursive [aux] applied to a value is itself a pure redex, so the greedy
           tactics would inline the next loop iteration and break the IH match. *)
        tp_pure. tp_pure. wp_pure. wp_pure.
        (* now both sides are [let: "t" := (rec…) (#i + #1) in v :: "t"]; bind the
           recursive call and reduce its index, then apply the IH. *)
        tp_bind (App (Val _) (BinOp _ _ _)) ; wp_bind (App (Val _) (BinOp _ _ _)).
        (* reduce ONLY the index [#i + #1 ⇝ #(i+1)] (do NOT [tp_pures]/[wp_pures]
           here — that would rec-unfold the focused [(rec…) (#i+#1)] and break the
           syntactic match with the IH's [(rec…) #(i+1)] head). *)
        tp_pure_at (BinOp _ _ _). wp_pure.
        replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1)%nat) by lia.
        (* the recursive spec call sits under the [::]-continuation context
           [AppRCtx (λ:"t", #b' :: "t")]; instantiate the IH's spec context [K2]
           with it (extended), and [wp_wand] the bound recursive WP into the
           [#b :: t] cons continuation. *)
        iApply (wp_wand with "[rhs]").
        { iApply ("IH" $! (i+1)%nat (AppRCtx (λ: "t", (#b' :: "t")) :: K2) with "[] rhs").
          iPureIntro; lia. }
        iIntros (vt) "(%vt' & %xs & %xs' & rhs & %Hxs & %Hxs' & %Hlen & %Hlen' & %HF)".
        (* reduce the SPEC cons FIRST (while the master WP is still live to host
           the [tp_] tactics), then the master cons; [list_cons] must be unfolded
           by hand (the [tp_]/[wp_] pure tactics do not unfold definitions). *)
        tp_normalise. rewrite /list_cons. tp_pures.
        rewrite /list_cons. wp_pures.
        (* [h :: t]: cons, length [S m], extend [Forall2]. *)
        iModIntro. iExists (InjRV (#b', vt')), (b :: xs), (b' :: xs'). iFrame "rhs".
        iPureIntro; cbn; intuition eauto.
        constructor. 2: done.
        simpl in h. etrans; first exact h.
        apply Rmult_le_compat_l; [apply IZR_le; lia| exact adj].
    }
    (* the program literal index is [#0] ([LitInt 0%Z]); the loop spec's [#i] at
       [i = 0] is [#(Z.of_nat 0)] — convertible; fold the goal/resource to match. *)
    change (LitInt 0) with (LitInt (Z.of_nat 0%nat)).
    (* run the loop at [(m,i) = (N,0)] (so [length xs = N]); its result list then
       discharges the [rnm_init] postcondition [Hpost]. *)
    iApply (wp_wand with "[rhs]").
    { iApply ("Hloop" $! N 0%nat K with "[] rhs"). iPureIntro; lia. }
    iIntros (vxs) "(%vxs' & %xs & %xs' & rhs & %)".
    iApply "Hpost".
    iExists _, _, _. iFrame. iPureIntro. intuition eauto.
  Qed.

Local Program Instance : Inject loc val := {| inject := LitV ∘ LitLbl |}.
Next Obligation. by intros ?? [=]. Qed.

(* γ := (dZ x x' <= 1) *)
Lemma rwp_list_map {A} `{!Inject A val} `{!Inject B val}
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
      ⤇ fill K (list_map_poly #() #() fv' lv')
  }}}
    list_map_poly #() #() fv lv @ E
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
  iIntros (Φ) "(#H & %H1 & %H2 & %Hlen & H3 & HP & HP' & Hspec) HΦ".
  (* [list_map_poly #() #()] = [list_map] up to head beta-steps: strip the two
     type-app thunks (3 [_pure] steps) on BOTH master and spec so the induction
     hypothesis is stated about the inner loop [list_map_go] (which the recursive
     occurrence in the body is headed by), exactly as the mono proof was about
     [list_map]. *)
  rewrite /list_map_poly. do 3 wp_pure. do 3 tp_pure.
  iInduction l as [|l_hd l_tl] "IH"
    forall (l' lv lv' fv fv' K Φ H1 H2 Hlen) "H H3 HP HP' Hspec HΦ".
  - destruct l'; last (simpl in *; lia).
    simpl. inversion H1. inversion H2. subst.
    rewrite /list_map_go.
    tp_pures. wp_pures.
    iApply "HΦ".
    iFrame. by simpl.
  - simpl in *.
    destruct l' as [|l'_hd l'_tl]; first (simpl in *; lia).
    simpl in H1, H2. destruct!/=.
    iDestruct "H3" as "[Hγ H3]".
    rewrite /list_map_go.
    (* one extra identity-unfold beta per recursion: [do 8 _pure] (vs the mono
       [list_map]'s implicit step count) walks past the [(λx,x) "l"] coercion and
       the [match]/projections to expose the recursive [list_map_go] call as a
       value-headed redex on each side; [_pures] would over-reduce (it unfolds the
       [rec] occurrence). *)
    do 8 tp_pure. do 8 wp_pure.
    rewrite -/list_map_go.
    tp_bind (list_map_go _ _); wp_bind (list_map_go _ _).
    iApply ("IH" $! l'_tl lv1 lv0 fv fv' _ _
              with "[//] [//] [//] H H3 HP HP' Hspec [HΦ Hγ]").
    iIntros (rvrec) "(%rv'rec & %xsr & %xsr' & %Hxsr & %Hxsr' & %Hlxs & %Hlxs' & Hsp & HΨ & HPxs & HPxs')".
    simpl.
    tp_pures.
    wp_pures.
    wp_bind (fv _).
    tp_bind (fv' _).
    iApply ("H" with "[$Hγ $Hsp $HPxs $HPxs']").
    iNext.
    iIntros (frv) "(%frv' & %fr & %fr' & -> & -> & Hspec & Hψ & HPf & HPf')".
    simpl.
    iDestruct (gwp_list_cons (g:=gwp_spec) with "[][][$]") as ">(%&?&K)"; first done.
    { iNext. iIntros (?) "K". iApply "K". }
    iDestruct "K" as "%".
    iApply gwp_list_cons; [done |].
    iNext.
    iIntros (?) "%".
    iApply "HΦ".
    iFrame.
    iPureIntro; repeat split; try done; simpl; lia.
Qed.

Lemma wp_alloc_tapes_noise :
  (forall (Δ num den : Z) K xs xs' vxs vxs',
      is_list xs vxs → is_list xs' vxs' → length xs = length xs' →
      Forall2 (λ x x' : Z, dZ x x' <= IZR Δ) xs xs' →
      {{{ ⤇ fill K ((list_map_poly #() #() (λ: "x", ("x", AllocSampleTape (sample_idx (D := D)) (Pair #num (Pair #(2 * den) "x")))))%V vxs') }}}
        (list_map_poly #() #() (λ: "x", ("x", AllocSampleTape (sample_idx (D := D)) (Pair #num (Pair #(2 * den) "x")))))%V vxs
        {{{ vxιs, RET vxιs ; ∃ vxιs' xιs xιs',
                ⌜is_list xιs vxιs⌝ ∗ ⌜length xιs = length xs⌝ ∗
                ⌜is_list xιs' vxιs'⌝ ∗ ⌜length xιs' = length xs'⌝ ∗
                ⌜ NoDup xιs.*2 ⌝ ∗ ⌜ NoDup xιs'.*2 ⌝ ∗
                ⤇ fill K vxιs' ∗
                [∗ list] '(x, ι) ; '(x', ι') ∈ xιs ; xιs',
              ι ↪N (num, 2*den, x; []) ∗ ι' ↪Nₛ (num, 2*den, x'; []) ∗
              ⌜dZ x x' <= IZR Δ⌝
  }}}).
Proof.
  iIntros (???????? hxs hxs' hlen adj post) "rhs post".
  iApply (rwp_list_map xs xs' vxs vxs'
            (λ: "x", ("x", AllocSampleTape (sample_idx (D := D)) (Pair #num (Pair #(2 * den) "x"))))%V
            (λ: "x", ("x", AllocSampleTape (sample_idx (D := D)) (Pair #num (Pair #(2 * den) "x"))))%V
            (λ x x', ⌜dZ x x' <= IZR Δ⌝)%I
            (λ '(x, ι) '(x', ι'), ⌜dZ x x' <= IZR Δ⌝ )%I
            (λ xιs, ([∗ list] xι ∈ xιs, let '(x, ι) := xι in ι ↪N (num, 2*den, x; [])) ∗ ⌜NoDup xιs.*2⌝)%I
            (λ xιs', ([∗ list] xι' ∈ xιs', let '(x', ι') := xι' in ι' ↪Nₛ (num, 2*den, x'; [])) ∗ ⌜NoDup xιs'.*2⌝)%I
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
           (ι ↪N (num,2 * den,x; []) ∗ ι' ↪Nₛ (num,2 * den,x'; [])))
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
     After [wp_pures] the [AllocSampleTape] [Pair] argument is already reduced to
     a value, so we fire the generic [wp_alloc_sample_tape]/[tp_alloc_sample_tape]
     on the reduced [AllocSampleTape idx (Val pv)] form directly; the resulting
     [α ↪ (sample_idx, PairV …, [])] is definitionally the [↪N]/[↪Nₛ] view. *)
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

  (** Headline RNM privacy, now stated as the internal-DP notion
      [hoare_diffpriv_classic_at] with the index-range-carrying codomain
      [fin (Nat.max 1 N)] (always inhabited, so no [0 < N] side-condition).
      The radius is fixed at [IZR C] and the [del] component is the tight [0].

      [1 ≤ C] is genuinely needed by the body (the tape-allocation/coupling
      machinery runs at the a-priori INTEGER gap [Δ*C] and requires [1 ≤ Δ*C]),
      so it stays as a hypothesis; the [classic_at] radius is then exactly that
      group size [C]. *)
  Lemma rnm_pres_diffpriv (Δ : Z) (C : Z) num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
    (1 <= Δ)%Z →
    (1 <= C)%Z →
    (0 < IZR num / IZR (2 * den)) →
    (∀ i : Z, ⊢ hoare_sensitive Sg (evalQ #i) (IZR Δ) dDB dZ) →
    ⊢ hoare_diffpriv_classic_at Sg (report_noisy_max_presampling num den evalQ #N)
        (IZR C * (IZR Δ * (IZR num / IZR den))) 0 (IZR C) dDB (fin (Nat.max 1 N)).
  Proof with (tp_pures ; wp_pures).
    intros HΔ HC εpos qi_sens.
    rewrite /hoare_diffpriv_classic_at.
    iIntros (K db db') "%db_adj".
    (* the [↯ 0] component is discarded. *)
    iIntros (post) "!> (rhs & ε & _) Hpost".
    wp_lam. tp_lam...
    destruct N as [|N'].
    {
      rewrite /list_init_poly/list_map_poly/list_map_go/list_max_index...
      (* [Nat.max 1 0 = 1]; return the sole inhabitant [0%fin : fin 1], whose
         injection [#(Z.of_nat (fin_to_nat 0%fin)) = #0] matches the empty-list
         default returned by [list_max_index NONE]. *)
      iModIntro. iApply ("Hpost" $! (0%fin : fin 1)). iExact "rhs".
    }
    set (N := S N'). assert (0 < N)%nat by (unfold N ; lia).
    tp_bind (list_init_poly _ _ _). wp_bind (list_init_poly _ _ _).
    iApply (rnm_init Δ C with "rhs") => //.
    1: lia.
    iIntros "!> % (% & % & % & rhs & % & % & % & % & %HF)". simpl...
    (* fold [IZR Δ * IZR C] into [IZR (Δ * C)] so the effective-[Δ*C] tape /
       coupling lemmas match the [rnm_init] gap bound syntactically. *)
    rewrite -mult_IZR in HF.
    tp_bind (list_map_poly _ _ _ _). wp_bind (list_map_poly _ _ _ _).
    wp_apply (wp_alloc_tapes_noise (Δ * C) with "rhs") => //.
    1: lia.
    iIntros "% (% & % & % & % & % & % & % & % & % & rhs & Htapes) /="...
    (* [IZR C * (IZR Δ * (num/den)) = IZR (Δ*C) * (num/den)], the effective-[Δ*C]
       per-query cost — group privacy scales the unit-radius cost linearly by C. *)
    assert (IZR C * (IZR Δ * (IZR num / IZR den)) =
              IZR (Δ * C) * (IZR num / IZR den))%R as Hcost
        by (rewrite mult_IZR; lra).
    rewrite Hcost.
    wp_apply (Hcouple (Δ * C) with "[$ε] [$Htapes] [rhs Hpost]") => //.
    1,2,3: lia.
    iIntros "(% & % & Htapes & %Hmax)".
    (* split the tapes assumption into three list-foralls (two unary ones and one that's pure about the dZ). *)
    iAssert (([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs',
               ι ↪N (num, 2 * den,x; [zs !!! k]))
             ∗
               ([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs',
                  ι' ↪Nₛ (num, 2 * den,x'; [zs' !!! k]) ∗ ⌜dZ x x' <= IZR (Δ * C)⌝)
            )%I with "[Htapes]" as "[Htapes Htapes']".
    {
      opose proof big_sepL2_sep as h.
      symmetry in h.
      iApply (h with "[Htapes]").
      iApply (big_sepL2_mono with "Htapes").
      iIntros (?[][]) "%% [?[??]]". iFrame.
    }
    iAssert (([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs',
                  ι' ↪Nₛ (num, 2 * den,x'; [zs' !!! k]))
             ∗
               ([∗ list] k↦'(x, ι);'(x', ι') ∈ xιs;xιs', ⌜dZ x x' <= IZR (Δ * C)⌝)
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
                     ι ↪N (num, 2 * den,x; [zs !!! k]))
                ∗
                  ([∗ list] k↦xι' ∈ xιs',
                     let '(x', ι') := xι' in
                     ⌜xs' !!! k = x'⌝ ∗ ⌜ιs' !!! k = ι'⌝ ∗
                     ι' ↪Nₛ (num, 2 * den,x'; [zs' !!! k]))
                ∗ ⌜Forall2 (λ x x', dZ x x' <= IZR (Δ * C)) xs xs'⌝
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
      - opose proof (big_sepL2_const_sepL_l (λ k '(x, ι), ι ↪N (num, 2 * den,x; [zs !!! k]))%I xιs xιs') as h.
        symmetry in h.
        iDestruct (h with "[Htapes]") as "[% Htapes]" ; clear h.
        { iApply (big_sepL2_mono with "Htapes").
          iIntros (? [] []). iIntros. done. }
        iApply (big_sepL_mono with "Htapes").
        iIntros (? []). iIntros. iFrame.
        iPureIntro. split.
        + apply list_lookup_total_correct. eapply lookup_fmap_fst. done.
        + apply list_lookup_total_correct. eapply lookup_fmap_snd. done.
      - opose proof (big_sepL2_const_sepL_r (λ k '(x, ι), ι ↪Nₛ (num, 2 * den,x; [zs' !!! k]))%I xιs xιs') as h.
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

    wp_bind (list_map_poly _ _ _ _).

    iApply (gwp_list_map_poly_idx (A:=Z*loc) (B:=Z)
              (Inject0 := (@Inject_prod Z _ loc _))
              (λ k '(x, ι), zs !!! k)
              xιs
              _
              _
              (λ k xι, let '(x, ι) := xι in ι ↪N (num, 2*den, x; [zs !!! k]))%I
              (λ k z', ⌜zs !!! k = z'⌝)%I
             with "[Htapes]").
    { repeat iSplit.
      - iModIntro.
        iIntros (k [x ι] Φ) "!> ι HΦ". simpl.
        wp_pures.
        (* The coupling left a concrete singleton tape [zs !!! k]; pin [z]/[zs] of
           the generic [wp_sample_tape] explicitly so its [↪] precondition (an fmap
           over [z :: zs]) matches the goal's [↪N (…; [zs !!! k])] syntactically —
           the generic tape stores [list val], so unification can't invert the
           fmap. *)
        wp_apply (wp_sample_tape lidx
                    (PairV (LitV (LitInt num)) (PairV (LitV (LitInt (2 * den))) (LitV (LitInt x))))
                    (LitV (LitInt (zs !!! k)))
                    ((λ z0 : Z, LitV (LitInt z0)) <$> ([] : list Z)) ι with "[$ι]") ; iIntros "ι".
        iApply "HΦ". done.
      - done.
      - iApply (big_sepL_mono with "Htapes").
        iIntros (?[]) "% [?[??]]". iFrame.
    }
    iIntros "!> % h_list_mapi". idtac...

    tp_pures.
    tp_bind (list_map_poly _ _ _ _).

    iMod (gwp_list_map_poly_idx (g:=gwp_spec)
                  (λ k '(x, ι), zs' !!! k) xιs'
                  _
                  vxιs'
                  (λ k '(x, ι), ι ↪Nₛ (num, 2*den, x; [zs' !!! k]))%I
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

    iMod (gwp_list_max_index (g:=gwp_spec) _ _ _
            (fun (i : val) => ⌜i = LitV (LitInt (List_max_index (mapi (λ (k : nat) '(_, _), zs' !!! k) xιs')))⌝)%I
          with "[] [] rhs")
      as (?) "[rhs %max_rhs]".
    1: done.
    { iIntros (?) "%hh". rewrite hh. done. }
    iApply gwp_list_max_index.
    1: done.
    iIntros "!> %i %Hi".
    (* [i = List_max_index (mapi … xιs)] is the impl-side argmax; it equals
       [List_max_index zs] (the [zs = mapi …] step from the original proof), and
       [zs] has length [N = S N' > 0], so [i < S N'].  Build the result index
       [nat_to_fin Hlt : fin (S N')]; then [inject (nat_to_fin Hlt) =
       #(Z.of_nat i)] matches both the program value [#i] and the spec [⤇]. *)
    destruct Hmax as (Hzs & Hzs' & Hmaxeq).
    (* impl [mapi]-list = [zs] *)
    assert (Hzseq : zs = mapi (λ (k : nat) '(_, _), zs !!! k) xιs).
    { eapply lookup_eq_pointwise.
      { rewrite mapi_length. lia. }
      intros. apply mapi2.
      apply list_lookup_lookup_total_lt. done. }
    (* [i < S N']: [i = List_max_index zs], and [zs] is nonempty of length [N]. *)
    assert (Hlt : (i < S N')%nat).
    { rewrite Hi -Hzseq list_max_index_eq.
      eapply Nat.lt_le_trans; first apply list_Z_max_bound; lia. }
    (* return the range-carrying index; [fin_to_nat (nat_to_fin Hlt) = i]. *)
    replace i with (fin_to_nat (nat_to_fin Hlt)) by apply fin_to_nat_to_fin.
    iApply ("Hpost" $! (nat_to_fin Hlt)).
    (* reconcile the spec side: [#(List_max_index (mapi … xιs'))] = [#i] via
       [list_Z_max zs = list_Z_max zs']. *)
    rewrite max_rhs.
    replace (List_max_index (mapi (λ (k : nat) '(_, _), zs' !!! k) xιs'))
      with (fin_to_nat (nat_to_fin Hlt)).
    { iExact "rhs". }
    rewrite fin_to_nat_to_fin Hi -Hzseq list_max_index_eq Hmaxeq.
    symmetry.
    (* spec [mapi]-list = [zs'] *)
    assert (Hzs'eq : zs' = mapi (λ (k : nat) '(_, _), zs' !!! k) xιs').
    { eapply lookup_eq_pointwise.
      { rewrite mapi_length. lia. }
      intros. apply mapi2'.
      apply list_lookup_lookup_total_lt. done. }
    rewrite -Hzs'eq list_max_index_eq. reflexivity.
  Qed.

End generic.
