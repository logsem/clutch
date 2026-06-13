(** Report-noisy-max (presampling) DP case study, ported from
    [clutch.diffpriv.examples.report_noisy_max] to the GENERIC language.
    "Enable" the Laplace distribution (one signature + one [SampleIn] instance),
    pin the spec-context [fill], and use the generic Laplace tape API
    ([AllocTapeLaplace]/[↪L]/[↪Lₛ]/[wp_laplace_tape]) and the list presampling
    coupling [hoare_couple_laplace_list] (from [report_noisy_max_lemmas]).

    See [report_noisy_max_pointwise] for the pointwise (coupling) variant and the
    rationale for [#[global] Opaque sample_idx]. *)
From iris.base_logic Require Export na_invariants.
From clutch.common Require Import inject.
From clutch.prelude Require Import tactics iris_ext.
From clutch.prob Require Import differential_privacy.
From clutch.gen_diffpriv Require Import adequacy all.
From clutch.gen_diffpriv.lib Require Import laplace laplace_tapes.
From clutch.gen_prob_lang Require Import gwp.list inject families.
From clutch.gen_prob_lang.spec Require Import spec_ra spec_rules.
From clutch.gen_diffpriv.examples Require Import report_noisy_max_lemmas.
From iris.prelude Require Import options.

(** Enable the Laplace distribution for this development. *)
Definition Srnm : Sig := [laplace_family].
#[global] Instance SampleIn_rnm : SampleIn laplace_family Srnm := ltac:(solve_SampleIn).
#[global] Opaque sample_idx.

(** [inject x : expr] resolves to the *unreduced* [@inject A expr _ x] rather
    than the [Val]-headed form; the spec reshape tactics need a [Val] head.  See
    [report_noisy_max_pointwise] for the full explanation. *)
Lemma inject_expr_Val {A} `{!Inject A val} (x : A) :
  (inject x : expr) = Val (inject x).
Proof. reflexivity. Qed.

(** Spec-side [GenWp] instance: the [gwp]-based list ADT ([gwp_list_mapi],
    [gwp_list_cons], [gwp_list_max_index]) is also run on the SPEC program (via
    [(g:=gwp_spec)]).  [gen_prob_lang]'s spec layer does not ship a spec-side
    [GenWp] (only the impl-side [gwp_wpre] in [derived_laws]), so we build it here
    from the generic spec step rules ([step_pure]/[step_alloc]/[step_load]/
    [step_store]) — the exact analogue of [prob_lang.spec.spec_rules.gwp_spec].
    INFRA GAP: ideally this would live in [gen_prob_lang.spec.spec_rules]. *)
Section spec_gwp.
  Context `{!specG_prob_lang Σ, invGS_gen hl Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Srnm)).
  Local Notation spec_update :=
    (@spec_update (lang_markov (gen_lang Srnm)) Σ _ _ _).

  Notation spec_wp :=
    (λ E e Ψ, ∀ K,
        ⤇ fill K e -∗ spec_update E (∃ (v : val), ⤇ fill K v ∗ Ψ v))%I.

  Lemma gwp_mixin_spec :
    GenWpMixin (S := Srnm) false spec_wp (λ l dq v, l ↦ₛ{dq} v)%I.
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

Section rnm.
  Context `{!diffprivGS Srnm Σ}.
  Local Notation fill := (@ectx_language.fill (gen_ectx_lang Srnm)).
  Local Notation lidx := (@sample_idx laplace_family Srnm _).
  (* the generic tape value standing in for [prob_lang]'s [Tape_Laplace] record *)
  Local Notation LapT num den mean zs :=
    (sample_idx (D := laplace_family), sf_param_to_val laplace_family (num, den, mean)%Z,
      ((λ z : Z, LitV (LitInt z)) <$> zs)).

  #[local] Open Scope R.

  Definition list_map' (v:val) :=
    (list_mapi (λ: <>, v))%E.

  Definition report_noisy_max_presampling (num den : Z) : val :=
    (* ↯ (num/den) ∗ evalQ is 1-sensitive ∗ N ∈ ℕ \ {0} ∗ 0 < num/2den ∗ dDB db db' <= 1 *)
    λ:"evalQ" "N" "d",
      let: "xs" := list_init "N" (λ:"i", "evalQ" "i" "d") in
      let: "xs_tapes" := list_map (λ:"x", ("x", AllocTapeLaplace #num #(2*den) "x")) "xs" in
      let: "noisy_xs" := list_map' (λ: "x_ι", Laplace #num #(2*den) (Fst "x_ι") (Snd "x_ι")) "xs_tapes" in
      list_max_index "noisy_xs".

  Lemma rnm_init (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (∀ i : Z, ⊢ hoare_sensitive Srnm (evalQ #i) 1 dDB dZ) →
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
Proof. (* TODO(port): proof OK in isolation, but in [gen] this lemmas .vo blows up memory (>16GB, OOM): with [Opaque sample_idx] (required so [LapT]/[ghost_map_elem_valid_2] unify) the big_sepL2 tape reshapes carry huge unreduced [sample_idx]-headed terms. Needs proof-engineering to shrink terms (or splitting). *) Admitted.

Lemma wp_alloc_tapes_laplace :
  (forall (num den : Z) K xs xs' vxs vxs',
      is_list xs vxs → is_list xs' vxs' → length xs = length xs' →
      Forall2 (λ x x' : Z, dZ x x' <= 1) xs xs' →
      {{{ ⤇ fill K ((list_map (λ: "x", ("x", AllocTapeLaplace #num #(2 * den) "x")))%V vxs') }}}
        (list_map (λ: "x", ("x", AllocTapeLaplace #num #(2 * den) "x")))%V vxs
        {{{ vxιs, RET vxιs ; ∃ vxιs' xιs xιs',
                ⌜is_list xιs vxιs⌝ ∗ ⌜length xιs = length xs⌝ ∗
                ⌜is_list xιs' vxιs'⌝ ∗ ⌜length xιs' = length xs'⌝ ∗
                ⌜ NoDup xιs.*2 ⌝ ∗ ⌜ NoDup xιs'.*2 ⌝ ∗
                ⤇ fill K vxιs' ∗
                [∗ list] '(x, ι) ; '(x', ι') ∈ xιs ; xιs',
              ι ↪L (num, 2*den, x; []) ∗ ι' ↪Lₛ (num, 2*den, x'; []) ∗
              ⌜dZ x x' <= 1⌝
  }}}).
Proof. (* TODO(port): same [gen] memory blowup as [rwp_list_map] — this lemma ALONE peaks ~8GB in [gen] (vs cheap in prob_lang): the [big_sepL2_const_sepL_l/r]/[ghost_map_elem_valid_2 (LapT ...)] reshapes over opaque-[sample_idx] tape values explode. *) Admitted.

  Lemma rnm_pres_diffpriv num den (evalQ : val) DB (dDB : Distance DB) (N : nat) K :
    (0 < IZR num / IZR (2 * den)) →
    (∀ i : Z, ⊢ hoare_sensitive Srnm (evalQ #i) 1 dDB dZ) →
    ∀ db db', dDB db db' <= 1 →
                {{{ ↯m (IZR num / IZR den) ∗
                    ⤇ fill K (report_noisy_max_presampling num den evalQ #N (of_val (inject db'))) }}}
                  report_noisy_max_presampling num den evalQ #N (of_val (inject db))
                  {{{ v, RET v ; ∃ (v' : val), ⤇ fill K v' ∗ ⌜ v = v' ⌝  }}}.
  Proof. (* TODO(port): reaches the [wp_apply (wp_laplace_tape ...)] / [tp_sample_tape] gwp workers; in [gen] the [Laplace] surface ([Sample sample_idx (Pair ..)]) does not match [wp_laplace_tape] after [wp_pures] reduces the [Pair] (line ~347: "No applicable tactic"). Needs gen-specific reshaping (cf. [report_noisy_max_pointwise] uses [tp_normalise]). Also depends on the two admitted heavy lemmas above. *) Admitted.

End rnm.

Lemma rnm_diffpriv_presampling num den (evalQ : val) DB (dDB : Distance DB) (N : nat) :
  (0 < IZR num / IZR (2 * den))%R →
  (0 <= IZR num / IZR den)%R →
  (∀ `{!diffprivGS Srnm Σ}, ∀ i : Z, ⊢ hoare_sensitive Srnm (evalQ #i) 1 dDB dZ) → ∀ σ,
      diffpriv_pure
        dDB
        (λ db, lim_exec (δ := lang_markov (gen_lang Srnm)) ((report_noisy_max_presampling num den evalQ #N (inject db)), σ))
        (IZR num / IZR den).
Proof. (* TODO(port): depends on [rnm_pres_diffpriv]. *) Admitted.
