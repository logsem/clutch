# `gen_prob_lang` / `gen_diffpriv` — a signature-generic probabilistic language and its DP logic

> Branch `gen-prob-lang`. This README is the entry point for the whole branch; it
> describes all the work on it, not the latest commit. Reviewer's-eye summary first,
> file map and rationale below.

## Why

In Clutch's `prob_lang`, every sampling primitive is hard-wired. Adding the discrete
Gaussian on `gaussian-dp` meant **cloning the entire Laplace stack (~1000 lines)** across
`lang`/`erasure`/`metatheory`/`spec_ra`/`primitive_laws`/`coupling_rules`/… Every new
`Z`-valued distribution cost the same again.

This branch rebuilds the language and the differential-privacy logic to be **parametric over
a signature `S : Sig` of sampling distribution families**. Adding a distribution now costs
**one `SampleFamily` instance** (whose only mathematical obligation is `mass = 1`) plus its
bespoke coupling rules — not a re-clone. The sole client is the DP logic; other logics
(`clutch`/`eris`/`tachis`) only sample uniform and stay on `prob_lang`.

## The two trees

- **`theories/gen_prob_lang/`** — the `S`-parametric *language* (no DP content). Operational
  semantics (`lang`/`metatheory`/`erasure`), spec-side ghost state (`spec/`), the distribution-family
  signature, injections (`inject`, incl. `Inject (fin M)`), notation, tactics, the `mkZNoise`/`mkZNoise4`
  noise builders (`znoise.v`) and the N-weight bin sampler (`categorical.v`), a generic weakest-pre
  with a full **generic list ADT** (`gwp/list.v`, the largest file here — underpins every list-valued
  case study; `list_init` is OCaml-faithful — forward, 0-indexed — and the combinators have
  polymorphic, syntactically-typeable variants), and a logical-relation **type system**
  (`typing/{types,contextual_refinement,list_typed}.v`).
- **`theories/gen_diffpriv/`** — the *DP logic*. The `Λ`-generic WP core
  (`clutch.diffpriv.{weakestpre,lifting,ectx_lifting}`) is **reused unchanged**, instantiated at
  `gen_lang S`; only the genuinely language-specific files are re-done here
  (`primitive_laws`, `coupling_rules`, `adequacy`), plus the **binary logical relation** stack
  (see below), the iDP definitions (`diffpriv_rules.v`), the distribution/mechanism libraries
  (`lib/`), and the case studies (`examples/`). Foundational *math* lives in `theories/prob/`
  (`differential_privacy.v`, `exponential.v`, `expmech{,_dp}.v`, `trunc_laplace.v`).

## Core abstraction (`gen_prob_lang/lang.v`)

```coq
Record SampleFamily := { sf_param sf_out : Type; … ;
  sf_sample : sf_param → distr sf_out;  sf_mass : ∀ p, SeriesC (sf_sample p) = 1; … }.
Definition Sig := list SampleFamily.
Class SampleIn (D : SampleFamily) (S : Sig) := { sample_idx : nat; sample_idx_S : S !! sample_idx = Some D }.
```

- **Positional identity** (`SampleIn` by `reflexivity`); resolution selects by the *named* family.
- **Monomorphic operational tape** (`expr`/`val`/`state` are `S`-independent); the typed,
  support-carrying view `l ↪[D] (p; xs)` lives only in the logic, faithful via `sf_inj` injectivity.
- Generic dispatch `sig_sample S i pv`; every per-family rule rests on the agreement lemma `sig_sample_at`.

### Working over a signature — no canonical-structure boilerplate

A development that reasons over a signature needs only the **typeclass context**; the
language is recovered from it, so **no canonical-structure declarations are required**:

```coq
Context {Sg : Sig} `{!SampleIn laplace_family Sg} `{!diffprivGS Sg Σ}.   (* unary WP    *)
Context {Sg : Sig} `{!diffprivRGS Sg Σ}.                                 (* relational  *)
```

`Λ = gen_lang Sg` resolves from the in-context `diffprivGS`/`diffprivRGS`/`GenWp Sg`
instance — *not* from the signature-independent `expr`/`val`, which is why `gen_lang`
cannot be a global canonical structure the way `prob_lang` is. The `PureExec`/`Atomic`
instances are signature-generic (`∀ S, … (gen_lang S) …`) and `reshape_expr` is purely
syntactic, so the WP/relational tactics work as-is. Add `Local Notation fill :=
(@ectx_language.fill (gen_ectx_lang Sg))` **only if you mention `fill` by name**, and a
plain `Let gen_markov_X := lang_markov (gen_lang Sg)` only if you name a `spec_updateGS`
markov.

The `gen_ectxi_lang`/`gen_ectx_lang`/`gen_lang`(`/lang_markov`) canonical chain is needed
*only* in the foundational, write-once language-level files whose sections have **no** GS
class to pin `Sg` (`gen_prob_lang/{class_instances,erasure,metatheory,wp_tactics,spec/*}`
and the `gen_weakestpre` mixin), where generic `ectxLanguage`/`markov` lemmas
(`ectx_language_atomic`, `pexec`/`exec`) must unify `LanguageOfEctx ?Λ`/`mstate ?δ` back
to `gen_lang Sg`. Everywhere else the chain is omitted.

## Binary logical relation & soundness

The full binary logical-relation / contextual-refinement stack is ported and `gen_lang S`-generic:
`model.v`, `interp.v` (value/expr interpretation), `fundamental.v` (the fundamental theorem),
`compatibility.v`, `app_rel_rules.v`, `rel_tactics.v`, `soundness.v`, `adequacy_rel.v` — delivering
the headline soundness theorem (`refines_sound` / contextual refinement `ctx_refines`).

The generalization payoff is **`sample.v` (`refines_sample`)**: *sufficient syntactic conditions*
under which sampling from **any** family is a sound extension of the logical relation — the param
type is an `EqType`, `sf_param_of_val` is total, and `sf_inj` lands in the output type's
interpretation `⟦τo⟧`. Proved once, instantiated at uniform / Laplace / coin. (This is the relational
analogue of "add a distribution = one `SampleFamily`": adding a *typed* primitive is one
side-condition discharge, not a new fundamental-theorem case.)

The **syntactic** type system extends in lock-step: each family carries a `SampleTyping D τp τo`
instance (param decodes from `τp`, output injects into `τo`), and `typing/types.v`'s
`Sample_typed` / `Sample_tape_typed` / `AllocSampleTape_typed` rules + the correspondingly extended
fundamental theorem make any use of `Sample`/`AllocSampleTape` well-typed — and self-related — from
that one instance (the syntactic twin of `refines_sample`; family instances in `families.v`, the
contextual-typing side in `contextual_refinement.v`, a canary in `sample_typing_canary.v`, a worked
case study in `sample_typing_case_study.v`). The same move types the list ADT — polymorphic
`list_map_poly` / `list_init_poly` / `list_fold_poly` and the (monomorphic) `list_max_index`
(`typing/list_typed.v`) — so **all three list congruences come *for free* from the fundamental
theorem**: `examples/gwp_list_rel.v` derives `refines_list_map` / `refines_list_init` /
`refines_list_max_index` from `fundamental_val` through the bridge `interp (TList τ) ≡ lrel_list`,
retiring the hand inductions.

## Internal-DP notions (`gen_diffpriv/diffpriv_rules.v`)

A central rationale block in that file is the source of truth; in brief:

- **`hoare_sensitive f c d_in d_out`** — `f` is `c`-Lipschitz from metric `d_in` to `d_out`.
- **`hoare_diffpriv_metric f ε δ dA B`** — *group-bound*, ∀-distance: at distance `c`, consumes
  `↯m (c·ε)` and `↯ (δ · grp ε c)` where `grp ε c = (e^{cε}−1)/(e^ε−1)` is exact group-privacy
  amplification. The **composition-friendly default** (`grp_comp`/`grp_mono_eps` drive the
  composition laws).
- **`hoare_diffpriv_classic_at f ε δ r dA B`** — *textbook* `(ε,δ)`-DP at adjacency radius `r`,
  with `δ` a fixed/tight value (no `grp`). `hoare_diffpriv_classic := classic_at … 1`. The home
  for **bounded-support / discrete mechanisms** whose optimal `δ` is a tail mass that saturates,
  and for fixed-budget statements over databases within a distance `r`.
- **Bridge**: `metric ⇒ classic` always (instantiate `c = 1`, `grp ε 1 = 1`); the converse is
  group privacy. The justifying **meta-level theory** is in `clutch.prob.differential_privacy`:
  the textbook DP predicates are stated over an adjacency **relation** (`diffpriv_pure_rel` /
  `diffpriv_approx_rel`, not a unit ball), the group-privacy induction `diffpriv_approx_rel_group`
  along an `adj_path`, the `grp` algebra (`grp_comp`/`grp_rec`/`grp_succ`/`grp_mono_eps`/`grp_mono_c`),
  the metric definition `diffpriv_metric`, the equivalence `diffpriv_metric_of_approx_rel` (**both
  directions proved**), and the all-distances sequential composition `diffpriv_metric_seq_comp_full`.
- This replaces a **deleted legacy notion**: a *linear* `(ε,δ)` definition (`hoare_diffpriv`/`wp_diffpriv`
  + a ~13-lemma composition cluster) was removed in the #25 consolidation — its `c·δ` profile is
  unsound for `δ > 0`, whereas `grp_mono_eps` shows the group-bound metric definition genuinely composes.
- **Composition laws** (the `_at`, `wp_bind`-friendly forms): `diffpriv_metric_sensitive_comp_at`
  (sens∘dp) genuinely `iApply`s; sequential / postprocessing compose as documented inline patterns
  (the reified forms β-reduce away under `wp_pures`, so they cannot be `iApply`ed — see the file's
  comments).

## Distribution families & mechanisms (`gen_diffpriv/lib/`)

| Family | Files | Notes |
|---|---|---|
| uniform | `uniform.v` | integer interface over the `fin` bijection coupling |
| coin / RR | `coin.v`, `randomized_response.v` | 0-cost exact coin coupling |
| one-sided exponential | `exponential.v`, `exponential_tapes.v` | for exp-mechanism / exp-RNM |
| (discrete) Laplace | `laplace.v`, `laplace_tapes.v`, `laplace_choice.v` | |
| truncated Laplace | `lib/trunc_laplace.v` (+ math in `prob/trunc_laplace.v`) | see below |
| exponential mechanism | `expmech.v` | ε-DP |

**Report-noisy-max** (`examples/report_noisy_max*.v`) is factored into **one noise-generic
library** (`report_noisy_max_generic.v`, over `mkZNoise sample mass`); Laplace and exponential
are thin instantiations. Headlines are stated as **`hoare_diffpriv_classic_at`** with a
range-carrying codomain **`fin (Nat.max 1 N)`** — so the selected index is exposed *structurally*
(carrying `< N`), feedable directly into a query's `hoare_sensitive` hypothesis. (`classic_at`,
not `metric`: the noise coupling presamples at an a-priori integer gap, which a real-valued
`metric` distance cannot scale to. `Nat.max 1 N` keeps the codomain inhabited at `N = 0`, so no
`0 < N` side-condition.)

Both noise instances also ship an **idiomatic, one-pass direct-sampling** variant
(`report_noisy_max_idiomatic.v`'s `rnm_direct1`: a deterministic `list_init` of scores fed through a
direct-`Sample` map — **no presampling tapes**) carrying the *same* DP guarantee
(`rnm_diffpriv_idiomatic` for Laplace, `rnm_exp_diffpriv_idiomatic` for exp). It is proved
`lim_exec`-equal to the presampling RNM through the binary logical relation — *both* refinement
directions, equality by antisymmetry (no unary-termination side condition) — so the existing
headline transports verbatim. The engine is a per-element **tape-erasure** law (`tape_erasure.v`,
with the supporting couplings in `coupling_rules.v`: a freshly-allocated tape, read exactly once, is
indistinguishable from a direct draw) composed through the free list congruences above; the
OCaml-faithful forward `list_init` is what makes the score-building and sampling orders line up.

**Truncated Laplace** decouples sensitivity `Δ` from truncation half-width `A`. The fundamental
result is a **tight all-shifts coupling** with optimal bad-set tail-mass `δ = Pr[Z > A−Δ]`
(`DPcoupl_trunc_lap_tight`); the looser group form is a corollary. Exposed as a `metric` instance
over plain `dZ` and a `classic` instance with the tight `δ`. Clean closed forms for the important
`Δ` cases. (`prob/trunc_laplace.v` is 0-admit.)

## Case studies (`gen_diffpriv/examples/`)

- **`select_then_measure.v`** — flagship multi-noise showcase: exp-RNM **selection** ∘
  truncated-Laplace **measurement**, over a 2-family signature. Stated as
  `hoare_diffpriv_classic_at … (fin (Nat.max 1 N) * Z)`; a single `hoare_sensitive` hypothesis
  drives both stages (the selected index, exposed as `fin`, is fed into it for the measurement).
- **`sparse_vector_technique.v`** — the live above-threshold / sparse-vector mechanism: a stateful
  budget odometer (`SVT_online_diffpriv` returns a query-answering closure + a budget invariant),
  with the batch headlines `SVT_stream_diffpriv` / `SVT_list_diffpriv` stated as
  `hoare_diffpriv_classic_at` at radius `C`. (The live SVT — distinct from the speculative,
  `Abort`ed `SVT_experiments.v` below.)
- `report_noisy_max{,_exp}.v`, `expmech` client, `randomized_response.v`, `adaptive_count.v`,
  `sum_queries.v`, `list.v` / `map.v`, and `exact_cache.v` — a live `δ > 0` study whose bound was
  **sharpened** from the (deleted) unsound linear form to the correct group bound during the #25
  cleanup; `composition_demo.v` (capstone multi-release).
- **Faithful ports** that match the original development exactly: `SVT_experiments.v`,
  `rnm_inspired_problems.v`, and the `pointwise_eq_*.v` family — these were `Abort`ed / `Admitted`
  upstream (speculative or open research) and are preserved as such; they contribute **no new
  admits/axioms** (an `Abort`ed lemma adds nothing to the context). The `pointwise_*` files are
  stale, left as-is.

## Tooling & build

- **Convenience tactics** `couple_X` / `couple_X_apply` (bundled bind+apply with smart credit
  routing) share a core in `proofmode.v`; one per distribution family.
- **Build**: a `dune-workspace` at the repo root is required (so `dune build` tolerates `/workspace`'s
  duplicate package). Build a single target with `dune build theories/gen_diffpriv/<file>.vo`; the
  whole branch with `find theories/gen_prob_lang theories/gen_diffpriv -name '*.v' | sed 's/\.v$/.vo/' | xargs dune build`.

## Status

Green; **no new admits or axioms** (only the faithful upstream `Abort`s noted above).
Deferred (out of scope for this branch):

- **`gen_eris` / `gen_tachis`** variants (the other logics gain nothing from the generalization).
- **Crypto port** (`from_approxis`) — needs a `gen_approxis`-style *relational* layer (a `rand`
  surface + `refines_couple_*` rules + `tychk`); foundations are ready, the relational surface is not.
- The **sequential/postprocessing `iApply` ceiling** — a reduction-control limitation; the
  inline-pattern workaround is in place and validated.
