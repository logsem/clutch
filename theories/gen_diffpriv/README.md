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
  semantics, metatheory, spec-side ghost state, the distribution-family signature, injections,
  notation, tactics, and a generic weakest-pre (`gwp/`) for the spec layer.
- **`theories/gen_diffpriv/`** — the *DP logic*. The `Λ`-generic WP core
  (`clutch.diffpriv.{weakestpre,lifting,ectx_lifting}`) is **reused unchanged**, instantiated at
  `gen_lang S`; only the genuinely language-specific files are re-done here
  (`primitive_laws`, `coupling_rules`, `adequacy`), plus the relational layer, the iDP
  definitions, the distribution/mechanism libraries (`lib/`), and the case studies (`examples/`).

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
  group privacy, via the meta-level `diffpriv_metric_*` equivalence in
  `clutch.prob.differential_privacy` (both directions proved). Complementary, not redundant.
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
- `report_noisy_max{,_exp}.v`, `expmech` client, `randomized_response.v`, `adaptive_count.v`,
  `sum_queries.v`, `composition_demo.v` (capstone multi-release).
- **Faithful ports** that match the original development exactly: `SVT_experiments.v`,
  `rnm_inspired_problems.v`, `pointwise_eq_*.v` — these were `Abort`ed / `Admitted` upstream
  (speculative or open research) and are preserved as such; they contribute **no new admits/axioms**
  (an `Abort`ed lemma adds nothing to the context). `pointwise_*` is stale, left as-is.

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
