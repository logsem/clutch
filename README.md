# Clutch
A higher-order probabilistic relational separation logic with support for asynchronous probabilistic couplings. 

## Building the development

The project is known to compile with
- [Coq](https://coq.inria.fr/) 8.16.1
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.8.0
- [Coquelicot](https://gitlab.inria.fr/coquelicot/coquelicot/) 3.2.0
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) 4.0.0
- [Autosubst](https://github.com/coq-community/autosubst) 1

The recommended way to install the dependencies is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create clutch 4.14.0
opam switch link clutch .
```
3. Add the Coq and Iris `opam` repositories.
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update
```
4. Install the right version of the dependencies as specified in the `iris-probability.opam` file.
```
opam install . --deps-only
```

You should now be able build the development by using `make -j N` where `N` is the number of cores available on your machine.

## Reference from the paper to the code

| §   | Kind       | Item                                                                                 | Coq file                       | Name                                      | Note |
|-----|------------|--------------------------------------------------------------------------------------|--------------------------------|-------------------------------------------|------|
| I   | Example    | $\mathit{eager}$                                                                     | [examples/lazy_eager_coin]     | `eager`                                   |      |
|     | Example    | $\mathit{lazy}$                                                                      |                                | `lazy`                                    |      |
| II  | Theorem    | 1 (Soundness)                                                                        | [typing/soundness]             | `refines_sound`                           |      |
|     | Rule       | $\text{\scriptsize REL-COUPLE-FLIPS}$                                                | [logrel/rel_rules]             | `refines_couple_flips`                    |      |
|     | Rule       | $\text{\scriptsize REL-ALLOC-TAPE-L}$                                                |                                | `refines_alloctape_l`                     |      |
|     | Rule       | $\text{\scriptsize REL-COUPLE-TAPE-L}$                                               |                                | `refines_couple_tape_flip`                |      |
|     | Rule       | $\text{\scriptsize REL-FLIP-TAPE-L}$                                                 |                                | `refines_flip_l`                          |      |
|     | Rule       | $\text{\scriptsize REL-FLIP-ERASE-R}$                                                |                                | `refines_couple_flips_r`                  |      |
|     | Example    | $\mathit{lazy'}$                                                                     | [examples/lazy_eager_coin]     | `lazy_with_tape`                          |      |
|     | Theorem    | $\vDash \mathit{lazy} \precsim \mathit{eager} : \text{unit} \rightarrow \text{bool}$ |                                | `lazy_eager_refinement`                   |      |
| III | Definition | 2 (Sub-distribution)                                                                 | [prob/distribution]            | `distr`                                   |      |
|     | Lemma      | 4 (Probability Monad)                                                                |                                | `dret_id_right`, etc.                     |      |
|     | Definition | $\mathbf{F}_{\mu{},\text{ref}}^\text{flip}$                                          | [prob_lang/lang]               | `expr`, `val`, `state`, `cfg`             |      |
|     | Definition | types *τ*                                                                            | [typing/types]                 | `type`                                    |      |
|     | Definition | CBV step relation ⟶                                                                  | [program_logic/ectx_language]  | `prim_step` (by lifting `head_step`)      |      |
|     | Definition | CBV step relation ⟶                                                                  | [program_logic/ectx_language]  | `prim_step` (by lifting `head_step`)      |      |
|     | Aux. def.  | CBV step relation ⟶                                                                  | [program_logic/ectx_language]  | `state_step`                              |      |
|     |            |                                                                                      | [prob_lang/lang]               | `head_step`                               |      |
|     | Aux. def.  | evaluation context                                                                   | [program_logic/ectxi_language] | `ectx = list ectx_item`                   |      |
|     | Aux. def.  | evaluation ctx. item                                                                 | [prob_lang/lang]               | `ectx_item`                               |      |
|     | Definition | $\text{exec}_n(e,σ)$                                                                 | [program_logic/exec]           | `exec`                                    |      |
|     | Definition | $\text{exec}_\Downarrow{}(ρ)$                                                        | [program_logic/exec]           | `lim_exec_val`                            |      |
|     | Rule       | t-tape                                                                               | [typing/types]                 | `TAllocTape` (part of `typed`)            |      |
|     | Rule       | t-flip                                                                               | [typing/types]                 | `TFlip`, `TFlipU` (part of `typed`)       |      |
|     | Definition | program context                                                                      | [typing/contextual_refinement] | `ctx_item`                                |      |
|     | Definition | typed prog. context                                                                  | [typing/contextual_refinement] | `typed_ctx_item`                          |      |
|     | Definition | contextual refinement                                                                | [typing/contextual_refinement] | `ctx_refines`                             |      |
|     | Definition | ctx'al equivalence                                                                   | [typing/contextual_refinement] | `ctx_equiv`                               |      |
| IV  | Definition | iProp                                                                                | imported from [Iris upstream]  | `iProp`                                   |      |
|     | Definition | $\ell \mapsto v$                                                                     | [prob_lang/primitive_laws]     | `ghost_map_elem prelocGS_heap`            |      |
|     | Definition | $\iota \hookrightarrow{} \vec{b}$                                                    | [prob_lang/primitive_laws]     | `ghost_map_elem prelocGS_tapes`           |      |
|     | Definition | $\ell \mapsto_{\mathsf{s}} v$                                                        | [prob_lang/spec_ra]            | `ghost_map_elem specGS_heap`              |      |
|     | Definition | $\iota \hookrightarrow_{\mathsf{s}} \vec{b}$                                         | [prob_lang/spec_ra]            | `ghost_map_elem specGS_tapes`             |      |
|     | Definition | Value interperation $⟦ τ ⟧_Δ(-,-)$                                 | [typing/interp]                | `interp`                                  |      |
|     | Definition | Value interperation $⟦ τ ⟧_Δ(-,-)$                                 | [logrel/model]                 | `lrel_bool`, `lrel_ref`, `lrel_tape`, etc |      |
|     | Definition | $e₁ \overset{\mathrm{pure}}{\rightsquigarrow} e₂$                                    | [program_logic/language]       | `PureExec`                                |      |
|     | Rule       | rel-pure-l                                                                           | [logrel/rel_rules]             | `refines_pure_l`                          |      |
|     | Rule       | rel-pure-r                                                                           | [logrel/rel_rules]             | `refines_pure_r`                          |      |
|     | Rule       | rel-alloc-l                                                                          | [logrel/rel_rules]             | `refines_alloc_l`                         |      |
|     | Rule       | rel-alloc-r                                                                          | [logrel/rel_rules]             | `refines_alloc_r`                         |      |
|     | Rule       | rel-load-l                                                                           | [logrel/rel_rules]             | `refines_load_l`                          |      |
|     | Rule       | rel-load-r                                                                           | [logrel/rel_rules]             | `refines_load_r`                          |      |
|     | Rule       | rel-store-l                                                                          | [logrel/rel_rules]             | `refines_store_l`                         |      |
|     | Rule       | rel-store-r                                                                          | [logrel/rel_rules]             | `refines_store_r`                         |      |
|     | Rule       | rel-pack                                                                             | [logrel/compatibility]         | `refines_pack`                            | (1)  |
|     | Rule       | rel-return                                                                           | [logrel/model]                 | `refines_ret`                             |      |
|     | Rule       | rel-bind                                                                             | [logrel/model]                 | `refines_bind`                            |      |
|     | Rule       | rel-flip-l                                                                           | [logrel/rel_rules]             | `refines_flipU_l`                         |      |
|     | Rule       | rel-alloc-tape-l                                                                     | [logrel/rel_rules]             | `refines_alloctape_l`                     |      |
|     | Rule       | rel-alloc-tape-r                                                                     | [logrel/rel_rules]             | `refines_alloctape_r`                     |      |
|     | Rule       | rel-flip-tape-l                                                                      | [logrel/rel_rules]             | `refines_flip_l`                          |      |
|     | Rule       | rel-flip-tape-r                                                                      | [logrel/rel_rules]             | `refines_flip_r`                          |      |
|     | Rule       | rel-flip-tape-empty-l                                                                | [logrel/rel_rules]             | `refines_flip_empty_l`                    |      |
|     | Rule       | rel-flip-tape-empty-r                                                                | [logrel/rel_rules]             | `refines_flip_empty_r`                    |      |
|     | Rule       | rel-couple-flips                                                                     | [logrel/rel_rules]             | `refines_couple_flips`                    |      |
|   | Rule | rel-couple-tape-l | [logrel/rel_rules] |                        |   |
|   | Rule | rel-couple-tape-r | [logrel/rel_rules] |                        |   |
|   | Rule | rel-couple-tapes  | [logrel/rel_rules] | `refines_couple_tapes` |   |
|   | Rule       | rel-na-inv-alloc              | [logrel/model]      | `refines_na_alloc`       |   |
|   | Rule       | rel-na-inv-open                                                                | [logrel/model]      | `refines_na_inv`         |   |
|   | Rule       | rel-na-inv-close                                                               | [logrel/model]      | `refines_na_close`       |   |
|   | Definition | $Δ \vDash e₁ \precsim e₂ : τ$                                                  | [logrel/model]      | `refines_def`            |   |
|   | Definition | $\text{spec}(e)$                                                               | [prob_lang/spec_ra] | `⤇ e` (`spec_prog_frag`) |   |
|   | Lemma      | $ι : \text{tape} ⊢ \text{flip} () ≅_{\text{ctx}} \text{flip}(ι) : \text{bool}$ | [examples/erasure]  | `flip_erasure_ctx`       |   |

(2) In the code, we often use the shorthand `refines_right K e` to refer to the combined `spec_ctx ∗ ⤇ K[e]`.

(1) `pack` for existential types has no operational meaning, and thus `pack e` simply stands for `e`. The requirement for `R` to be persistent in the `rel-pack` rule is reflected in the code by the fact that logical relations are defined as persistent predicates (see [logrel/model]).


[examples/lazy_eager_coin]: theories/examples/lazy_eager_coin.v
[logrel/rel_rules]: theories/logrel/rel_rules.v
[prob/distribution]: theories/prob/distribution.v
[prob_lang/lang]: theories/prob_lang/lang.v
[program_logic/ectx_language]: theories/program_logic/ectx_language.v
[program_logic/ectxi_language]: theories/program_logic/ectxi_language.v
[program_logic/exec]: theories/program_logic/exec.v
[program_logic/language]: theories/program_logic/language.v
[typing/contextual_refinement]: theories/typing/contextual_refinement.v
[typing/soundness]: theories/typing/soundness.v
[typing/types]: theories/typing/types.v
[prob_lang/primitive_laws]: theories/prob_lang/primitive_laws.v
[prob_lang/spec_ra]: theories/prob_lang/spec_ra.v
[logrel/model]: theories/logrel/model.v

[iris upstream]: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/iprop.v
