## Reference from the paper to the code

| §   | Kind       | Item                                                                                 | Coq file                             | Name                                      | Note |
|-----|------------|--------------------------------------------------------------------------------------|--------------------------------------|-------------------------------------------|------|
| 1   | Example    | $\mathit{eager}$                                                                     | [examples/lazy_eager_coin]           | `eager`                                   |      |
|     | Example    | $\mathit{lazy}$                                                                      |                                      | `lazy`                                    |      |
| 2   | Theorem    | 1 (Soundness)                                                                        | [typing/soundness]                   | `refines_sound`                           |      |
|     | Rule       | $\text{\scriptsize REL-COUPLE-RANDS}$                                                | [rel_logic/rel_rules]                | `refines_couple_rands_lr`                 |      |
|     | Rule       | $\text{\scriptsize REL-ALLOC-TAPE-L}$                                                |                                      | `refines_alloctape_l`                     |      |
|     | Rule       | $\text{\scriptsize REL-COUPLE-TAPE-L}$                                               |                                      | `refines_couple_tape_rand`                |      |
|     | Rule       | $\text{\scriptsize REL-RAND-TAPE-L}$                                                 |                                      | `refines_rand_l`                          |      |
|     | Rule       | $\text{\scriptsize REL-RAND-ERASE-R}$                                                |                                      | `refines_couple_rands_r`                  |      |
|     | Example    | $\mathit{lazy'}$                                                                     | [examples/lazy_eager_coin]           | `lazy_with_tape`                          |      |
|     | Theorem    | $\vDash \mathit{lazy} \precsim \mathit{eager} : \text{unit} \rightarrow \text{bool}$ |                                      | `lazy_eager_refinement`                   |      |
| 3   | Definition | 2 (Sub-distribution)                                                                 | [prob/distribution]                  | `distr`                                   |      |
|     | Lemma      | 4 (Probability Monad)                                                                |                                      | `dret_id_right`, etc.                     |      |
|     | Definition | $\mathbf{F}_{\mu{},\text{ref}}^\text{flip}$                                          | [prob_lang/lang]                     | `expr`, `val`, `state`, `cfg`             |      |
|     | Definition | types *τ*                                                                            | [typing/types]                       | `type`                                    |      |
|     | Definition | $\text{step}$                                                                        | [program_logic/ectx_language]        | `prim_step` (by lifting `head_step`)      |      |
|     | Aux. def.  | stepping relation for top redices                                                    | [prob_lang/lang]                     | `head_step`                               |      |
|     | Aux. def.  | evaluation context                                                                   | [program_logic/ectxi_language]       | `ectx = list ectx_item`                   |      |
|     | Aux. def.  | evaluation ctx. item                                                                 | [prob_lang/lang]                     | `ectx_item`                               |      |
|     | Definition | $\text{exec}_n(e,σ)$                                                                 | [program_logic/exec]                 | `exec`                                    |      |
|     | Definition | $\text{exec}(ρ)$                                                                     | [program_logic/exec]                 | `lim_exec_val ρ`                          |      |
|     | Definition | $\text{exec}_\Downarrow{}(ρ)$                                                        | [program_logic/exec]                 | `SeriesC(lim_exec_val ρ)`                 |      |
|     | Rule       | $\text{\scriptsize T-TAPE}$                                                          | [typing/types]                       | `TAllocTape` (part of `typed`)            |      |
|     | Rule       | $\text{\scriptsize T-RAND}$                                                          | [typing/types]                       | `TRand`, `TRandU` (part of `typed`)       |      |
|     | Definition | program context                                                                      | [typing/contextual_refinement]       | `ctx_item`                                |      |
|     | Definition | typed prog. context                                                                  | [typing/contextual_refinement]       | `typed_ctx_item`                          |      |
|     | Definition | contextual refinement                                                                | [typing/contextual_refinement_alt]   | `ctx_refines_alt`                         | (1)  |
|     | Definition | contextual refinement                                                                | [typing/contextual_refinement]       | `ctx_refines`                             |      |
|     | Definition | contextual equivalence                                                               | [typing/contextual_refinement]       | `ctx_equiv`                               |      |
| 4   | Definition | iProp                                                                                | imported from [Iris upstream]        | `iProp`                                   |      |
|     | Definition | $\ell \mapsto v$                                                                     | [rel_logic/primitive_laws]           | `ghost_map_elem clutchGS_heap`            |      |
|     | Definition | $\iota \hookrightarrow{} \vec{b}$                                                    | [rel_logic/primitive_laws]           | `ghost_map_elem clutchGS_tapes`           |      |
|     | Definition | $\ell \mapsto_{\mathsf{s}} v$                                                        | [rel_logic/spec_ra]                  | `ghost_map_elem specGS_heap`              |      |
|     | Definition | $\iota \hookrightarrow_{\mathsf{s}} \vec{b}$                                         | [rel_logic/spec_ra]                  | `ghost_map_elem specGS_tapes`             |      |
|     | Definition | Value interperation $⟦ τ ⟧_Δ(-,-)$                                                   | [typing/interp]                      | `interp`                                  |      |
|     | Definition | Value interperation $⟦ τ ⟧_Δ(-,-)$                                                   | [rel_logic/model]                    | `lrel_bool`, `lrel_ref`, `lrel_tape`, etc |      |
|     | Definition | $e₁ \overset{\mathrm{pure}}{\rightsquigarrow} e₂$                                    | [program_logic/language]             | `PureExec`                                |      |
|     | Rule       | $\text{\scriptsize REL-PURE-L}$                                                      | [rel_logic/rel_rules]                | `refines_pure_l`                          |      |
|     | Rule       | $\text{\scriptsize REL-PURE-R}$                                                      | [rel_logic/rel_rules]                | `refines_pure_r`                          |      |
|     | Rule       | $\text{\scriptsize REL-ALLOC-L}$                                                     | [rel_logic/rel_rules]                | `refines_alloc_l`                         |      |
|     | Rule       | $\text{\scriptsize REL-ALLOC-R}$                                                     | [rel_logic/rel_rules]                | `refines_alloc_r`                         |      |
|     | Rule       | $\text{\scriptsize REL-LOAD-L}$                                                      | [rel_logic/rel_rules]                | `refines_load_l`                          |      |
|     | Rule       | $\text{\scriptsize REL-LOAD-R}$                                                      | [rel_logic/rel_rules]                | `refines_load_r`                          |      |
|     | Rule       | $\text{\scriptsize REL-STORE-L}$                                                     | [rel_logic/rel_rules]                | `refines_store_l`                         |      |
|     | Rule       | $\text{\scriptsize REL-STORE-R}$                                                     | [rel_logic/rel_rules]                | `refines_store_r`                         |      |
|     | Rule       | $\text{\scriptsize REL-PACK}$                                                        | [rel_logic/compatibility]            | `refines_pack`                            | (2)  |
|     | Rule       | $\text{\scriptsize REL-RETURN}$                                                      | [rel_logic/model]                    | `refines_ret`                             |      |
|     | Rule       | $\text{\scriptsize REL-BIND}$                                                        | [rel_logic/model]                    | `refines_bind`                            |      |
|     | Rule       | $\text{\scriptsize REL-RAND-L}$                                                      | [rel_logic/rel_rules]                | `refines_randU_l`                         |      |
|     | Rule       | $\text{\scriptsize REL-RAND-R}$                                                      | [rel_logic/rel_rules]                | `refines_randU_r`                         |      |
|     | Rule       | $\text{\scriptsize REL-ALLOC-TAPE-L}$                                                | [rel_logic/rel_rules]                | `refines_alloctape_l`                     |      |
|     | Rule       | $\text{\scriptsize REL-ALLOC-TAPE-R}$                                                | [rel_logic/rel_rules]                | `refines_alloctape_r`                     |      |
|     | Rule       | $\text{\scriptsize REL-RAND-TAPE-L}$                                                 | [rel_logic/rel_rules]                | `refines_rand_l`                          |      |
|     | Rule       | $\text{\scriptsize REL-RAND-TAPE-R}$                                                 | [rel_logic/rel_rules]                | `refines_rand_r`                          |      |
|     | Rule       | $\text{\scriptsize REL-RAND-TAPE-EMPTY-L}$                                           | [rel_logic/rel_rules]                | `refines_rand_empty_l`                    |      |
|     | Rule       | $\text{\scriptsize REL-RAND-TAPE-EMPTY-R}$                                           | [rel_logic/rel_rules]                | `refines_rand_empty_r`                    |      |
|     | Rule       | $\text{\scriptsize REL-COUPLE-RANDS}$                                                | [rel_logic/rel_rules]                | `refines_couple_rands_lr`                 |      |
|     | Rule       | $\text{\scriptsize REL-COUPLE-TAPE-L}$                                               | [rel_logic/rel_rules]                | `refines_couple_TU`                       |      |
|     | Rule       | $\text{\scriptsize REL-COUPLE-TAPE-R}$                                               | [rel_logic/rel_rules]                | `refines_couple_UT`                       |      |
|     | Rule       | $\text{\scriptsize REL-COUPLE-TAPES}$                                                | [rel_logic/rel_rules]                | `refines_couple_tapes`                    |      |
|     | Rule       | $\text{\scriptsize REL-NA-INV-ALLOC}$                                                | [rel_logic/model]                    | `refines_na_alloc`                        |      |
|     | Rule       | $\text{\scriptsize REL-NA-INV-OPEN}$                                                 | [rel_logic/model]                    | `refines_na_inv`                          |      |
|     | Rule       | $\text{\scriptsize REL-NA-INV-CLOSE}$                                                | [rel_logic/model]                    | `refines_na_close`                        |      |
| 5.1 | Definition | ($R$-) coupling                                                                      | [prob/couplings]                     | `is_coupl`, `is_Rcoupl`                   |      |
|     | Lemma      | 6 (Composition of couplings)                                                         | [prob/couplings]                     | `Rcoupl_dret`, `Rcoupl_dbind`             |      |
|     | Lemma      | 7 (lifting of equality)                                                              | [prob/couplings]                     | `Rcoupl_eq`                               |      |
|     | Rule       | $\text{\scriptsize WP-WAND}$                                                         | [program_logic/weakestpre]           | `wp_wand`                                 |      |
|     | Rule       | $\text{\scriptsize WP-BIND}$                                                         | [program_logic/weakestpre]           | `wp_bind`                                 |      |
|     | Rule       | $\text{\scriptsize WP-LOAD}$                                                         | [rel_logic/primitive_laws]           | `wp_load`                                 |      |
|     | Rule       | $\text{\scriptsize WP-COUPLE-RANDS}$                                                 | [rel_logic/coupling_rules]           | `wp_couple_rand_rand`                     |      |
|     | Rule       | $\text{\scriptsize WP-COUPLE-TAPE-L}$                                                | [rel_logic/coupling_rules]           | `wp_couple_tape_rand`                     |      |
|     | Definition | weakest precondition                                                                 | [program_logic/weakestpre]           | `wp`, `wp_pre`                            |      |
|     | Definition | execCoupl                                                                            | [program_logic/weakestpre]           | `exec_coupl`, `exec_couple_pre`           |      |
|     | Rule       | execCoupl rule for $\text{step}(ρ_1) \sim \text{step}(ρ_1') : R$                     | [program_logic/weakestpre]           | `exec_coupl_prim_steps`                   |      |
|     | Rule       | execCoupl rule for $\text{ret}(ρ_1) \sim \text{step}(ρ_1') : R$                      | [program_logic/weakestpre]           | `exec_coupl_prim_step_l`                  |      |
|     | Definition | *state step* relation                                                                | [prob_lang/lang]                     | `state_step`, `state_step_pmf`            |      |
|     | Rule       | execCoupl rule for $\text{step}_ι(σ_1) \sim \text{step}(ρ_1') : R$                   | [program_logic/weakestpre]           | `exec_coupl_state_prim`                   |      |
|     | Rule       | $\text{\scriptsize SPEC-PURE}$                                                       | [rel_logic/spec_rules]               | `step_pure`                               |      |
|     | Rule       | $\text{\scriptsize SPEC-STORE}$                                                      | [rel_logic/spec_rules]               | `step_store`                              |      |
|     | Definition | $\text{spec}_\circ(ρ)$                                                               | [rel_logic/spec_ra]                  | `⤇ e` (`spec_prog_frag`)                  |      |
|     | Definition | $\text{specInterp}_\bullet(ρ)$                                                       | [rel_logic/spec_ra]                  | `spec_interp_auth`                        |      |
|     | Definition | specInv                                                                              | [rel_logic/spec_ra]                  | `spec_inv`                                |      |
|     | Definition | specCtx                                                                              | [rel_logic/spec_ra]                  | `spec_ctx`                                | (3)  |
|     | Definition | $G(ρ)$ and $S(ρ)$ as used in $\text{wp}$                                             | [rel_logic/primitive_laws]           | `clutchGS_irisGS`                         |      |
| 5.2 | Definition | $Δ \vDash e₁ \precsim e₂ : τ$                                                        | [rel_logic/model]                    | `refines_def`                             |      |
|     | Lemma      | $ι : \text{tape} ⊢ \text{rand} () ≅_{\text{ctx}} \text{flip}(ι) : \text{bool}$       | [examples/erasure]                   | `flip_erasure_ctx`                        |      |
| 5.3 | Definition | 8 (Left-Partial Coupling)                                                            | [prob/couplings]                     | `is_refcoupl`                             |      |
|     | Definition | R-left-partial-coupling                                                              | [prob/couplings]                     | `is_refRcoupl`                            |      |
|     | Lemma      | 9                                                                                    | [prob/couplings]                     | `Rcoupl_refRcoupl`                        |      |
|     | Lemma      | 10                                                                                   | [prob/couplings]                     | `refRcoupl_eq_elim`                       |      |
|     | Theorem    | 11 (Adequacy)                                                                        | [rel_logic/adequacy]                 | `wp_refRcoupl`                            |      |
|     | Lemma      | 12 (Erasure)                                                                         | [prob_lang/erasure]                  | `prim_coupl_step_prim`                    |      |
|     | Definition | Contextual closure of refinement                                                     | [typing/interp]                      | `bin_log_related`                         |      |
|     | Rule       | $\text{\scriptsize RAND-COMPAT}$                                                     | [rel_logic/compatibility]            | `refines_rand_tape`                       |      |
|     | Theorem    | 13 (Fundamental theorem)                                                             | [typing/fundamental]                 | `fundamental`                             |      |
|     | Theorem    | 14 (Soundness)                                                                       | [typing/soundness]                   | `refines_sound`                           |      |
| 6.1 | Example    | Lazy/eager coin                                                                      | [examples/lazy_eager_coin]           |                                           |      |
| 6.2 | Example    | ElGamal public key encryption                                                        | [examples/crypto/ElGamal]            |                                           |      |
| 6.3 | Example    | Hash functions                                                                       | [examples/hash]                      |                                           |      |
| 6.4 | Example    | Lazily sampled big integers                                                          | [examples/lazy_int]                  |                                           |      |
| A   | Example    | Counterexample                                                                       | [examples/counterexample]            |                                           |      |
| C.1 | Example    | Sangiorgi and Vignudelli's example                                                   | [examples/env_bisim]                 |                                           |      |
| C.4 | Example    | Random Generators from Hashes                                                        | [examples/rng], [examples/split_rng] |                                           |      |

(1) In the code, we use `ctx_refines` more than `ctx_refines_alt`, which matches the exact definition of the paper. Nothing is lost, since we prove that `ctx_refines` implies `ctx_refines_alt` in `Lemma ctx_refines_impl_alt` (see [typing/contextual_refinement_alt]).

(2) `pack` for existential types has no operational meaning, and thus `pack e` simply stands for `e`. The requirement for `R` to be persistent in the `rel-pack` rule is reflected in the code by the fact that logical relations are defined as persistent predicates (see [rel_logic/model]).

(3) In the code, we often use the shorthand `refines_right K e` to refer to the combined `spec_ctx ∗ ⤇ K[e]`.

[examples/counterexample]: theories/examples/counterexample.v
[examples/crypto/ElGamal]: theories/examples/crypto/ElGamal.v
[examples/env_bisim]: theories/examples/env_bisim.v
[examples/erasure]: theories/examples/erasure.v
[examples/hash]: theories/examples/hash.v
[examples/lazy_eager_coin]: theories/examples/lazy_eager_coin.v
[examples/lazy_int]: theories/examples/lazy_int.v
[examples/rng]: theories/examples/rng.v
[examples/split_rng]: theories/examples/split_rng.v
[rel_logic/compatibility]: theories/rel_logic/compatibility.v
[rel_logic/model]: theories/rel_logic/model.v
[rel_logic/rel_rules]: theories/rel_logic/rel_rules.v
[rel_logic/primitive_laws]: theories/rel_logic/primitive_laws.v
[rel_logic/coupling_rules]: theories/rel_logic/coupling_rules.v
[prob/couplings]: theories/prob/couplings.v
[prob/distribution]: theories/prob/distribution.v
[rel_logic/adequacy]: theories/rel_logic/adequacy.v
[prob_lang/erasure]: theories/prob_lang/erasure.v
[prob_lang/lang]: theories/prob_lang/lang.v
[rel_logic/spec_ra]: theories/rel_logic/spec_ra.v
[rel_logic/spec_rules]: theories/rel_logic/spec_rules.v
[program_logic/ectx_language]: theories/program_logic/ectx_language.v
[program_logic/ectxi_language]: theories/program_logic/ectxi_language.v
[program_logic/exec]: theories/program_logic/exec.v
[program_logic/language]: theories/program_logic/language.v
[program_logic/weakestpre]: theories/program_logic/weakestpre.v
[typing/contextual_refinement]: theories/typing/contextual_refinement.v
[typing/contextual_refinement_alt]: theories/typing/contextual_refinement_alt.v
[typing/fundamental]: theories/typing/fundamental.v
[typing/interp]: theories/typing/interp.v
[typing/soundness]: theories/typing/soundness.v
[typing/types]: theories/typing/types.v

[iris upstream]: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/iprop.v
