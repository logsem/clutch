## Reference from the paper to the code

| §   | Kind          | Item                                       | Coq file                            | Name                                    | Note                                                                     |
|-----|---------------|--------------------------------------------|-------------------------------------|-----------------------------------------|--------------------------------------------------------------------------|
| 2.1 | Example       | ``coinToss``                               | `tachis/examples/geometric.v`       | `geo`                                   |                                                                          |
| 2.2 | Example       | ``op``                                     |                                     |                                         |                                                                          |
| 3.1 | Definition    | Discrete subdistribution                   | `prob/distribution.v`               | `distr`                                 |                                                                          |
| 3.1 | Definition    | Discrete distribution monad                | `prob/distribution.v`               | `dbind`, `dret`, etc                    |                                                                          |
| 3.1 | Definition    | `RandML`                                   | `prob_lang/lang.v`                  |                                         |                                                                          |
| 3.1 | Definition    | `step`                                     | `common/ectx_language.v`            | `prim_step`                             |                                                                          |
| 3.1 | Definition    | `exec_n`                                   | `common/exec.v`                     | `exec`                                  |                                                                          |
| 3.1 | Definition    | `exec`                                     | `common/exec.v`                     | `lim_exec_val`                          |                                                                          |
| 3.2 | Definition    | Cost model                                 | `tachis/ert_weakestpre.v`           | `Costfun`                               |                                                                          |
| 3.2 | Definition    | Expected cost, $m$ steps                   | `tachis/adequacy.v`                 | `ERT `                                  |                                                                          |
| 3.2 | Definition    | Expected cost (limit)                      | `tachis/adequacy.v`                 | `lim_ERT `                              |                                                                          |
| 3.2 | Definition    | `cost_all`                                 | `tachis/cost_models.v`              | `CostLanguageCtx_Cost1_prob_lang `      |                                                                          |
| 3.2 | Definition    | `cost_app`                                 | `tachis/cost_models.v`              | `CostApp`                               |                                                                          |
| 3.2 | Definition    | `cost_rand`                                | `tachis/cost_models.v`              | `CostEntropy`                           |                                                                          |
| 3.2 | Definition    | `cost_tick`                                | `tachis/cost_models.v`              | `CostTick`                              |                                                                          |
| 4.1 | Definition    | `iProp`                                    | Imported from Iris                  | `iProp`                                 |                                                                          |
| 4.1 | Definition    | Credit assertion                           | `tachis/expected_time_credits.v`    | `ec`                                    | `⧖ x` is notation in our development for `$ x`                           |
| 4.1 | Rule          | Credit splitting rule                      | `tachis/expected_time_credits.v`    | `etc_split`, `etc_combine`              |                                                                          |
| 4.2 | Theorem       | Adqeuacy (Hoare Triples)                   |                                     |                                         |                                                                          |
| 4.2 | Rule          | `HT-BIND`                                  |                                     |                                         |                                                                          |
| 4.2 | Rule          | `HT-FRAME`                                 |                                     |                                         |                                                                          |
| 4.2 | Rule          | `HT-LOAD`                                  | `tachis/primitive_laws.v`           | `wp_load`                               |                                                                          |
| 4.2 | Rule          | `HT-RAND`                                  | `tachis/primitive_laws.v`           | `wp_rand`                               |                                                                          |
| 4.2 | Rule          | `HT-REC`                                   |                                     |                                         |                                                                          |
| 4.2 | Rule          | `HT-RAND-EXP`                              | `tachis/ert_rules.v`                | `wp_couple_rand_adv_comp_strong'`       |                                                                          |
| 4.3 | File          | Cost model tactics                         | `tachis/proofmode.v`                |                                         | See eg. `wp_*` tactics                                                   |
| 5.1 | Example       | Coupon Collector                           | `tachis/examples/couponcollector.v` | `wp_coupon_collection `                 |                                                                          |
| 5.2 | Example       | Fischer Yates Shuffle                      | `tachis/examples/fisher_yates.v`    | `wp_fisher_yates `                      |                                                                          |
| 5.4 | Example       | Hash map                                   | `tachis/examples/hashmap/hashmap.v` | `wp_amortized_hm_insert_new `           |                                                                          |
| 5.4 | Example       | Ammortized Hash map                        | `tachis/examples/hashmap/hashmap.v` | `wp_hm_insert_new`, `wp_hm_lookup_new ` |                                                                          |
| 5.5 | Example       | Quicksort Time bound                       | `tachis/examples/quicksort.v`       | `qs_time_bound `                        |                                                                          |
| 5.5 | Example       | Quicksort Expected entropy bound           | `tachis/examples/quicksort.v`       | `qs_ent_bound`                          |                                                                          |
| 5.6 | Example       | Meldable heap implementation               | `tachis/examples/meldable_heap.v`   | `meld_heap_spec `                       |                                                                          |
| 5.6 | Specification | Abstract comparator specification `isComp` | `tachis/examples/min_heap_spec.v`   | `comparator`                            |                                                                          |
| 5.6 | Specification | Abstract min-heap specification            | `tachis/examples/min_heap_spec.v`   | `min_heap`                              |                                                                          |
| 5.7 | Example       | `isComp` instance for lists                | `tachis/examples/kway_merge.v`      | `Z_list_comparator `                    |                                                                          |
| 5.7 | Example       | k-way merge abstract specification         | `tachis/examples/kway_merge.v`      | `wp_merge `                             |                                                                          |
| 5.7 | Example       | Composed `O(n log k)` meldable heap merge  | `tachis/examples/kway_merge.v`      | `wp_meldable_merge `                    |                                                                          |
| 6   | Definition    | Hoare triple                               |                                     |                                         |                                                                          |
| 6.1 | Definition    | Cost interpretation                        |                                     |                                         |                                                                          |
| 6.1 | Definition    | Expected Cost modality                     | `tachis/ert_weakestpre.v`           | `ERM `                                  | See `ERM_unfold` for the equation at the start of 6.1                    |
| 6.1 | Definition    | Weakest precondition                       | `tachis/ert_weakestpre.v`           | `ert_wp`                                | See `ert_wp_unfold `, `ert_wp_pre ` for the equation at the start of 6.1 |
| 6.1 | Definition    | Cost credit resource algebra               | `tachis/expected_time_credits.v`    | `etcGS `                                |                                                                          |
| 6.1 | Definition    | Cost interpretation                        | `tachis/expected_time_credits.v`    | `etc_supply`                            |                                                                          |
| 6.1 | Definition    | Cost budget                                | `tachis/expected_time_credits.v`    | `ec`                                    | `⧖ x` is notation in our development for `$ x`                           |
| 6.1 | Rule          | Agreement Rule                             | `tachis/expected_time_credits.v`    | `etc_supply_bound `                     |                                                                          |
| 6.1 | Rule          | Spending Rule                              | `tachis/expected_time_credits.v`    | `etc_supply_decrease `                  |                                                                          |
| 6.1 | Rule          | Acquiring Rule                             | `tachis/expected_time_credits.v`    | `etc_supply_increase `                  |                                                                          |
| 6.2 | Theorem       | Adequacy (Weakest Preconditions)           | `tachis/adequacy.v`                 | `wp_correct_lim `                       |                                                                          |
| 6.3 | Remark        | Finite `cost_app` cost implies AST         | `tachis/adequacy.v`                 | `wp_ERT_ast'`                           |                                                                          |


## Things from the paper
- Pg 4
  - HT-REC
  - HT-IF
  - HT-FLIP-EXP?
  - HT rand `wp_couple_rand_constant ` (?)
- Pg 10. Note about HT-FRAME?

- Change names to RandML?


# Things from the development
- [x] `tachis/adequacy.v`
  - ERT section?
  - Any of these?
    - `wp_ERT` ?
    - `wp_ERT_lim`?
    - `wp_ERT_ast` ?
- [x] `tachis/cost_models.v`
- [x] `tachis/derived_laws.v`
  - Array stuff for examples?
  - WP rules for allocation
- [x] `tachis/ectx_lifting.v`
- [x] `tachis/ert_rules.v`
- [ ] `tachis/ert_weakestpre.v`
  - CTX lang stuff
  - Frame and wand rules? (is `frame_ert_wp` frame?)
- [x] `tachis/expected_time_credits.v`
  - Other credit properties here?
- [x] `tachis/lifting.v`
- [x] `tachis/primitive_laws.v`
- [ ] `tachis/problang_wp.v`
- [ ] `tachis/proofmode.v`
  - Any specific tactics?

-- Remove all tapes 



## Per-file deletion on these 
- [ ] `bi/weakestpre.v`

- [ ] `prob/countable_sum.v`
- [ ] `prob/couplings.v`
- [ ] `prob/couplings_app.v`
- [ ] `prob/distribution.v`
- [ ] `prob/generic_lifting.v`
- [ ] `prob/graded_predicate_lifting.v`
- [ ] `prob/markov.v`

- [ ] `common/ectxi_language.v`
- [ ] `common/ectx_language.v`
- [ ] `common/erasable.v`
- [ ] `common/exec.v`
- [ ] `common/inject.v`
- [ ] `common/language.v`

- [ ] `prob_lang/spec/*`
- [ ] `prob_lang/typing/*`
- [ ] `prob_lang/class_instances.v`
- [ ] `prob_lang/ctx_subst.v`
- [ ] `prob_lang/erasure.v`
- [ ] `prob_lang/exec_lang.v`
- [ ] `prob_lang/lang.v`
- [ ] `prob_lang/locations.v`
- [ ] `prob_lang/metatheory.v`
- [ ] `prob_lang/notation.v`
- [ ] `prob_lang/tactics.v`
- [ ] `prob_lang/wp_tactics.v`

- [ ] `base_logic/error_credits.v`
- [ ] `base_logic/spec_auth_markov.v`
- [ ] `base_logic/spec_update.v`

- [ ] `prelude/uniform_list.v`
- [ ] `prelude/stdpp_ext.v`
- [ ] `prelude/mc_stdlib.v`
- [ ] `prelude/iris_ext.v`
- [ ] `prelude/fin.v`
- [ ] `prelude/classical.v`
- [ ] `prelude/base.v`
- [ ] `prelude/Series_ext.v`
- [ ] `prelude/Reals_ext.v`
- [ ] `prelude/NNRbar.v`
- [ ] `prelude/Coquelicot_ext.v`
- [ ] `prelude/zmodp_fin.v`
- [ ] `prelude/asubst.v`
- [ ] `prelude/properness.v`





