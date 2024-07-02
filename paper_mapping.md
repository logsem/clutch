## Reference from the paper to the code

| §   | Kind          | Item                                       | Coq file                                     | Name                                                 | Note                                                                     |
|-----|---------------|--------------------------------------------|----------------------------------------------|------------------------------------------------------|--------------------------------------------------------------------------|
| 2.1 | Example       | ``coinToss``                               | [theories/tachis/examples/geometric.v]       | `geo`                                                |                                                                          |
| 2.2 | Example       | ``op`` non-amortized                       | [theories/tachis/examples/amortized.v]       | `wp_op_ert`                                        |                                                                          |
| 2.2 | Example       | ``op`` amortized                           | [theories/tachis/examples/amortized.v]       | `wp_op_n_aert`                                      |                                                                          |
| 3.1 | Definition    | Discrete subdistribution                   | [theories/prob/distribution.v]               | `distr`                                              |                                                                          |
| 3.1 | Definition    | Discrete distribution monad                | [theories/prob/distribution.v]               | `dbind`, `dret`, etc                                 |                                                                          |
| 3.1 | Definition    | `RandML`                                   | [theories/prob_lang/lang.v]                  | Whole file                                           |                                                                          |
| 3.1 | Definition    | `step`                                     | [theories/common/ectx_language.v]            | `prim_step`                                          |                                                                          |
| 3.1 | Definition    | `exec_n`                                   | [theories/common/exec.v]                     | `exec`                                               |                                                                          |
| 3.1 | Definition    | `exec`                                     | [theories/common/exec.v]                     | `lim_exec_val`                                       |                                                                          |
| 3.2 | Definition    | Cost model                                 | [theories/tachis/ert_weakestpre.v]           | `Costfun`                                            |                                                                          |
| 3.2 | Definition    | Expected cost, $m$ steps                   | [theories/tachis/adequacy.v]                 | `ERT`                                               |                                                                          |
| 3.2 | Definition    | Expected cost (limit)                      | [theories/tachis/adequacy.v]                 | `lim_ERT`                                           |                                                                          |
| 3.2 | Definition    | `cost_all`                                 | [theories/tachis/cost_models.v]              | `CostLanguageCtx_Cost1_prob_lang`                   |                                                                          |
| 3.2 | Definition    | `cost_app`                                 | [theories/tachis/cost_models.v]              | `CostApp`                                            |                                                                          |
| 3.2 | Definition    | `cost_rand`                                | [theories/tachis/cost_models.v]              | `CostEntropy`                                        |                                                                          |
| 3.2 | Definition    | `cost_tick`                                | [theories/tachis/cost_models.v]              | `CostTick`                                           |                                                                          |
| 4.1 | Definition    | `iProp`                                    | Imported from [Iris upstream]                | `iProp`                                              |                                                                          |
| 4.1 | Definition    | Credit assertion                           | [theories/tachis/expected_time_credits.v]    | `ec`                                                 | `⧖ x` is notation in our development for `$ x`                           |
| 4.1 | Rule          | Credit splitting rule                      | [theories/tachis/expected_time_credits.v]    | `etc_split`, `etc_combine`                           |                                                                          |
| 4.2 | Theorem       | Adqeuacy (Hoare Triples)                   | [theories/tachis/adequacy.v]                 | Derivable from `wp_correct_lim`                     |                                                                          |
| 4.2 | Rule          | `HT-BIND`                                  | [theories/tachis/ert_weakestpre.v]           | `ert_wp_bind`                                       | See also `tac_wp_bind` in `tachis/proofmode.v`                           |
| 4.2 | Rule          | `HT-FRAME`                                 | [theories/tachis/ert_weakestpre.v]           | Derivable from `ert_wp_frame_l` and `ert_wp_frame_r` | See also `frame_ert_wp `                                                 |
| 4.2 | Rule          | `HT-LOAD`                                  | [theories/tachis/primitive_laws.v]           | `wp_load`                                            |                                                                          |
| 4.2 | Rule          | `HT-RAND`                                  | [theories/tachis/primitive_laws.v]           | `wp_rand`                                            |                                                                          |
| 4.2 | Rule          | `HT-REC`                                   | [theories/tachis/primitive_laws.v]           | `wp_rec_löb`                                         |                                                                          |
| 4.2 | Rule          | `HT-RAND-EXP`                              | [theories/tachis/ert_rules.v]                | `wp_couple_rand_adv_comp_strong'`                    |                                                                          |
| 4.3 | File          | Cost model tactics                         | [theories/tachis/proofmode.v]                | Whole file                                           | See eg. `wp_*` tactics                                                   |
| 5.1 | Example       | Coupon Collector                           | [theories/tachis/examples/couponcollector.v] | `wp_coupon_collection`                              |                                                                          |
| 5.2 | Example       | Fischer Yates Shuffle                      | [theories/tachis/examples/fisher_yates.v]    | `wp_fisher_yates`                                   |                                                                          |
| 5.4 | Example       | Hash map                                   | [theories/tachis/examples/hashmap/hashmap.v] | `wp_amortized_hm_insert_new`                        |                                                                          |
| 5.4 | Example       | Ammortized Hash map                        | [theories/tachis/examples/hashmap/hashmap.v] | `wp_hm_insert_new`, `wp_hm_lookup_new`              |                                                                          |
| 5.5 | Example       | Quicksort Time bound                       | [theories/tachis/examples/quicksort.v]       | `qs_time_bound`                                     |                                                                          |
| 5.5 | Example       | Quicksort Expected entropy bound           | [theories/tachis/examples/quicksort.v]       | `qs_ent_bound`                                       |                                                                          |
| 5.6 | Example       | Meldable heap implementation               | [theories/tachis/examples/meldable_heap.v]   | `meld_heap_spec`                                    |                                                                          |
| 5.6 | Specification | Abstract comparator specification `isComp` | [theories/tachis/examples/min_heap_spec.v]   | `comparator`                                         |                                                                          |
| 5.6 | Specification | Abstract min-heap specification            | [theories/tachis/examples/min_heap_spec.v]   | `min_heap`                                           |                                                                          |
| 5.7 | Example       | `isComp` instance for lists                | [theories/tachis/examples/kway_merge.v]      | `Z_list_comparator`                                 |                                                                          |
| 5.7 | Example       | k-way merge abstract specification         | [theories/tachis/examples/kway_merge.v]      | `wp_merge`                                          |                                                                          |
| 5.7 | Example       | Composed `O(n log k)` meldable heap merge  | [theories/tachis/examples/kway_merge.v]      | `wp_meldable_merge`                                 |                                                                          |
| 6   | Definition    | Hoare triple                               | [theories/bi/weakestpre.v]                   | Defined as ``Notations``                             |                                                                          |
| 6.1 | Definition    | Expected Cost modality                     | [theories/tachis/ert_weakestpre.v]           | `ERM`                                               | See `ERM_unfold` for the equation at the start of 6.1                    |
| 6.1 | Definition    | Weakest precondition                       | [theories/tachis/ert_weakestpre.v]           | `ert_wp`                                             | See `ert_wp_unfold`, `ert_wp_pre` for the equation at the start of 6.1 |
| 6.1 | Definition    | Cost credit resource algebra               | [theories/tachis/expected_time_credits.v]    | `etcGS`                                             |                                                                          |
| 6.1 | Definition    | Cost interpretation                        | [theories/tachis/expected_time_credits.v]    | `etc_supply`                                         |                                                                          |
| 6.1 | Definition    | Cost budget                                | [theories/tachis/expected_time_credits.v]    | `ec`                                                 | `⧖ x` is notation in our development for `$ x`                           |
| 6.1 | Rule          | Agreement Rule                             | [theories/tachis/expected_time_credits.v]    | `etc_supply_bound`                                  |                                                                          |
| 6.1 | Rule          | Spending Rule                              | [theories/tachis/expected_time_credits.v]    | `etc_supply_decrease`                               |                                                                          |
| 6.1 | Rule          | Acquiring Rule                             | [theories/tachis/expected_time_credits.v]    | `etc_supply_increase`                               |                                                                          |
| 6.2 | Theorem       | Adequacy (Weakest Preconditions)           | [theories/tachis/adequacy.v]                 | `wp_correct_lim`                                    |                                                                          |
| 6.3 | Remark        | Finite `cost_app` cost implies AST         | [theories/tachis/adequacy.v]                 | `wp_ERT_ast'`                                        |                                                                          |




[theories/tachis/examples/geometric.v]: theories/tachis/examples/geometric.v
[theories/tachis/examples/amortized.v]: theories/tachis/examples/amortized.v
[theories/prob/distribution.v]: theories/prob/distribution.v
[theories/prob_lang/lang.v]: theories/prob_lang/lang.v
[theories/common/ectx_language.v]: theories/common/ectx_language.v
[theories/common/exec.v]: theories/common/exec.v
[theories/tachis/ert_weakestpre.v]: theories/tachis/ert_weakestpre.v
[theories/tachis/adequacy.v]: theories/tachis/adequacy.v
[theories/tachis/cost_models.v]: theories/tachis/cost_models.v
[theories/tachis/expected_time_credits.v]: theories/tachis/expected_time_credits.v
[theories/tachis/ert_weakestpre.v]: theories/tachis/ert_weakestpre.v
[theories/tachis/primitive_laws.v]: theories/tachis/primitive_laws.v
[theories/tachis/ert_rules.v]: theories/tachis/ert_rules.v
[theories/tachis/proofmode.v]: theories/tachis/proofmode.v
[theories/tachis/examples/couponcollector.v]: theories/tachis/examples/couponcollector.v
[theories/tachis/examples/fisher_yates.v]: theories/tachis/examples/fisher_yates.v
[theories/tachis/examples/hashmap/hashmap.v]: theories/tachis/examples/hashmap/hashmap.v
[theories/tachis/examples/quicksort.v]: theories/tachis/examples/quicksort.v
[theories/tachis/examples/meldable_heap.v]: theories/tachis/examples/meldable_heap.v
[theories/tachis/examples/min_heap_spec.v]: theories/tachis/examples/min_heap_spec.v
[theories/tachis/examples/kway_merge.v]: theories/tachis/examples/kway_merge.v
[theories/bi/weakestpre.v]: theories/bi/weakestpre.v
[theories/tachis/ert_weakestpre.v]: theories/tachis/ert_weakestpre.v
[theories/tachis/expected_time_credits.v]: theories/tachis/expected_time_credits.v


[Iris upstream]: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/iprop.v
