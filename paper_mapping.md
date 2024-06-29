## Reference from the paper to the code

| §        | Kind          | Item                                                 | Coq file                  | Name                               | Note |
|----------|---------------|------------------------------------------------------|---------------------------|------------------------------------|------|
| 2.1      | Example       | ``coinToss``                                         |                           |                                    |      |
| 2.2      | Example       | ``op``                                               |                           |                                    |      |
| 3.1      | Definition    | Discrete subdistribution                             |                           |                                    |      |
| 3.1      | Definition    | Discrete distribution monad                          |                           |                                    |      |
| 3.1      | Definition    | `RandML`                                             |                           |                                    |      |
| 3.1      | Definition    | $\text{\scriptsize step}$                            |                           |                                    |      |
| 3.1      | Definition    | $\text{\scriptsize exec}_n$                          |                           |                                    |      |
| 3.1      | Definition    | $\text{\scriptsize exec}$                            |                           |                                    |      |
| 3.2      | Definition    | Cost model                                           | `tachis/ert_weakestpre.v` | `Costfun`                          |      |
| 3.2      | Definition    | Expected cost, $m$ steps                             |                           |                                    |      |
| 3.2      | Definition    | Expected cost                                        |                           |                                    |      |
| 3.2      | Definition    | $\text{\scriptsize cost}_\text{\scriptsize all}$     | `tachis/cost_models.v`    | `CostLanguageCtx_Cost1_prob_lang ` |      |
| 3.2      | Definition    | $\text{\scriptsize cost}_\text{\scriptsize app}$     | `tachis/cost_models.v`    | `CostApp`                          |      |
| 3.2      | Definition    | $\text{\scriptsize cost}_\text{\scriptsize rand}$    | `tachis/cost_models.v`    | `CostEntropy`                      |      |
| 3.2      | Definition    | $\text{\scriptsize cost}_\text{\scriptsize tick}$    | `tachis/cost_models.v`    | `CostTick`                         |      |
| 4.1      | Definition    | `iProp`                                              |                           |                                    |      |
| 4.1      | Definition    | Credit assertion                                     |                           |                                    |      |
| 4.1      | Rule          | Credit splitting rule                                |                           |                                    |      |
| 4.2      | Theorem       | Adqeuacy (Hoare Triples)                             |                           |                                    |      |
| 4.2      | Rule          | $\text{\scriptsize HT-BIND}$                         |                           |                                    |      |
| 4.2      | Rule          | $\text{\scriptsize HT-LOAD}$                         |                           |                                    |      |
| 4.2      | Rule          | $\text{\scriptsize HT-RAND}$                         |                           |                                    |      |
| 4.2      | Rule          | $\text{\scriptsize HT-REC}$                          |                           |                                    |      |
| 4.3      | ??            | Cost model tactics                                   |                           |                                    |      |
| 5.1      | Example       | Coupon collector program                             |                           |                                    |      |
| 5.1      | Example       | Repeat Draw specification                            |                           |                                    |      |
| 5.2      | Example       | `repeatSwap` definition                              |                           |                                    |      |
| 5.2      | Example       | `shuffle` definition                                 |                           |                                    |      |
| 5.2      | Example       | `shuffle` specification                              |                           |                                    |      |
| 5.3      | Example       | `sampleThree` definition                             |                           |                                    |      |
| 5.3      | Example       | `sampleThree` specification                          |                           |                                    |      |
| 5.3      | Example       | `initSampler` definition                             |                           |                                    |      |
| 5.3      | Example       | `initSampler` specification                          |                           |                                    |      |
| 5.3      | Example       | `prefetch` definition                                |                           |                                    |      |
| 5.3      | Example       | `prefetch ` specification                            |                           |                                    |      |
| 5.4, A?? | Example       | `isHashMap` definition                               |                           |                                    |      |
| 5.4, A?? | Example       | `insert` definition                                  |                           |                                    |      |
| 5.4, A?? | Example       | `insert` exact specification                         |                           |                                    |      |
| 5.4, A?? | Example       | `insert` approximate specification                   |                           |                                    |      |
| 5.5      | Example       | `qSort` definition                                   |                           |                                    |      |
| 5.5      | Example       | `isPureComp` definition                              |                           |                                    |      |
| 5.5      | Example       | $t_m$ definition                                     |                           |                                    |      |
| 5.5      | Example       | $t_m$ upper bound                                    |                           |                                    |      |
| 5.5      | Example       | `qSort` specification                                |                           |                                    |      |
| 5.5      | Example       | `ix_rk`                                              |                           |                                    |      |
| 5.5      | Example       | `ix_rev`                                             |                           |                                    |      |
| 5.5      | Example       | Credit distribution function `d`                     |                           |                                    |      |
| 5.5      | Example       | Entropy recurrence relation `e`                      |                           |                                    |      |
| 5.6      | Example       | Meldable heap implementation                         |                           |                                    |      |
| 5.6      | Specification | Abstract comparator specification `isComp`           |                           |                                    |      |
| 5.6      | Specification | Abstract min-heap specification                      |                           |                                    |      |
| 5.6      | Example       | Type `BinaryTree`                                    |                           |                                    |      |
| 5.6      | Example       | Function `treeToList`                                |                           |                                    |      |
| 5.6      | Specification | `isBinaryTree`                                       |                           |                                    |      |
| 5.6      | Example       | `isMeldHeapVal`                                      |                           |                                    |      |
| 5.6      | Example       | `isMeldHeapRef`                                      |                           |                                    |      |
| 5.6      | Example       | $\text{t}^\text{meld}$                               |                           |                                    |      |
| 5.6      | Specification | `meld` specification                                 |                           |                                    |      |
| 5.6      | Example       | $\text{tc}^\text{dist}$                              |                           |                                    |      |
| 5.6      | Example       | Meldable heap abstract min-heap instance             |                           |                                    |      |
| 5.7      | Example       | `repeatRemove`                                       |                           |                                    |      |
| 5.7      | Example       | `merge`                                              |                           |                                    |      |
| 5.7      | Example       | `isComp` instance for lists                          |                           |                                    |      |
| 5.7      | Specification | `merge` specification                                |                           |                                    |      |
| 5.7      | Example       | Composed $\mathcal{O}(n \log k)$ merge specification |                           |                                    |      |
| 6        | Definition    | Hoare triple                                         |                           |                                    |      |
| 6.1      | Definition    | Cost interpretation                                  |                           |                                    |      |
| 6.1      | Definition    | Expected Cost modality                               |                           |                                    |      |
| 6.1      | Definition    | Weakest precondition                                 |                           |                                    |      |
| 6.1      | Definition    | Cost credit resource algebra                         |                           |                                    |      |
| 6.1      | Rule          | Agreement Rule                                       |                           |                                    |      |
| 6.1      | Rule          | Spending Rule                                        |                           |                                    |      |
| 6.1      | Rule          | Acquiring Rule                                       |                           |                                    |      |
| 6.2      | Theorem       | Adequacy (Weakest Preconditions)                     | `tachis/adequacy.v`       | `wp_correct_lim `                  |      |
| 6.3      | Remark        | Finite `cost_app` cost implies AST                   | `tachis/adequacy.v`       | `wp_ERT_ast'`                      |      |


## Things from the paper
- Pg 4
  - HT-REC
  - HT-IF
  - HT-FLIP-EXP
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
- [ ] `tachis/ert_rules.v`
- [ ] `tachis/ert_weakestpre.v`
- [ ] `tachis/expected_time_credits.v`
- [ ] `tachis/lifting.v`
- [ ] `tachis/primitive_laws.v`
- [ ] `tachis/problang_wp.v`
- [ ] `tachis/proofmode.v`


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





