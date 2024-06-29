## Reference from the paper to the code

| §        | Kind          | Item                                                 | Coq file | Name | Note |
|----------|---------------|------------------------------------------------------|----------|------|------|
| 2.1      | Example       | ``coinToss``                                         |          |      |      |
| 2.2      | Example       | ``op``                                               |          |      |      |
| 3.1      | Definition    | Discrete subdistribution                             |          |      |      |
| 3.1      | Definition    | Discrete distribution monad                          |          |      |      |
| 3.1      | Definition    | `RandML`                                             |          |      |      |
| 3.1      | Definition    | $\text{\scriptsize step}$                            |          |      |      |
| 3.1      | Definition    | $\text{\scriptsize exec}_n$                          |          |      |      |
| 3.1      | Definition    | $\text{\scriptsize exec}$                            |          |      |      |
| 3.2      | Definition    | Cost model                                           |          |      |      |
| 3.2      | Definition    | Expected cost, $m$ steps                             |          |      |      |
| 3.2      | Definition    | Expected cost                                        |          |      |      |
| 3.2      | Definition    | $\text{\scriptsize cost}_\text{\scriptsize all}$     |          |      |      |
| 3.2      | Definition    | $\text{\scriptsize cost}_\text{\scriptsize app}$     |          |      |      |
| 3.2      | Definition    | $\text{\scriptsize cost}_\text{\scriptsize rand}$    |          |      |      |
| 3.2      | Definition    | $\text{\scriptsize cost}_\text{\scriptsize tick}$    |          |      |      |
| 4.1      | Definition    | `iProp`                                              |          |      |      |
| 4.1      | Definition    | Credit assertion                                     |          |      |      |
| 4.1      | Rule          | Credit splitting rule                                |          |      |      |
| 4.2      | Theorem       | Adqeuacy  (Hoare Triples)                            |          |      |      |
| 4.2      | Rule          | $\text{\scriptsize HT-BIND}$                         |          |      |      |
| 4.2      | Rule          | $\text{\scriptsize HT-LOAD}$                         |          |      |      |
| 4.2      | Rule          | $\text{\scriptsize HT-RAND}$                         |          |      |      |
| 4.2      | Rule          | $\text{\scriptsize HT-REC}$                          |          |      |      |
| 4.3      | ??            | Cost model tactics                                   |          |      |      |
| 5.1      | Example       | Coupon collector program                             |          |      |      |
| 5.1      | Example       | Repeat Draw specification                            |          |      |      |
| 5.2      | Example       | `repeatSwap` definition                              |          |      |      |
| 5.2      | Example       | `shuffle` definition                                 |          |      |      |
| 5.2      | Example       | `shuffle` specification                              |          |      |      |
| 5.3      | Example       | `sampleThree` definition                             |          |      |      |
| 5.3      | Example       | `sampleThree` specification                          |          |      |      |
| 5.3      | Example       | `initSampler` definition                             |          |      |      |
| 5.3      | Example       | `initSampler` specification                          |          |      |      |
| 5.3      | Example       | `prefetch` definition                                |          |      |      |
| 5.3      | Example       | `prefetch ` specification                            |          |      |      |
| 5.4, A?? | Example       | `isHashMap` definition                               |          |      |      |
| 5.4, A?? | Example       | `insert` definition                                  |          |      |      |
| 5.4, A?? | Example       | `insert` exact specification                         |          |      |      |
| 5.4, A?? | Example       | `insert` approximate specification                   |          |      |      |
| 5.5      | Example       | `qSort` definition                                   |          |      |      |
| 5.5      | Example       | `isPureComp` definition                              |          |      |      |
| 5.5      | Example       | $t_m$ definition                                     |          |      |      |
| 5.5      | Example       | $t_m$ upper bound                                    |          |      |      |
| 5.5      | Example       | `qSort` specification                                |          |      |      |
| 5.5      | Example       | `ix_rk`                                              |          |      |      |
| 5.5      | Example       | `ix_rev`                                             |          |      |      |
| 5.5      | Example       | Credit distribution function `d`                     |          |      |      |
| 5.5      | Example       | Entropy recurrence relation `e`                      |          |      |      |
| 5.6      | Example       | Meldable heap implementation                         |          |      |      |
| 5.6      | Specification | Abstract comparator specification `isComp`           |          |      |      |
| 5.6      | Specification | Abstract min-heap specification                      |          |      |      |
| 5.6      | Example       | Type `BinaryTree`                                    |          |      |      |
| 5.6      | Example       | Function `treeToList`                                |          |      |      |
| 5.6      | Specification | `isBinaryTree`                                       |          |      |      |
| 5.6      | Example       | `isMeldHeapVal`                                      |          |      |      |
| 5.6      | Example       | `isMeldHeapRef`                                      |          |      |      |
| 5.6      | Example       | $\text{t}^\text{meld}$                               |          |      |      |
| 5.6      | Specification | `meld` specification                                 |          |      |      |
| 5.6      | Example       | $\text{tc}^\text{dist}$                              |          |      |      |
| 5.6      | Example       | Meldable heap abstract min-heap instance             |          |      |      |
| 5.7      | Example       | `repeatRemove`                                       |          |      |      |
| 5.7      | Example       | `merge`                                              |          |      |      |
| 5.7      | Example       | `isComp` instance for lists                          |          |      |      |
| 5.7      | Specification | `merge` specification                                |          |      |      |
| 5.7      | Example       | Composed $\mathcal{O}(n \log k)$ merge specification |          |      |      |
| 6        | Definition    | Hoare triple                                         |          |      |      |
| 6.1      | Definition    | Cost interpretation                                  |          |      |      |
| 6.1      | Definition    | Expected Cost modality                               |          |      |      |
| 6.1      | Definition    | Weakest precondition                                 |          |      |      |
| 6.1      | Definition    | Cost credit resource algebra                         |          |      |      |
| 6.1      | Rule          | Agreement Rule                                       |          |      |      |
| 6.1      | Rule          | Spending Rule                                        |          |      |      |
| 6.1      | Rule          | Acquirng Rule                                        |          |      |      |
| 6.2      | Theorem       | Adqeuacy (Weakest Preconditions)                     |          |      |      |


## ??
- Pg 4
  - HT-REC
  - HT-IF
  - HT-FLIP-EXP
- Pg 10. Note about HT-FRAME?

- Change names to RandML?
- Does the remark at the end of section 6 have a lemma?
