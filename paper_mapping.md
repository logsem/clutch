## Reference from the paper to the code

| §   | Kind                | Item                                      | Coq file                                                               | Name                                                 | Note                                                     |
|-----|---------------------|-------------------------------------------|------------------------------------------------------------------------|------------------------------------------------------|----------------------------------------------------------|
| 2.1 | Rule                | ``ERR-SPLIT``                             | [theories/base_logic/error_credits.v]                                  | `ec_combine`                                         |                                                          |
| 2.1 | Rule                | `HT-RAND-EXP`                             | [theories/coneris/error_rules.v]                                       | `wp_couple_rand_adv_comp1'`                          |                                                          |
| 2.1 | Rule                | `ERR-1`                                   | [theories/base_logic/error_credits.v]                                  | `ec_contradict`                                      |                                                          |
| 2.1 | Example             | `conTwoAdd`                               | [theories/coneris/examples/con_two_add.v]                              | `two_add_prog'`                                      |                                                          |
| 2.1 | Rule                | `HT-PAR-COMP`                             | [theories/coneris/lib/par.v]                                           | `wp_par`                                             |                                                          |
| 2.1 | Rule                | `HT-INV-ALLOC`                            | Imported from [Iris invariant]                                         | `inv_alloc`                                          |                                                          |
| 2.1 | Rule                | `INV-DUP`                                 | Imported from [Iris invariant]                                         | `inv_persistent`                                     |                                                          |
| 2.1 | Rule                | `HT-INV-OPEN`                             | Imported from [Iris invariant]                                         | Derived from `inv_acc`                               |                                                          |
| 2.1 | Example             | Fig 2                                     | [theories/coneris/examples/random_counter/impl1.v]                     | `new_counter1` etc.                                  |                                                          |
| 3.1 | Definition          | Discrete subdistribution                  | [theories/prob/distribution.v]                                         | `distr`                                              |                                                          |
| 3.1 | Definition          | Discrete distribution monad               | [theories/prob/distribution.v]                                         | `dbind`, `dret`, etc                                 |                                                          |
| 3.2 | Definition          | `ConcRandML`                              | [theories/con_prob_lang/lang.v]                                        | Whole file                                           |                                                          |
| 3.3 | Definition          | `step`                                    | [theories/common/ectx_language.v]                                      | `prim_step`                                          |                                                          |
| 3.3 | Definition          | `schStep`                                 | [theories/prob/mdp.v]                                                  | `sch_step`                                           |                                                          |
| 3.3 | Definition          | `exec`                                    | [theories/prob/mdp.v]                                                  | `sch_exec` and `sch_lim_exec`                        |                                                          |
| 3.3 | Definition          | `pexec`                                   | [theories/prob/mdp.v]                                                  | `sch_pexec`                                          |                                                          |
| 4.1 | Definition          | `iProp`                                   | Imported from [Iris iprop]                                             | `iProp`                                              |                                                          |
| 4.1 | Theorem             | `Adequacy`                                | [theories/coneris/adequacy.v]                                          | `wp_pgl_lim`                                         |                                                          |
| 4.1 | Theorem             | `Safety`                                  | [theories/coneris/adequacy.v]                                          | `wp_safety`                                          |                                                          |
| 4.2 | Rule                | `HT-BIND`                                 | [theories/coneris/weakestpre.v]                                        | `pgl_wp_bind`                                        |                                                          |
| 4.2 | Rule                | `HT-FRAME`                                | [theories/coneris/weakestpre.v]                                        | Derivable from `pgl_wp_frame_l` and `pgl_wp_frame_r` |                                                          |
| 4.2 | Rule                | `HT-LOAD`                                 | [theories/coneris/primitive_laws.v]                                    | `wp_load`                                            |                                                          |
| 4.2 | Rule                | `HT-INV-ALLOC`                            |                                                                        |                                                      | See previously from Sec 2.1                              |
| 4.2 | Rule                | `HT-INV-OPEN`                             |                                                                        |                                                      | See previously from Sec 2.1                              |
| 4.2 | Rule                | `INV-OPEN`                                | Imported from [Iris invariant]                                         | `inv_acc`                                            |                                                          |
| 4.2 | Rule                | `HT-FUPD-ELIM`                            | [theories/coneris/weakestpre.v]                                        | `elim_modal_fupd_pgl_wp_atomic`                      |                                                          |
| 4.2 | Various Definitions | Tapes                                     |                                                                        |                                                      | See previously in the language and operational semantics |
| 4.2 | Rule                | `HT-ALLOC-TAPE`                           | [theories/coneris/primitive_laws.v]                                    | `wp_alloc_tape`                                      |                                                          |
| 4.2 | Rule                | `HT-RAND-TAPE`                            | [theories/coneris/primitive_laws.v]                                    | `wp_rand_tape`                                       |                                                          |
| 4.2 | Rule                | `PUPD-RET`                                | [theories/coneris/wp_update.v]                                         | `state_update_ret`                                   |                                                          |
| 4.2 | Rule                | `PUPD-BIND`                               | [theories/coneris/wp_update.v]                                         | `state_update_bind`                                  |                                                          |
| 4.2 | Rule                | `PUPD-FUPD`                               | [theories/coneris/wp_update.v]                                         | Derived from `state_update_fupd_change`              |                                                          |
| 4.2 | Rule                | `PUPD-PRESAMPLE-EXP`                      | [theories/coneris/error_rules.v]                                       | `state_update_presample_exp`                         |                                                          |
| 4.2 | Rule                | `PUPD-ERR`                                | [theories/coneris/wp_update.v]                                         | `state_update_epsilon_err`                           |                                                          |
| 5.1 | Example             | Fig 4                                     | [theories/coneris/examples/random_counter3/random_counter.v]           | Whole file                                           |                                                          |
| 5.1 | Example             | Fig 5                                     | [theories/coneris/examples/random_counter/random_counter.v]            | Whole file                                           |                                                          |
| 5.2 | Example             | `conTwoAdd` with tapes                    | [theories/coneris/examples/random_counter/client.v]                    | Whole file                                           |                                                          |
| 5.2 | Example             | `twoIncr`                                 | [theories/coneris/examples/random_counter/client2.v]                   | Whole file                                           |                                                          |
| 5.3 | Example             | First implementation of random counter    | [theories/coneris/examples/random_counter/impl1.v]                     | Whole file                                           |                                                          |
| 5.3 | Example             | Second implementation of random counter   | [theories/coneris/examples/random_counter/impl2.v]                     | Whole file                                           |                                                          |
| 5.3 | Example             | Third implementation of random counter    | [theories/coneris/examples/random_counter/impl3.v]                     | Whole file                                           |                                                          |
| 6.1 | Example             | Thread-safe hash functions specification  | [theories/coneris/examples/hash/con_hash_interface4.v]                 | Whole file                                           |                                                          |
| 6.1 | Example             | Thread-safe hash functions implementation | [theories/coneris/examples/hash/con_hash_impl4.v]                      | Whole file                                           |                                                          |
| 6.2 | Example             | Bloom filter                              | [theories/coneris/examples/bloom_filter/concurrent_bloom_filter_alt.v] | Whole file                                           |                                                          |
| 6.3 | Example             | Lazy random sampler specification         | [theories/coneris/examples/lazy_rand/lazy_rand_interface.v]            | Whole file                                           |                                                          |
| 6.3 | Example             | Lazy random sampler implementation        | [theories/coneris/examples/lazy_rand/lazy_rand_impl.v]                 | Whole file                                           |                                                          |
| 6.3 | Example             | `lazyRace`                                | [theories/coneris/examples/lazy_rand/lazy_rand_race.v]                 | Whole file                                           |                                                          |
| 6.4 | Examples            | Other case studies                        |                                                                        |                                                      | See [theories/coneris/README.md]                         |
| 7.1 | Definition          | Weakest precondition                      | [theories/coneris/weakestpre.v]                                        | `pgl_wp_def`                                         |                                                          |
| 7.1 | Definition          | State step precondition                   | [theories/coneris/weakestpre.v]                                        | `state_step_coupl`                                   |                                                          |
| 7.1 | Definition          | Program step precondition                 | [theories/coneris/weakestpre.v]                                        | `prog_coupl`                                         |                                                          |
| 7.1 | Definition          | `schErasable`                             | [theories/common/sch_erasable.v]                                       | `sch_erasable`                                       |                                                          |
| 7.1 | Definition          | Probabilistic update modality             | [theories/coneris/wp_update.v]                                         | `state_update`                                       |                                                          |
| 7.2 | Lemma               | `Adequacy simplified`                     | [theories/coneris/adequacy.v]                                          | `wp_pgl_multi`                                       |                                                          |
	



[theories/base_logic/error_credits.v]: theories/base_logic/error_credits.v
[theories/prob/distribution.v]: theories/prob/distribution.v
[theories/con_prob_lang/lang.v]: theories/con_prob_lang/lang.v
[theories/common/ectx_language.v]: theories/common/ectx_language.v
[theories/common/sch_erasable.v]: theories/common/sch_erasable.v
[theories/prob/mdp.v]: theories/prob/mdp.v
[theories/coneris/error_rules.v]: theories/coneris/error_rules.v
[theories/coneris/weakestpre.v]: theories/coneris/weakestpre.v
[theories/coneris/primitive_laws.v]: theories/coneris/primitive_laws.v
[theories/coneris/wp_update.v]: theories/coneris/wp_update.v
[theories/coneris/adequacy.v]: theories/coneris/adequacy.v
[theories/coneris/lib/par.v]: theories/coneris/lib/par.v
[theories/coneris/examples/con_two_add.v]: theories/coneris/examples/con_two_add.v
[theories/coneris/examples/random_counter/random_counter.v]: theories/coneris/examples/random_counter/random_counter.v
[theories/coneris/examples/random_counter3/random_counter.v]: theories/coneris/examples/random_counter3/random_counter.v
[theories/coneris/examples/random_counter/impl1.v]: theories/coneris/examples/random_counter/impl1.v
[theories/coneris/examples/random_counter/impl2.v]: theories/coneris/examples/random_counter/impl2.v
[theories/coneris/examples/random_counter/impl3.v]: theories/coneris/examples/random_counter/impl3.v
[theories/coneris/examples/random_counter/client.v]: theories/coneris/examples/random_counter/client.v
[theories/coneris/examples/random_counter/client2.v]: theories/coneris/examples/random_counter/client2.v
[theories/coneris/examples/hash/con_hash_interface4.v]: theories/coneris/examples/hash/con_hash_interface4.v
[theories/coneris/examples/hash/con_hash_impl4.v]: theories/coneris/examples/hash/con_hash_impl4.v
[theories/coneris/examples/bloom_filter/concurrent_bloom_filter_alt.v]: theories/coneris/examples/bloom_filter/concurrent_bloom_filter_alt.v
[theories/coneris/examples/lazy_rand/lazy_rand_interface.v]: theories/coneris/examples/lazy_rand/lazy_rand_interface.v
[theories/coneris/examples/lazy_rand/lazy_rand_impl.v]: theories/coneris/examples/lazy_rand/lazy_rand_impl.v
[theories/coneris/examples/lazy_rand/lazy_rand_race.v]: theories/coneris/examples/lazy_rand/lazy_rand_race.v
[theories/coneris/README.md]: theories/coneris/README.md


[Iris iprop]: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/iprop.v
[Iris invariant]: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/invariants.v
