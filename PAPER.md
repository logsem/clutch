# Paper mapping

| § | Item                        | File                                    | Name                                                                                          |
|---|-----------------------------|-----------------------------------------|-----------------------------------------------------------------------------------------------|
| 1 | fix                         | [caliper/examples/nat_random_walk.v]    | `myrec`                                                                                       |
|   | F                           | [caliper/examples/nat_random_walk.v]    | `F`                                                                                           |
|   | Symmetric random walk       | [caliper/examples/nat_random_walk.v]    | `nat_random_walk`                                                                             |
| 2 | Def. 2.1                    | [prob/distribution.v]                   | `distr`                                                                                       |
|   | Def. 2.2                    | -                                       | n/a                                                                                           |
|   | Lem. 2.3                    | [prob/distribution.v]                   | `dbind`, `dret`,`dret_id_right`, `dret_id_left`,`dbind_assoc`, `dbind_comm`, ...              |
|   | Def. 2.4                    | [prob/markov.v]                         | `markov`                                                                                      |
|   | $exec_n$                    | [prob/markov.v]                         | `exec`                                                                                        |
|   | $exec$                      | [prob/markov.v]                         | `lim_exec`                                                                                    |
|   | Lem. 2.5                    | [prob/markov.v]                         | `lim_exec_leq_mass`                                                                           |
|   | ProbLang                    | [prob_lang/lang.v]                      | `expr`, `val`, `ectx_item`, `state`, `head_step`                                              |
| 2 | Def. 2.6                    | [prob/couplings.v]                      | `refRcoupl`                                                                                   |
|   | Lem. 2.7                    | [prob/couplings.v]                      | `refRcoupl_eq_elim`                                                                           |
|   | Lem. 2.8                    | [prob/couplings.v]                      | `refRcoupl_mass_eq`                                                                           |
| 3 | RWP-PURE                    | [caliper/lifting.v]                     | `rwp_pure_step`                                                                               |
|   | RWP-ALLOC                   | [caliper/primitive_laws.v]              | `rwp_alloc` [*]                                                                               |
|   | RWP-LOAD                    | [caliper/primitive_laws.v]              | `rwp_load` [*]                                                                                |
|   | RWP-STORE                   | [caliper/primitive_laws.v]              | `rwp_store` [*]                                                                               |
|   | RWP-RAND                    | [caliper/primitive_laws.v]              | `rwp_rand` [*]                                                                                |
|   | RWP-VAL                     | [caliper/weakestpre.v]                  | `rwp_value`                                                                                   |
|   | RWP-BIND                    | [caliper/weakestpre.v]                  | `rwp_bind`                                                                                    |
|   | RWP-MONO                    | [caliper/weakestpre.v]                  | `rwp_mono`                                                                                    |
|   | RWP-FRAME                   | [caliper/weakestpre.v]                  | `rwp_frame_l`                                                                                 |
|   | Thm. 3.1                    | [caliper/adequacy.v]                    | `rwp_soundness_mass`                                                                          |
|   | Fig. 2, Löb                 | Iris                                    |                                                                                               |
|   | RWP-SPEC-DET                | [caliper/derived_laws.v]                | `rwp_spec_det`                                                                                |
|   | RWP-COUPL-RAND              | [caliper/derived_laws.v]                | `rwp_coupl_rand`                                                                              |
| 4 | cpl                         | [caliper/weakestpre.v]                  | `rwp_coupl`                                                                                   |
|   | rwp                         | [caliper/weakestpre.v]                  | `rwp_def`                                                                                     |
|   | Plain g. refinement         | [caliper/adequacy.v]                    | `refines`                                                                                     |
|   | Lem. 4.1                    | [caliper/adequacy.v]                    | `rwp_refines`                                                                                 |
|   | Lem. 4.2                    | [prob/couplings.v]                      | `refRcoupl_dret`, `refRcoupl_dbind`                                                           |
|   | Lem. 4.3                    | [caliper/adequacy.v]                    | `refines_soundness_laterN` [**]                                                               |
|   | Thm. 4.4                    | Iris                                    | `laterN_soundness`                                                                            |
|   | Cor. 4.5                    | [caliper/adequacy.v]                    | `refines_soundness`                                                                           |
|   | Cor. 4.6                    | [caliper/adequacy.v]                    | `rwp_soundness`                                                                               |
| 5 | RWP-TAPE-ALLOC              | [caliper/primitive_laws.v]              | `rwp_alloc_tape` [*]                                                                          |
|   | RWP-TAPE-EMPTY              | [caliper/primitive_laws.v]              | `rwp_rand_tape_empty` [*]                                                                     |
|   | RWP-TAPE                    | [caliper/primitive_laws.v]              | `rwp_rand_tape` [*]                                                                           |
|   | Lem. 5.1                    | [caliper/prob_lang/erasure.v]           | `lim_exec_eq_erasure`                                                                         |
| 6 | Repeated Coin Flips         | [caliper/examples/coin_random_walk.v]   | `random_walk`, `rwp_coin_flips`                                                               |
|   | Recursion Through the Store | [caliper/examples/nat_random_walk.v]    | `nat_random_walk`, `wp_myrec`, `wp_nat_rw`                                                    |
|   | List Generators             | [caliper/examples/listgen.v]            | `random_walk_nested`, `wp_listgen_flip`, `wp_listgen_list_bool`                               |
|   | Lazy Real                   | [caliper/examples/lazy_real.v]          | `two_coins`, `cmps`, `lazy_no`, `rwp_init`, `rwp_cmp`                                         |
|   | Treap                       | [caliper/examples/treap.v]              | `is_treap`, `wp_insert`                                                                       |
|   | Stack                       | [caliper/examples/lib/list.v]           | `is_queue`, `queue`, `wp_queue_create`, `wp_queue_add`, `wp_queue_take_0`, `wp_queue_take_Sn_ |
|   | Galton-Watson Tree          | [caliper/examples/galton_watson_tree.v] | `gwp`, `gen_tree`, `wp_gen_tree` [***], `task_spec`, `task_queue`, `wp_run` [***]             |

[*] Written in "Texan triple" style for convenience. See notation in [bi/weakestpre.v].

[**] The statement contains an extra `except_0` and `later` modality. C.f. the discussion at the top of `caliper/adequacy.v`, this is an irrelevant technicality of  Iris's definition of the "fancy update modality" that we have omitted from the paper.

[***] The statement and proof makes use of Iris's so-called "non-atomic" invariants. We have aux. notation for working with these defined in `caliper/seq_weakestpre.v`.
