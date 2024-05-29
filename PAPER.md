# Paper mapping

| § | Item                        | File                   | Name                                                                                          |
|---|-----------------------------|------------------------|-----------------------------------------------------------------------------------------------|
| 1 | fix                         | [nat_random_walk.v]    | `myrec`                                                                                       |
|   | F                           | [nat_random_walk.v]    | `F`                                                                                           |
|   | Symmetric random walk       | [nat_random_walk.v]    | `nat_random_walk`                                                                             |
| 2 | Def. 2.1                    | [distribution.v]       | `distr`                                                                                       |
|   | Def. 2.2                    | -                      | n/a                                                                                           |
|   | Lem. 2.3                    | [distribution.v]       | `dbind`, `dret`,`dret_id_right`, `dbind_assoc`, ...                                           |
|   | Def. 2.4                    | [markov.v]             | `markov`                                                                                      |
|   | $exec_n$                    | [markov.v]             | `exec`                                                                                        |
|   | $exec$                      | [markov.v]             | `lim_exec`                                                                                    |
|   | Lem. 2.5                    | [markov.v]             | `lim_exec_leq_mass`                                                                           |
|   | ProbLang                    | [lang.v]               | `expr`, `val`, `ectx_item`, `state`, `head_step`                                              |
| 2 | Def. 2.6                    | [couplings.v]          | `refRcoupl`                                                                                   |
|   | Lem. 2.7                    | [couplings.v]          | `refRcoupl_eq_elim`                                                                           |
|   | Lem. 2.8                    | [couplings.v]          | `refRcoupl_mass_eq`                                                                           |
| 3 | RWP-PURE                    | [lifting.v]            | `rwp_pure_step`                                                                               |
|   | RWP-ALLOC                   | [primitive_laws.v]     | `rwp_alloc` [1]                                                                               |
|   | RWP-LOAD                    | [primitive_laws.v]     | `rwp_load` [1]                                                                                |
|   | RWP-STORE                   | [primitive_laws.v]     | `rwp_store` [1]                                                                               |
|   | RWP-RAND                    | [primitive_laws.v]     | `rwp_rand` [1]                                                                                |
|   | RWP-VAL                     | [weakestpre.v]         | `rwp_value`                                                                                   |
|   | RWP-BIND                    | [weakestpre.v]         | `rwp_bind`                                                                                    |
|   | RWP-MONO                    | [weakestpre.v]         | `rwp_mono`                                                                                    |
|   | RWP-FRAME                   | [weakestpre.v]         | `rwp_frame_l`                                                                                 |
|   | Thm. 3.1                    | [adequacy.v]           | `rwp_soundness_mass`                                                                          |
|   | Fig. 2, Löb                 | Iris                   |                                                                                               |
|   | RWP-SPEC-DET                | [derived_laws.v]       | `rwp_spec_det`                                                                                |
|   | RWP-COUPL-RAND              | [derived_laws.v]       | `rwp_coupl_rand`                                                                              |
| 4 | cpl                         | [weakestpre.v]         | `rwp_coupl`                                                                                   |
|   | rwp                         | [weakestpre.v]         | `rwp_def`                                                                                     |
|   | Plain guarded refinement    | [adequacy.v]           | `refines`                                                                                     |
|   | Lem. 4.1                    | [adequacy.v]           | `rwp_refines`                                                                                 |
|   | Lem. 4.2                    | [couplings.v]          | `refRcoupl_dret`, `refRcoupl_dbind`                                                           |
|   | Lem. 4.3                    | [adequacy.v]           | `refines_soundness_laterN` [2]                                                                |
|   | Thm. 4.4                    | Iris                   | `laterN_soundness`                                                                            |
|   | Cor. 4.5                    | [adequacy.v]           | `refines_soundness`                                                                           |
|   | Cor. 4.6                    | [adequacy.v]           | `rwp_soundness`                                                                               |
| 5 | RWP-TAPE-ALLOC              | [primitive_laws.v]     | `rwp_alloc_tape` [1]                                                                          |
|   | RWP-TAPE-EMPTY              | [primitive_laws.v]     | `rwp_rand_tape_empty` [1]                                                                     |
|   | RWP-TAPE                    | [primitive_laws.v]     | `rwp_rand_tape` [1]                                                                           |
|   | Lem. 5.1                    | [erasure.v]            | `lim_exec_eq_erasure`                                                                         |
| 6 | Repeated Coin Flips         | [coin_random_walk.v]   | `random_walk`, `rwp_coin_flips`                                                               |
|   | Recursion Through the Store | [nat_random_walk.v]    | `nat_random_walk`, `wp_myrec`, `wp_nat_rw`                                                    |
|   | List Generators             | [listgen.v]            | `random_walk_nested`, `wp_listgen_flip`, `wp_listgen_list_bool`                               |
|   | Lazy Real                   | [lazy_real.v]          | `two_coins`, `cmps`, `lazy_no`, `rwp_init`, `rwp_cmp`                                         |
|   | Treap                       | [treap.v]              | `is_treap`, `wp_insert`                                                                       |
|   | Stack                       | [list.v]               | `is_queue`, `queue`, `wp_queue_create`, `wp_queue_add`, `wp_queue_take_0`, `wp_queue_take_Sn` |
|   | Galton-Watson Tree          | [galton_watson_tree.v] | `gwp`, `gen_tree`, `wp_gen_tree` [3], `task_spec`, `task_queue`, `wp_run` [3]                 |

[1] Written in "Texan triple" style for convenience. See notation in [bi/weakestpre.v].

[2] The statement contains an extra `except_0` and `later` modality. C.f. the discussion at the top of [adequacy.v], this is an mostly irrelevant technicality of Iris' definition of the "fancy update modality" which we omit from the paper.

[3] The statement and proof make use of Iris' so-called "non-atomic" invariants. We have aux. notation for working with these defined in [seq_weakestpre.v].

[nat_random_walk.v]: theories/caliper/examples/nat_random_walk.v
[distribution.v]: theories/prob/distribution.v
[markov.v]: theories/prob/markov.v
[lang.v]: theories/prob_lang/lang.v
[couplings.v]: theories/prob/couplings.v
[lifting.v]: theories/caliper/lifting.v
[primitive_laws.v]: theories/caliper/primitive_laws.v
[weakestpre.v]: theories/caliper/weakestpre.v
[adequacy.v]: theories/caliper/adequacy.v
[derived_laws.v]: theories/caliper/derived_laws.v
[couplings.v]: theories/prob/couplings.v
[erasure.v]: theories/prob_lang/erasure.v
[coin_random_walk.v]: theories/caliper/examples/coin_random_walk.v
[nat_random_walk.v]: theories/caliper/examples/nat_random_walk.v
[listgen.v]: theories/caliper/examples/listgen.v
[lazy_real.v]: theories/caliper/examples/lazy_real.v
[treap.v]: theories/caliper/examples/treap.v
[list.v]: theories/caliper/examples/lib/list.v
[galton_watson_tree.v]: theories/caliper/examples/galton_watson_tree.v
[seq_weakestpre.v]: theories/caliper/seq_weakestpre.v
[bi/weakestpre.v]: theories/bi/weakestpre.v
