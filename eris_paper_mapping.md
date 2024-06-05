
## Reference from the paper to the code

Our contributions of the Eris logic can mostly be found in the folder [theories/eris/](theories/eris/).

| § | Kind       | Item                                   | Coq file                                                                        | Name                       | Note                                                                                     |
|---|------------|----------------------------------------|---------------------------------------------------------------------------------|----------------------------|------------------------------------------------------------------------------------------|
| 1 | Example    | Specification of List.iter with errors | [theories/eris/lib/list.v]                                                  | `wp_list_iter_err`        |                                                                                          |
|   | Rule       | $\text{\scriptsize HT-BIND-EXP}$       | [theories/eris/weakestpre.v]                                             | `pgl_wp_bind`               | We present a normal bind rule, which can be instantiated easily to include error credits |
| 2 | Definition | Subdistribution                                   | [theories/prob/distribution.v]                                                  | `distr`                    |                                                                                          |
|   | Definition | Probability monad                      | [theories/prob/distribution.v]                                                  | `dret_id_right`, etc       |                                                                                          |
|   | Definition | Probability of predicate               | [theories/prob/distribution.v]                                                  | `prob`                     |                                                                                          |
|   | Definition | Partial graded lifting                 | [theories/prob/graded_predicate_lifting.v]                                                  | `pgl`                  |                                                                                          |
|   | Definition | Total graded lifting                   | [theories/prob/graded_predicate_lifting.v]                                                  | `tgl`            |                                                                                          |
|   | Definition | $\lambda^\text{rand}_\text{ref}$       | [theories/prob_lang/lang.v]                                                     | Whole file                 |                                                                                          |
|   | Definition | step                                   | [theories/common/ectx_language.v]                                               | `prim_step`                |                                                                                          |
|   | Definition | $\text{exec}_n$                        | [theories/common/exec.v]                                                        | `exec`                     |                                                                                          |
|   | Definition | $\text{exec}$                          | [theories/common/exec.v]                                                        | `lim_exec_val`             |                                                                                          |
| 3 | Definition | iProp                                  | imported from [Iris upstream]                                                   | `iProp`                    |                                                                                          |
|   | Definition | Ownership of error credits             | [theories/eris/error_credits.v]                                             | `ec`                       |                                                                                          |
|   | Rule       | Splitting error credits                | [theories/eris/error_credits.v]                                             | `ec_split`                 |                                                                                          |
|   | Rule       | Decreasing error credits               | [theories/eris/error_credits.v]                                             | `ec_weaken`                |                                                                                          |
|   | Rule       | Deriving False from 1 error credit     | [theories/eris/error_credits.v]                                             | `ec_spend`                 |                                                                                          |
|   | Theorem    | Adequacy of Eris                       | [theories/eris/adequacy.v]                                                  | `wp_pgl_lim`       | Hoare triples are defined, the theorem follows directly from the definition and `wp_pgl_lim` |
|   | Rules      | Various rules of HeapLang              | [theories/eris/primitive_laws.v]                                            | `wp_load` etc.             |                                                                                          |
|   | Rule       | $\text{\scriptsize HT-RAND-ERR-LIST}$  | [theories/eris/error_rules.v]                                                  | `wp_rand_err_list_nat`     |                                                                                          |
|   | Rule       | $\text{\scriptsize HT-BIND-SIMPL}$     | [theories/eris/weakestpre.v]                                             | `pgl_wp_bind`               | We present a normal bind rule, which can be instantiated easily to include error credits |
|   | Rule       | $\text{\scriptsize RAND-EXP}$          | [theories/eris/error_rules.v]                                                  | `wp_couple_rand_adv_comp1` |                                                                                          |
|   | Example    | Synthetic example from Fig. 1          | [theories/eris/examples/eris_examples.v]                                               | Section `test`             |                                                                                          |
| 4 | Example    | Dynamic vectors under faulty allocator | [theories/eris/examples/dynamic_vec.v]                                               |                            |                                                                                          |
|   | Example    | Non-amortized non-resizing hash        | [theories/eris/examples/hash.v]                                                      | Section `simple_bit_hash`  |                                                                                          |
|   | Example    | Amortized non-resizing hash            | [theories/eris/examples/hash.v]                                                      | Section `amortized_hash`   |                                                                                          |
|   | Example    | Amortized resizing hash                | [theories/eris/examples/cf_hash.v]                                                   |                            |                                                                                          |
|   | Example    | Amortized resizing hash map            | [theories/eris/examples/cf_hashmap.v]                                                |                            |                                                                                          |
|   | Example    | Merkle trees                           | [theories/eris/examples/merkle/merkle_tree.v]                                        |                            |                                                                                          |
|   | Example    | Unreliable storage with merkle trees   | [theories/eris/examples/merkle/unreliable.v]                                         |                            |                                                                                          |
| 5 | Theorem    | Total adequacy of Eris<sub>t</sub>     | [theories/eris/total_adequacy.v]                                            | `twp_tgl`        |                                                                                          |
|   | Theorem    | Almost sure termination (AST)          | [theories/eris/total_adequacy.v]                                            | `twp_tgl_limit`  |                                                                                          |
|   | Example    | Rejection samplers                     | [theories/eris/examples/approximate_samplers/approx_higherorder_rejection_sampler.v] |                            |                                                                                          |
|   | Rule       | $\text{\scriptsize ALLOC-TAPE}$        | [theories/eris/primitive_laws.v]                                            | `wp_alloc_tape`            |                                                                                          |
|   | Rule       | $\text{\scriptsize LOAD-TAPE}$         | [theories/eris/primitive_laws.v]                                            | `wp_rand_tape`             |                                                                                          |
|   | Rule       | $\text{\scriptsize STORE-TAPE}$        | [theories/eris/error_rules.v]                                                  | `wp_presample`             |                                                                                          |
|   | Rule       | $\text{\scriptsize PRESAMPLE-EXP}$     | [theories/eris/error_rules.v]                                                  | `wp_presample_adv_comp`    |                                                                                          |
|   | Rule       | $\text{\scriptsize PRESAMPLE-PLANNER}$ | [theories/eris/error_rules.v]                                                  | `presample_planner`        |                                                                                          |
|   | Example    | WalkSAT                                | [theories/eris/examples/approximate_samplers/approx_walkSAT.v]                       |                            |                                                                                          |
| 6 | Definition | Weakest precondition predicate         | [theories/eris/weakestpre.v]                                             | `pgl_wp_pre`                |                                                                                          |
|   | Definition | Graded lifting modality, execUpTo      | [theories/eris/weakestpre.v]                                             | `glm_pre`              |                                                                                          |
|   | Rule       | $\text{\scriptsize UPTO-PRIM}$         | [theories/eris/weakestpre.v]                                             | `glm_prim_step`        |                                                                                          |
|   | Rule       | $\text{\scriptsize UPTO-EXP}$          | [theories/eris/weakestpre.v]                                             | `glm_adv_comp`         |                                                                                          |
|   | Theorem    | Limit WP adequacy                      | [theories/eris/adequacy.v]                                                  | `wp_union_bound_lim`       |                                                                                          |
	
	
	
[theories/eris/lib/list.v]: theories/eris/lib/list.v
[theories/eris/weakestpre.v]: theories/eris/weakestpre.v 
[theories/prob/distribution.v]: theories/prob/distribution.v 
[theories/prob/graded_predicate_lifting.v]: theories/prob/graded_predicate_lifting.v 
[theories/prob_lang/lang.v]: theories/prob_lang/lang.v
[theories/common/ectx_language.v]: theories/common/ectx_language.v
[theories/common/exec.v]: theories/common/exec.v
[theories/eris/error_credits.v]: theories/eris/error_credits.v
[theories/eris/adequacy.v]: theories/eris/adequacy.v
[theories/eris/primitive_laws.v]: theories/eris/primitive_laws.v
[theories/eris/error_rules.v]: theories/eris/error_rules.v
[theories/eris/examples/eris_examples.v]: theories/eris/examples/eris_examples.v
[theories/eris/examples/dynamic_vec.v]: theories/eris/examples/dynamic_vec.v
[theories/eris/examples/hash.v]: theories/eris/examples/hash.v
[theories/eris/examples/cf_hash.v]: theories/eris/examples/cf_hash.v
[theories/eris/examples/cf_hashmap.v]: theories/eris/examples/cf_hashmap.v
[theories/eris/examples/merkle/merkle_tree.v]: theories/eris/examples/merkle/merkle_tree.v
[theories/eris/examples/merkle/unreliable.v]: theories/eris/examples/merkle/unreliable.v
[theories/eris/total_adequacy.v]: theories/eris/total_adequacy.v
[theories/eris/examples/approximate_samplers/approx_walkSAT.v]: theories/eris/examples/approximate_samplers/approx_walkSAT.v
[theories/eris/examples/approximate_samplers/approx_higherorder_rejection_sampler.v]: theories/eris/examples/approximate_samplers/approx_higherorder_rejection_sampler.v




[iris upstream]: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/iprop.v
