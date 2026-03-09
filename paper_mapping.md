## Reference from the paper to the code

| §   | Kind                | Item                          | Coq file                                                | Name                                                 | Note                                                                |
|-----|---------------------|-------------------------------|---------------------------------------------------------|------------------------------------------------------|---------------------------------------------------------------------|
| 1.1 | Example             | `fImpl` and `fSpec`           |                                                         |                                                      | This is a specific instance of `batchImpl` and `batchSpec` from 3.3 |
| 2.1 | Definition          | Discrete subdistribution      | [theories/prob/distribution.v]                          | `distr`                                              |                                                                     |
| 2.1 | Definition          | Discrete distribution monad   | [theories/prob/distribution.v]                          | `dbind`, `dret`, etc                                 |                                                                     |
| 2.1 | Definition          | Null distribution             | [theories/prob/distribution.v]                          | `dzero`                                              |                                                                     |
| 2.1 | Definition          | Uniform distribution          | [theories/prob/distribution.v]                          | `dunif`                                              |                                                                     |
| 2.1 | Definition          | Expected value                | [theories/prob/distribution.v]                          | `Expval`                                             |                                                                     |
| 2.1 | Definition          | Approximate coupling          | [theories/prob/couplings_app.v]                         | `ARcoupl`                                            |                                                                     |
| 2.2 | Definition          | `ConcRandML`                  | [theories/con_prob_lang/lang.v]                         | Whole file                                           |                                                                     |
| 2.3 | Definition          | `step`                        | [theories/common/ectx_language.v]                       | `prim_step`                                          |                                                                     |
| 2.3 | Definition          | `schStep`                     | [theories/prob/mdp.v]                                   | `sch_step`                                           |                                                                     |
| 2.3 | Definition          | `exec`                        | [theories/prob/mdp.v]                                   | `sch_exec` and `sch_lim_exec`                        |                                                                     |
| 2.3 | Definition          | `pexec`                       | [theories/prob/mdp.v]                                   | `sch_pexec`                                          |                                                                     |
| 2.4 | Definition          | Contextual refinement         | [theories/con_prob_lang/typing/contextual_refinement.v] | `ctx_refines`                                        |                                                                     |
| 3   | Definition          | `iProp`                       | Imported from [Iris iprop]                              | `iProp`                                              |                                                                     |
| 3   | Theorem             | Adequacy                      | [theories/foxtrot/adequacy.v]                           | `foxtrot_adequacy`                                   |                                                                     |
| 3.1 | Definition          | Refinement judgment           | [theories/foxtrot/binary_rel/binary_model.v]            | `refines`                                            |                                                                     |
| 3.1 | Lemma               | Fundamental Lemma of Bin LR   | [theories/foxtrot/binary_rel/binary_fundamental.v]      | `fundamental`                                        |                                                                     |
| 3.1 | Lemma               | Soundness                     | [theories/foxtrot/binary_rel/binary_soundness.v]        | `refines_sound`                                      |                                                                     |
| 3.1 | Definition          | Unary LR                      | [theories/foxtrot/unary_rel/unary_model.v]              | `refines`                                            |                                                                     |
| 3.1 | Lemma               | Fundamental Lemma of Un LR    | [theories/foxtrot/unary_rel/unary_fundamental.v]        | `fundamental`                                        |                                                                     |
| 3.2 | Rule                | `HT-BIND`                     | [theories/foxtrot/weakestpre.v]                         | `wp_bind`                                            |                                                                     |
| 3.2 | Rule                | `HT-FRAME`                    | [theories/foxtrot/weakestpre.v]                         | Derivable from `wp_frame_l` and `wp_frame_r`         |                                                                     |
| 3.2 | Rule                | `HT-LOAD`                     | [theories/foxtrot/primitive_laws.v]                     | `wp_load`                                            |                                                                     |
| 3.2 | Rule                | `HT-FORK`                     | [theories/foxtrot/primitive_laws.v]                     | `wp_fork`                                            |                                                                     |
| 3.2 | Rule                | `HT-INV-ALLOC`                | Imported from [Iris invariant]                          | `inv_alloc`                                          |                                                                     |
| 3.2 | Rule                | `HT-INV-OPEN`                 | Imported from [Iris invariant]                          | Derived from`inv_acc`                                |                                                                     |
| 3.2 | Rule                | `HT-PAR-COMP`                 | [theories/foxtrot/lib/par.v]                            | `wp_par`                                             |                                                                     |
| 3.2 | Definition          | Probabilistic Update Modality | [theories/foxtrot/pupd.v]                               | `pupd`                                               |                                                                     |
| 3.2 | Rule                | `PUPD-RET`                    | [theories/foxtrot/pupd.v]                               | `pupd_ret`                                           |                                                                     |
| 3.2 | Rule                | `PUPD-BIND`                   | [theories/foxtrot/pupd.v]                               | `pupd_bind`                                          |                                                                     |
| 3.2 | Rule                | `HT-PUPD-ELIM`                | [theories/foxtrot/pupd.v]                               | `elim_modal_pupd_wp'                                 |                                                                     |
| 3.2 | Rule                | `PUPD-LOAD`                   | [theories/foxtrot/primitive_laws.v]                     | `pupd_load`                                          |                                                                     |
| 3.2 | Rule                | `PUPD-FORK`                   | [theories/foxtrot/primitive_laws.v]                     | `pupd_fork`                                          |                                                                     |
| 3.2 | Rule                | `PUPD-PAR-COMP`               | [theories/foxtrot/lib/par.v]                            | `tp_par`                                             |                                                                     |
| 3.2 | Rule                | `HT-COUPLE`                   | [theories/foxtrot/couplings_rules.v]                    | `wp_couple_rand_rand`                                |                                                                     |
| 3.2 | Example             | Entropy mixer                 | [theories/foxtrot/examples/entropy_mixer.v]             | Whole file                                           |                                                                     |
| 3.3 | Example             | Batch sampling                | [theories/foxtrot/examples/batch_sampling.v]            | Whole file                                           |                                                                     |
| 3.3 | Definition          | Tapes                         |                                                         |                                                      | See `ConcRandML`                                                    |
| 3.3 | Rule                | `HT-ALLOC-TAPE`               | [theories/foxtrot/primitive_laws.v]                     | `wp_alloc_tape`                                      |                                                                     |
| 3.3 | Rule                | `PUPD-ALLOC-TAPE`             | [theories/foxtrot/primitive_laws.v]                     | `pupd_alloc_tape`                                    |                                                                     |
| 3.3 | Rule                | `HT-RAND-TAPE`                | [theories/foxtrot/primitive_laws.v]                     | `wp_rand_tape`                                       |                                                                     |
| 3.3 | Example             | Paradox of presampling on RHS | [theories/foxtrot/examples/presample_rhs.v]             | Whole file                                           |                                                                     |
| 3.3 | Rule                | `HT-COUPLE-RAND-LBL`          | [theories/foxtrot/coupling_rules.v]                     | `wp_couple_rand_rand_lbl`                            |                                                                     |
| 3.3 | Rule                | `PUPD-cOUPLE-LBL-RAND`        | [theories/foxtrot/coupling_rules.v]                     | `pupd_couple_tape_rand`                              |                                                                     |
| 3.3 | Rule                | `PUPD-COUPLE-TWO-RANDS-RAND`  | [theories/foxtrot/coupling_rules.v]                     | `pupd_couple_two_tapes_rand`                         |                                                                     |
| 3.3 | Rule                | `HT-COUPLE-RAND-TWO-RANDS`    | [theories/foxtrot/coupling_rules.v]                     | `wp_couple_rand_two_rands`                           |                                                                     |
| 3.3 | Example             | Rejection Sampler             | [theories/foxtrot/examples/rejection_samplers.v]        | Whole file                                           |                                                                     |
| 3.3 | Rule                | `HT-COUPLE_FRAGMENTED`        | [theories/foxtrot/coupling_rules.v]                     | `wp_couple_fragmented_rand_rand_inj`                 |                                                                     |
| 3.3 | Rule                | `ERR-SPLIT`                   | [theories/base_logic/error_credits.v]                   | `ec_combine`                                         |                                                                     |
| 3.3 | Rule                | `ERR-1`                       | [theories/base_logic/error_credits.v]                   | `ec_contradict`                                      |                                                                     |
| 3.3 | Rule                | `PUPD-ERR`                    | [theories/foxtrot/primitive_laws.v]                     | `pupd_epsilon_err`                                   |                                                                     |
| 3.3 | Rule                | `IND-ERR-AMP`                 | [theories/base_logic/error_credits.v]                   | `ec_ind_simpl`                                       |                                                                     |
| 3.3 | Rule                | `PUPD-COUPLE-FRAGMENTED`      | [theories/foxtrot/coupling_rules.v]                     | `pupd_couple_fragmented_tape_rand_inj_rev'`          |                                                                     |
| 4.1 | Example             | Adversarial von Neumann Coin  | [theories/foxtrot/examples/von_neumann.v]               | Whole file                                           |                                                                     |
| 4.2 | Example             | Sodium sampling               | [theories/foxtrot/examples/libsodium.v]                 | Whole file                                           |                                                                     |
| 4.3 | Example             | Aguirre and Birkedal Example  | [theories/foxtrot/examples/nodet_example.v]             | Whole file                                           |                                                                     |
| 4.3 | Example             | Concurrent one-time pad       | [theories/foxtrot/examples/encryption.v]                | Whole file                                           |                                                                     |
| 4.3 | Example             | Algebraic theory              | [theories/foxtrot/examples/algebraic.v]                 | Whole file                                           |                                                                     |
| 5.1 | Definition          | FIsch                         | [theories/foxtrot/full_info.v]                          | `full_info_oscheduler`                               |                                                                     |
| 5.1 | Definition          | FItpStep                      | [theories/foxtrot/oscheduler.v]                         | `step'`                                              |                                                                     |
| 5.1 | Definition          | FIschStep                     | [theories/foxtrot/oscheduler.v]                         | `osch_step_or_none`                                  |                                                                     |
| 5.1 | Definition          | FIexec                        | [theories/foxtrot/oscheduler.v]                         | `osch_exec` and `osch_lim_exec`                      |                                                                     |
| 5.1 | Lemma               | Lemma 5.1                     | [theories/foxtrot/oscheduler.v]                         | `osch_to_sch`                                        |                                                                     |
| 5.1 | Lemma               | Lemma 5.2                     | [theories/foxtrot/full_info.v]                          | `full_info_lift_osch_lim_exec`                       |                                                                     |
| 5.1 | Lemma               | Lemma 5.3                     | [theories/foxtrot/full_info.v]                          | `full_info_append_osch_lim_exec`                     |                                                                     |
| 5.2 | Definition          | Weakest precondition          | [theories/foxtrot/weakestpre.v]                         | `wp_def`                                             |                                                                     |
| 5.2 | Definition          | Spec-coupling precondition    | [theories/foxtrot/weakestpre.v]                         | `spec_coupl`                                         |                                                                     |
| 5.2 | Definition          | `schErasable`                 | [theories/common/sch_erasable.v]                        | `sch_erasable`                                       |                                                                     |
| 5.2 | Definition          | Program-coupling precondition | [theories/foxtrot/weakestpre.v]                         | `prog_coupl`                                         |                                                                     |
| 5.2 | Definition          | Probabilistic Update Modality | [theories/foxtrot/pupd.v]                               | `pupd`                                               |                                                                     |
| 5.3 | Lemma               | Iris choice                   | [theories/prelude/iris_ext.v]                           | `iris_choice`                                        |                                                                     |
| 5.3 | Lemma               | Lemma 5.6                     | [theories/foxtrot/adequacy.v]                           | `foxtrot_adequacy_full_info_intermediate_multi`      |                                                                     |




[theories/prob/distribution.v]: theories/prob/distribution.v
[theories/prob/couplings_app.v]: theories/prob/couplings_app.v
[theories/con_prob_lang/lang.v]: theories/con_prob_lang/lang.v
[theories/common/ectx_language.v]: theories/common/ectx_language.v
[theories/prob/mdp.v]: theories/prob/mdp.v
[theories/con_prob_lang/typing/contextual_refinement.v]: theories/con_prob_lang/typing/contextual_refinement.v
[Iris iprop]: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/iprop.v
[theories/foxtrot/adequacy.v]: theories/foxtrot/adequacy.v
[theories/foxtrot/binary_rel/binary_model.v]: theories/foxtrot/binary_rel/binary_model.v
[theories/foxtrot/binary_rel/binary_fundamental.v]: theories/foxtrot/binary_rel/binary_fundamental.v
[theories/foxtrot/binary_rel/binary_soundness.v]: theories/foxtrot/binary_rel/binary_soundness.v
[theories/foxtrot/unary_rel/unary_model.v]: theories/foxtrot/unary_rel/unary_model.v
[theories/foxtrot/unary_rel/unary_fundamental.v]: theories/foxtrot/unary_rel/unary_fundamental.v
[theories/foxtrot/weakestpre.v]: theories/foxtrot/weakestpre.v
[theories/foxtrot/primitive_laws.v]: theories/foxtrot/primitive_laws.v
[Iris invariant]: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/invariants.v
[theories/foxtrot/lib/par.v]: theories/foxtrot/lib/par.v
[theories/foxtrot/pupd.v]: theories/foxtrot/pupd.v
[theories/foxtrot/couplings_rules.v]: theories/foxtrot/couplings_rules.v
[theories/foxtrot/examples/entropy_mixer.v]: theories/foxtrot/examples/entropy_mixer.v
[theories/foxtrot/examples/batch_sampling.v]: theories/foxtrot/examples/batch_sampling.v
[theories/foxtrot/examples/presample_rhs.v]: theories/foxtrot/examples/presample_rhs.v
[theories/foxtrot/examples/rejection_samplers.v]: theories/foxtrot/examples/rejection_samplers.v
[theories/base_logic/error_credits.v]: theories/base_logic/error_credits.v
[theories/foxtrot/examples/von_neumann.v]: theories/foxtrot/examples/von_neumann.v
[theories/foxtrot/examples/libsodium.v]: theories/foxtrot/examples/libsodium.v
[theories/foxtrot/examples/nodet_example.v]: theories/foxtrot/examples/nodet_example.v
[theories/foxtrot/examples/encryption.v]: theories/foxtrot/examples/encryption.v
[theories/foxtrot/examples/algebraic.v]: theories/foxtrot/examples/algebraic.v
[theories/foxtrot/full_info.v]: theories/foxtrot/full_info.v
[theories/foxtrot/oscheduler.v]: theories/foxtrot/oscheduler.v
[theories/common/sch_erasable.v]: theories/common/sch_erasable.v
[theories/prelude/iris_ext.v]: theories/prelude/iris_ext.v
