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




[theories/base_logic/error_credits.v]: theories/base_logic/error_credits.v
[theories/prob/distribution.v]: theories/prob/distribution.v
[theories/con_prob_lang/lang.v]: theories/con_prob_lang/lang.v
[theories/common/ectx_language.v]: theories/common/ectx_language.v
[theories/common/sch_erasable.v]: theories/common/sch_erasable.v
[theories/prob/mdp.v]: theories/prob/mdp.v


[Iris iprop]: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/iprop.v
[Iris invariant]: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/invariants.v