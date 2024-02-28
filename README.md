# Eris

This is the artifact of the Eris logic, highlighted in the ICFP 2024 submission "Error Credits: Resourceful Reasoning about Error Bounds for Higher-Order Probabilistic Programs"."
The logic is built using the [Iris](https://iris-project.org) program logic framework and mechanized in the [Coq proof assistant](https://coq.inria.fr/).

This project is built on top of the [Clutch](https://dl.acm.org/doi/10.1145/3632868) project. 


## Building the development

The project is known to compile with

- [Coq](https://coq.inria.fr/) 8.18
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.9.0
- [Coquelicot](https://gitlab.inria.fr/coquelicot/coquelicot/) 3.3.1
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) 4.1.0
- [Autosubst](https://github.com/coq-community/autosubst) 1.8
- [Mathcomp-solvable](https://github.com/math-comp/math-comp) 1.17.0

The recommended way to install the dependencies is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create eris 4.14.1
opam switch link eris .
```
3. Add the Coq and Iris `opam` repositories.
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update
```
4. Install the right version of the dependencies as specified in the `eris.opam` file.
```
opam install . --deps-only
```

You should now be able to build the development by using `make -j N` where `N` is the number of cores available on your machine.


--------------------------------------------------------------------------------------


## Reference from the paper to the code

Our contributions of the Eris logic can mostly be found in the folder [theories/ub_logic/](theories/ub_logic/).

| § | Kind       | Item                                   | Coq file                                                  | Name                       | Note                                                                                     |
|---|------------|----------------------------------------|-----------------------------------------------------------|----------------------------|------------------------------------------------------------------------------------------|
| 1 | Example    | Specification of List.iter with errors | [theories/ub_logic/lib/list.v]                            | `wp_list_iter_err1`        |                                                                                          |
|   | Rule       | $\text{\scriptsize HT-BIND-EXP}$       | [theories/ub_logic/ub_weakestpre.v]                       | `ub_wp_bind`               | We present a noraml bind rule, which can be instantiated easily to include error credits |
| 2 | Definition | Mass                                   | [theories/prob/distribution.v]                            | `distr`                    |                                                                                          |
|   | Definition | Probability monad                      | [theories/prob/distribution.v]                            | `dret_id_right`, etc       |                                                                                          |
|   | Definition | Probability of predicate               | [theories/prob/distribution.v]                            | `prob`                     |                                                                                          |
|   | Definition | Partial graded lifting                 | [theories/prob/union_bounds.v]                            | `ub_lift`                  |                                                                                          |
|   | Definition | Total graded lifting                   | [theories/prob/union_bounds.v]                            | `total_ub_lift`            |                                                                                          |
|   | Definition | $\lambda^\text{rand}_\text{ref}        | [theories/prob_lang/lang.v]                               | Whole file                 |                                                                                          |
|   | Definition | step                                   | [theories/common/ectx_language.v]                         | `prim_step`                |                                                                                          |
|   | Definition | $\text{exec}_n$                        | [theories/common/exec.v]                                  | `exec`                     |                                                                                          |
|   | Definition | $\text{exec}$                          | [theories/common/exec.v]                                  | `lim_exec_val`             |                                                                                          |
| 3 | Definition | iProp                                  | imported from [Iris upstream]                             | `iProp`                    |                                                                                          |
|   | Definition | Ownership of error credits             | [theories/ub_logic/error_credits.v]                       | `ec`                       |                                                                                          |
|   | Rule       | Splitting error credits                | [theories/ub_logic/error_credits.v]                       | `ec_split`                 |                                                                                          |
|   | Rule       | Decreasing error credits               | [theories/ub_logic/error_credits.v]                       | `ec_weaken`                |                                                                                          |
|   | Rule       | Deriving False from 1 error credit     | [theories/ub_logic/error_credits.v]                       | `ec_spend`                 |                                                                                          |
|   | Theorem    | Adequacy of Eris                       | [theories/ub_logic/adequacy.v]                            | `wp_union_bound_lim`       |                                                                                          |
|   | Rules      | Various rules of HeapLang              | [theories/ub_logic/primitive_laws.v]                      | `wp_load` etc.             |                                                                                          |
|   | Rule       | $\text{\scriptsize HT-RAND-ERR-LIST}$  | [theories/ub_logic/ub_rules.v]                            | `wp_rand_err_list_nat`     |                                                                                          |
|   | Rule       | $\text{\scriptsize HT-BIND-SIMPL}$     | [theories/ub_logic/ub_weakestpre.v]                       | `ub_wp_bind`               | We present a noraml bind rule, which can be instantiated easily to include error credits |
|   | Rule       | $\text{\scriptsize RAND-EXP}$          | [theories/ub_logic/ub_rules.v]                            | `wp_couple_rand_adv_comp1` |                                                                                          |
|   | Example    | Synthetic example from Fig. 1          | [theories/ub_logic/ub_examples.v]                         | Section `test`             |                                                                                          |
| 4 | Example    | Dynamic vectors under faulty allocator | [theories/ub_logic/dynamic_vec.v]                         |                            |                                                                                          |
|   | Example    | Non-amortized non-resizing hash        | [theories/ub_logic/hash.v]                                | Section `simple_bit_hash`  |                                                                                          |
|   | Example    | Amortized non-resizing hash            | [theories/ub_logic/hash.v]                                | Section `amortized_hash`   |                                                                                          |
|   | Example    | Amortized resizing hash                | [theories/ub_logic/cf_hash.v]                             |                            |                                                                                          |
|   | Example    | Amortized resizing hash map            | [theories/ub_logic/cf_hashmap.v]                          |                            |                                                                                          |
|   | Example    | Merkle trees                           | [theories/ub_logic/merkle/merkle_tree.v]                  |                            |                                                                                          |
|   | Example    | Unreliable storage with merkle trees   | [theories/ub_logic/merkle/unreliable.v]                   |                            |                                                                                          |
| 5 | Theorem    | Total adequacy of Eris_t               | [theories/ub_logic/total_adequacy.v]                      | `twp_total_ub_lift`        |                                                                                          |
|   | Theorem    | Almost sure termination (AST)          | [theories/ub_logic/total_adequacy.v]                      | `twp_total_ub_lift_limit`  |                                                                                          |
|   | Example    | Rejection samplers                     |                                                           |                            |                                                                                          |
|   | Rule       | $\text{\scriptsize ALLOC-TAPE}$        | [theories/ub_logic/primitive_laws.v]                      | `wp_alloc_tape`            |                                                                                          |
|   | Rule       | $\text{\scriptsize LOAD-TAPE}$         | [theories/ub_logic/primitive_laws.v]                      | `wp_rand_tape`             |                                                                                          |
|   | Rule       | $\text{\scriptsize STORE-TAPE}$        | [theories/ub_logic/primitive_laws.v]                      | `wp_presample`             |                                                                                          |
|   | Rule       | $\text{\scriptsize PRESAMPLE-PLANNER}$ | [theories/ub_logic/ub_rules.v]                            | `presample_planner`        |                                                                                          |
|   | Example    | WalkSAT                                | [theories/examples/approximate_samplers/approx_walkSAT.v] |                            |                                                                                          |
| 6 | Definition | Weakest precondition predicate         | [theories/ub_logic/ub_weakestpre.v]                       | `ub_wp_pre`                |                                                                                          |
|   | Definition | Graded lifting modality, execUpTo      | [theories/ub_logic/ub_weakestpre.v]                       | `exec_ub_pre`              |                                                                                          |
|   | Rule       | $\text{\scriptsize UPTO-PRIM}$         | [theories/ub_logic/ub_weakestpre.v]                       | `exec_ub_prim_step`        |                                                                                          |
|   | Rule       | $\text{\scriptsize UPTO-EXP}$          | [theories/ub_logic/ub_weakestpre.v]                       | `exec_ub_adv_comp`         |                                                                                          |
	
	
	
[theories/ub_logic/lib/list.v]: theories/ub_logic/lib/list.v
[theories/ub_logic/ub_weakestpre.v]: theories/ub_logic/ub_weakestpre.v 
[theories/prob/distribution.v]: theories/prob/distribution.v 
[theories/prob/union_bounds.v]: theories/prob/union_bounds.v 
[theories/prob_lang/lang.v]: theories/prob_lang/lang.v
[theories/common/ectx_language.v]: theories/common/ectx_language.v
[theories/common/exec.v]: theories/common/exec.v
[theories/ub_logic/error_credits.v]: theories/ub_logic/error_credits.v
[theories/ub_logic/adequacy.v]: theories/ub_logic/adequacy.v
[theories/ub_logic/primitive_laws.v]: theories/ub_logic/primitive_laws.v
[theories/ub_logic/ub_rules.v]: theories/ub_logic/ub_rules.v
[theories/ub_logic/ub_examples.v]: theories/ub_logic/ub_examples.v
[theories/ub_logic/dynamic_vec.v]: theories/ub_logic/dynamic_vec.v
[theories/ub_logic/hash.v]: theories/ub_logic/hash.v
[theories/ub_logic/cf_hash.v]: theories/ub_logic/cf_hash.v
[theories/ub_logic/cf_hashmap.v]: theories/ub_logic/cf_hashmap.v
[theories/ub_logic/merkle/merkle_tree.v]: theories/ub_logic/merkle/merkle_tree.v
[theories/ub_logic/merkle/unreliable.v]: theories/ub_logic/merkle/unreliable.v
[theories/ub_logic/total_adequacy.v]: theories/ub_logic/total_adequacy.v
[theories/examples/approximate_samplers/approx_walkSAT.v]: theories/examples/approximate_samplers/approx_walkSAT.v




[iris upstream]: https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/iprop.v
