# Modular Specifications and Implementations of Random Samplers in Higher-Order Separation Logic

This repository contains the formal development of the CPP26 submission of the
same title. The logic is built using the [Iris](https://iris-project.org)
program logic framework and mechanized in the [Rocq prover](https://rocq-prover.org/).


## Building the development

The project is known to compile with

- [Coq](https://coq.inria.fr/) 8.19.1
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.10.0
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) 4.2.0
- [Coquelicot](https://gitlab.inria.fr/coquelicot/coquelicot/) 3.4.1
- [Autosubst](https://github.com/coq-community/autosubst) 1.8
- [Mathcomp-solvable](https://github.com/math-comp/math-comp) 2.2.0

The recommended way to install the dependencies is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create clutch 4.14.1
opam switch link clutch .
```
(The switch creation might fail on systems with a gcc version >= 15. If this happens a fix is to run the first command with the option `CC=gcc-14`)
3. Add the Coq and Iris `opam` repositories.
```
opam repo add rocq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update
```
4. Install the right version of the dependencies as specified in the `clutch.opam` file.
```
opam install . --deps-only
```

You should now be able to build the development by using `make -j N` where `N` is the number of cores available on your machine.

## Mechanization of the submission

The main mechanization of the contribution can be found in [`theories/eris/lib/sampling/`](theories/eris/lib/sampling/). The
table below provides a mapping between the code and the paper.


| §       | Kind          | Item                                                          | Coq file                                                    | Name                                                             | Note                                                                                                           |
| ------- | ------------- | ------------------------------------------------------------- | ----------------------------------------------------------- | ---------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------- |
| 2       | Rule          | $\text{\scriptsize HT-RAND-EXP}$                              | [theories/eris/error_rules.v]                               | `wp_couple_rand_adv_comp1`                                       |                                                                                                                |
|         | Rule          | $\text{\scriptsize HT-RAND-AVOID}$                            | [theories/eris/error_rules.v]                               | `wp_rand_err_amp_nat`                                            | a more general version                                                                                         |
|         | Spec          | naïve spec for `bern`                                         | [theories/eris/lib/sampling/bernoulli/interface.v]          | `bernoulli_success_spec_simple`, `bernoulli_failure_spec_simple` | instantiated `b` as 2 cases                                                                                    |
|         | Spec          | Specification for `bern`                                      | [theories/eris/lib/sampling/bernoulli/interface.v]          | `twp_bernoulli_scale`                                            |                                                                                                                |
|         | Theorem       | Antecedent for adequacy                                       | [theories/eris/lib/sampling/distribution_adequacy.v]        | `twp_μ_adv_comp`                                                 | Theorem 2.1                                                                                                    |
| 3       | Comment       |                                                               |                                                             |                                                                  | Please check the [eris paper mapping](https://github.com/logsem/clutch/blob/icfp24-eris/eris_paper_mapping.md) |
| 4       | Definition    | DistrImpl typeclass                                           | [theories/eris/lib/sampling/distr_impl.v]                   | `distr_impl`                                                     | Figure 4                                                                                                       |
|         | Theorem       | Distribution Adequacy Theorem                                 | [theories/eris/lib/sampling/distribution_adequacy.v]        | `μ_impl_is_μ`                                                    | Theorem 4.1                                                                                                    |
|         | Rule          | $\text{\scriptsize PRESAMPLE-DISTR-PLANNER}$                  | [theories/eris/lib/sampling/distr_impl.v]                   | `distr_presample_planner`                                        |                                                                                                                |
|         | Rule          | Abstract Planner rule                                         | [theories/eris/lib/sampling/abstract_planner.v]             | `abstract_planner`                                        |                                                                                                                |
| 5.1     | Definition    | `bern`                                                        | [theories/eris/lib/sampling/bernoulli/implementation.v]     | `bernoulli`                                                      |                                                                                                                |
|         | Lemma         | $\text{\scriptsize HT-BERNOULLI-EXP}$                         | [theories/eris/lib/sampling/bernoulli/implementation.v]     | `twp_bernoulli_scale`                                            |                                                                                                                |
|         | Definition    | Translation Predicate for Bernoulli                           | [theories/eris/lib/sampling/bernoulli/tape.v]               |                                                                  | Figure 5                                                                                                       |
|         | Lemma         | $\text{\scriptsize BERNOULLI-ALLOC-TAPE}$                     | [theories/eris/lib/sampling/bernoulli/implementation.v]     | `twp_bernoulli_alloc`                                            |                                                                                                                |
|         | Lemma         | $\text{\scriptsize LOAD-BERNOULLI-TAPE}$                      | [theories/eris/lib/sampling/bernoulli/implementation.v]     | `twp_bernoulli_tape`                                             |                                                                                                                |
|         | Lemma         | $\text{\scriptsize PRESAMPLE-BERNOULLI-EXP}$                  | [theories/eris/lib/sampling/bernoulli/implementation.v]     | `twp_presample_bernoulli_adv_comp`                               |                                                                                                                |
|         | Lemma         | $\text{\scriptsize PRESAMPLE-BERNOULLI-PLANNER}$              | [theories/eris/lib/sampling/bernoulli/interface.v]          | `twp_presample_bernoulli_planner`                                |                                                                                                                |
|         | Example       | `martingale`                                                  | [theories/eris/lib/sampling/examples/bernoulli.v]           | `Section Roulette`                                               |                                                                                                                |
| 5.2-5.4 | Distributions |                                                               | [theories/eris/lib/sampling/]                               |                                                                  | File structures are all similar to Bernoulli                                                                   |
| 5.5     | Definition    | $\text{\scriptsize trig-nil}$, $\text{\scriptsize trig-snoc}$ | [theories/eris/lib/sampling/utils/triangle.v]               | `trig_nil`, `trig_snoc`                                          |                                                                                                                |
|         | Definition    | `ownTrig`                                                     | [theories/eris/lib/sampling/beta_binomial/implementation.v] | `own_trig`                                                       | Figure 6                                                                                                       |
|         | Definition    | `hsup`                                                        | [theories/eris/lib/sampling/beta_binomial/beta_tapes.v]     | `β_hsup`                                                         |                                                                                                                |
|         | Definition    | `bottom-loc`, `right-loc`                                     | [theories/eris/lib/sampling/beta_binomial/implementation.v] | `sub_loc_fail`, `sub_loc_success`                                |                                                                                                                |
|         | Definition    | `betabin`                                                     | [theories/eris/lib/sampling/beta_binomial/implementation.v] | `polya`                                                          |                                                                                                                |
  
[theories/eris/error_rules.v]: theories/eris/error_rules.v
[theories/eris/lib/sampling/distribution_adequacy.v]: theories/eris/lib/sampling/distribution_adequacy.v
[theories/prob/distribution.v]: theories/prob/distribution.v
[theories/common/exec.v]: theories/common/exec.v
[theories/common/ectx_language.v]: theories/common/ectx_language.v
[theories/eris/lib/sampling/distr_impl.v]: theories/eris/lib/sampling/distr_impl.v
[theories/eris/lib/sampling/bernoulli/implementation.v]: theories/eris/lib/sampling/bernoulli/implementation.v
[theories/eris/lib/sampling/bernoulli/tape.v]: theories/eris/lib/sampling/bernoulli/tape.v
[theories/eris/lib/sampling/bernoulli/interface.v]: theories/eris/lib/sampling/bernoulli/interface.v
[theories/eris/lib/sampling/examples/bernoulli.v]: theories/eris/lib/sampling/examples/bernoulli.v
[theories/eris/lib/sampling/]: theories/eris/lib/sampling/
[theories/eris/lib/sampling/utils/triangle.v]: theories/eris/lib/sampling/utils/triangle.v
[theories/eris/lib/sampling/beta_binomial/implementation.v]: theories/eris/lib/sampling/beta_binomial/implementation.v
[theories/eris/lib/sampling/beta_binomial/beta_tapes.v]: theories/eris/lib/sampling/beta_binomial/beta_tapes.v
[theories/eris/lib/sampling/abstract_planner.v]: theories/eris/lib/sampling/abstract_planner.v



## Axioms

The development relies on axioms for classical reasoning and an axiomatization of the reals numbers, both found in Coq's standard library. For example, the following list is produced when executing the command `Print Assumptions roulette_martingale_tape_spec.` in [`theories/eris/lib/sampling/examples/bernoulli.v`](theories/eris/lib/sampling/examples/bernoulli.v):

```
ClassicalDedekindReals.sig_not_dec : ∀ P : Prop, {¬ ¬ P} + {¬ P}
ClassicalDedekindReals.sig_forall_dec : ∀ P : nat → Prop, (∀ n : nat, {P n} + {¬ P n}) → {n : nat | ¬ P n} + {∀ n : nat, P n}
propositional_extensionality : ∀ P Q : Prop, P ↔ Q → P = Q
functional_extensionality_dep : ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x), (∀ x : A, f x = g x) → f = g
ClassicalEpsilon.constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
```
