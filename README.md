# Coneris Project

This repository contains the mechanized development of Coneris.

For the artifact evaluation, we plan to submit a more fully-fledged artifact including in particular a mapping between the paper and the Coq development.

For the sake of supplementing the paper, we provide the following brief pointers:
- the operational semantics is defined in `theories/con_prob_lang/lang.v`
- the adequacy theorems are proven in `theories/coneris/adequacy.v`
- the Bloom filter case study is in `theories/coneris/examples/concurrent_bloom_filter.v`
- the HOCAP spec for the randomized counter is in `theories/coneris/examples/random_counter/random_counter.v`
- the weakest precondition is defined in `theories/coneris/weakestpre.v`
- the probabilistic update modality is defined in `theories/coneris/wp_update.v` under the name `state_update`


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
opam switch create coneris 4.14.1
opam switch link coneris .
```
3. Add the Coq and Iris `opam` repositories.
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update
```
4. Install the right version of the dependencies as specified in the `coneris.opam` file.
```
opam install . --deps-only
```

You should now be able to build the development by using `make -j N` where `N` is the number of cores available on your machine.

## Axioms

The development relies on axioms for classical reasoning and an axiomatization of the reals numbers, both found in Coq's standard library. For example, the following list is produced when compiling the file [`theories/coneris/coneris_print_assumptions.v`](theories/coneris/coneris_print_assumptions.v) which executes the Coq command `Print Assumptions coneris_results.`, where `coneris_results` refers to the proof of the Bloom filter spec and the adequacy theorems:

```
ClassicalDedekindReals.sig_not_dec : ∀ P : Prop, {¬ ¬ P} + {¬ P}
ClassicalDedekindReals.sig_forall_dec
  : ∀ P : nat → Prop, (∀ n : nat, {P n} + {¬ P n}) → {n : nat | ¬ P n} + {∀ n : nat, P n}
propositional_extensionality : ∀ P Q : Prop, P ↔ Q → P = Q
functional_extensionality_dep
  : ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x), (∀ x : A, f x = g x) → f = g
ClassicalEpsilon.constructive_indefinite_description
  : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
```

