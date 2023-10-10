# Clutch

A higher-order probabilistic relational separation logic with support for asynchronous probabilistic couplings. 
The logic is built using the [Iris](https://iris-project.org) program logic framework and mechanized in the [Coq proof assistant](https://coq.inria.fr/).

## Preprint

A preprint describing this work is available on arXiv.

> Gregersen, S.O., Aguirre, A., Haselwarter, P. G., Tassarotti, J. and Birkedal, L., 2023. Asynchronous Probabilistic Couplings in Higher-Order Separation Logic. [arXiv preprint arXiv:2301.10061](https://arxiv.org/abs/2301.10061).

[This table](paper_mapping.md) maps definitions, concepts, and results found in the paper to the Coq formalization.

## Building the development

The project is known to compile with

- [Coq](https://coq.inria.fr/) 8.16.1
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.8.0
- [Coquelicot](https://gitlab.inria.fr/coquelicot/coquelicot/) 3.3.1
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) 4.0.0
- [Autosubst](https://github.com/coq-community/autosubst) 1.8
- [Mathcomp-solvable](https://github.com/math-comp/math-comp) 1.17.0

The recommended way to install the dependencies is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create clutch 4.14.1
opam switch link clutch .
```
3. Add the Coq and Iris `opam` repositories.
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update
```
4. Install the right version of the dependencies as specified in the `clutch.opam` file.
```
opam install . --deps-only
```

You should now be able to build the development by using `make -j N` where `N` is the number of cores available on your machine.

## Axioms

The development relies on axioms for classical reasoning and an axiomatization of the reals numbers, both found in Coq's standard library. The following list is produced when executing the command `Print Assumptions eager_lazy_equiv.` in [`theories/examples/lazy_eager_coin.v`](theories/examples/lazy_eager_coin.v):

```
ClassicalDedekindReals.sig_not_dec : ∀ P : Prop, {¬ ¬ P} + {¬ P}
ClassicalDedekindReals.sig_forall_dec : ∀ P : nat → Prop, (∀ n : nat, {P n} + {¬ P n}) → {n : nat | ¬ P n} + {∀ n : nat, P n}
functional_extensionality_dep : ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x), (∀ x : A, f x = g x) → f = g
constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
classic : ∀ P : Prop, P ∨ ¬ P
```

