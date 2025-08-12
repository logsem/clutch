# Clutch Project

This repository contains the formal development of multiple higher-order probabilistic separation logics for proving properties of higher-order probabilistic programs.
All of the logics are built using the [Iris](https://iris-project.org) program logic framework and mechanized in the [Coq proof assistant](https://coq.inria.fr/).

## Publications

[**Modular Reasoning about Error Bounds for Concurrent Probabilistic Programs**](https://dl.acm.org/doi/10.1145/3747514)<br>
*Kwing Hei Li, Alejandro Aguirre, Simon Oddershede Gregersen, Philipp G. Haselwarter, Joseph Tassarotti, Lars Birkedal*<br>
In ICFP 2025: ACM SIGPLAN International Conference on Functional Programming

[**Approximate Relational Reasoning for Higher-Order Probabilistic Programs**](https://dl.acm.org/doi/10.1145/3704877)<br>
*Philipp G. Haselwarter, Kwing Hei Li, Alejandro Aguirre, Simon Oddershede Gregersen, Joseph Tassarotti, Lars Birkedal*<br>
In POPL 2025: ACM SIGPLAN Symposium on Principles of Programming Languages

[**Tachis: Higher-Order Separation Logic with Credits for Expected Costs**](https://doi.org/10.1145/3689753)<br>
*Philipp G. Haselwarter, Kwing Hei Li, Markus de Medeiros, Simon Oddershede Gregersen, Alejandro Aguirre, Joseph Tassarotti, Lars Birkedal*<br>
In OOPSLA 2024: ACM SIGPLAN Conference on Object-Oriented Programming, Systems, Languages, and Applications

[**Error Credits: Resourceful Reasoning about Error Bounds for Higher-Order Probabilistic Programs**](https://doi.org/10.1145/3674635)<br>
*Alejandro Aguirre, Philipp G. Haselwarter, Markus de Medeiros, Kwing Hei Li, Simon Oddershede Gregersen, Joseph Tassarotti, Lars Birkedal*<br>
In ICFP 2024: ACM SIGPLAN International Conference on Functional Programming

[**Almost-Sure Termination by Guarded Refinement**](https://doi.org/10.1145/3674632) <br>
*Simon Oddershede Gregersen, Alejandro Aguirre, Philipp G. Haselwarter, Joseph Tassarotti, Lars Birkedal*<br>
In ICFP 2024: ACM SIGPLAN International Conference on Functional Programming

[**Asynchronous Probabilistic Couplings in Higher-Order Separation Logic**](https://dl.acm.org/doi/10.1145/3632868)<br>
*Simon Oddershede Gregersen, Alejandro Aguirre, Philipp G. Haselwarter, Joseph Tassarotti, Lars Birkedal*<br>
In POPL 2024: ACM SIGPLAN Symposium on Principles of Programming Languages

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

## Axioms

The development relies on axioms for classical reasoning and an axiomatization of the reals numbers, both found in Coq's standard library. For example, the following list is produced when executing the command `Print Assumptions eager_lazy_equiv.` in [`theories/clutch/examples/lazy_eager_coin.v`](theories/clutch/examples/lazy_eager_coin.v):

```
ClassicalDedekindReals.sig_not_dec : ∀ P : Prop, {¬ ¬ P} + {¬ P}
ClassicalDedekindReals.sig_forall_dec : ∀ P : nat → Prop, (∀ n : nat, {P n} + {¬ P n}) → {n : nat | ¬ P n} + {∀ n : nat, P n}
functional_extensionality_dep : ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x), (∀ x : A, f x = g x) → f = g
constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
classic : ∀ P : Prop, P ∨ ¬ P
```

