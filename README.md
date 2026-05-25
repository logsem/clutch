# Elton

This repository contains the formal development of Elton, a higher-order separation logic for reasoning about adversarial probabilistic programs.
Elton is built using the [Iris](https://iris-project.org) program logic framework and mechanized in the [Rocq prover](https://rocq-prover.org/).

## Building the development

The project is known to compile with

- [Rocq](https://rocq-prover.org/) 9.1.1
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.13.0
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) 4.5.0
- [Coquelicot](https://gitlab.inria.fr/coquelicot/coquelicot/) 3.4.4
- [Autosubst](https://github.com/coq-community/autosubst) dev
- [Mathcomp](https://github.com/math-comp/math-comp) 2.5.0
- [Mathcomp Analysis](https://github.com/math-comp/analysis) 1.14

The recommended way to install the dependencies locally is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create elton 4.14.2
opam switch link elton .
```
3. Add the Rocq `opam` repository.
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam repo add iris-dev git+https://gitlab.mpi-sws.org/iris/opam.git
opam update
```
4. Install the right version of the dependencies as specified in the `rocq-elton.opam` file.
```
opam install ./rocq-elton.opam --deps-only
```

You should now be able to build the development by using `dune build`  (or `dune build --display=short` for more detailed display log info).

## Axioms

The development relies on axioms for classical reasoning and an axiomatization of the reals numbers, both found in Rocq's standard library. For example, the following list is produced when executing the command `Print Assumptions eager_lazy_equiv.` in [`theories/clutch/examples/lazy_eager_coin.v`](theories/clutch/examples/lazy_eager_coin.v):

```
ClassicalDedekindReals.sig_not_dec : ∀ P : Prop, {¬ ¬ P} + {¬ P}
ClassicalDedekindReals.sig_forall_dec : ∀ P : nat → Prop, (∀ n : nat, {P n} + {¬ P n}) → {n : nat | ¬ P n} + {∀ n : nat, P n}
functional_extensionality_dep : ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x), (∀ x : A, f x = g x) → f = g
constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
classic : ∀ P : Prop, P ∨ ¬ P
```

