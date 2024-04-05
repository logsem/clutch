# Tachis

## Building the development

The project is known to compile with

- [Coq](https://coq.inria.fr/) 8.18
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.9.0
- [Coquelicot](https://gitlab.inria.fr/coquelicot/coquelicot/) 3.3.1
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) 4.1.0

The recommended way to install the dependencies is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create tachis 4.14.1
opam switch link tachis .
```
3. Add the Coq and Iris `opam` repositories.
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update
```
4. Install the right version of the dependencies as specified in the `tachis.opam` file.
```
opam install . --deps-only
```

You should now be able to build the development by using `make -j N` where `N` is the number of cores available on your machine.

## Axioms

The development relies on axioms for classical reasoning and an axiomatization of the reals numbers, both found in Coq's standard library. The following list is produced when executing the command `Print Assumptions`.

```
ClassicalDedekindReals.sig_not_dec : ∀ P : Prop, {¬ ¬ P} + {¬ P}
ClassicalDedekindReals.sig_forall_dec : ∀ P : nat → Prop, (∀ n : nat, {P n} + {¬ P n}) → {n : nat | ¬ P n} + {∀ n : nat, P n}
functional_extensionality_dep : ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x), (∀ x : A, f x = g x) → f = g
constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
classic : ∀ P : Prop, P ∨ ¬ P
```

