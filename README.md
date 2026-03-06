# Foxtrot

This repository contains the development of the Foxtrot logic, in the PLDI submission "Contextual Refinement of Higher-Order Concurrent Probabilistic Programs".
Foxtrot is built using the [Iris](https://iris-project.org) program logic framework and mechanized in the [Rocq prover](https://rocq-prover.org/).

Foxtrot is built on top of the infrastructure supporting the [Clutch](https://dl.acm.org/doi/abs/10.1145/3632868) logic. 

## Building the development

The project is known to compile with

- [Rocq](https://rocq-prover.org/) 9.0
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.12.0
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) 4.4.0
- [Coquelicot](https://gitlab.inria.fr/coquelicot/coquelicot/) 3.4.4
- [Autosubst](https://github.com/coq-community/autosubst) 1.9
- [Mathcomp](https://github.com/math-comp/math-comp) 2.5.0
- [Mathcomp Analysis](https://github.com/math-comp/analysis) 1.14

The recommended way to install the dependencies locally is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create foxtrot 4.14.2
opam switch link foxtrot .
```
3. Add the Rocq `opam` repository.
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
```
4. Install the right version of the dependencies as specified in the `rocq-foxtrot.opam` file.
```
opam install ./rocq-foxtrot.opam --deps-only
```

You should now be able to build the development by using `dune build`.

Note that this command might produce various warnings of the form, which can all be safely ignored:
```
Warning: in file xxx, library
         xxx is required
         from root Coquelicot and has not been found in the loadpath!
         [module-not-found,filesystem,default]
```

## Axioms

The development relies on axioms for classical reasoning and an axiomatization of the reals numbers, both found in Rocq's standard library. For example, the following list is produced when compiling `print_assumptions.v` in the `/theories/foxtrot` directory:

```
ClassicalDedekindReals.sig_not_dec : forall P : Prop, {~ ~ P} + {~ P}
ClassicalDedekindReals.sig_forall_dec
  : forall P : nat -> Prop,
    (forall n : nat, {P n} + {~ P n}) -> {n : nat | ~ P n} + {forall n : nat, P n}
PropExtensionality.propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
FunctionalExtensionality.functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g
ClassicalEpsilon.constructive_indefinite_description
  : forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```