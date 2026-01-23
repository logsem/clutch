# Clutch Project

This repository contains the formal development of a number of higher-order probabilistic separation logics for proving properties of higher-order probabilistic programs.
All of the logics are built using the [Iris](https://iris-project.org) program logic framework and mechanized in the [Rocq prover](https://rocq-prover.org/).

## Tutorial

If you want to work through our tutorial material, follow the instructions in the [link](https://github.com/logsem/clutch/blob/main/theories/eris/tutorial/readme.md).

## Publications

[**Modular Specifications and Implementations of Random Samplers in Higher-Order Separation Logic**](https://doi.org/10.1145/3779031.3779109)<br>
*Virgil Marionneau, Félix Sassus-Bourda, Alejandro Aguirre, Lars Birkedal*<br>
In CPP 2026: Certified Programs and Proofs

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
opam switch create clutch 4.14.2
opam switch link clutch .
```
3. Add the Rocq `opam` repository.
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
```
4. Install the right version of the dependencies as specified in the `rocq-clutch.opam` file.
```
opam install ./rocq-clutch.opam --deps-only
```

You should now be able to build the development by using `dune build`, or `dune build theories/eris/tutorial/tutorial.vo` to build only the files required for the tutorial.

## Visual Studio Code

The repository contains configuration files and pre-built Docker images for use with the Visual Studio Code [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) extension.
The Dev Containers extension lets you use a pre-built Docker image as a full-featured development environment. This means you that you do not have to worry about installing dependencies and polluting your file system.

1. Install [Docker](https://www.docker.com/) and [Visual Studio Code](https://code.visualstudio.com/). (The Dev Containers extension unfortunately does not support VSCodium)
2. Make sure Docker is running.
3. Install the [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) and [VsRocq](https://marketplace.visualstudio.com/items?itemName=rocq-prover.vsrocq) extensions in Visual Studio Code. 
4. Open the Clutch repository in Visual Studio Code. A pop-up should now ask you if you want to reopen the project in a container. Select `clutch arm64 container` or `clutch x86-64 container`, depending on the architecture of your machine.
5. After the container has been loaded, open a terminal window in Visual Studio Code (`Terminal` > `New Terminal` in the toolbar). This terminal is running inside the Docker container.
6. Run `dune build` to build the development. (Be aware that VsRocq does not automatically re-build dependencies)

See more about the Dev Containers extension at [this link](https://code.visualstudio.com/docs/devcontainers/containers)

## Axioms

The development relies on axioms for classical reasoning and an axiomatization of the reals numbers, both found in Rocq's standard library. For example, the following list is produced when executing the command `Print Assumptions eager_lazy_equiv.` in [`theories/clutch/examples/lazy_eager_coin.v`](theories/clutch/examples/lazy_eager_coin.v):

```
ClassicalDedekindReals.sig_not_dec : ∀ P : Prop, {¬ ¬ P} + {¬ P}
ClassicalDedekindReals.sig_forall_dec : ∀ P : nat → Prop, (∀ n : nat, {P n} + {¬ P n}) → {n : nat | ¬ P n} + {∀ n : nat, P n}
functional_extensionality_dep : ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x), (∀ x : A, f x = g x) → f = g
constructive_indefinite_description : ∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
classic : ∀ P : Prop, P ∨ ¬ P
```

