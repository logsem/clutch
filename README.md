# Clutch
A higher-order probabilistic relational separation logic with support for asynchronous probabilistic couplings. 

## Preprint

[Asynchronous Probabilistic Couplings in Higher-Order Separation Logic](https://arxiv.org/abs/2301.10061).


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
opam switch create clutch 4.14.0
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

## Reference from the paper to the code

We collected a detailed correspondence mapping the concepts from the paper to the corresponding Coq code in [this table](code_paper_map.md).
