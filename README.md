# Tachis: Higher-Order Separation Logic with Credits for Expected Costs

This is the artifact for the Tachis logic, submitted to OOPSLA 2024 under "Tachis: Higher-Order Separation Logic with Credits for Expected Costs".  
The file `paper_mapping.md` relates definitions, rules, and theorems from the paper into the Coq formalization. 

Tachis is built using the [Iris](https://iris-project.org) program logic framework and mechanized in the [Coq proof assistant](https://coq.inria.fr/). 

This project is built on top of [Clutch](https://github.com/logsem/clutch)

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
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update
```
4. Install the right version of the dependencies as specified in the `clutch.opam` file.
```
opam install . --deps-only
```

You should now be able to build the development by using `make -j N` where `N` is the number of cores available on your machine.
