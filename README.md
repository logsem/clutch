# Clutch
A higher-order probabilistic relational separation logic with support for asynchronous probabilistic couplings. 

## Building the development

The project is known to compile with
- [Coq](https://coq.inria.fr/) 8.16.1
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.8.0
- [Coquelicot](https://gitlab.inria.fr/coquelicot/coquelicot/) 3.2.0
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) 4.0.0
- [Autosubst](https://github.com/coq-community/autosubst) 1

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
4. Install the right version of the dependencies as specified in the `iris-probability.opam` file.
```
opam install . --deps-only
```

You should now be able build the development by using `make -j N` where `N` is the number of cores available on your machine.
