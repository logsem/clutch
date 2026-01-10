# Tutorial: Verifying Probabilistic Programs Using Separation Logic

This tutorial is an introduction to probabilistic program verification in modern separation logic.

The tutorial comprises a list of interactive exercises in the form of incomplete proofs with hints.

More information can be found at
- the [POPL tutorial website](https://popl26.sigplan.org/details/POPL-2026-tutorials/8/Verifying-Probabilistic-Programs-Using-Separation-Logic)
- the [Clutch project readme](https://github.com/logsem/clutch/)


## Prerequesites

### Background Knowledge

Basic knowledge of the Rocq prover is assumed. Consult, e.g., [Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/toc.html) for an introduction to basic logic and tactics in Rocq.

We do not assume familiarity with the Iris separation logic framework. We will only introduce as much Iris as required to understand the examples; for more information see the [Iris tutorial](https://github.com/logsem/iris-tutorial) and the Iris proof mode [cheatsheet](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md).

The probabilistic separation logic this tutorial is based on was published in

[**Error Credits: Resourceful Reasoning about Error Bounds for Higher-Order Probabilistic Programs**](https://doi.org/10.1145/3674635)<br>
*Alejandro Aguirre, Philipp G. Haselwarter, Markus de Medeiros, Kwing Hei Li, Simon Oddershede Gregersen, Joseph Tassarotti, Lars Birkedal*<br>
In ICFP 2024: ACM SIGPLAN International Conference on Functional Programming


### Software

#### The Rocq prover

To work through the tutorial, a working Rocq setup and IDE / text editor is required ([instructions](https://rocq-prover.org/install)).

#### Rocq libraries

The recommended way to install the Rocq libraries we depend on is through [opam](https://opam.ocaml.org/doc/Install.html).

0. Clone this repository. Run the subsequent shell commands from the root of the repository (not this folder).
1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed with Rocq (a version greater than 2.0 is required).
2. Create a new "switch" (self-contained set of Rocq and OCaml libraries) and link it to the project.
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

### Visual Studio Code

The repository contains configuration files and pre-built Docker images for use with the Visual Studio Code [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) extension.
The Dev Containers extension lets you use a pre-built Docker image as a full-featured development environment. This means you that you do not have to worry about installing dependencies and polluting your file system.

1. Install [Docker](https://www.docker.com/) and [Visual Studio Code](https://code.visualstudio.com/). (The Dev Containers extension unfortunately does not support VSCodium or the open source build of VSCode, so Microsoft's release of VSCode is required)
2. Make sure Docker is running.
3. Install the "Dev Containers" and "VsRocq" extensions in Visual Studio Code.
4. Open the Clutch repository in Visual Studio Code. A pop-up should now ask you if you want to reopen the project in a container. Select `clutch arm64 container` or `clutch x86-64 container`, depending on the architecture of your machine.
5. After the container has been loaded, open a terminal window in Visual Studio Code (`Terminal` > `New Terminal` in the toolbar). This terminal is running inside the Docker container.
6. Run `dune build` to build the development. (Be aware that VsRocq does not automatically re-build dependencies)

See more about the Dev Containers extension at [this link](https://code.visualstudio.com/docs/devcontainers/containers)

## Contents

The tutorial will feature a mix of lectures from the organizers and exercises. The plan is to progress as follows.

1. [basic.v](./basic.v): basic separation logic; "error credits" as separation logic resource; manipulating error credits; simple random sampling.
2. [quicksort.v](./quicksort.v): correctness of randomized quicksort.
3. [geometric.v](./geometric.v): sampling from the geometric distribution.
4. [hash_interface.v](./hash_interface.v), [bloom_filter_single.v](./bloom_filter_single.v): Bloom filters based on hash functions. Bound on probability of false positives.
5. [geometric_total.v](./geometric_total.v): reasoning about total correctness and almost sure termination of geometric samplers.


## Contact information

Please feel free to contact the POPL'26 tutors via email at alejandro@cs.au.dk gregersen@cispa.de philipp@haselwarter.org
