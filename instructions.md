# Approximate Relational Reasoning for Higher-Order Probabilistic Programs - Formalization Artifact

This artifact contains the Coq development accompanying the POPL 2025 submission "Approximate Relational Reasoning for Higher-Order Probabilistic Programs".

## Contents

- The file `docker-approxis.tar.gz` contains a (compressed) Docker image that contains a working, compiled version of Approxis and all of its dependencies.

- The file `coq-approxis.tar.gz` contains the Coq development.

- The file `Dockerfile` was used to create the Docker image by running the command `docker build -t approxis . && docker save approxis:latest | gzip > docker-approxis.tar.gz`. The Docker image was created on Arch Linux, with a current version of Docker (date: 2024-10-16, version: 27.3.1, build ce1223035a). To successfully build the image, the files `coq-approxis.tar.gz` and `Dockerfile` should be in the current working directory.

- The file `approxis.ova` contains a virtual machine image with a compiled version of Approxis, Emacs, and ProofGeneral. VirtualBox 7.1.4 was used to create the VM image.

## Usage

Please refer to the file `README.md` in `coq-approxis.tar.gz` for information about the main results of the POPL submission as well as manual installation instructions.

The Docker image can be loaded via the command `docker load < docker-approxis.tar.gz`. We recommend either working with the provided image or following the installation instructions in the readme. 

To run an interactive Docker shell, execute the command `docker run -i --name approxis -t approxis`. From the interactive shell, one can check that the results of the paper have been proven without "admits" by examining the file collecting the main results and re-compiling it:

```
cat theories/approxis/approxis_examples.v
touch theories/approxis/approxis_examples.v
make
```

This sequence of commands will print Coq's the mathematical axioms for real numbers and classical logic.

The virtual machine can be imported in VirtualBox via File -> Import Appliance. The VM is based on the Xubuntu distribution. A script to launch Emacs for Approxis is on the desktop. The user and password for the VM are `approxis` and `approxis` respectively.
