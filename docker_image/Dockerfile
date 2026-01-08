FROM debian:bookworm

RUN apt-get -y update
RUN apt-get -y upgrade
RUN apt-get -y install make gcc patch git unzip bubblewrap curl libgmp-dev bzip2 pkg-config gawk g++

ARG OPAMYES=true
ENV OPAMROOTISOK=true

RUN curl -sL https://github.com/ocaml/opam/releases/download/2.2.1/opam-2.2.1-x86_64-linux -o opam
RUN install opam /usr/local/bin/opam
RUN rm -rf opam

RUN opam init
RUN eval $(opam env)
RUN opam repo add --set-default coq-released https://coq.inria.fr/opam/released
RUN opam repo add --set-default iris-dev https://gitlab.mpi-sws.org/iris/opam.git

RUN opam switch create stable ocaml.4.14.2
RUN eval $(opam env)
RUN opam update
RUN opam install dune rocq-core.9.0.0 rocq-stdlib.9.0.0 coq-iris.4.4.0
RUN opam install coq-coquelicot.3.4.4 coq-autosubst.1.9 coq-hierarchy-builder.1.10.1 coq-mathcomp-ssreflect.2.5.0 coq-mathcomp-analysis.1.14.0
RUN opam install vsrocq-language-server

RUN opam switch stable
RUN eval $(opam env)
RUN opam update

RUN echo 'eval $(opam env)' >> ~/.bashrc
