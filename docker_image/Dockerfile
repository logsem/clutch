FROM debian:trixie

RUN apt-get -y update
RUN apt-get -y upgrade
RUN apt-get -y install make gcc patch git unzip bubblewrap curl libgmp-dev bzip2 pkg-config gawk g++

ARG OPAMYES=true
ENV OPAMROOTISOK=true

RUN curl -sL https://github.com/ocaml/opam/releases/download/2.5.0/opam-2.5.0-x86_64-linux -o opam
RUN install opam /usr/local/bin/opam
RUN rm opam

RUN opam init --bare
RUN eval $(opam env)
RUN opam repo add --set-default coq-released https://coq.inria.fr/opam/released
RUN opam repo add --set-default iris-dev https://gitlab.mpi-sws.org/iris/opam.git
RUN opam update

RUN opam switch create clutch --empty
RUN curl -sL 'https://raw.githubusercontent.com/logsem/clutch/refs/heads/main/rocq-clutch.opam' -o rocq-clutch.opam
RUN opam install ./rocq-clutch.opam --deps-only
RUN rm rocq-clutch.opam
RUN eval $(opam env)
RUN opam install vsrocq-language-server.2.3.4

RUN git clone https://gitlab.inria.fr/coquelicot/coquelicot.git
RUN cp coquelicot/theories/* ~/.opam/clutch/lib/coq/user-contrib/Coquelicot && rm -rf coquelicot

RUN echo 'eval $(opam env)' >> ~/.bashrc
