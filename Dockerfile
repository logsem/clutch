FROM "mathcomp/mathcomp:2.2.0-coq-8.19"

ARG NJOBS=4

WORKDIR /home/coq/coneris

COPY . .

RUN set -x \
    && opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git \
    && opam update -y \
    && opam pin add -n -y -k path coneris . \
    && opam install --confirm-level=unsafe-yes -j ${NJOBS} . --deps-only \
    && sudo chown -R coq:coq /home/coq/coneris \
    && opam clean -a -c -s --logs \
    && make -j ${NJOBS}
