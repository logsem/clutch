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
# The patched coq-lsp that the RocqSolid MCP server talks to (see below).
RUN opam repo add --set-default rocq-solid https://github.com/bn-peters/rocq-solid-mcp-opam.git
RUN opam update

RUN opam switch create clutch --empty
RUN curl -sL 'https://raw.githubusercontent.com/logsem/clutch/refs/heads/main/rocq-clutch.opam' -o rocq-clutch.opam
# rocq-solid-mcp-lsp is listed here, with --deps-only, so that its dependency
# memprof-limits is installed in the same step as Rocq.  memprof-limits is an
# optional dependency of rocq-runtime: installing it later would recompile
# Rocq and every library.
# rocq-solid-mcp-lsp is built per Rocq version (0.2.5+9.0, +9.1, +9.2) and
# requires exactly that version.  Pin the build that matches the Rocq of
# rocq-clutch.opam: unpinned, opam picks the newest build and upgrades Rocq
# (and mathcomp with it) past what the development supports.
RUN opam install ./rocq-clutch.opam rocq-solid-mcp-lsp.0.2.5+9.1 --deps-only
RUN rm rocq-clutch.opam
RUN eval $(opam env)
RUN opam install vsrocq-language-server.2.3.4 rocq-solid-mcp-lsp.0.2.5+9.1

RUN git clone https://gitlab.inria.fr/coquelicot/coquelicot.git
RUN cp coquelicot/theories/* ~/.opam/clutch/lib/coq/user-contrib/Coquelicot && rm -rf coquelicot

# RocqSolid (https://github.com/bn-peters/rocq-solid-mcp): an MCP server that
# lets coding agents check Rocq files and query proof states.  It is a Python
# program; uv installs it together with a private Python, as the command
# `rocq-solid-mcp` in /usr/local/bin.  It is registered for Claude Code in
# /.mcp.json at the root of the repository.
COPY --from=ghcr.io/astral-sh/uv:latest /uv /uvx /usr/local/bin/
ENV UV_TOOL_BIN_DIR=/usr/local/bin UV_TOOL_DIR=/opt/uv/tools UV_PYTHON_INSTALL_DIR=/opt/uv/python
RUN uv tool install --python 3.12 rocq-solid-mcp==1.0.0

RUN echo 'eval $(opam env)' >> ~/.bashrc
