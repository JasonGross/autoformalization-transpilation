#!/bin/bash
set -e
# Download OPAM installer and run it
curl -fsSL https://opam.ocaml.org/install.sh > opam.sh
echo "" | sh opam.sh

# Disable sandboxing (required for Docker containers)
export OPAMSANDBOX=none

# Initialize OPAM without setup and source environment
opam init -y --disable-sandboxing --auto-setup --comp=4.14.2
opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

echo 'eval $(opam env)' >> ~/.bashrc
