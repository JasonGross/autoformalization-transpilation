#!/bin/bash
# Download OPAM installer and run it
curl -fsSL https://opam.ocaml.org/install.sh > opam.sh
echo "" | sh opam.sh

# Disable sandboxing (required for Docker containers)
export OPAMSANDBOX=none

# Initialize OPAM without setup and source environment
opam init --disable-sandboxing --no-setup
eval $(opam env)

# Create Coq development switch with required repositories and packages
opam switch create coq-dev \
  --repositories=coq-core-dev=https://coq.inria.fr/opam/core-dev,\
coq-extra-dev=https://coq.inria.fr/opam/extra-dev,\
default=https://opam.ocaml.org \
  --packages=ocaml.4.14.2,coq.dev

cd /root
git clone https://github.com/JasonGross/coq-lean-import
cd /root/coq-lean-import
git checkout lean4-rebased
opam pin add 'git+https://github.com/JasonGross/coq-lean-import.git#lean4-rebased' -y

echo 'eval $(opam env)' >> ~/.bashrc

# Setup Coq import
cd /root/autoformalization
cat << EOF > target.v
From LeanImport Require Import Lean.
Redirect "target.log" Lean Import "target.out".
EOF
