#!/bin/bash
set -e

opam pin add -yn 'git+https://github.com/JasonGross/coq-lean-import.git#lean4-rebased'

opam install -y coq coq-lean-import

# Allow for editing of coq-lean-import more easily
cd /root
ln -s "$(opam var coq-lean-import:build)" coq-lean-import

# Setup Coq import
cd /root/autoformalization
cat << EOF > target.v
From LeanImport Require Import Lean.
Redirect "target.log" Lean Import "target.out".
EOF
