#!/bin/bash
set -e

# cd /root
# git clone https://github.com/JasonGross/coq-lean-import --branch lean4-rebased
# cd /root/coq-lean-import
opam pin add -yn 'git+https://github.com/JasonGross/coq-lean-import.git#lean4-rebased'

opam install -y coq coq-lean-import

# allow for editing of coq-lean-import more easily
cd /root
ln -s "$(opam var coq-lean-import:build)" coq-lean-import

# /root/autoformalization doesn't seem to exist?
# # Setup Coq import
# cd /root/autoformalization
# cat << EOF > target.v
# From LeanImport Require Import Lean.
# Redirect "target.log" Lean Import "target.out".
# EOF
