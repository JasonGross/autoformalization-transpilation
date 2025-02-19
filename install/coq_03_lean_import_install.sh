#!/bin/bash
set -e

opam pin add -yn 'git+https://github.com/coq-community/rocq-lean-import.git'

opam install -y coq coq-lean-import

# Allow for editing of coq-lean-import more easily
cd /root
ln -s "$(opam var coq-lean-import:build)" coq-lean-import
