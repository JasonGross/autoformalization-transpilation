#!/bin/bash
set -e

# opam pin add -yn rocq-lean-import dev

opam install -y coq rocq-lean-import

# Allow for editing of coq-lean-import more easily
cd /root
ln -s "$(opam var rocq-lean-import:build)" coq-lean-import
