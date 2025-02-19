#!/bin/bash
set -e

opam pin add -yn rocq-lean-import

opam install -y coq rcoq-lean-import

# Allow for editing of coq-lean-import more easily
cd /root
ln -s "$(opam var rcoq-lean-import:build)" coq-lean-import
