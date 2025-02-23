#!/bin/bash
set -e

# These commits are not particularly principled

# checkout Coq to 5c7f0150dd555e22b0830d9ca93b8aee5dff4d4c
cd /root
# git clone https://github.com/coq/coq.git
git clone https://github.com/JasonGross/coq.git
# (cd /root/coq && git checkout 5c7f0150dd555e22b0830d9ca93b8aee5dff4d4c)
(cd /root/coq && git checkout unset-universe-checking-qsort)

# checkout vscoq to d5629060e60dc5951dbf5a9c8e446254f667c5d2
git clone https://github.com/coq/vscoq.git
(cd /root/vscoq && git checkout d5629060e60dc5951dbf5a9c8e446254f667c5d2)

# passing -n allows pinning multiple repositories simultaneously before installing any of them so that there is less risk of version conflicts
opam pin add -yn --kind=path /root/coq
opam pin add -yn --kind=path /root/vscoq/language-server
opam pin add -yn menhir 20240715
opam pin add -yn ocamlformat 0.27.0
opam install -y coq vscoq-language-server coq-dpdgraph menhir ocamlformat
