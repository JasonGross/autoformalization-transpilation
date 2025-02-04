#!/bin/bash
set -e

# These commits are not particularly principled

# checkout Coq to 5c7f0150dd555e22b0830d9ca93b8aee5dff4d4c
cd /root
git clone https://github.com/coq/coq.git
(cd /root/coq && git checkout 5c7f0150dd555e22b0830d9ca93b8aee5dff4d4c)

# checkout vscoq to 78839d1077bd4ef20a4a91f0478c3c9bd79f1b0f
git clone https://github.com/coq/vscoq.git
(cd /root/vscoq && git checkout 78839d1077bd4ef20a4a91f0478c3c9bd79f1b0f)

# passing -n allows pinning multiple repositories simultaneously before installing any of them so that there is less risk of version conflicts
opam pin add -yn --kind=path /root/coq
opam pin add -yn --kind=path /root/vscoq/language-server
opam install -y coq vscoq-language-server coq-dpdgraph
