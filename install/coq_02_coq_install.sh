#!/bin/bash
set -e

# These commits are not particularly principled

# checkout Coq to c22a07452968a5f7e22720b3b3adaf2710eb27dd
cd /root
git clone https://github.com/coq/coq.git
(cd /root/coq && git checkout c22a07452968a5f7e22720b3b3adaf2710eb27dd)

# checkout vscoq to d5734a0 (d5734a0f458242f26021742623ad632c51e79890)
git clone https://github.com/coq/vscoq.git
(cd /root/vscoq && git checkout d5734a0f458242f26021742623ad632c51e79890)

# passing -n allows pinning multiple repositories simultaneously before installing any of them so that there is less risk of version conflicts
opam pin add -yn --kind=path /root/coq
opam pin add -yn --kind=path /root/vscoq/language-server
opam install -y coq vscoq-language-server coq-dpdgraph
