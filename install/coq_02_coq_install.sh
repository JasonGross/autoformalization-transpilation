#!/bin/bash
set -e

# These commits are not particularly principled

# checkout Coq to ac32339 (ac32339db951a48d24ac965a1f36391170c15bce)
cd /root
git clone https://github.com/coq/coq.git
(cd /root/coq && git checkout ac32339db951a48d24ac965a1f36391170c15bce)

# checkout vscoq to d5734a0 (d5734a0f458242f26021742623ad632c51e79890)
git clone https://github.com/coq/vscoq.git
(cd /root/vscoq && git checkout d5734a0f458242f26021742623ad632c51e79890)

# passing -n allows pinning multiple repositories simultaneously before installing any of them so that there is less risk of version conflicts
opam pin add -yn --kind=path /root/coq
opam pin add -yn --kind=path /root/vscoq/language-server
opam install -y coq vscoq-language-server
