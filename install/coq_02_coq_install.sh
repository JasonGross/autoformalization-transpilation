#!/bin/bash
set -e

# checkout Coq to ac32339 (ac32339db951a48d24ac965a1f36391170c15bce)
cd /root
git clone https://github.com/coq/coq.git
(cd /root/coq && git checkout ac32339db951a48d24ac965a1f36391170c15bce)

# passing -n allows pinning multiple repositories simultaneously before installing any of them so that there is less risk of version conflicts
opam pin add -yn --kind=path /root/coq
opam install -y coq