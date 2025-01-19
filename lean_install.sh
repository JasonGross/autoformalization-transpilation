#!/bin/bash
set -e
# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf > script.sh && chmod +x script.sh && ./script.sh -y

# Install lean4export
cd /root
git clone https://github.com/leanprover/lean4export.git
cd lean4export
git checkout d7978498
. $HOME/.elan/env
lake build