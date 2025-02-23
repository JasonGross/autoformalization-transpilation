#!/usr/bin/env bash
cd "$(dirname "${BASH_SOURCE[0]}")"
./make_single_file.py raw_data/lf/_CoqProject $(git ls-files 'raw_data/lf/*.v') -o single_file_data/lf/
./make_single_file.py raw_data/flocq/_CoqProject $(git ls-files --recurse-submodules 'raw_data/flocq/src/*.v' | grep -v _8_12) -o single_file_data/flocq/
(cd raw_data/CompCert && ./configure x86_64-linux -ignore-coq-version)
(cd raw_data/CompCert && make)
./make_single_file.py raw_data/CompCert/_CoqProject $(git ls-files --recurse-submodules 'raw_data/CompCert/*.v') -o single_file_data/CompCert/