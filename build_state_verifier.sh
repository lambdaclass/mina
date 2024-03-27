#!/bin/sh

if [ ! -d "$(pwd)/_opam" ]; then
  opam switch create ./ 4.14.0 -y
fi
eval $(opam env)
opam switch import opam.export -y
sh scripts/pin-external-packages.sh
make build
cd src/lib/state_verifier
dune build

