#!/bin/sh
BASE="../../../.."
COQCOPTS="-q  -I . -R ../.. FingerTree"

# ML extraction
cd ml
coqc ${COQCOPTS} Extract.v

echo "type ('a, 'b) pair = 'a * 'b" > datatypes.mli2
cat datatypes.mli >> datatypes.mli2
mv datatypes.mli2 datatypes.mli
echo "type ('a, 'b) pair = 'a * 'b" >> datatypes.ml

# Haskell
cd ../hs
coqc ${COQCOPTS} Extract.v

echo "type Pair a b = (a,b)" >> Datatypes.hs
sed -i .bak -e "s/v -> a/a -> v/g" Monoid.hs
