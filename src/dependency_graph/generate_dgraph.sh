#!/bin/bash

outputDir="/root/lf/dgraph"
mkdir -p "$outputDir"

declare -A nodeMap
nextId=1

files=(
  "AltAuto" "AltAutoTest" "Auto" "AutoTest" "Basics" "BasicsTest" "Bib" "BibTest"
  "Extraction" "ExtractionTest" "Imp" "ImpCEvalFun" "ImpCEvalFunTest" "ImpParser"
  "ImpParserTest" "IndPrinciples" "IndPrinciplesTest" "Induction" "InductionTest"
  "IndProp" "IndPropTest" "Lists" "ListsTest" "Logic" "LogicTest" "Maps"
  "MapsTest" "Poly" "PolyTest" "Postscript" "PostscriptTest" "Preface"
  "PrefaceTest" "ProofObjects" "ProofObjectsTest" "Rel" "RelTest" "Tactics" "TacticsTest"
)

for file in "${files[@]}"; do
  echo "Processing $file.v..."

  tempDpd="$outputDir/$file.dpd"

  cat <<EOF > temp_$file.v
Require dpdgraph.dpdgraph.
From LF Require $file.
Set DependGraph File "$tempDpd".
Print FileDependGraph $file.
EOF

  coqc -R . LF -q temp_$file.v

  if [ -f "$tempDpd" ]; then
    echo "Dependency graph saved to $tempDpd"
  fi

  rm temp_$file.v
  rm -f temp_$file.{aux,glob,vo,vok,vos}
  rm -f .temp_$file.{aux,glob,vo,vok,vos}
done

echo "All dependency graphs saved under $outputDir."

python3 /root/lf/combine_graph.py

cd "$outputDir"

find . -type f -name "*.dpd" ! -name "dgraph.dpd" -delete

echo "Only dgraph.dpd remains in $outputDir."
