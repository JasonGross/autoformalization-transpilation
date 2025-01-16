#!/bin/bash

output_file="dgraph.dpd"

> $output_file

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

  cat <<EOF > temp_$file.v
Require dpdgraph.dpdgraph.
From LF Require $file.
Set DependGraph File "temp.dpd".
Print FileDependGraph $file.
EOF

  coqc -R . LF -q temp_$file.v
  
  if [ -f temp.dpd ]; then
    cat temp.dpd >> $output_file
    rm temp.dpd
  fi
  
  rm temp_$file.v
  rm -f temp_$file.{aux,glob,vo,vok,vos}
  rm -f .temp_$file.{aux,glob,vo,vok,vos}
done

sed -i '/MISSING/d' $output_file

echo "Dependency graphs for all files have been appended to $output_file, and lines with 'MISSING' have been removed."
