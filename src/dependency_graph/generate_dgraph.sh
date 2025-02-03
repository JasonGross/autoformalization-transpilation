#!/bin/bash

output_dir="/root/lf/dgraph"
mkdir -p "$output_dir"

declare -A node_map
next_id=1

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

  temp_dpd="$output_dir/$file.dpd"

  cat <<EOF > temp_$file.v
Require dpdgraph.dpdgraph.
From LF Require $file.
Set DependGraph File "$temp_dpd".
Print FileDependGraph $file.
EOF

  coqc -R . LF -q temp_$file.v

  if [ -f "$temp_dpd" ]; then
    echo "Dependency graph saved to $temp_dpd"
  fi

  rm temp_$file.v
  rm -f temp_$file.{aux,glob,vo,vok,vos}
  rm -f .temp_$file.{aux,glob,vo,vok,vos}
done

echo "All dependency graphs saved under $output_dir."

# Run the script to combine dependency graphs
python3 /root/lf/combine_graph.py

# Navigate to dgraph directory
cd "$output_dir"

# Remove all individual .dpd files except dgraph.dpd
find . -type f -name "*.dpd" ! -name "dgraph.dpd" -delete

echo "Only dgraph.dpd remains in $output_dir."
