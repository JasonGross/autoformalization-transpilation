#!/bin/bash

# Define output directory
outputDir="/root/autoformalization/src/dataset/dependency_graph"
mkdir -p "$outputDir"

# Get the correct project root dynamically
projectRoot="/root/autoformalization/src/dataset/raw_data/lf"

# Define files to process
files=(
  "AltAuto" "AltAutoTest" "Auto" "AutoTest" "Basics" "BasicsTest" "Bib" "BibTest"
  "Extraction" "ExtractionTest" "Imp" "ImpCEvalFun" "ImpCEvalFunTest" "ImpParser"
  "ImpParserTest" "IndPrinciples" "IndPrinciplesTest" "Induction" "InductionTest"
  "IndProp" "IndPropTest" "Lists" "ListsTest" "Logic" "LogicTest" "Maps"
  "MapsTest" "Poly" "PolyTest" "Postscript" "PostscriptTest" "Preface"
  "PrefaceTest" "ProofObjects" "ProofObjectsTest" "Rel" "RelTest" "Tactics" "TacticsTest"
)

# Process each file
for file in "${files[@]}"; do
  echo "Processing $file.v..."

  tempDpd="$outputDir/$file.dpd"

  # Create a temporary Coq file
  cat <<EOF > temp_$file.v
Require dpdgraph.dpdgraph.
From LF Require $file.
Set DependGraph File "$tempDpd".
Print FileDependGraph $file.
EOF

  # Run coqc with corrected path
  if ! coqc -q -Q "$projectRoot" LF temp_$file.v; then
    echo "Error processing $file.v. Skipping..."
    rm -f temp_$file.v
    continue
  fi

  # Confirm success
  if [ -f "$tempDpd" ]; then
    echo "Dependency graph saved to $tempDpd"
  fi

  # Cleanup temp files
  rm temp_$file.v
  rm -f temp_$file.{aux,glob,vo,vok,vos}
  rm -f .temp_$file.{aux,glob,vo,vok,vos}
done

echo "All dependency graphs saved under $outputDir."

# Check if combine_graph.py exists before running
combineScript="/root/lf/combine_graph.py"
if [ -f "$combineScript" ]; then
  python3 "$combineScript"
else
  echo "Warning: $combineScript not found. Skipping graph combination."
fi

# Remove unnecessary .dpd files, keeping only dgraph.dpd
cd "$outputDir" || exit
find . -type f -name "*.dpd" ! -name "dgraph.dpd" -delete

echo "Only dgraph.dpd remains in $outputDir."
