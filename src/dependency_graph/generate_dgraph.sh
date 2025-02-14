#!/bin/bash

# Get the script's directory dynamically
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Define output directory relative to script location
outputDir="$SCRIPT_DIR/../dataset/dependency_graph"
mkdir -p "$outputDir"

# Define project root dynamically
projectRoot="$SCRIPT_DIR/../dataset/raw_data/lf"

echo "Output directory: $outputDir"
echo "Project root: $projectRoot"

# Verify that projectRoot exists before proceeding
if [ ! -d "$projectRoot" ]; then
    echo "Error: Project root directory '$projectRoot' does not exist!"
    exit 1
fi

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
  rm -f temp_$file.v
  rm -f temp_$file.{aux,glob,vo,vok,vos}
  rm -f .temp_$file.{aux,glob,vo,vok,vos}
done

echo "All dependency graphs saved under $outputDir."

# Path for combine_graph.py (relative to script)
combineScript="$SCRIPT_DIR/combine_graph.py"

# Check if combine_graph.py exists before running
if [ -f "$combineScript" ]; then
    echo "Running combine_graph.py..."
    python3 "$combineScript"
else
    echo "Warning: $combineScript not found. Skipping graph combination."
fi

# Remove unnecessary .dpd files, keeping only dgraph.dpd
cd "$outputDir" || exit
find . -type f -name "*.dpd" ! -name "dgraph.dpd" -delete

echo "dgraph.dpd in $outputDir."
