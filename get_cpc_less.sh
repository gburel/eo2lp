#!/bin/bash
cd ../cvc5 && git pull && cd - || exit 1

# Define source and destination base paths
SRC="../cvc5/proofs/eo/cpc"
DEST="../cpc-less"

# Define directories and their files
declare -A files=(
    ["programs"]="Arith Nary Utils"
    ["rules"]="Arith Booleans Builtin Rewrites Uf"
    ["theories"]="Arith Builtin Ints"
)

# Create directories and copy files
for dir in "${!files[@]}"; do
    mkdir -p "$DEST/$dir"
    for file in ${files[$dir]}; do
        cp "$SRC/$dir/$file.eo" "$DEST/$dir/"
    done
done