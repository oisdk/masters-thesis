#!/usr/bin/env bash

# This script creates an Everything.agda file in the agda directory.
# It contains an import statement for every module in the agda/
# directory. This means if you typecheck it it will typecheck every
# agda file.
#
# Run it from *above* the agda/ directory.
cd agda || exit
if [ -f "$1.agda" ]; then
    echo "file agda/$1.agda already exists: you must supply a module name which does not already exist"
    exit 17
fi
everything_file=$(mktemp)
trap 'rm -f $everything_file' 0 2 3 15
find . -type f \( -name "*.agda" -o -name "*.lagda" \) > "$everything_file"
sort -o "$everything_file" "$everything_file"
{
  echo "{-# OPTIONS --cubical --prop #-}"
  echo ""
  echo "module $1 where"
  echo ""
  echo "-- This file imports every module in the project. Click on"
  echo "-- a module name to go to its source."
  echo ""
  cat "$everything_file" | cut -c 3-               \
                         | cut -f1 -d'.'           \
                         | sed 's/\//\./g'         \
                         | sed 's/^/open import /'
} > "$1.agda"
