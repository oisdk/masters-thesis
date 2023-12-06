#!/usr/bin/env bash
set -euo pipefail

# Agda needs to be run in the source directory of the project to work
# correctly.
# Run this script with a path (like agda/Example.lagda) from the
# directory *above* agda/

cd agda || exit
sh ../scripts/agda-tex.sh "$1"
