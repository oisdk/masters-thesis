#!/usr/bin/env bash
set -euo pipefail

# This script finds all literate agda files that are not used
# in a tex file

all_lagda=$(mktemp)
trap 'rm -f $all_lagda' 0 2 3 15
find agda -type f -name "*.lagda" | sort > "$all_lagda"

used_lagda=$(mktemp)
trap 'rm -f $used_lagda' 0 2 3 15
sh scripts/displayed-lagda.sh > "$used_lagda"

comm -23 "$all_lagda" "$used_lagda"
