#!/usr/bin/env bash

set -euo pipefail

# This script returns the tags in each lagda file that are not referenced in a .tex file

used_tags=$(mktemp)
trap 'rm -f $used_tags' 0 2 3 15

all_tags=$(mktemp)
trap 'rm -f $all_tags' 0 2 3 15

file_tags=$(mktemp)
trap 'rm -f $file_tags' 0 2 3 15

{ grep "ExecuteMetaData[^}]*}" -hor ./* --include=\*.tex --exclude-dir=agda || test $? = 1; } | cut -c 17- | sort | uniq > "$file_tags"

find agda -type f -name '*.lagda' | while read -r file ; do
  echo "$file"

  tex_file=${file//\.lagda/.tex}

  { grep "%<\*[^>]*>" "$file" -ho || test $? = 1; } | cut -c 4- | sed 's/.$//' | sort | uniq > "$all_tags"
  { grep "$tex_file" "$file_tags" -h || test $? = 1; } | sed -E 's/[^{]*{([^}]*)}/\1/' | sort | uniq > "$used_tags"
  comm -3 "$all_tags" "$used_tags" | sed 's/^/    /'
done
