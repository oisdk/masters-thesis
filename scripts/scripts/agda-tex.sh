#!/usr/bin/env bash
set -euo pipefail

if [ -x "$(command -v agda-2.6.2)" ]; then
  AGDA='agda-2.6.2'
else
  AGDA='agda'
fi

code="${1#agda/}"
dir=$(dirname "$code")
texfile=$(basename "$code" .lagda).tex
$AGDA --latex --latex-dir=. "$code"
sed -i -e -f ../scripts/replace.sed "$dir/$texfile"
backup="$dir/$texfile-e"
if [ -f "$backup" ] ; then
    rm "$backup"
fi
