#!/usr/bin/env bash
set -euo pipefail

cd agda || exit
find . -type f -name '*.lagda' | while read -r code ; do
    dir=$(dirname "$code")
    file=$(basename "$code" .lagda).tex
    if [ ! -e "$dir/$file" ]
    then
        sh ../scripts/agda-tex.sh "agda/$code"
    fi
done
