#!/bin/bash

./scripts/init-local-lhs-files.sh

find haskell -type f -name '*.lhs' | while read -r code ; do
    dir=$(dirname "$code")
    file="$dir"/$(basename "$code" .lhs).tex
    if [ ! -e "$file" ]
    then
        ./scripts/haskell-from-toplevel.sh "$code"
    fi
done
