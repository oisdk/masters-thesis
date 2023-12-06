#!/usr/bin/env bash
set -euo pipefail

# This script finds all of the agda snippets included in tex files

grep "\\\ExecuteMetaData\[agda/[^]]*]" -hro ./* --include=\*.tex | cut -c 18- | sed 's/\.tex]$/\.lagda/' | sort | uniq
