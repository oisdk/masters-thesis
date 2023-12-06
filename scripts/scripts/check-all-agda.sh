#!/usr/bin/env bash
set -euo pipefail

cd agda || exit 2
sh scripts/check-all.sh
