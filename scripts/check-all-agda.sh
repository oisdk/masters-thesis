#!/usr/bin/env bash

sh scripts/generate-everything-agda.sh EveryModule
every_module_file="$(pwd)/agda/EveryModule.agda"
trap "rm -f $every_module_file" 0 2 3 15
cd agda || exit 2
agda EveryModule.agda
