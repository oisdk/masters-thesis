#!/bin/bash

if [ ! -f "locallhs2TeX.lhs" ]; then
    echo "%include polycode.fmt" > "locallhs2TeX.lhs"
    echo "%include forall.fmt" >> "locallhs2TeX.lhs"
fi

if [ ! -f "locallhs2TeX.sty" ]; then
    lhs2TeX -o "locallhs2TeX.sty" "locallhs2TeX.lhs"
fi
