#!/bin/bash

if [[ -z $1 || -z $2 ]]; then
    echo "Usage: replace PATTERN_FROM PATTERN_INTO."
    echo "Find and replace a pattern in all Haskell source files."
    exit -1;
fi

find src/ -name '*.hs' -exec sed -i "s/$1/$2/g" {} \;
