#!/bin/bash

target=$1

stack run -- $target

if [[ $1 -ne 0 ]]; then
    exit -1
else
    more ./test/Resource/$target.dfy
fi
