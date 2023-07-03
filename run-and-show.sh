#!/bin/bash

target=$1

stack run -- $target

if [[ $? -ne 0 ]]; then
    exit -1
else
    more ./test/Resource/$target.dfy
fi
