#!/bin/bash

if [[ -z "$1" || -z "$2" ]]; then
    echo "Usage: diff examples between [1] and [2]"
    exit -1
fi

git diff $3 $1..$2 -- . ':!src/' ':!ancilla/' ':!app/' ':!git-utils' ':!notes/' ':!test/'
