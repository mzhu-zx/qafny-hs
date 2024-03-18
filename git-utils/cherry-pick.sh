#!/bin/bash

if [[ -z "$1" || -z "$2" ]]; then
    echo "Usage: cherry pick from [1] to [2]"
    exit -1
fi

git cherry-pick --strategy=ort --strategy-option=theirs $1...$2
