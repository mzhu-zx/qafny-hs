#!/bin/bash

if [[ -s $1 || -s $2 ]]; then
    echo "Usage: cherry pick from [1] to [2]"
fi

git cherry-pick --strategy=ort --strategy-option=theirs $1...$2
