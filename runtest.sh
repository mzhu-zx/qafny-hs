#!/bin/bash

samples=$(cd test/Resource; ls *.qfy)

for f in $samples; do
    test=${f%.*}
    stack run -- $test
    if [ $? -ne 0 ]; then
        echo "Test failed when executing 'stack run -- $test'"
        exit -1
    fi
done
