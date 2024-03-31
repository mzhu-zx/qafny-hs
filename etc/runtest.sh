#!/bin/bash

samples=$(cd test/Resource; ls *.qfy)

for f in $samples; do
    status="r"
    while [[ $status = "r" ]]; do 
        test=${f%.*}
        stack run -- $test
        if [[ $? -eq 0 ]]; then
            break
        fi
        echo "Test failed when executing 'stack run -- $test'"
        read -n1 \
             -p"Put 's' to skip, 'r' to rety and any other character to exit." \
             status
        echo ""
        if [[ $status = "s" ]]; then
            break
        elif [[ $status != "r" ]]; then
            echo "Test interrupted!"
            exit -1;
        fi
    done
done
